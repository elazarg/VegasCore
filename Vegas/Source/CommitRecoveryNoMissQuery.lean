/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryNoMissStep
import Vegas.Source.CommitRecoveryAttemptOrigin
import Vegas.Source.CommitRecoveryErasure
import Vegas.Source.CommitRecoveryBlockPath

/-! # Source query normalization within its actual commitment attempt

Every private typed signal and original action is retained. The public
exclusion controls in one source-time interval are changed together, including
the information tags on all own actions. Source time counts original logical
instructions, independently of native callbacks.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private def attemptSignal (who : Player) (cut : Nat) (excluded : Finset Player) (time : Nat)
    (signal : setup.ProtocolView who × (Finset Player × Nat × Nat)) :=
  (signal.1, if cut ≤ time then (excluded, signal.2.2) else signal.2)

private def attemptWord (who : Player) (cut : Nat) (excluded : Finset Player) :
    List (setup.ProtocolView who × (Finset Player × Nat × Nat)) →
      List (setup.ProtocolView who × (Finset Player × Nat × Nat))
  | [] => []
  | signal :: past => setup.attemptSignal who cut excluded past.length signal ::
      attemptWord who cut excluded past

private theorem attemptWord_length (who : Player) (cut : Nat) (excluded : Finset Player)
    (word : List (setup.ProtocolView who × (Finset Player × Nat × Nat))) :
    (setup.attemptWord who cut excluded word).length = word.length := by
  induction word with
  | nil => rfl
  | cons signal past ih => exact congrArg Nat.succ ih

private theorem attemptSignal_idempotent (who : Player) (cut : Nat) (excluded : Finset Player)
    (time : Nat) (signal : setup.ProtocolView who × (Finset Player × Nat × Nat)) :
    setup.attemptSignal who cut excluded time
        (setup.attemptSignal who cut excluded time signal) =
      setup.attemptSignal who cut excluded time signal := by
  unfold attemptSignal
  split <;> rfl

private theorem attemptWord_idempotent (who : Player) (cut : Nat) (excluded : Finset Player)
    (word : List (setup.ProtocolView who × (Finset Player × Nat × Nat))) :
    setup.attemptWord who cut excluded (setup.attemptWord who cut excluded word) =
      setup.attemptWord who cut excluded word := by
  induction word with
  | nil => rfl
  | cons signal past ih =>
      simp only [attemptWord, setup.attemptWord_length, setup.attemptSignal_idempotent, ih]

private def attemptBase (who : Player) (cut : Nat) (excluded : Finset Player)
    (information : setup.commitRecoverySignals.InfoState who) :
    setup.commitRecoverySignals.InfoState who :=
  (setup.attemptSignal who cut excluded information.2.length information.1,
    setup.attemptWord who cut excluded information.2)

/-- Normalize the exclusion controls from one original source instruction
onward, retaining all typed private views, actions and their complete tags. -/
def commitRecoveryWithAttemptExclusions (who : Player) (cut : Nat) (excluded : Finset Player)
    (information : setup.commitRecoveryModel.InfoState who) :
    setup.commitRecoveryModel.InfoState who :=
  (setup.attemptBase who cut excluded information.1,
    information.2.map (fun record => (setup.attemptBase who cut excluded record.1, record.2)))


/-- Normalization retains the current typed view, both attempt identity fields
and the logical length of the original signal word. -/
theorem commitRecoveryWithAttemptExclusions_controls (who : Player) (cut : Nat)
    (excluded : Finset Player) (information : setup.commitRecoveryModel.InfoState who) :
    (setup.commitRecoveryWithAttemptExclusions who cut excluded information).1.1.1 =
        information.1.1.1 ∧
      (setup.commitRecoveryWithAttemptExclusions who cut excluded information).1.1.2.2 =
        information.1.1.2.2 ∧
      (setup.commitRecoveryWithAttemptExclusions who cut excluded information).1.2.length =
        information.1.2.length := by
  simp only [commitRecoveryWithAttemptExclusions, attemptBase, setup.attemptWord_length,
    attemptSignal]
  split <;> simp

/-- At or after the entry cut, the current signal contains the prescribed
exclusions. Every typed component of that signal is unchanged. -/
theorem commitRecoveryWithAttemptExclusions_current_excluded (who : Player) (cut : Nat)
    (excluded : Finset Player) (information : setup.commitRecoveryModel.InfoState who)
    (inside : cut ≤ information.1.2.length) :
    (setup.commitRecoveryWithAttemptExclusions who cut excluded information).1.1.2.1 =
      excluded := by
  simp only [commitRecoveryWithAttemptExclusions, attemptBase, attemptSignal, inside, ↓reduceIte]

private theorem attemptWord_excluded_at_cut (who : Player) (cut : Nat)
    (excluded : Finset Player)
    (word : List (setup.ProtocolView who × (Finset Player × Nat × Nat)))
    (inside : cut < word.length) :
    ((setup.attemptWord who cut excluded word)[word.length - (cut + 1)]?).map
        (fun signal => signal.2.1) = some excluded := by
  induction word with
  | nil => simp only [List.length_nil] at inside; omega
  | cons signal past ih =>
      by_cases boundary : cut = past.length
      · subst cut
        simp only [List.length_cons, Nat.sub_self, attemptWord,
          List.getElem?_cons_zero, Option.map_some, attemptSignal, le_refl, ↓reduceIte]
      · have earlier : cut < past.length := by simp only [List.length_cons] at inside; omega
        have index : (signal :: past).length - (cut + 1) =
            past.length - (cut + 1) + 1 := by simp only [List.length_cons]; omega
        rw [index, attemptWord, List.getElem?_cons_succ]
        exact ih earlier

/-- The original entry timestamp has exactly the prescribed exclusion set
in the normalized complete signal word. -/
theorem commitRecoveryWithAttemptExclusions_at_cut (who : Player) (cut : Nat)
    (excluded : Finset Player) (information : setup.commitRecoveryModel.InfoState who)
    (inside : cut ≤ information.1.2.length) :
    let normalized := setup.commitRecoveryWithAttemptExclusions who cut excluded information
    ((normalized.1.1 :: normalized.1.2)[information.1.2.length - cut]?).map
      (fun signal => signal.2.1) = some excluded := by
  have index : (information.1.1 :: information.1.2).length - (cut + 1) =
      information.1.2.length - cut := by simp only [List.length_cons]; omega
  have entry := setup.attemptWord_excluded_at_cut who cut excluded
    (information.1.1 :: information.1.2) (by simp only [List.length_cons]; omega)
  rw [index] at entry
  exact entry

private theorem attemptBase_idempotent (who : Player) (cut : Nat) (excluded : Finset Player)
    (information : setup.commitRecoverySignals.InfoState who) :
    setup.attemptBase who cut excluded (setup.attemptBase who cut excluded information) =
      setup.attemptBase who cut excluded information := by
  simp only [attemptBase, setup.attemptWord_length, setup.attemptSignal_idempotent,
    setup.attemptWord_idempotent]

theorem commitRecoveryWithAttemptExclusions_idempotent (who : Player) (cut : Nat)
    (excluded : Finset Player) (information : setup.commitRecoveryModel.InfoState who) :
    setup.commitRecoveryWithAttemptExclusions who cut excluded
        (setup.commitRecoveryWithAttemptExclusions who cut excluded information) =
      setup.commitRecoveryWithAttemptExclusions who cut excluded information := by
  simp only [commitRecoveryWithAttemptExclusions, setup.attemptBase_idempotent, List.map_map]
  congr 1
  apply List.map_congr_left
  intro record _
  exact Prod.ext (setup.attemptBase_idempotent who cut excluded record.1) rfl

private theorem attemptWord_map (who : Player) (cut : Nat) (excluded : Finset Player)
    (transform : setup.ProtocolView who → setup.ProtocolView who)
    (word : List (setup.ProtocolView who × (Finset Player × Nat × Nat))) :
    (setup.attemptWord who cut excluded word).map
        (fun signal => (transform signal.1, signal.2)) =
      setup.attemptWord who cut excluded
        (word.map (fun signal => (transform signal.1, signal.2))) := by
  induction word with
  | nil => rfl
  | cons signal past ih =>
      simp only [attemptWord, List.map_cons, List.length_map]
      rw [ih]
      unfold attemptSignal
      rfl

/-- Erasing retired private words commutes with normalizing the current
attempt's public exclusion scan. Both operations preserve the original input
and every live typed private cell. -/
theorem commitRecoveryWithAttemptExclusions_erased (who : Player) (cut : Nat)
    (excluded : Finset Player) (information : setup.commitRecoveryModel.InfoState who) :
    setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryWithAttemptExclusions who cut excluded information) =
      setup.commitRecoveryWithAttemptExclusions who cut excluded
        (setup.commitRecoveryErasedInformation who information) := by
  unfold commitRecoveryWithAttemptExclusions commitRecoveryErasedInformation
  simp only [List.map_nil, attemptBase, attemptSignal, List.length_map]
  apply Prod.ext
  · apply Prod.ext
    · split <;> rfl
    · exact setup.attemptWord_map who cut excluded
        (Option.map (ProtocolView.publicOnly who setup.program)) information.1.2
  · rfl

private theorem attemptWord_before (who : Player) (cut : Nat) (excluded : Finset Player)
    (word : List (setup.ProtocolView who × (Finset Player × Nat × Nat)))
    (before : word.length ≤ cut) : setup.attemptWord who cut excluded word = word := by
  induction word with
  | nil => rfl
  | cons signal past ih =>
      have earlier : ¬ cut ≤ past.length := by simp only [List.length_cons] at before; omega
      simp only [attemptWord, attemptSignal, earlier, ↓reduceIte]
      rw [ih (by simp only [List.length_cons] at before; omega)]

private theorem attemptBase_before (who : Player) (cut : Nat) (excluded : Finset Player)
    (information : setup.commitRecoverySignals.InfoState who)
    (before : information.2.length < cut) :
    setup.attemptBase who cut excluded information = information := by
  have earlier : ¬ cut ≤ information.2.length := by omega
  simp only [attemptBase, attemptSignal, earlier, ↓reduceIte,
    setup.attemptWord_before who cut excluded information.2 (by omega), Prod.eta]

private theorem signal_word_length (who : Player) :
    ∀ {state : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace state),
      (setup.commitRecoverySignals.infoOf who trace).2.length = trace.length
  | _, .start => rfl
  | _, .extend prior joint legal supported => by
      rw [InfoSignals.infoOf_extend]
      exact congrArg Nat.succ (signal_word_length who prior)

private theorem own_record_before (who : Player) :
    ∀ {state : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace state)
      (record : setup.commitRecoverySignals.InfoState who × CommitRecoveryMove Player L),
      record ∈ setup.commitRecoverySignals.ownPlay who trace → record.1.2.length < trace.length
  | _, .start, _, member => by cases member
  | _, .extend prior joint legal supported, record, member => by
      rw [InfoSignals.ownPlay_extend] at member
      cases chosen : joint who with
      | none =>
          simp only [chosen] at member
          have earlier := own_record_before who prior record member
          simp only [Trace.length]
          omega
      | some action =>
          simp only [chosen, List.mem_cons] at member
          rcases member with same | earlier
          · subst record
            rw [setup.signal_word_length who prior]
            exact Nat.lt_succ_self _
          · have bound := own_record_before who prior record earlier
            simp only [Trace.length]
            omega

/-- At the literal saved entry, the normalizer is the identity on the actual
entire source query, including the private words and all old own-play tags. -/
theorem commitRecoveryWithAttemptExclusions_at_entry (who : Player)
    (entry : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some entry)) :
    setup.commitRecoveryWithAttemptExclusions who prior.length entry.excluded
        (setup.commitRecoveryModel.infoOf who prior) =
      setup.commitRecoveryModel.infoOf who prior := by
  change setup.commitRecoveryWithAttemptExclusions who prior.length entry.excluded
    (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who prior) =
      setup.commitRecoverySignals.withOwnPlayRecall.infoOf who prior
  rw [InfoSignals.withOwnPlayRecall_infoOf]
  apply Prod.ext
  · simp only [commitRecoveryWithAttemptExclusions, attemptBase,
      setup.signal_word_length who prior,
      setup.attemptWord_before who prior.length entry.excluded _ (by
        rw [setup.signal_word_length who prior]), attemptSignal, le_refl, ↓reduceIte]
    apply Prod.ext
    · have current := setup.commitRecoverySignals_current who prior
      have recordedE :
          (setup.commitRecoverySignals.infoOf who prior).1.2.1 = entry.excluded := by
        simpa only [commitRecoveryPublic] using
          congrArg (fun signal => signal.2.1) current
      exact Prod.ext rfl (Prod.ext recordedE.symm rfl)
    · rfl
  · change (setup.commitRecoverySignals.ownPlay who prior).map
      (fun record => (setup.attemptBase who prior.length entry.excluded record.1, record.2)) = _
    calc
      _ = (setup.commitRecoverySignals.ownPlay who prior).map id := by
        apply List.map_congr_left
        intro record member
        exact Prod.ext (setup.attemptBase_before who prior.length entry.excluded record.1
          (setup.own_record_before who prior record member)) rfl
      _ = _ := by simp only [List.map_id]


/-- Extending two actual source traces preserves their same current-attempt
exclusion-normalization relation, with the original own action retained. -/
theorem normalized_information_extend (who : Player) (cut : Nat)
    (excluded : Finset Player)
    {leftSource leftTarget rightSource rightTarget : setup.commitRecoveryProtocol.State}
    (left : setup.commitRecoveryProtocol.Trace leftSource)
    (right : setup.commitRecoveryProtocol.Trace rightSource)
    (leftJoint rightJoint : Player → Option (CommitRecoveryMove Player L))
    (leftLegal : setup.commitRecoveryProtocol.Legal leftSource leftJoint)
    (rightLegal : setup.commitRecoveryProtocol.Legal rightSource rightJoint)
    (leftSupport : leftTarget ∈
      (setup.commitRecoveryProtocol.step leftSource ⟨leftJoint, leftLegal⟩).support)
    (rightSupport : rightTarget ∈
      (setup.commitRecoveryProtocol.step rightSource ⟨rightJoint, rightLegal⟩).support)
    (previous : setup.commitRecoveryModel.infoOf who right =
      setup.commitRecoveryWithAttemptExclusions who cut excluded
        (setup.commitRecoveryModel.infoOf who left))
    (ownChoice : rightJoint who = leftJoint who)
    (signal : (setup.commitRecoveryPrivate who rightTarget,
        setup.commitRecoveryPublic rightTarget) =
      setup.attemptSignal who cut excluded (left.length + 1)
        (setup.commitRecoveryPrivate who leftTarget, setup.commitRecoveryPublic leftTarget)) :
    setup.commitRecoveryModel.infoOf who (right.extend rightJoint rightLegal rightSupport) =
      setup.commitRecoveryWithAttemptExclusions who cut excluded
        (setup.commitRecoveryModel.infoOf who (left.extend leftJoint leftLegal leftSupport)) := by
  change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who _) =
    setup.commitRecoveryWithAttemptExclusions who cut excluded
      (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who _)
  rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf]
  change setup.commitRecoverySignals.withOwnPlayRecall.infoOf who right =
    setup.commitRecoveryWithAttemptExclusions who cut excluded
      (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who left) at previous
  rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf] at previous
  have base := congrArg Prod.fst previous
  have record := congrArg Prod.snd previous
  change setup.commitRecoverySignals.infoOf who right =
    setup.attemptBase who cut excluded (setup.commitRecoverySignals.infoOf who left) at base
  change setup.commitRecoverySignals.ownPlay who right =
    (setup.commitRecoverySignals.ownPlay who left).map
      (fun record => (setup.attemptBase who cut excluded record.1, record.2)) at record
  apply Prod.ext
  · rw [InfoSignals.infoOf_extend, InfoSignals.infoOf_extend]
    change ((setup.commitRecoveryPrivate who rightTarget,
        setup.commitRecoveryPublic rightTarget),
      (setup.commitRecoverySignals.infoOf who right).1 ::
        (setup.commitRecoverySignals.infoOf who right).2) = _
    rw [base]
    simp only [commitRecoveryWithAttemptExclusions, attemptBase]
    change ((setup.commitRecoveryPrivate who rightTarget,
      setup.commitRecoveryPublic rightTarget), _) =
      (setup.attemptSignal who cut excluded
        ((setup.commitRecoverySignals.infoOf who left).2.length + 1)
        (setup.commitRecoveryPrivate who leftTarget, setup.commitRecoveryPublic leftTarget), _)
    rw [setup.signal_word_length who left]
    apply Prod.ext signal
    change setup.attemptSignal who cut excluded left.length
        (setup.commitRecoverySignals.infoOf who left).1 :: _ =
      setup.attemptSignal who cut excluded
        (setup.commitRecoverySignals.infoOf who left).2.length
        (setup.commitRecoverySignals.infoOf who left).1 :: _
    rw [setup.signal_word_length who left]
  · rw [InfoSignals.ownPlay_extend, InfoSignals.ownPlay_extend, ownChoice]
    cases leftJoint who with
    | none => exact record
    | some action =>
        change (_, _) :: _ = (_, _) :: _
        rw [base, record]

/-- Every genuine prefix strictly inside a commitment attempt has a genuine
replay from the literal saved history with no new omissions. The entire
information state, including all own-play tags, is the normalized original. -/
theorem commitRecovery_noMiss_prefix_information (who : Player)
    (point : SourceProgram.ProtocolState setup.program)
    (excluded : Finset Player) (generation : Nat)
    (prior : setup.commitRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint point excluded generation)))
    (committing : ProtocolState.atCommit setup.program point = true)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) (retained : TracePrefix prior trace)
    (inside : trace.length + ProtocolState.commitEnd setup.program point <
      prior.length + ProtocolState.remaining setup.program point)
    (survives : who ∉ (setup.commitRecoveryPublic state).1) :
    ∃ current replay : CommitRecoveryState setup.program,
      state = some current ∧ current.saved = point ∧
      current.entryExcluded = excluded ∧ current.generation = generation ∧
      ∃ replayTrace : setup.commitRecoveryProtocol.Trace (some replay),
        TracePrefix prior replayTrace ∧ replayTrace.length = trace.length ∧
        replay.saved = point ∧ replay.entryExcluded = excluded ∧
        replay.generation = generation ∧ replay.excluded = excluded ∧
        ProtocolState.observe who setup.program replay.point =
          ProtocolState.observe who setup.program current.point ∧
        setup.commitRecoveryModel.infoOf who replayTrace =
          setup.commitRecoveryWithAttemptExclusions who prior.length excluded
            (setup.commitRecoveryModel.infoOf who trace) := by
  induction retained with
  | refl =>
      exact ⟨_, _, rfl, rfl, rfl, rfl, prior, .refl, rfl,
        rfl, rfl, rfl, rfl, rfl,
        (setup.commitRecoveryWithAttemptExclusions_at_entry who _ prior).symm⟩
  | @extend source target earlier kept joint legal reached ih =>
      have previousInside : earlier.length + ProtocolState.commitEnd setup.program point <
          prior.length + ProtocolState.remaining setup.program point := by
        simp only [Trace.length] at inside
        omega
      have previousSurvives : who ∉ (setup.commitRecoveryPublic source).1 := fun member =>
        survives (setup.commitRecovery_step_excluded_subset joint legal reached member)
      obtain ⟨current, replay, rfl, saved, entryE, gen, replayTrace, replayKept, lengths,
          replaySaved, replayEntry, replayGen, replayE, views, information⟩ :=
        ih previousInside previousSurvives
      obtain ⟨middle, same, middleCommit, middleEnd, rank⟩ :=
        setup.commitRecovery_prefix_inside_commit
          (CommitRecoveryState.atPoint point excluded generation) prior committing
          earlier kept previousInside
      have equal := Option.some.inj same
      subst middle
      change _ ∈ ((current.step joint).map some).support at reached
      obtain ⟨next, nextSupport, rfl⟩ :=
        (PMF.mem_support_map_iff some (current.step joint) _).mp reached
      obtain ⟨raw, rawMember, nextEq⟩ :=
        (PMF.mem_support_map_iff _ _ _).mp nextSupport
      have rawSupport : raw.1 ∈
          (ProtocolState.recoveryStep setup.program current.point current.excluded joint).support :=
        by
        rw [← map_val_pmfToSubtype
          (ProtocolState.recoveryStep setup.program current.point current.excluded joint)
          (fun result supported => ProtocolState.recoveryStep_excluded_monotone setup.program
            current.point current.excluded joint result supported)]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨raw, rawMember, rfl⟩
      have rawSurvives : who ∉ raw.1.2 := by
        change who ∉ next.excluded at survives
        simpa only [← nextEq, CommitRecoveryState.close_excluded,
          CommitRecoveryState.install] using survives
      have currentSurvives : who ∉ current.excluded := previousSurvives
      have savedSurvives : who ∉ excluded := by
        intro member
        exact currentSurvives (current.entered (entryE.symm ▸ member))
      obtain ⟨right, rightLegal, ownChoice, noMiss, rightRaw, rightSupport,
          nextViews, rightE⟩ := CommitRecoveryState.noMiss_instruction who current replay views.symm
        middleCommit
        currentSurvives (replayE.symm ▸ savedSurvives) joint legal.2 raw.1 rawSupport rawSurvives
      have running : ¬ ProtocolState.terminal setup.program current.point := legal.1
      have rawRank := ProtocolState.recoveryStep_remaining setup.program current.point
        current.excluded joint raw.1 running rawSupport
      change earlier.length + ProtocolState.remaining setup.program current.point =
        prior.length + ProtocolState.remaining setup.program point at rank
      have rawInside : ProtocolState.commitEnd setup.program point <
          ProtocolState.remaining setup.program raw.1.1 := by
        simp only [Trace.length] at inside
        omega
      have sameRemaining : ProtocolState.remaining setup.program raw.1.1 =
          ProtocolState.remaining setup.program rightRaw.1 := by
        have leftRank := ProtocolView.position_add_remaining who setup.program raw.1.1
        have rightRank := ProtocolView.position_add_remaining who setup.program rightRaw.1
        have samePosition := congrArg (ProtocolView.position who setup.program) nextViews
        omega
      let rightImage := replay.install rightRaw
        (ProtocolState.recoveryStep_excluded_monotone setup.program replay.point replay.excluded
          right rightRaw rightSupport)
      have leftClose : (current.install raw.1 raw.2).close = current.install raw.1 raw.2 :=
        (current.install raw.1 raw.2).close_eq_self_of_remaining_gt
          (saved.symm ▸ committing) (saved.symm ▸ rawInside)
      have rightClose : rightImage.close = rightImage :=
        rightImage.close_eq_self_of_remaining_gt (replaySaved.symm ▸ committing) (by
          change ProtocolState.commitEnd setup.program replay.saved <
            ProtocolState.remaining setup.program rightRaw.1
          rw [replaySaved, ← sameRemaining]
          exact rawInside)
      have rightImageSupport : rightImage.close ∈ (replay.step right).support := by
        let law := ProtocolState.recoveryStep setup.program replay.point replay.excluded right
        let keep := fun result (member : result ∈ law.support) =>
          ProtocolState.recoveryStep_excluded_monotone setup.program replay.point
            replay.excluded right result member
        have member : rightRaw ∈ ((pmfToSubtype law keep).map Subtype.val).support := by
          rw [map_val_pmfToSubtype]
          exact rightSupport
        obtain ⟨sample, sampleMember, sampleEq⟩ := (PMF.mem_support_map_iff _ _ _).mp member
        apply (PMF.mem_support_map_iff _ _ _).mpr
        refine ⟨sample, sampleMember, ?_⟩
        have equal : sample = ⟨rightRaw, keep rightRaw rightSupport⟩ := Subtype.ext sampleEq
        cases equal
        rfl
      rw [rightClose] at rightImageSupport
      have rightProtocolLegal : setup.commitRecoveryProtocol.Legal (some replay) right := by
        refine ⟨?_, rightLegal⟩
        have replayCommit : ProtocolState.atCommit setup.program replay.point = true := by
          rw [← ProtocolState.atCommit_observe setup.program replay.point who, views,
            ProtocolState.atCommit_observe, middleCommit]
        intro terminal
        have zero := (ProtocolState.remaining_zero_iff_terminal setup.program replay.point).mpr
          terminal
        have positive := ProtocolState.commitEnd_lt_remaining setup.program replay.point
          replayCommit
        omega
      have rightProtocolSupport : some rightImage ∈
          (setup.commitRecoveryProtocol.step (some replay) ⟨right, rightProtocolLegal⟩).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨rightImage, rightImageSupport, rfl⟩
      let finalTrace := replayTrace.extend right rightProtocolLegal rightProtocolSupport
      rw [leftClose] at nextEq
      subst next
      refine ⟨_, rightImage, rfl, saved, entryE, gen, finalTrace,
        .extend replayKept right rightProtocolLegal rightProtocolSupport, ?_,
        replaySaved, replayEntry, replayGen, ?_, nextViews.symm, ?_⟩
      · simp only [finalTrace, Trace.length, lengths]
      · exact rightE.trans replayE
      · apply setup.normalized_information_extend who prior.length excluded earlier replayTrace
          joint right legal rightProtocolLegal reached rightProtocolSupport information ownChoice
        have time : prior.length ≤ earlier.length + 1 := by
          have bound := kept.length_le
          omega
        simp only [attemptSignal, time, ↓reduceIte, commitRecoveryPrivate, Option.map_some,
          commitRecoveryPublic, CommitRecoveryState.install, rightImage,
          rightE, replayE, replayGen, gen, replaySaved, saved, nextViews]

end Vegas.SourceProgram.Setup
