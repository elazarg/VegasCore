/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryNoMissQuery

/-! # A genuine no-new-omission source query from the original full information

The current instruction position and the public saved rank determine the
literal source-time cut. The saved exclusion set is read from that position
in the original signal word. No independently chosen source history enters
the definition.
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolView

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem position_erased (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (view : ProtocolView who program),
      position who program (eraseHistory who program view) = position who program view
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, view => by
      cases view <;> simp only [eraseHistory, position, Sum.elim_inl, Sum.elim_inr,
        position_erased who next]
  | _, _, .commit _ _ _ _ next, view => by
      cases view <;> simp only [eraseHistory, position, Sum.elim_inl, Sum.elim_inr,
        position_erased who next]
  | _, _, .reveal _ _ _ _ _ _ next, view => by
      cases view <;> simp only [eraseHistory, position, Sum.elim_inl, Sum.elim_inr,
        position_erased who next]

end Vegas.SourceProgram.ProtocolView

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- The logical time at which the currently saved attempt began. -/
def commitRecoveryAttemptStart (who : Player)
    (information : setup.commitRecoveryModel.InfoState who) : Nat :=
  information.1.2.length -
    ((information.1.1.1.map (ProtocolView.position who setup.program)).getD 0 -
      information.1.1.2.2.2)

/-- The exclusions observed at the saved attempt's genuine entry signal. -/
def commitRecoverySavedExclusions (who : Player)
    (information : setup.commitRecoveryModel.InfoState who) : Finset Player :=
  (((information.1.1 :: information.1.2)[information.1.2.length -
      setup.commitRecoveryAttemptStart who information]?).map
    (fun signal => signal.2.1)).getD information.1.1.2.1

/-- Remove only new exclusions in the current commitment segment, in every
original signal and every own-play tag. All typed cells and actions remain. -/
def commitRecoveryNoMissInformation (who : Player)
    (information : setup.commitRecoveryModel.InfoState who) :
    setup.commitRecoveryModel.InfoState who :=
  if information.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true ∧
      who ∉ information.1.1.2.1 ∧
      who ∉ setup.commitRecoverySavedExclusions who information then
    setup.commitRecoveryWithAttemptExclusions who
      (setup.commitRecoveryAttemptStart who information)
      (setup.commitRecoverySavedExclusions who information) information
  else information


private theorem attemptStart_normalized (who : Player) (cut : Nat) (excluded : Finset Player)
    (information : setup.commitRecoveryModel.InfoState who) :
    setup.commitRecoveryAttemptStart who
        (setup.commitRecoveryWithAttemptExclusions who cut excluded information) =
      setup.commitRecoveryAttemptStart who information := by
  obtain ⟨view, controls, length⟩ :=
    setup.commitRecoveryWithAttemptExclusions_controls who cut excluded information
  unfold commitRecoveryAttemptStart
  rw [view, length, controls]

private theorem savedExclusions_normalized (who : Player)
    (information : setup.commitRecoveryModel.InfoState who) :
    setup.commitRecoverySavedExclusions who
        (setup.commitRecoveryWithAttemptExclusions who
          (setup.commitRecoveryAttemptStart who information)
          (setup.commitRecoverySavedExclusions who information) information) =
      setup.commitRecoverySavedExclusions who information := by
  have bound : setup.commitRecoveryAttemptStart who information ≤ information.1.2.length :=
    Nat.sub_le _ _
  have entry := setup.commitRecoveryWithAttemptExclusions_at_cut who
    (setup.commitRecoveryAttemptStart who information)
    (setup.commitRecoverySavedExclusions who information) information bound
  let normalized := setup.commitRecoveryWithAttemptExclusions who
    (setup.commitRecoveryAttemptStart who information)
    (setup.commitRecoverySavedExclusions who information) information
  change (((normalized.1.1 :: normalized.1.2)[normalized.1.2.length -
    setup.commitRecoveryAttemptStart who normalized]?).map
      (fun signal => signal.2.1)).getD normalized.1.1.2.1 =
        setup.commitRecoverySavedExclusions who information
  rw [setup.attemptStart_normalized,
    (setup.commitRecoveryWithAttemptExclusions_controls who _ _ information).2.2]
  exact congrArg (fun result => result.getD normalized.1.1.2.1) entry

private theorem attemptStart_erased (who : Player)
    (information : setup.commitRecoveryModel.InfoState who) :
    setup.commitRecoveryAttemptStart who
        (setup.commitRecoveryErasedInformation who information) =
      setup.commitRecoveryAttemptStart who information := by
  unfold commitRecoveryAttemptStart commitRecoveryErasedInformation
  simp only [List.length_map, Option.map_map, Function.comp_def]
  congr 3
  cases information.1.1.1 with
  | none => rfl
  | some view =>
      simpa only [Option.map_some] using
        congrArg some (ProtocolView.position_erased who setup.program view)

private theorem savedExclusions_erased (who : Player)
    (information : setup.commitRecoveryModel.InfoState who) :
    setup.commitRecoverySavedExclusions who
        (setup.commitRecoveryErasedInformation who information) =
      setup.commitRecoverySavedExclusions who information := by
  unfold commitRecoverySavedExclusions
  rw [setup.attemptStart_erased]
  unfold commitRecoveryErasedInformation
  simp only [List.length_map]
  have controls : ∀ (current : setup.ProtocolView who × (Finset Player × Nat × Nat))
      (past : List (setup.ProtocolView who × (Finset Player × Nat × Nat))) (index : Nat),
      ((((current.1.map (ProtocolView.eraseHistory who setup.program), current.2) ::
          past.map (fun signal =>
            (signal.1.map (ProtocolView.publicOnly who setup.program), signal.2)))[index]?).map
          (fun signal => signal.2.1)) =
        ((current :: past)[index]?).map (fun signal => signal.2.1) := by
    intro current past index
    cases index with
    | zero => rfl
    | succ index =>
        simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_map,
          Function.comp_def]
  rw [controls]

/-- Normalizing a source query twice is exactly the same full information
state. The source information model itself is unchanged. -/
theorem commitRecoveryNoMissInformation_idempotent (who : Player)
    (information : setup.commitRecoveryModel.InfoState who) :
    setup.commitRecoveryNoMissInformation who
        (setup.commitRecoveryNoMissInformation who information) =
      setup.commitRecoveryNoMissInformation who information := by
  unfold commitRecoveryNoMissInformation
  split
  · rename_i original
    split
    · rw [setup.attemptStart_normalized, setup.savedExclusions_normalized,
        setup.commitRecoveryWithAttemptExclusions_idempotent]
    · rfl
  · rfl

/-- Current-attempt omission normalization commutes with erasing remembered
private source words. The exact original public chronology is retained. -/
theorem commitRecoveryNoMissInformation_erased (who : Player)
    (information : setup.commitRecoveryModel.InfoState who) :
    setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who information) =
      setup.commitRecoveryNoMissInformation who
        (setup.commitRecoveryErasedInformation who information) := by
  have condition :
      (setup.commitRecoveryErasedInformation who information).1.1.1.elim false
          (ProtocolView.atCommit who setup.program) =
        information.1.1.1.elim false (ProtocolView.atCommit who setup.program) := by
    change (information.1.1.1.map (ProtocolView.eraseHistory who setup.program)).elim false
      (ProtocolView.atCommit who setup.program) = _
    cases information.1.1.1 with
    | none => rfl
    | some view => exact ProtocolView.atCommit_eraseHistory who setup.program view
  unfold commitRecoveryNoMissInformation
  rw [condition, setup.savedExclusions_erased]
  change setup.commitRecoveryErasedInformation who (if _ then _ else _) =
    if _ then _ else _
  split
  · rw [ite_eq_left (by assumption), setup.attemptStart_erased,
      setup.commitRecoveryWithAttemptExclusions_erased]
  · rw [ite_eq_right (by assumption)]

/-- Equal live reads and complete old public windows give equal normalized
queries. Current-attempt exclusions may differ, while the genuine saved-entry
depth and exclusions remain fixed. -/
theorem commitRecoveryNoMissInformation_eq_of_window (who : Player)
    (left right : setup.commitRecoveryModel.InfoState who)
    (cut : Nat) (excluded : Finset Player)
    (leftOwn : left.2 = []) (rightOwn : right.2 = [])
    (leftCommit : left.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true)
    (rightCommit : right.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true)
    (leftActive : who ∉ left.1.1.2.1) (rightActive : who ∉ right.1.1.2.1)
    (entryActive : who ∉ excluded)
    (leftCut : setup.commitRecoveryAttemptStart who left = cut)
    (rightCut : setup.commitRecoveryAttemptStart who right = cut)
    (leftEntry : setup.commitRecoverySavedExclusions who left = excluded)
    (rightEntry : setup.commitRecoverySavedExclusions who right = excluded)
    (controls : List.Forall₂ (fun first second =>
      first.1 = second.1 ∧ first.2.2 = second.2.2)
        (left.1.1 :: left.1.2) (right.1.1 :: right.1.2))
    (past : (left.1.1 :: left.1.2).reverse.take cut =
      (right.1.1 :: right.1.2).reverse.take cut) :
    setup.commitRecoveryNoMissInformation who left =
      setup.commitRecoveryNoMissInformation who right := by
  have leftGuard : left.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true ∧
      who ∉ left.1.1.2.1 ∧ who ∉ setup.commitRecoverySavedExclusions who left := by
    exact ⟨leftCommit, leftActive, leftEntry.symm ▸ entryActive⟩
  have rightGuard : right.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true ∧
      who ∉ right.1.1.2.1 ∧ who ∉ setup.commitRecoverySavedExclusions who right := by
    exact ⟨rightCommit, rightActive, rightEntry.symm ▸ entryActive⟩
  unfold commitRecoveryNoMissInformation
  rw [ite_eq_left leftGuard, ite_eq_left rightGuard, leftCut, rightCut, leftEntry, rightEntry]
  exact setup.commitRecoveryWithAttemptExclusions_eq_of_window who cut excluded
    left right leftOwn rightOwn controls past

/-- The total transformation preserves the original legal source menu, even
at labels that are not produced by a source history. -/
theorem commitRecoveryNoMissInformation_menu (who : Player)
    (information : setup.commitRecoveryModel.InfoState who) :
    setup.commitRecoveryModel.menu who (setup.commitRecoveryNoMissInformation who information) =
      setup.commitRecoveryModel.menu who information := by
  unfold commitRecoveryNoMissInformation
  split
  · rename_i normalized
    have view := (setup.commitRecoveryWithAttemptExclusions_controls who
      (setup.commitRecoveryAttemptStart who information)
      (setup.commitRecoverySavedExclusions who information) information).1
    have excluded := setup.commitRecoveryWithAttemptExclusions_current_excluded who
      (setup.commitRecoveryAttemptStart who information)
      (setup.commitRecoverySavedExclusions who information) information (Nat.sub_le _ _)
    ext choice
    change setup.commitRecoveryMenu who _ choice ↔ setup.commitRecoveryMenu who _ choice
    cases choice <;> simp only [commitRecoveryMenu, commitRecoveryActive, view, excluded,
      normalized.2.1, normalized.2.2, not_false_eq_true, and_true]
  · rfl

/-- Choices at the normalized query and the original full source query have
exactly the same underlying action, with their actual menu proofs. -/
def commitRecoveryNoMissChoice (who : Player)
    (information : setup.commitRecoveryModel.InfoState who) :
    setup.commitRecoveryModel.Choice who information ≃
      setup.commitRecoveryModel.Choice who
        (setup.commitRecoveryNoMissInformation who information) where
  toFun choice := ⟨choice.1, by
    rw [setup.commitRecoveryNoMissInformation_menu who information]
    exact choice.2⟩
  invFun choice := ⟨choice.1, by
    rw [← setup.commitRecoveryNoMissInformation_menu who information]
    exact choice.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual reduced query obtained by both transformations is an
idempotent label on the original source information space. -/
theorem commitRecoveryNoMissInformation_erased_idempotent (who : Player)
    (information : setup.commitRecoveryModel.InfoState who) :
    setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who
          (setup.commitRecoveryErasedInformation who
            (setup.commitRecoveryNoMissInformation who information))) =
      setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who information) := by
  rw [← setup.commitRecoveryNoMissInformation_erased,
    setup.commitRecoveryNoMissInformation_idempotent,
    setup.commitRecoveryErasedInformation_idempotent]

/-- The combined reduced query transports the actual original source choice
without changing its underlying action. -/
def commitRecoveryNoMissErasedChoice (who : Player)
    (information : setup.commitRecoveryModel.InfoState who) :
    setup.commitRecoveryModel.Choice who information ≃
      setup.commitRecoveryModel.Choice who
        (setup.commitRecoveryErasedInformation who
          (setup.commitRecoveryNoMissInformation who information)) :=
  (setup.commitRecoveryNoMissChoice who information).trans
    (setup.commitRecoveryErasedChoice who (setup.commitRecoveryNoMissInformation who information))

/-- No source instruction is inserted or deleted by the global query map. -/
theorem commitRecoveryNoMissInformation_word_length (who : Player)
    (information : setup.commitRecoveryModel.InfoState who) :
    (setup.commitRecoveryNoMissInformation who information).1.2.length =
      information.1.2.length := by
  unfold commitRecoveryNoMissInformation
  split
  · exact (setup.commitRecoveryWithAttemptExclusions_controls who _ _ information).2.2
  · rfl

/-- The combined key has the original full source logical clock, including
passive transitions, retries and exhausted restore. -/
theorem commitRecoveryNoMissInformation_erased_word_length (who : Player)
    (information : setup.commitRecoveryModel.InfoState who) :
    (setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who information)).1.2.length =
      information.1.2.length := by
  change ((setup.commitRecoveryNoMissInformation who information).1.2.map _).length = _
  rw [List.length_map, setup.commitRecoveryNoMissInformation_word_length]

private theorem model_base (who : Player) {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.commitRecoveryModel.infoOf who trace).1 =
      setup.commitRecoverySignals.infoOf who trace := by
  change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who trace).1 = _
  rw [InfoSignals.withOwnPlayRecall_infoOf]

private theorem signal_length (who : Player) :
    ∀ {state : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace state),
      (setup.commitRecoverySignals.infoOf who trace).2.length = trace.length
  | _, .start => rfl
  | _, .extend prior joint legal support => by
      rw [InfoSignals.infoOf_extend]
      exact congrArg Nat.succ (signal_length who prior)

private theorem prior_signal (who : Player)
    {first last : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace first)
    (trace : setup.commitRecoveryProtocol.Trace last) (retained : TracePrefix prior trace) :
    (((setup.commitRecoverySignals.infoOf who trace).1 ::
        (setup.commitRecoverySignals.infoOf who trace).2)[trace.length - prior.length]?) =
      some (setup.commitRecoverySignals.infoOf who prior).1 := by
  induction retained with
  | refl => simp only [Nat.sub_self, List.getElem?_cons_zero]
  | @extend source target earlier kept joint legal support ih =>
      rw [InfoSignals.infoOf_extend]
      have index : earlier.length + 1 - prior.length = earlier.length - prior.length + 1 := by
        have bound := kept.length_le
        omega
      change (_ :: (setup.commitRecoverySignals.infoOf who earlier).1 ::
        (setup.commitRecoverySignals.infoOf who earlier).2)[earlier.length + 1 - prior.length]? = _
      rw [index, List.getElem?_cons_succ]
      exact ih

/-- The cut read from full source information is the literal retained entry
history, not an arbitrary earlier checkpoint at the same rank. -/
theorem commitRecoveryAttemptStart_of_entry (who : Player)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (prior : setup.commitRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint current.saved current.entryExcluded current.generation)))
    (retained : TracePrefix prior trace)
    (rank : trace.length + ProtocolState.remaining setup.program current.point =
      prior.length + ProtocolState.remaining setup.program current.saved) :
    setup.commitRecoveryAttemptStart who (setup.commitRecoveryModel.infoOf who trace) =
      prior.length := by
  unfold commitRecoveryAttemptStart
  rw [setup.model_base who trace, setup.signal_length who trace,
    setup.commitRecoverySignals_current who trace]
  simp only [commitRecoveryPrivate, Option.map_some, Option.getD_some, commitRecoveryPublic]
  have position := ProtocolView.position_add_remaining who setup.program current.point
  have savedBound := ProtocolState.remaining_le_instructionCount setup.program current.saved
  have timeBound := retained.length_le
  omega

/-- The exclusion set read at that cut is exactly the saved entry exclusions,
with later in-attempt omissions retained elsewhere in the original query. -/
theorem commitRecoverySavedExclusions_of_entry (who : Player)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (prior : setup.commitRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint current.saved current.entryExcluded current.generation)))
    (retained : TracePrefix prior trace)
    (rank : trace.length + ProtocolState.remaining setup.program current.point =
      prior.length + ProtocolState.remaining setup.program current.saved) :
    setup.commitRecoverySavedExclusions who (setup.commitRecoveryModel.infoOf who trace) =
      current.entryExcluded := by
  unfold commitRecoverySavedExclusions
  rw [setup.commitRecoveryAttemptStart_of_entry who current trace prior retained rank,
    setup.model_base who trace, setup.signal_length who trace,
    setup.prior_signal who prior trace retained, setup.commitRecoverySignals_current who prior]
  rfl

/-- At every actual surviving commitment query, the global transformation is
the full information of a genuine replay from the same literal saved history.
Accepted failed values and the original earlier public chronology are kept. -/
theorem commitRecoveryNoMissInformation_genuine (who : Player)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (survives : who ∉ current.excluded) :
    ∃ replay : CommitRecoveryState setup.program,
      ∃ replayTrace : setup.commitRecoveryProtocol.Trace (some replay),
        replay.excluded = current.entryExcluded ∧
        replay.entryExcluded = current.entryExcluded ∧
        replay.saved = current.saved ∧ replay.generation = current.generation ∧
        ProtocolState.observe who setup.program replay.point =
          ProtocolState.observe who setup.program current.point ∧
        setup.commitRecoveryModel.infoOf who replayTrace =
          setup.commitRecoveryNoMissInformation who
            (setup.commitRecoveryModel.infoOf who trace) ∧
        ∃ prior : setup.commitRecoveryProtocol.Trace
            (some (CommitRecoveryState.atPoint current.saved current.entryExcluded
              current.generation)),
          TracePrefix prior trace ∧ TracePrefix prior replayTrace ∧
          replayTrace.length = trace.length ∧
          trace.length + ProtocolState.remaining setup.program current.point =
            prior.length + ProtocolState.remaining setup.program current.saved := by
  obtain ⟨prior, retained, rank⟩ := setup.commitRecovery_attempt_entry current trace committing
  have frontier := setup.commitRecovery_blockFrontier trace
  have savedCommit : ProtocolState.atCommit setup.program current.saved = true := by
    rcases frontier with ⟨saved, _live, _ending⟩ | same
    · exact saved
    · rwa [same]
  have ending : ProtocolState.commitEnd setup.program current.point =
      ProtocolState.commitEnd setup.program current.saved := by
    rcases frontier with ⟨_saved, _live, ending⟩ | same
    · exact ending
    · rw [same]
  have positive := ProtocolState.commitEnd_lt_remaining setup.program current.point committing
  have inside : trace.length + ProtocolState.commitEnd setup.program current.saved <
      prior.length + ProtocolState.remaining setup.program current.saved := by omega
  obtain ⟨actual, replay, actualState, _actualSaved, _actualEntry, _actualGen,
      replayTrace, replayRetained, length, saved, replayEntry, gen, excluded, views, info⟩ :=
    setup.commitRecovery_noMiss_prefix_information who current.saved current.entryExcluded
      current.generation prior savedCommit trace retained inside survives
  have actualEq := Option.some.inj actualState
  cases actualEq
  refine ⟨replay, replayTrace, excluded, replayEntry, saved, gen, views, ?_,
    prior, retained, replayRetained, length, rank⟩
  have entryExclusions :=
    setup.commitRecoverySavedExclusions_of_entry who current trace prior retained rank
  have savedSurvives : who ∉ current.entryExcluded := fun member =>
    survives (current.entered member)
  rw [info, commitRecoveryNoMissInformation]
  have currentSignal := setup.commitRecoverySignals_current who trace
  rw [setup.model_base who trace, currentSignal]
  simp only [commitRecoveryPrivate, Option.map_some, Option.elim_some,
    ProtocolState.atCommit_observe, committing, commitRecoveryPublic, survives,
    not_false_eq_true, true_and]
  rw [entryExclusions, ite_eq_left savedSurvives,
    setup.commitRecoveryAttemptStart_of_entry who current trace prior retained rank]

/-- Every reached normalized query is the full information of a genuine
source history. Nonterminal queries have nonterminal witnesses, even when
the observer is inactive. The erased label can therefore index the original
played reduced table. -/
theorem commitRecoveryNoMissInformation_genuine_history (who : Player)
    (history : setup.commitRecoveryProtocol.History) :
    ∃ replay : setup.commitRecoveryProtocol.History,
      setup.commitRecoveryModel.infoOf who replay.trace =
        setup.commitRecoveryNoMissInformation who
          (setup.commitRecoveryModel.infoOf who history.trace) ∧
      (¬ setup.commitRecoveryProtocol.terminal history.state →
        ¬ setup.commitRecoveryProtocol.terminal replay.state) := by
  rcases history with ⟨state, trace⟩
  cases state with
  | none =>
      refine ⟨⟨none, trace⟩, ?_, fun running => running⟩
      unfold commitRecoveryNoMissInformation
      rw [setup.model_base who trace, setup.commitRecoverySignals_current who trace]
      simp only [commitRecoveryPrivate, Option.map_none, Option.elim_none, Bool.false_eq_true,
        false_and, ↓reduceIte]
  | some current =>
      by_cases committing : ProtocolState.atCommit setup.program current.point = true
      · by_cases survives : who ∉ current.excluded
        · obtain ⟨replay, replayTrace, _excluded, _entryExcluded, _saved, _gen,
              views, info, _prefix⟩ :=
            setup.commitRecoveryNoMissInformation_genuine who current trace committing survives
          refine ⟨⟨some replay, replayTrace⟩, info, fun _running => ?_⟩
          have replayCommit : ProtocolState.atCommit setup.program replay.point = true := by
            rw [← ProtocolState.atCommit_observe setup.program replay.point who, views,
              ProtocolState.atCommit_observe, committing]
          change ¬ ProtocolState.terminal setup.program replay.point
          intro terminal
          have zero := (ProtocolState.remaining_zero_iff_terminal setup.program replay.point).mpr
            terminal
          have positive := ProtocolState.commitEnd_lt_remaining setup.program replay.point
            replayCommit
          omega
        · refine ⟨⟨some current, trace⟩, ?_, fun running => running⟩
          unfold commitRecoveryNoMissInformation
          rw [setup.model_base who trace, setup.commitRecoverySignals_current who trace]
          simp only [commitRecoveryPublic, survives, false_and, and_false, ↓reduceIte]
      · refine ⟨⟨some current, trace⟩, ?_, fun running => running⟩
        unfold commitRecoveryNoMissInformation
        rw [setup.model_base who trace, setup.commitRecoverySignals_current who trace]
        simp only [commitRecoveryPrivate, Option.map_some, Option.elim_some,
          ProtocolState.atCommit_observe, committing, Bool.false_eq_true, false_and, ↓reduceIte]

end Vegas.SourceProgram.Setup
