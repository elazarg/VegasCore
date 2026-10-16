/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryErasedContinuation
import Vegas.Source.CommitRecoveryCommitUnique
import Vegas.Source.CommitRecoveryBlockPath

/-! # Actual failed source attempts have a common erased continuation

The compared histories start at the same original saved history. Their
commitment values may differ, including accepted failed values. The original
omission word is retained. The actual close dispatcher, rather than an
assumed reset observation, determines the continuation boundary.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Config

omit [IExpr.ResultTypes L] in
private theorem public_commit_congr {Γ : SourceCtx Player L} {payload : L.Ty}
    (who owner : Player) (name : VarId) (guard : SourceGuard L Γ owner name payload)
    (first second : Config Player L Γ)
    (same : (first.view who).1.publicOnly = (second.view who).1.publicOnly)
    (left right : PublicationResult (L.Val payload)) :
    ((commitSuccessor name guard first left).view who).1.publicOnly =
      ((commitSuccessor name guard second right).view who).1.publicOnly := by
  apply congrArg SourceObservation.mk
  funext cellName cell member
  cases member with
  | here => rfl
  | there member =>
      have previous := congrArg
        (fun view : SourceObservation L who Γ => view.cells cellName cell member) same
      cases cell <;> exact previous

omit [IExpr.ResultTypes L] in
private theorem public_automatic_congr {Γ : SourceCtx Player L} {payload : L.Ty}
    (who owner : Player) (name : VarId) (first second : Config Player L Γ)
    (same : (first.view who).1.publicOnly = (second.view who).1.publicOnly) :
    ((automaticCommit name owner payload first).view who).1.publicOnly =
      ((automaticCommit name owner payload second).view who).1.publicOnly := by
  apply congrArg SourceObservation.mk
  funext cellName cell member
  cases member with
  | here => rfl
  | there member =>
      have previous := congrArg
        (fun view : SourceObservation L who Γ => view.cells cellName cell member) same
      cases cell <;> exact previous

end Config

namespace ProtocolState

private theorem public_entry_congr {Γ : SourceCtx Player L} {O : Finset VarId}
    (who : Player) (program : SourceProgram Player L Γ O) (first second : Config Player L Γ)
    (same : (first.view who).1.publicOnly = (second.view who).1.publicOnly) :
    ProtocolView.publicOnly who program (observe who program (entry program first)) =
      ProtocolView.publicOnly who program (observe who program (entry program second)) := by
  cases program <;> simp only [entry, observe, ProtocolView.publicOnly, Sum.elim_inl, same]

private theorem public_control (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (first second : ProtocolState program),
      ProtocolView.publicOnly who program (observe who program first) =
        ProtocolView.publicOnly who program (observe who program second) →
      remaining program first = remaining program second ∧
        atCommit program first = atCommit program second ∧
        commitEnd program first = commitEnd program second
  | _, _, .ret _, _, _, _ => ⟨rfl, rfl, rfl⟩
  | _, _, .sample _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact ⟨rfl, rfl, rfl⟩
      · cases same
      · cases same
      · exact public_control who next _ _ (Sum.inr.inj same)
  | _, _, .commit _ _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact ⟨rfl, rfl, rfl⟩
      · cases same
      · cases same
      · exact public_control who next _ _ (Sum.inr.inj same)
  | _, _, .reveal _ _ _ _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact ⟨rfl, rfl, rfl⟩
      · cases same
      · cases same
      · exact public_control who next _ _ (Sum.inr.inj same)

/-- The actual commitment kernel exposes the omission and source position,
not the chosen hidden typed result. Accepted failure remains a hidden result. -/
theorem recoveryStep_commit_public_congr (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (first second : ProtocolState program),
      ProtocolView.publicOnly who program (observe who program first) =
        ProtocolView.publicOnly who program (observe who program second) →
      atCommit program first = true →
      ∀ (excluded : Finset Player) (left right : Player → Option (CommitRecoveryMove Player L)),
      (∀ owner, CommitRecoveryMove.missed (left owner) = CommitRecoveryMove.missed (right owner)) →
      ∀ l ∈ (recoveryStep program first excluded left).support,
      ∀ r ∈ (recoveryStep program second excluded right).support,
        ProtocolView.publicOnly who program (observe who program l.1) =
            ProtocolView.publicOnly who program (observe who program r.1) ∧ l.2 = r.2
  | _, _, .ret _, _, _, _, committing, _, _, _, _, _, _, _, _ => by cases committing
  | _, _, .sample _ _ _ next, first, second, same, committing,
      excluded, left, right, missed, l, lm, r, rm => by
      cases first with
      | inl _ => cases committing
      | inr first =>
          cases second with
          | inl _ => cases same
          | inr second =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next first excluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next second excluded right) _).mp rm
              subst l
              subst r
              obtain ⟨views, exclusions⟩ := recoveryStep_commit_public_congr who next first second
                (Sum.inr.inj same) committing excluded left right missed
                lowerLeft lowerLeftMember lowerRight lowerRightMember
              exact ⟨congrArg Sum.inr views, exclusions⟩
  | _, _, .commit name owner fresh guard next, first, second, same, committing,
      excluded, left, right, missed, l, lm, r, rm => by
      cases first with
      | inl first =>
          cases second with
          | inr _ => cases same
          | inl second =>
              have old := congrArg (fun view : DecisionView who _ => view.1) (Sum.inl.inj same)
              simp only [recoveryStep, Sum.elim_inl] at lm rm
              by_cases inactive : owner ∈ excluded
              · rw [ite_eq_left inactive, PMF.mem_support_pure_iff] at lm rm
                subst l; subst r
                exact ⟨congrArg Sum.inr (public_entry_congr who next _ _
                  (Config.public_automatic_congr who owner name first second old)), rfl⟩
              · rw [ite_eq_right inactive, PMF.mem_support_pure_iff] at lm rm
                subst l; subst r
                exact ⟨congrArg Sum.inr (public_entry_congr who next _ _
                  (Config.public_commit_congr who owner name guard first second old _ _)),
                  by rw [missed owner]⟩
      | inr first =>
          cases second with
          | inl _ => cases same
          | inr second =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next first excluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next second excluded right) _).mp rm
              subst l
              subst r
              obtain ⟨views, exclusions⟩ := recoveryStep_commit_public_congr who next first second
                (Sum.inr.inj same) committing excluded left right missed
                lowerLeft lowerLeftMember lowerRight lowerRightMember
              exact ⟨congrArg Sum.inr views, exclusions⟩
  | _, _, .reveal _ _ _ _ _ _ next, first, second, same, committing,
      excluded, left, right, missed, l, lm, r, rm => by
      cases first with
      | inl _ => cases committing
      | inr first =>
          cases second with
          | inl _ => cases same
          | inr second =>
              simp only [recoveryStep, Sum.elim_inr] at lm rm
              obtain ⟨lowerLeft, lowerLeftMember, leftShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next first excluded left) _).mp lm
              obtain ⟨lowerRight, lowerRightMember, rightShape⟩ := (PMF.mem_support_map_iff
                (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
                (recoveryStep next second excluded right) _).mp rm
              subst l
              subst r
              obtain ⟨views, exclusions⟩ := recoveryStep_commit_public_congr who next first second
                (Sum.inr.inj same) committing excluded left right missed
                lowerLeft lowerLeftMember lowerRight lowerRightMember
              exact ⟨congrArg Sum.inr views, exclusions⟩

end ProtocolState

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId}
  {program : SourceProgram Player L Γ O}

/-- A genuine failed close restores the same saved semantic source on both
sides, for either retry or exhausted automatic completion. The different
attempted typed values and their retained action words are not assumed equal. -/
theorem close_eraseHistory_eq_of_failure (first second : CommitRecoveryState program)
    (saved : first.saved = second.saved) (excluded : first.excluded = second.excluded)
    (entryExcluded : first.entryExcluded = second.entryExcluded)
    (generation : first.generation = second.generation)
    (leftFinished : first.Finished) (rightFinished : second.Finished)
    (failed : first.NewFailure) : first.close.eraseHistory = second.close.eraseHistory := by
  have rightFailed : second.NewFailure := by
    simpa only [NewFailure, excluded, entryExcluded] using failed
  have survivors : first.Survives ↔ second.Survives := by
    simp only [Survives, saved, excluded]
  by_cases leftSurvives : first.Survives
  · rw [first.close_of_retry leftFinished failed leftSurvives,
      second.close_of_retry rightFinished rightFailed (survivors.mp leftSurvives)]
    simp only [retry, atPoint, restored, eraseHistory, ProtocolState.withHistory_withHistory,
      saved, excluded, generation]
  · rw [first.close_of_exhausted leftFinished failed leftSurvives,
      second.close_of_exhausted rightFinished rightFailed
        (fun survives => leftSurvives (survivors.mpr survives))]
    simp only [exhausted, atPoint, restored, eraseHistory,
      ProtocolState.withHistory_automaticCommitBlock, ProtocolState.withHistory_withHistory,
      saved, excluded, generation]

private theorem step_raw_result (state : CommitRecoveryState program)
    (joint : Player → Option (CommitRecoveryMove Player L)) (target : CommitRecoveryState program)
    (supported : target ∈ (state.step joint).support) :
    ∃ result : {result : ProtocolState program × Finset Player // state.excluded ⊆ result.2},
      result.1 ∈ (ProtocolState.recoveryStep program state.point state.excluded joint).support ∧
        target = (state.install result.1 result.2).close := by
  obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  refine ⟨result, ?_, rfl⟩
  rw [← map_val_pmfToSubtype
    (ProtocolState.recoveryStep program state.point state.excluded joint)
    (fun result supported => ProtocolState.recoveryStep_excluded_monotone program state.point
      state.excluded joint result supported)]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩

end CommitRecoveryState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

def attemptPublicSignal (who : Player) (state : setup.commitRecoveryProtocol.State) :=
  ((setup.commitRecoveryPrivate who state).map (ProtocolView.publicOnly who setup.program),
    setup.commitRecoveryPublic state)

def attemptPublicRecall (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :=
  let information := setup.commitRecoverySignals.infoOf who trace
  (information.1 :: information.2).map
    (fun signal => (signal.1.map (ProtocolView.publicOnly who setup.program), signal.2))

private theorem publicRecall_extend (who : Player)
    {state : setup.commitRecoveryProtocol.State} (trace : setup.commitRecoveryProtocol.Trace state)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal state joint)
    {target : setup.commitRecoveryProtocol.State}
    (realized : target ∈ (setup.commitRecoveryProtocol.step state ⟨joint, legal⟩).support) :
    setup.attemptPublicRecall who (trace.extend joint legal realized) =
      setup.attemptPublicSignal who target :: setup.attemptPublicRecall who trace := by
  rw [attemptPublicRecall, InfoSignals.infoOf_extend]
  rfl

theorem erasedInformation_publicRecall (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    setup.commitRecoveryErasedInformation who (setup.commitRecoveryModel.infoOf who trace) =
      ((((setup.commitRecoveryPrivate who state).map
          (ProtocolView.eraseHistory who setup.program), setup.commitRecoveryPublic state),
        (setup.attemptPublicRecall who trace).tail), []) := by
  change setup.commitRecoveryErasedInformation who
    (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who trace) = _
  rw [InfoSignals.withOwnPlayRecall_infoOf]
  change ((((setup.commitRecoverySignals.infoOf who trace).1.1.map
      (ProtocolView.eraseHistory who setup.program),
      (setup.commitRecoverySignals.infoOf who trace).1.2),
      (setup.commitRecoverySignals.infoOf who trace).2.map
        (fun signal =>
          (signal.1.map (ProtocolView.publicOnly who setup.program), signal.2))), []) = _
  simp only [attemptPublicRecall, List.map_cons, List.tail_cons]
  rw [setup.commitRecoverySignals_current who trace]

private theorem publicSignal_congr (who : Player)
    (first second : CommitRecoveryState setup.program)
    (views : ProtocolView.publicOnly who setup.program
        (ProtocolState.observe who setup.program first.point) =
      ProtocolView.publicOnly who setup.program
        (ProtocolState.observe who setup.program second.point))
    (excluded : first.excluded = second.excluded)
    (generation : first.generation = second.generation)
    (saved : first.saved = second.saved) :
    setup.attemptPublicSignal who (some first) =
      setup.attemptPublicSignal who (some second) := by
  simp only [attemptPublicSignal, commitRecoveryPrivate, Option.map_some,
    commitRecoveryPublic, views, excluded, generation, saved]

private theorem publicRecall_of_erased_states
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (left : setup.commitRecoveryProtocol.Trace leftState)
    (right : setup.commitRecoveryProtocol.Trace rightState)
    (states : leftState.map CommitRecoveryState.eraseHistory =
      rightState.map CommitRecoveryState.eraseHistory)
    (publicRecall : ∀ who, setup.attemptPublicRecall who left =
      setup.attemptPublicRecall who right) :
    setup.commitRecoveryErasedHistory ⟨leftState, left⟩ =
      setup.commitRecoveryErasedHistory ⟨rightState, right⟩ := by
  refine Prod.ext states ?_
  funext who
  change setup.commitRecoveryErasedInformation who (setup.commitRecoveryModel.infoOf who left) =
    setup.commitRecoveryErasedInformation who (setup.commitRecoveryModel.infoOf who right)
  rw [setup.erasedInformation_publicRecall who left,
    setup.erasedInformation_publicRecall who right, publicRecall who]
  have privateEq := congrArg (fun state => setup.commitRecoveryPrivate who state) states
  have publicEq := congrArg setup.commitRecoveryPublic states
  cases leftState with
  | none => cases rightState <;> cases states; rfl
  | some first =>
      cases rightState with
      | none => cases states
      | some second =>
          simp only [Option.map_some, commitRecoveryPrivate, CommitRecoveryState.eraseHistory]
            at privateEq
          rw [← ProtocolView.eraseHistory_observe who setup.program first.point,
            ← ProtocolView.eraseHistory_observe who setup.program second.point] at privateEq
          simp only [Option.map_some, commitRecoveryPublic, CommitRecoveryState.eraseHistory,
            ProtocolState.remaining_withHistory] at publicEq
          exact congrArg (fun current => ((current, _), [])) (Prod.ext privateEq publicEq)

private def omissionRecall {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :=
  (setup.recoveryJointRecall trace).map
    (fun joint owner => CommitRecoveryMove.missed (joint owner))

private theorem omissionRecall_length {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.omissionRecall trace).length = trace.length := by
  rw [omissionRecall, List.length_map, setup.recoveryJointRecall_length]

private theorem inside_attempt_public_eq
    (observer : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (leftTrace : setup.commitRecoveryProtocol.Trace leftState)
    (rightTrace : setup.commitRecoveryProtocol.Trace rightState)
    (leftRetained : TracePrefix prior leftTrace) (rightRetained : TracePrefix prior rightTrace)
    (sameWord : setup.omissionRecall leftTrace = setup.omissionRecall rightTrace)
    (inside : leftTrace.length + ProtocolState.commitEnd setup.program first.point <
      prior.length + ProtocolState.remaining setup.program first.point) :
    ∃ left right : CommitRecoveryState setup.program,
      leftState = some left ∧ rightState = some right ∧
      left.saved = first.saved ∧ right.saved = first.saved ∧
      left.entryExcluded = first.entryExcluded ∧ right.entryExcluded = first.entryExcluded ∧
      left.generation = first.generation ∧ right.generation = first.generation ∧
      left.excluded = right.excluded ∧
      (∀ who, ProtocolView.publicOnly who setup.program
          (ProtocolState.observe who setup.program left.point) =
        ProtocolView.publicOnly who setup.program
          (ProtocolState.observe who setup.program right.point)) ∧
      (∀ who, setup.attemptPublicRecall who leftTrace =
        setup.attemptPublicRecall who rightTrace) := by
  induction leftRetained generalizing rightState with
  | refl =>
      have lengths := congrArg List.length sameWord
      rw [setup.omissionRecall_length, setup.omissionRecall_length] at lengths
      have equal := rightRetained.eq_of_length lengths
      cases equal
      exact ⟨first, first, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        fun _ => rfl, fun _ => rfl⟩
  | @extend source target earlier kept joint legal reached ih =>
      cases rightRetained with
      | refl =>
          have lengths := congrArg List.length sameWord
          rw [setup.omissionRecall_length, setup.omissionRecall_length] at lengths
          have lower := kept.length_le
          simp only [Trace.length] at lengths
          omega
      | @extend rightSource rightTarget rightEarlier rightKept rightJoint rightLegal rightReached =>
          have words := List.cons.inj sameWord
          have previousInside : earlier.length +
              ProtocolState.commitEnd setup.program first.point <
              prior.length + ProtocolState.remaining setup.program first.point := by
            simp only [Trace.length] at inside
            omega
          obtain ⟨left, right, rfl, rfl, leftSaved, rightSaved, leftEntry, rightEntry,
            leftGeneration, rightGeneration, exclusions, views, publicPast⟩ :=
              ih rightEarlier rightKept words.2 previousInside
          obtain ⟨middle, middleState, middleCommit, middleEnd, middleRank⟩ :=
            setup.commitRecovery_prefix_inside_commit first prior committing earlier kept
              previousInside
          have middleEq := Option.some.inj middleState
          subst middle
          change _ ∈ ((left.step joint).map some).support at reached
          change _ ∈ ((right.step rightJoint).map some).support at rightReached
          obtain ⟨leftNext, leftSupport, rfl⟩ :=
            (PMF.mem_support_map_iff some (left.step joint) _).mp reached
          obtain ⟨rightNext, rightSupport, rfl⟩ :=
            (PMF.mem_support_map_iff some (right.step rightJoint) _).mp rightReached
          obtain ⟨l, lm, lnext⟩ := left.step_raw_result joint leftNext leftSupport
          obtain ⟨r, rm, rnext⟩ := right.step_raw_result rightJoint rightNext rightSupport
          have rraw : r.1 ∈
              (ProtocolState.recoveryStep setup.program right.point left.excluded
              rightJoint).support :=
            exclusions.symm ▸ rm
          have rawPublic : ∀ who,
              ProtocolView.publicOnly who setup.program
                (ProtocolState.observe who setup.program l.1.1) =
              ProtocolView.publicOnly who setup.program
                (ProtocolState.observe who setup.program r.1.1) := fun who =>
            (ProtocolState.recoveryStep_commit_public_congr who setup.program left.point right.point
              (views who) middleCommit left.excluded joint rightJoint
              (congrFun words.1) l.1 lm r.1 rraw).1
          have rawExcluded : l.1.2 = r.1.2 :=
            (ProtocolState.recoveryStep_commit_public_congr observer setup.program
              left.point right.point (views observer) middleCommit left.excluded joint rightJoint
              (congrFun words.1) l.1 lm r.1 rraw).2
          have running : ¬ ProtocolState.terminal setup.program left.point := by
            intro terminal
            have zero := (ProtocolState.remaining_zero_iff_terminal setup.program left.point).mpr
              terminal
            have positive := ProtocolState.commitEnd_lt_remaining setup.program left.point
              middleCommit
            omega
          have rawRank := ProtocolState.recoveryStep_remaining setup.program left.point
            left.excluded joint l.1 running lm
          have frontier := setup.commitRecovery_blockFrontier earlier
          have savedCommit : ProtocolState.atCommit setup.program left.saved = true := by
            rcases frontier with ⟨saved, _live, _end⟩ | same
            · exact saved
            · rwa [same]
          have savedEnd : ProtocolState.commitEnd setup.program left.point =
              ProtocolState.commitEnd setup.program left.saved := by
            rcases frontier with ⟨_saved, _live, ending⟩ | same
            · exact ending
            · rw [same]
          have rawInside : ProtocolState.commitEnd setup.program left.saved <
              ProtocolState.remaining setup.program l.1.1 := by
            simp only [Trace.length] at inside
            omega
          have rawRanks := (ProtocolState.public_control observer setup.program l.1.1 r.1.1
            (rawPublic observer)).1
          have savedPair : left.saved = right.saved := leftSaved.trans rightSaved.symm
          have lclose : (left.install l.1 l.2).close = left.install l.1 l.2 :=
            (left.install l.1 l.2).close_eq_self_of_remaining_gt savedCommit rawInside
          have rclose : (right.install r.1 r.2).close = right.install r.1 r.2 :=
            (right.install r.1 r.2).close_eq_self_of_remaining_gt
              (savedPair ▸ savedCommit) (by
                change ProtocolState.commitEnd setup.program right.saved <
                  ProtocolState.remaining setup.program r.1.1
                rw [← savedPair, ← rawRanks]
                exact rawInside)
          rw [lclose] at lnext
          rw [rclose] at rnext
          subst leftNext
          subst rightNext
          refine ⟨_, _, rfl, rfl, leftSaved, rightSaved, leftEntry, rightEntry,
            leftGeneration, rightGeneration, rawExcluded, rawPublic, ?_⟩
          intro who
          rw [setup.publicRecall_extend, setup.publicRecall_extend, publicPast who]
          congr 1
          exact setup.publicSignal_congr who _ _ (rawPublic who) rawExcluded
            (leftGeneration.trans rightGeneration.symm) savedPair


private theorem publicSignal_erase (who : Player)
    (state : setup.commitRecoveryProtocol.State) :
    setup.attemptPublicSignal who (state.map CommitRecoveryState.eraseHistory) =
      setup.attemptPublicSignal who state := by
  cases state with
  | none => rfl
  | some current =>
      simp only [attemptPublicSignal, Option.map_some, commitRecoveryPrivate,
        commitRecoveryPublic, CommitRecoveryState.eraseHistory,
        ProtocolState.remaining_withHistory]
      rw [← ProtocolView.eraseHistory_observe who setup.program current.point,
        ProtocolView.publicOnly_eraseHistory]

/-- Two genuine full commitment windows with the same original saved history
and omission word have the same complete erased retry or exhausted history.
All attempted typed choices, including accepted failure, may differ. The
public signal word and the actual restored state are derived from the source
steps; equality at the reset endpoint is not supplied. -/
theorem commitRecovery_failed_attempt_erased_eq
    (observer : Player) (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (leftTrace : setup.commitRecoveryProtocol.Trace leftState)
    (rightTrace : setup.commitRecoveryProtocol.Trace rightState)
    (leftRetained : TracePrefix prior leftTrace) (rightRetained : TracePrefix prior rightTrace)
    (sameOmissions :
      (setup.recoveryJointRecall leftTrace).map
          (fun joint owner => CommitRecoveryMove.missed (joint owner)) =
        (setup.recoveryJointRecall rightTrace).map
          (fun joint owner => CommitRecoveryMove.missed (joint owner)))
    (boundary : leftTrace.length + ProtocolState.commitEnd setup.program first.point =
      prior.length + ProtocolState.remaining setup.program first.point)
    (failed : leftState.elim False
      (fun left => (left.excluded \ first.entryExcluded).Nonempty)) :
    setup.commitRecoveryErasedHistory ⟨leftState, leftTrace⟩ =
      setup.commitRecoveryErasedHistory ⟨rightState, rightTrace⟩ := by
  have sameWord : setup.omissionRecall leftTrace = setup.omissionRecall rightTrace := sameOmissions
  induction leftRetained generalizing rightState with
  | refl =>
      have below := ProtocolState.commitEnd_lt_remaining setup.program first.point committing
      omega
  | @extend source target earlier kept joint legal reached _ih =>
      cases rightRetained with
      | refl =>
          have lengths := congrArg List.length sameWord
          rw [setup.omissionRecall_length, setup.omissionRecall_length] at lengths
          have lower := kept.length_le
          simp only [Trace.length] at lengths
          omega
      | @extend rightSource rightTarget rightEarlier rightKept rightJoint rightLegal rightReached =>
          have words := List.cons.inj sameWord
          have previousInside : earlier.length +
              ProtocolState.commitEnd setup.program first.point <
              prior.length + ProtocolState.remaining setup.program first.point := by
            simp only [Trace.length] at boundary
            omega
          obtain ⟨beforeLeft, beforeRight, rfl, rfl, leftSaved, rightSaved, leftEntry, rightEntry,
            leftGeneration, rightGeneration, exclusions, views, publicPast⟩ :=
              setup.inside_attempt_public_eq observer first prior committing earlier rightEarlier
                kept rightKept words.2 previousInside
          obtain ⟨middle, middleState, middleCommit, middleEnd, middleRank⟩ :=
            setup.commitRecovery_prefix_inside_commit first prior committing earlier kept
              previousInside
          have middleEq := Option.some.inj middleState
          subst middle
          change _ ∈ ((beforeLeft.step joint).map some).support at reached
          change _ ∈ ((beforeRight.step rightJoint).map some).support at rightReached
          obtain ⟨left, leftSupport, rfl⟩ :=
            (PMF.mem_support_map_iff some (beforeLeft.step joint) _).mp reached
          obtain ⟨right, rightSupport, rfl⟩ :=
            (PMF.mem_support_map_iff some (beforeRight.step rightJoint) _).mp rightReached
          change (left.excluded \ first.entryExcluded).Nonempty at failed
          obtain ⟨l, lm, lnext⟩ := beforeLeft.step_raw_result joint left leftSupport
          obtain ⟨r, rm, rnext⟩ := beforeRight.step_raw_result rightJoint right rightSupport
          have rraw : r.1 ∈ (ProtocolState.recoveryStep setup.program beforeRight.point
              beforeLeft.excluded rightJoint).support := exclusions.symm ▸ rm
          have rawPublic := ProtocolState.recoveryStep_commit_public_congr observer setup.program
            beforeLeft.point beforeRight.point (views observer) middleCommit beforeLeft.excluded
            joint rightJoint (congrFun words.1) l.1 lm r.1 rraw
          have rawRanks := (ProtocolState.public_control observer setup.program l.1.1 r.1.1
            rawPublic.1).1
          have running : ¬ ProtocolState.terminal setup.program beforeLeft.point := by
            intro terminal
            have zero := (ProtocolState.remaining_zero_iff_terminal setup.program
              beforeLeft.point).mpr terminal
            have positive := ProtocolState.commitEnd_lt_remaining setup.program beforeLeft.point
              middleCommit
            omega
          have rawRank := ProtocolState.recoveryStep_remaining setup.program beforeLeft.point
            beforeLeft.excluded joint l.1 running lm
          have frontier := setup.commitRecovery_blockFrontier earlier
          have savedCommit : ProtocolState.atCommit setup.program beforeLeft.saved = true := by
            rcases frontier with ⟨saved, _live, _end⟩ | same
            · exact saved
            · rwa [same]
          have savedEnd : ProtocolState.commitEnd setup.program beforeLeft.point =
              ProtocolState.commitEnd setup.program beforeLeft.saved := by
            rcases frontier with ⟨_saved, _live, ending⟩ | same
            · exact ending
            · rw [same]
          have rawFinished : (beforeLeft.install l.1 l.2).Finished := by
            refine ⟨savedCommit, ?_⟩
            change ProtocolState.remaining setup.program l.1.1 =
              ProtocolState.commitEnd setup.program beforeLeft.saved
            simp only [Trace.length] at boundary
            omega
          have savedPair : beforeLeft.saved = beforeRight.saved :=
            leftSaved.trans rightSaved.symm
          have rightFinished : (beforeRight.install r.1 r.2).Finished := by
            refine ⟨savedPair ▸ savedCommit, ?_⟩
            change ProtocolState.remaining setup.program r.1.1 =
              ProtocolState.commitEnd setup.program beforeRight.saved
            rw [← rawRanks, ← savedPair]
            exact rawFinished.2
          have rawFailed : (beforeLeft.install l.1 l.2).NewFailure := by
            have outputExcluded : left.excluded = l.1.2 := by
              rw [lnext, CommitRecoveryState.close_excluded]
              rfl
            simpa only [CommitRecoveryState.NewFailure, CommitRecoveryState.install,
              leftEntry, outputExcluded] using failed
          have states : left.eraseHistory = right.eraseHistory := by
            rw [lnext, rnext]
            exact CommitRecoveryState.close_eraseHistory_eq_of_failure _ _ savedPair rawPublic.2
              (leftEntry.trans rightEntry.symm) (leftGeneration.trans rightGeneration.symm)
              rawFinished rightFinished rawFailed
          apply setup.publicRecall_of_erased_states
            (leftState := some left) (rightState := some right) _ _ (congrArg some states)
          intro who
          rw [setup.publicRecall_extend, setup.publicRecall_extend, publicPast who]
          congr 1
          have signals := congrArg (fun state => setup.attemptPublicSignal who state)
            (congrArg some states)
          simpa only [← Option.map_some, setup.publicSignal_erase] using signals


end Setup
end Vegas.SourceProgram
