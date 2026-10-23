/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryErasedStep
import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound

/-! # Source continuations under erased private-word prescriptions

The original source runner and information histories are retained. The
prescription condition identifies only action laws at the same erased
information. Actual chance, exclusion, restore and close transitions supply
the continuation comparison.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- Terminal semantic readout does not read remembered choices. -/
theorem readout_withHistory : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (past : History Player L),
    readout program (withHistory program point past) = readout program point
  | _, _, .ret _, _, _ => rfl
  | _, _, .sample _ _ _ next, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => exact readout_withHistory next point past
  | _, _, .commit _ _ _ _ next, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => exact readout_withHistory next point past
  | _, _, .reveal _ _ _ _ _ _ next, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => exact readout_withHistory next point past

end ProtocolState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- The actual semantic source state and every owner's erased full query. -/
def commitRecoveryErasedHistory (history : setup.commitRecoveryProtocol.History) :
    setup.commitRecoveryProtocol.State ×
      ((who : Player) → setup.commitRecoveryModel.InfoState who) :=
  (history.state.map CommitRecoveryState.eraseHistory,
    fun who => setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryModel.infoOf who history.trace))

/-- The next erased queries keep all old public signals. Only the private
remembered words and their derived own-play tags are absent. -/
def commitRecoveryNextErasedHistory
    (before : setup.commitRecoveryProtocol.State ×
      ((who : Player) → setup.commitRecoveryModel.InfoState who))
    (next : setup.commitRecoveryProtocol.State) :
    setup.commitRecoveryProtocol.State ×
      ((who : Player) → setup.commitRecoveryModel.InfoState who) :=
  (next, fun who =>
    (((setup.commitRecoveryPrivate who next, setup.commitRecoveryPublic next),
      (((before.2 who).1.1.1.map (ProtocolView.publicOnly who setup.program),
        (before.2 who).1.1.2) :: (before.2 who).1.2)), []))

private theorem erased_private (who : Player) (state : setup.commitRecoveryProtocol.State) :
    setup.commitRecoveryPrivate who (state.map CommitRecoveryState.eraseHistory) =
      (setup.commitRecoveryPrivate who state).map
        (ProtocolView.eraseHistory who setup.program) := by
  cases state with
  | none => rfl
  | some current => exact congrArg some (ProtocolView.eraseHistory_observe who _ _).symm

private theorem erased_public (state : setup.commitRecoveryProtocol.State) :
    setup.commitRecoveryPublic (state.map CommitRecoveryState.eraseHistory) =
      setup.commitRecoveryPublic state := by
  cases state with
  | none => rfl
  | some current =>
      simp only [Option.map_some, commitRecoveryPublic, CommitRecoveryState.eraseHistory,
        ProtocolState.remaining_withHistory]

/-- An actual next logical signal depends on the old erased query and actual
next semantic state, without assuming equality of old private signal words. -/
theorem commitRecoveryErasedHistory_extend
    (history : setup.commitRecoveryProtocol.History)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal history.state joint)
    {target : setup.commitRecoveryProtocol.State}
    (realized : target ∈ (setup.commitRecoveryProtocol.step history.state ⟨joint, legal⟩).support) :
    setup.commitRecoveryErasedHistory (history.extend legal realized) =
      setup.commitRecoveryNextErasedHistory (setup.commitRecoveryErasedHistory history)
        (target.map CommitRecoveryState.eraseHistory) := by
  refine Prod.ext rfl ?_
  funext who
  let old := setup.commitRecoveryErasedInformation who
    (setup.commitRecoveryModel.infoOf who history.trace)
  change setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryModel.infoOf who (history.trace.extend joint legal realized)) =
    (((setup.commitRecoveryPrivate who (target.map CommitRecoveryState.eraseHistory),
        setup.commitRecoveryPublic (target.map CommitRecoveryState.eraseHistory)),
      (old.1.1.1.map (ProtocolView.publicOnly who setup.program), old.1.1.2) :: old.1.2), [])
  rw [setup.erased_private, setup.erased_public]
  dsimp only [old]
  rw [InfoSignals.infoOf_extend]
  simp only [commitRecoveryErasedInformation, commitRecoveryModel,
    InfoSignals.withOwnPlayRecall, commitRecoverySignals, List.map_cons, Option.map_map,
    Function.comp_def, ProtocolView.publicOnly_eraseHistory]

private theorem step_erased_state
    {first second : setup.commitRecoveryProtocol.State}
    (same : first.map CommitRecoveryState.eraseHistory =
      second.map CommitRecoveryState.eraseHistory)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (firstLegal : setup.commitRecoveryProtocol.Legal first joint)
    (secondLegal : setup.commitRecoveryProtocol.Legal second joint) :
    (setup.commitRecoveryProtocol.step first ⟨joint, firstLegal⟩).map
        (Option.map CommitRecoveryState.eraseHistory) =
      (setup.commitRecoveryProtocol.step second ⟨joint, secondLegal⟩).map
        (Option.map CommitRecoveryState.eraseHistory) := by
  cases first with
  | none => cases second <;> cases same; rfl
  | some first =>
      cases second with
      | none => cases same
      | some second =>
          have states := Option.some.inj same
          simp only [commitRecoveryProtocol, PMF.map_comp]
          change (first.step joint).map (some ∘ CommitRecoveryState.eraseHistory) =
            (second.step joint).map (some ∘ CommitRecoveryState.eraseHistory)
          rw [← PMF.map_comp, ← PMF.map_comp, ← first.step_eraseHistory,
            ← second.step_eraseHistory, states]

/-- Terminal status cannot depend on a discarded source word. -/
theorem commitRecovery_terminal_eq_of_erased
    {first second : setup.commitRecoveryProtocol.State}
    (same : first.map CommitRecoveryState.eraseHistory =
      second.map CommitRecoveryState.eraseHistory) :
    setup.commitRecoveryProtocol.terminal first ↔ setup.commitRecoveryProtocol.terminal second := by
  cases first with
  | none => cases second <;> cases same; rfl
  | some first =>
      cases second with
      | none => cases same
      | some second =>
          have ranks := congrArg (fun state : CommitRecoveryState setup.program =>
            ProtocolState.remaining setup.program state.point) (Option.some.inj same)
          simp only [CommitRecoveryState.eraseHistory, ProtocolState.remaining_withHistory] at ranks
          change ProtocolState.terminal setup.program first.point ↔
            ProtocolState.terminal setup.program second.point
          rw [← ProtocolState.remaining_zero_iff_terminal,
            ← ProtocolState.remaining_zero_iff_terminal, ranks]

variable [Fintype Player]

private theorem terminal_eq_until (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (history : setup.commitRecoveryProtocol.History) :
    setup.commitRecoveryModel.runBehavioralTerminalFrom certificate profile history =
      setup.commitRecoveryModel.runBehavioralUntil certificate profile (fun _ => False)
        history := by
  rw [setup.commitRecoveryModel.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate
    profile (fun _ => False)]
  calc
    _ = (setup.commitRecoveryModel.runBehavioralUntil certificate profile (fun _ => False)
        history).bind PMF.pure := by
      apply bind_congr_on_support
      intro final supported
      have ended := setup.commitRecoveryModel.mem_support_runBehavioralUntil certificate profile
        (fun _ => False) history final supported
      exact setup.commitRecoveryProtocol.randomizedBackwardLaw_of_terminal
        (ended.resolve_left (fun impossible => impossible))
    _ = _ := PMF.bind_pure _

end Setup
end Vegas.SourceProgram
