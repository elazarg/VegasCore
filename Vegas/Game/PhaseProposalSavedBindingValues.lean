/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryBindingAlternatives
import Vegas.Game.PhaseProposalObservableDebt
import Vegas.Game.PhaseProposalSourceUsability

/-! # Actual saved usable bindings outside observable saved debt -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
/-- The selected retry point restores the original typed cells while
retaining its actual private memory. Properness is transported through the
two original suffix embeddings, without identifying checkpoint packages. -/
theorem RecoverySourceCheckpoint.bindingsHoldValues_of_restored_point
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {before after : PhaseRuntimeState (serviceGraph setup mode)}
    (first : RecoverySourceCheckpoint setup mode before)
    (next : RecoverySourceCheckpoint setup mode after) (who : Player)
    (proper : first.source.BindingsHoldValues who) (past : SourceProgram.History Player L)
    (point : next.residual.lift (ProtocolState.entry next.residual.tail next.source) =
      ProtocolState.withHistory setup.program
        (first.residual.lift (ProtocolState.entry first.residual.tail first.source)) past) :
    next.source.BindingsHoldValues who := by
  apply (ProtocolState.bindingsHoldValues_entry who next.residual.tail next.source).mp
  apply (next.origin.bindingsHoldValues_lift who _).mp
  rw [point]
  apply (ProtocolState.bindingsHoldValues_withHistory who setup.program _ past).mpr
  exact (first.origin.bindingsHoldValues_lift who _).mpr
    ((ProtocolState.bindingsHoldValues_entry who first.residual.tail first.source).mpr proper)

/-- Absence of the actual GLOBAL saved failure classifier yields successful
focal saved bindings. Both previously resolved failures and pending failed
cells are handled by the same original initialized source-history alternative. -/
theorem RecoverySourceWitness.bindingsHoldValues_of_no_saved_failure
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (wellFormed : setup.WellFormed)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (witness : RecoverySourceWitness setup mode plan control.execution.application)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (noSaved : ¬ phaseProposalSavedBindingFailure setup mode runtime leaks who event
      (control.execution.observe (phaseApplication runtime leaks) who)) :
    witness.checkpoint.source.BindingsHoldValues who := by
  have absent := mt (phaseProposalSavedBindingFailure_iff_of_seed_request setup mode runtime
    leaks plan maximal horizon scheduler trace witness.checkpoint witness.aligned who event payload
      binding request).mpr noSaved
  have alternative := (setup.commitRecovery_bindingsHoldValues_or_failedBinding wellFormed
    witness.checkpoint.trace who _ rfl).1
  rcases alternative with proper | failed
  · intro name payload cell
    exact ((ProtocolState.bindingsHoldValues_entry who witness.checkpoint.residual.tail _).mp
      ((witness.checkpoint.origin.bindingsHoldValues_lift who _).mp proper)) cell
  · exact (absent failed).elim

/-- The ordinary reset properness gate follows from actual foreign generated
history regularity and observable absence of focal saved debt. Accepted
canceled focal failures in private recall remain unrestricted. -/
theorem RecoverySourceWitness.bindingsHoldValues_of_no_saved_failure_and_foreign_good
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (wellFormed : setup.WellFormed)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control))
    (witness : RecoverySourceWitness setup mode plan control.execution.application)
    (focal : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding focal payload)
    (request : control.execution.application.SeedRequest focal
      ⟨control.execution.application.attempt, event⟩)
    (noSaved : ¬ phaseProposalSavedBindingFailure setup mode runtime leaks focal event
      (control.execution.observe (phaseApplication runtime leaks) focal))
    (foreign : ∀ owner, owner ≠ focal →
      owner ∉ control.execution.application.current.excluded →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon scheduler owner ⟨some control, trace⟩) :
    ∀ owner, owner ∉ control.execution.application.current.excluded →
      witness.checkpoint.source.BindingsHoldValues owner := by
  intro owner active
  by_cases same : owner = focal
  · subst owner
    have raw : ((phaseApplication runtime leaks).protocol
        (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
        horizon scheduler).Trace (some control) := by
      have equal : ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)) =
          setup.initialLaw.map (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) :=
        PMF.map_comp _ _ _
      exact equal ▸ (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler
        trace
    exact witness.bindingsHoldValues_of_no_saved_failure setup mode wellFormed runtime leaks plan
      maximal horizon scheduler raw focal event payload binding request noSaved
  · exact witness.checkpoint.bindingsHoldValues_of_no_generated_unusable setup mode wellFormed
      runtime leaks bounds plan horizon scheduler control trace owner active
        (foreign owner same active)

end Vegas
