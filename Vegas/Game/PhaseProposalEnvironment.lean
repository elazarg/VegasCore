/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalTransition
import Vegas.Game.PhaseProposalExecution
import Vegas.Pending.PhaseProposalFrameStep
import Interaction.ReactiveTrafficIdentity

/-! # Actual environment processing accumulates the same source proposal archive -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- This uses the real external counted prefix to discharge the normalizer's
packet frame. Its selected source checkpoint is exactly the one returned by
the shared raw transition producer. -/
theorem RecoverySourceWitness.environment_archivedProposals
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (bounds : MessageBounds ((toEventGraph setup.program).withMode mode))
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (witness : RecoverySourceWitness setup mode plan control.execution.application)
    (prior : witness.checkpoint.ArchivedProposals control.execution.network.inputs)
    (command : (phaseApplication runtime leaks).Command)
    (next : (phaseApplication runtime leaks).Execution)
    (reached : next ∈ (control.execution.environmentStep
      (phaseApplication runtime leaks) command).support) :
    ∃ nextWitness : RecoverySourceWitness setup mode plan next.application,
      nextWitness.checkpoint.ArchivedProposals next.network.inputs := by
  let app := phaseApplication runtime leaks
  let inputs := setup.initialLaw.map encodeInputs
  have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
    horizon scheduler trace
  have mapped : setup.initialLaw.map (fun draw => PhaseRuntimeState.initial plan
    (encodeInputs draw)) =
      inputs.map (PhaseRuntimeState.initial plan) := by rw [PMF.map_comp]; rfl
  have counted : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    rw [← mapped]
    exact trace
  have origins := PhaseProposal.openingOrigins_history runtime leaks plan inputs horizon scheduler
    control (by rw [← mapped]; exact rawTrace)
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨witness, prior⟩
  | activate owner =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _supported, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨witness, prior⟩
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : control.execution.network.lookup id with
      | none => exact ⟨witness, prior⟩
      | some message =>
          change ∃ nextWitness : RecoverySourceWitness setup mode plan
              ((app.handle control.execution.application message).getD
                control.execution.application),
            nextWitness.checkpoint.ArchivedProposals control.execution.network.inputs
          cases accepted : app.handle control.execution.application message with
          | none => exact ⟨witness, prior⟩
          | some state =>
              change control.execution.application.handle runtime message = some state at accepted
              unfold PhaseRuntimeState.handle at accepted
              split at accepted
              · rename_i allowed
                obtain ⟨result, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
                obtain ⟨nextWitness, delta⟩ := witness.after_handle runtime leaks maximal
                  message result
                  allowed handled
                refine ⟨nextWitness, ?_⟩
                let raw : PhaseRuntimeState ((toEventGraph setup.program).withMode mode) :=
                  {control.execution.application with current :=
                    (control.execution.application.current.inclusionResult
                      message.payload.packet.call result)}
                let checkpoint := witness.checkpoint.transfer (other := raw) rfl rfl rfl
                have old : checkpoint.ArchivedProposals control.execution.network.inputs := by
                  intro observer active
                  exact prior observer (fun excluded => active
                    (control.execution.application.current.inclusionResult_excluded_subset
                      message.payload.packet.call result excluded))
                have present := (app.retained_envelopes_mem_inputs control.execution
                  (app.history_provenance _ horizon scheduler rawTrace)
                  (app.history_inputRecall _ horizon scheduler rawTrace)).lookup id message found
                have frame := PhaseProposal.NormalizationFrame.inclusion runtime leaks control
                  origins message present result handled
                exact RecoverySourceCheckpoint.ArchivedProposals.normalize plan checkpoint
                  nextWitness.checkpoint runtime leaks bounds inputs
                  horizon scheduler control counted frame witness.order.frontier.adjacent old delta
              · cases accepted
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ (control.execution.application.environment runtime command).support at changed
      unfold PhaseRuntimeState.environment at changed
      split at changed
      · rename_i authorized
        obtain ⟨result, nativeSupport, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp changed
        obtain ⟨nextWitness, delta⟩ := witness.after_environment runtime leaks maximal
          command result
          authorized nativeSupport
        refine ⟨nextWitness, ?_⟩
        let raw : PhaseRuntimeState ((toEventGraph setup.program).withMode mode) :=
          {control.execution.application with current :=
            (control.execution.application.current.environmentResult command result)}
        let checkpoint := witness.checkpoint.transfer (other := raw) rfl rfl rfl
        have old : checkpoint.ArchivedProposals control.execution.network.inputs := by
          intro observer active
          exact prior observer (fun excluded => active
            (control.execution.application.current.environmentResult_excluded_subset command result
              excluded))
        have frame := PhaseProposal.NormalizationFrame.environment runtime leaks control origins
          command result nativeSupport
        exact RecoverySourceCheckpoint.ArchivedProposals.normalize plan checkpoint
                  nextWitness.checkpoint runtime leaks bounds inputs
          horizon scheduler control counted frame witness.order.frontier.adjacent old delta
      · cases (PMF.mem_support_pure_iff _ _).mp changed
        exact ⟨witness, prior⟩

end Vegas
