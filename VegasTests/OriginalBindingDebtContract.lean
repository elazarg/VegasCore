/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalStandingBindingDebt

/-! # Original closing debt contract -/

noncomputable section

namespace VegasTests

open Vegas Vegas.SourceProgram Vegas.EventGraph Vegas.EventGraphRuntime Interaction
  GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

example
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (current before ending : (phaseApplication runtime leaks).Control)
    (currentTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some current))
    (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some before))
    (kept : TracePrefix currentTrace prior)
    (same : current.execution.application.attempt = before.execution.application.attempt)
    (witness : RecoverySourceWitness setup mode plan before.execution.application)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : current.execution.application.phases = phase :: remaining)
    (kind : phase.kind = .commitment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : current.execution.application.SeedRequest who
      ⟨current.execution.application.attempt, event⟩)
    (failed : phaseProposalCurrentBindingFailure setup mode runtime leaks who event
      (current.execution.observe (phaseApplication runtime leaks) who))
    (raw : RecoveryState (serviceGraph setup mode))
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt)
    (finished : phase.Finished (phase.drain raw))
    (clean : ¬ (((phase.drain raw).excluded \ before.execution.application.entry.excluded) ∩
      phase.owners).Nonempty)
    (normalized : ending.execution.application =
      ({ before.execution.application with current := raw } :
        PhaseRuntimeState (serviceGraph setup mode)).normalize)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner) :
    PhaseCheckpointDebt setup mode plan who ending.execution.application := by
  exact phaseProposal_current_binding_failure_checkpointed_at_original_close setup mode runtime
    leaks bounds plan maximal horizon scheduler current before ending currentTrace prior kept same
      witness phase remaining installed kind who event payload binding request failed raw effect
        changed finished clean normalized sourceProfile

end VegasTests
