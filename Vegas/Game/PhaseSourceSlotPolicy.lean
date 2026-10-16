/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoverySlotComponent
import Vegas.Game.PhaseSourcePolicy
import Vegas.Pending.PhaseOpeningPolicy
import Interaction.ReactiveMenuPolicy

/-! # Public-request dispatch with value-preserving binding slots -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

/-- Copy source results with fresh-slot randomization and disclose canonically at openings. -/
def phaseSourceSlotPolicy (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (who : Player) :
    (phaseApplication runtime leaks).Policy :=
  phasePolicyDispatch setup mode runtime leaks (fun owner event payload binding =>
      PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding (fun _ _ =>
      PMF.pure true))
    (fun owner event payload binding => phaseRecoverySlotPolicy setup mode runtime leaks bounds
      wellFormed assessment owner event payload binding) who

theorem phaseSourceSlotPolicy_covered (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed
      assessment who past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  exact phasePolicyDispatch_covered (opened := (fun owner event payload binding past view response
      supported => PhaseCount.phaseOpeningPolicy_covered runtime leaks bounds owner event payload
      binding (fun _ _ => PMF.pure true) past view response supported)) setup mode runtime leaks
      bounds (fun owner event payload binding => PhaseCount.phaseOpeningPolicy runtime leaks
      bounds owner event payload binding (fun _ _ => PMF.pure true))
    (fun owner event payload binding => phaseRecoverySlotPolicy setup mode runtime leaks bounds
      wellFormed assessment owner event payload binding)
    (fun owner event payload binding past view response supported =>
      phaseRecoverySlotPolicy_covered setup mode runtime leaks bounds wellFormed assessment
        owner event payload binding past view response supported) who past view response supported

theorem phaseSourceSlotPolicy_binding (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (execution : (phaseApplication runtime leaks).Execution) {inputs}
    (valid : execution.application.Invariant inputs) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩) :
    phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed assessment who
        (execution.recall who) (execution.observe (phaseApplication runtime leaks) who) =
      phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed assessment who
        event payload binding (execution.recall who)
        (execution.observe (phaseApplication runtime leaks) who) := by
  exact phasePolicyDispatch_binding setup mode runtime leaks (fun owner event payload binding =>
      PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding (fun _ _ =>
      PMF.pure true))
    (fun owner event payload binding => phaseRecoverySlotPolicy setup mode runtime leaks bounds
      wellFormed assessment owner event payload binding)
    execution valid who event payload binding request

theorem phaseSourceSlotPolicy_opening (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (execution : (phaseApplication runtime leaks).Execution) {inputs}
    (valid : execution.application.Invariant inputs) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding who payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve who payload binding checks)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩) :
    phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed assessment who
        (execution.recall who) (execution.observe (phaseApplication runtime leaks) who) =
      PhaseCount.phaseOpeningPolicy runtime leaks bounds who event payload binding
        (fun _ _ => PMF.pure true) (execution.recall who)
          (execution.observe (phaseApplication runtime leaks) who) := by
  exact phasePolicyDispatch_opening setup mode runtime leaks (fun owner event payload binding =>
      PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding (fun _ _ =>
      PMF.pure true))
    (fun owner event payload binding => phaseRecoverySlotPolicy setup mode runtime leaks bounds
      wellFormed assessment owner event payload binding)
    execution valid who event payload binding checks outputEq codeEq request

/-- The covered physical recipe has its exact finite-menu representation. -/
def phaseSourceSlotStrategy (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (who : Player) :
    ((PhaseCount.onePacketMenu runtime leaks bounds).information initial
      horizon scheduler).BehavioralPolicy who :=
  (PhaseCount.onePacketMenu runtime leaks bounds).restrictPolicy initial horizon scheduler who
    (phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed assessment who)

/-- Forgetting finite-menu witnesses recovers the complete physical law at
every input, without a fallback or a first-response wrapper. -/
theorem phaseSourceSlotStrategy_map_val (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    ((phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial horizon
      scheduler who) (some (past, view))).map Subtype.val =
      (phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed assessment who
        past view).map some := by
  exact (PhaseCount.onePacketMenu runtime leaks bounds).restrictPolicy_map_val initial horizon
    scheduler who _ past view (fun response supported => phaseSourceSlotPolicy_covered setup mode
      runtime leaks bounds wellFormed assessment who past view response supported)

end Vegas
