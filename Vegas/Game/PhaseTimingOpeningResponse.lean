/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourceTimingPolicy

/-! # Actual opening laws of guarded serial timing components -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks

/-- Every selected serial retains the original canonical opening law at an
actual resolve request. The WAIT option remains the globally silent policy. -/
theorem phaseSourceTimingPolicy_opening_eq_source (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (serial : Fin bounds.candidateCount) (execution : (app).Execution) {inputs}
    (valid : execution.application.Invariant inputs) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : EventGraph.FieldRef (serviceGraph setup mode).layout (.binding who payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve who payload binding checks)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩) :
    phaseSourceTimingPolicy setup mode runtime leaks bounds wellFormed assessment (some serial)
        who (execution.recall who) (execution.observe app who) =
      phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
        (execution.recall who) (execution.observe app who) := by
  have timed := phasePolicyDispatch_opening setup mode runtime leaks (fun owner event payload
      binding => PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding
      (fun _ _ => PMF.pure true))
    (fun owner event payload binding => phaseRecoveryTimingPolicy setup mode runtime leaks bounds
      wellFormed assessment owner event payload binding (some serial)) execution valid who event
        payload binding checks outputEq codeEq request
  have canonical := phaseSourcePolicy_opening setup mode runtime leaks bounds wellFormed assessment
    execution valid who event payload binding checks outputEq codeEq request
  exact timed.trans canonical.symm

end Vegas
