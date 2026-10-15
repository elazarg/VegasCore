/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseFiniteNature
import Vegas.Pending.PhaseCountMenu
import Vegas.Game.RevealService
import Interaction.ReactiveFiniteAssessment

/-! # Finite physical source histories from the original branching assumptions -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A finite original setup law, finitely branching leaks and finite scheduler
choices give finite actual counted histories at every bounded horizon. These
are the explicit branching assumptions of the asynchronous service interface. -/
theorem phase_source_history_finite
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    [setup.FiniteInitialLaw] [leaks.FiniteSupport]
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode)) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (schedulerFinite : ∀ past view, (scheduler past view).support.Finite) :
    Finite ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)))
        horizon scheduler).History := by
  let := phaseApplication_finiteNature runtime leaks
    (setup.initialLaw.map (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)))
    scheduler (by
      rw [PMF.support_map]
      exact setup.initialLaw_support_finite.image _) schedulerFinite
  infer_instance

end Vegas
