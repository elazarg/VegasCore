/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphDisclosureAction
import Vegas.Pending.PhaseOriginalObservation
import Vegas.Game.RevealService

/-! # Exact original observations for compiled disclosing phase policies -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (source : setup.program.BehavioralProfile)

local notation "compiled" => EventGraph.toModeProfile (toEventGraph setup.program) mode
  (compileEventProfile setup.program source)

/-- Supported original memories for a globally disclosing compiled source
profile preserve the entire physical configuration at every initialized clear
counted phase history. No intended source counterpart is assumed. -/
theorem phase_compiled_originalConfig_of_clear
    (disclosing : ∀ who, Disclosing setup.program (source who))
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅)
    (consistent : ∀ who,
      (runtime.prescribedReactivePolicy (PhaseNativeProjection.nativeLeaks leaks plan) who
        (compiled who)).Consistent
          ((PhaseNativeProjection.execution runtime leaks plan current.execution).recall who))
    (memories : Player → List (Option (serviceGraph setup mode).Completion))
    (supported : ∀ who, memories who ∈
      ((runtime.prescribedReactiveImplementation (PhaseNativeProjection.nativeLeaks leaks plan)
        who (compiled who)).posterior
          ((PhaseNativeProjection.execution runtime leaks plan
            current.execution).recall who)).support) :
    runtime.originalConfig (PhaseNativeProjection.nativeLeaks leaks plan)
      (PhaseNativeProjection.execution runtime leaks plan current.execution) memories =
        current.execution.application.current.native.config := by
  apply PhaseNativeProjection.originalConfig_eq_of_clear runtime leaks plan bounds inputs horizon
    scheduler trace clear compiled ?_ consistent memories supported
  intro who event actor observation action positive payload outputEq
  let observed := (toEventGraph setup.program).fromModeObservation mode who
    ((serviceGraph setup mode).normalizeObservation event who observation)
  have chosen : action ∈ ((compileEventPolicy setup.program who (source who)) event
      (show (toEventGraph setup.program).actor? event = some who from actor) observed).support :=
    positive
  have law := compileEventPolicy_disclosing_publication_true setup.program who (source who)
    (disclosing who) event actor observed payload outputEq
  have mapped : cast (congrArg EventField.Action outputEq) action ∈
      (((compileEventPolicy setup.program who (source who)) event actor observed).map
        (cast (congrArg EventField.Action outputEq))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨action, chosen, rfl⟩
  rw [law, PMF.mem_support_pure_iff] at mapped
  exact mapped

end Vegas
