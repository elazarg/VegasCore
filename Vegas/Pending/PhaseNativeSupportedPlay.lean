/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativeControlLaw
import Interaction.ReactiveResponseEvaluation
import Interaction.ReactiveRecovery

/-! # Supported physical control play supplies actual counted histories and recall -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks

/-- Original finite-fuel policy play supplies a real counted trace and all
players' supported-action recall. Neither datum is a separate replay premise. -/
theorem supported_control_play (bounds : MessageBounds graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (P).Scheduler) (players : Player → (P).Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view)
    (fuel : Nat) (state : (P).ProtocolState)
    (supported : state ∈ ((fun law => law.bind ((P).controlStep
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler players))^[fuel]
        (PMF.pure none)).support) :
    ∃ _trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace state,
      ∀ control, state = some control →
        ∀ who, (players who).Consistent (control.execution.recall who) := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have faithful := ((P).consistentRecall_policyInvariant players).canonical_run initial horizon
    scheduler (fun _state _member who => .nil) fuel state (by
      rw [(P).run_map_state]
      exact supported)
  have law := menu.run_restrict_control_steps initial horizon scheduler players
    (menu.admissible_of_covered initial horizon scheduler players covered) fuel
      (menu.protocol initial horizon scheduler).initHistory
  change _ = (fun law => law.bind ((P).controlStep initial horizon scheduler players))^[fuel]
    (PMF.pure none) at law
  have present : state ∈ ((fun law =>
      law.bind ((P).controlStep initial horizon scheduler players))^[fuel]
        (PMF.pure none)).support := supported
  rw [← law, PMF.mem_support_map_iff] at present
  obtain ⟨history, _present, same⟩ := present
  cases same
  refine ⟨history.trace, ?_⟩
  intro control equality
  rw [equality] at faithful
  exact faithful

end Vegas.EventGraphRuntime.PhaseNativeProjection
