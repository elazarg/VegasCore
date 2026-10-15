/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhasePacketAddress
import Vegas.Pending.PhasePlanSuffix

/-! # Canonical source addresses of requests at genuine clear histories -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A genuine clear current request has its unique static source phase and
zero retry generation. This holds for arbitrary schedulers and player replies. -/
theorem phase_request_address_of_clear
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (who : Player) (coordinate : CommitAttemptEvent graph)
    (request : control.execution.application.SeedRequest who coordinate) :
    coordinate.attempt = ⟨plan.eventPhase coordinate.event, 0⟩ := by
  have suffix := phasePlanSuffix_history runtime leaks plan inputs horizon scheduler trace
  have generation := (phase_clear_history runtime leaks plan inputs horizon scheduler control trace
    clear).1
  rw [request.1]
  obtain ⟨phase, member, inside⟩ := request.2.1
  cases installed : control.execution.application.phases with
  | nil => simp only [installed, List.head?_nil, Option.not_mem_none] at member
  | cons current remaining =>
      simp only [installed, List.head?_cons, Option.mem_some_iff] at member
      subst phase
      have currentMember : current ∈ control.execution.application.phases := by
        simp only [installed, List.mem_cons, true_or]
      have address := plan.eventPhase_of_mem current (suffix.subset currentMember)
        coordinate.event inside
      simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
        Option.getD_some, generation]
      rw [address]

end Vegas.EventGraphRuntime
