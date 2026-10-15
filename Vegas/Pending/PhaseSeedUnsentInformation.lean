/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedUnsentQueries
import Interaction.ReactiveRoundTrace

/-! # All original inclusion-coin candidates at an actual unsent information site -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Actual full owner recall suffices to certify that no own signed packet for
this coordinate appears anywhere in the permanent network input list. -/
theorem network_unsent_of_information (initial : PMF (PhaseRuntimeState graph))
    (bounds : MessageBounds graph) (horizon : Nat) (scheduler : (app).Scheduler)
    (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      initial horizon scheduler).Trace (some ⟨remaining, some owner, execution⟩))
    (coordinate : PhaseSeedAddress graph)
    (unsent : ∀ message ∈ (app).outputs (execution.recall owner),
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false) :
    ∀ message ∈ execution.network.inputs,
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false := by
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon
    scheduler trace
  have recalled := (app).history_inputRecall initial horizon scheduler raw
  intro message authentic
  by_cases missing : PhaseSeedScheduler.ownPacket coordinate.1 owner message = false
  · exact missing
  · have own : PhaseSeedScheduler.ownPacket coordinate.1 owner message = true :=
      Bool.eq_true_of_not_eq_false missing
    have sender : message.sender = owner := (of_decide_eq_true own).1
    have output : message ∈ (app).outputs (execution.recall owner) := by
      rw [← recalled owner]
      exact List.mem_filter.mpr ⟨authentic, by simp only [sender, decide_true]⟩
    exact Bool.noConfusion (own.symm.trans (unsent message output))

/-- At an actual unsent owner information site, the complete recorded command
filter is identical for ALL original seeds sharing a first delay. This statement
includes the current activation query and uses the original retained recall. -/
theorem coordinateConsistent_iff_of_unsent_information
    (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (initial : PMF (PhaseRuntimeState graph))
    (bounds : MessageBounds graph) (horizon : Nat) (scheduler : (app).Scheduler)
    (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      initial horizon scheduler).Trace (some ⟨remaining, some owner, execution⟩))
    (coordinate : PhaseSeedAddress graph)
    (actor : graph.actor? coordinate.1.event = some owner)
    (unsent : ∀ message ∈ (app).outputs (execution.recall owner),
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false)
    (first second : Seed runtime delay) (same : first.1 = second.1) :
    (controller runtime leaks delay bound priority).coordinateConsistentFrom rest coordinate first
      [] execution.environmentRecall ↔
    (controller runtime leaks delay bound priority).coordinateConsistentFrom rest coordinate second
      [] execution.environmentRecall := by
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let idle := execution.respond app owner ⟨none⟩
  have networkUnsent := network_unsent_of_information runtime leaks initial bounds horizon
    scheduler remaining owner execution trace coordinate unsent
  obtain ⟨idleTrace⟩ := menu.trace_respond initial horizon scheduler remaining execution owner
    ⟨none⟩ trace (PhaseCount.silence_onePacket runtime leaks bounds owner
      (execution.recall owner) (execution.observe app owner))
  have supported := menu.roundSupported_uniform initial horizon scheduler idleTrace
  have rounds : idle ∈ ((app).roundsFrom initial scheduler menu.uniformResponses
      idle.environmentRecall.length).support := supported.2
  obtain ⟨state, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ rounds)
  have compared := coordinateConsistent_iff_of_unsent_first_eq runtime leaks delay bound priority
    rest coordinate owner actor scheduler menu.uniformResponses idle.environmentRecall.length
    state idle reached networkUnsent first second same
  simpa only [idle, (app).respond_environmentRecall] using compared

end Vegas.EventGraphRuntime.PhaseSeedCalendar
