/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedWindowReceipt

/-! # Every actual completion path includes the original protected envelope -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Genuine bounded calendar completion forces the original protected envelope
to be accepted along the same supported continuation. The actual raw graph
completion is kept even if phase normalization immediately retires its namespace. -/
theorem protected_eventually_included (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (enough : serviceHorizon runtime ≤ horizon)
    (players : Player → (app).Policy) (count : Nat) (execution next : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks delay bound priority).family seeds)).Trace
        (some ⟨count, none, execution⟩))
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ (PhaseCount.onePacketMenu runtime leaks bounds).actions who past view)
    {input : graph.Inputs} (valid : execution.application.Invariant input)
    (phases : execution.application.Ordered)
    (wordRecall : PhaseSeedScheduler.WordRecall runtime leaks execution)
    (clean : PhaseCount.CountClean runtime leaks execution)
    (continued : next ∈ ((app).runRounds
      ((controller runtime leaks delay bound priority).family seeds) players count
        execution).support)
    (owner : Player) (coordinate : PhaseSeedAddress graph)
    (requested : execution.application.SeedRequest owner coordinate.1)
    (entered : Nat)
    (activated : execution.application.current.native.activatedAt coordinate.1.event = some entered)
    (started : entered ≤ execution.application.current.native.clock)
    (unclosed : (execution.application.current.native.clock, coordinate) ∉
      replayClosed runtime leaks priority seeds.1 execution.environmentRecall)
    (message : Message Player (CommitAttemptPacket graph))
    (recorded : (execution.application.current.native.clock - entered, message) ∈
      (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner execution.environmentRecall
        (execution.observeEnvironment app)).emissions)
    (protection : execution.application.current.native.clock - entered +
      bound coordinate.1.event < runtime.deadline coordinate.1.event) :
    (message.id, true) ∈ next.receipts ∧
    ∃ (used tail : Nat) (prior after : (app).Execution) (native : State graph)
      (ready : prior.application.current.native.config.cut.Ready coordinate.1.event)
      (action : graph.Action coordinate.1.event),
      used + 1 + tail = count ∧
      prior ∈ ((app).runRounds
        ((controller runtime leaks delay bound priority).family seeds) players used
          execution).support ∧
      (.include message.id : (app).Command) ∈
        (((controller runtime leaks delay bound priority).family seeds)
          prior.environmentRecall (prior.observeEnvironment app)).support ∧
      after ∈ (prior.environmentStep app (.include message.id)).support ∧
      next ∈ ((app).runRounds
        ((controller runtime leaks delay bound priority).family seeds) players tail after).support ∧
      (app).handle prior.application message = some after.application ∧
      EventGraphRuntime.handle runtime prior.application.current.native
        ⟨message.id, message.payload.packet.call⟩ = some native ∧
      native.config ∈ (prior.application.current.native.config.step
        coordinate.1.event ready action).support ∧
      after.application = ({prior.application with
        current := prior.application.current.inclusionResult message.payload.packet.call native } :
          PhaseRuntimeState graph).normalize := by
  have sum : entered + (execution.application.current.native.clock - entered) =
      execution.application.current.native.clock := by omega
  exact service_tick_eventually_included runtime leaks delay bound priority seeds bounds plan
    ordered maximal inputs horizon enough players count execution next trace covered valid phases
      wordRecall clean continued owner coordinate requested entered activated started
      (execution.application.current.native.clock - entered) (by omega) (by omega)
      (by simpa only [sum] using unclosed)
      (execution.application.current.native.clock - entered) message recorded (Or.inl protection)

end Vegas.EventGraphRuntime.PhaseSeedCalendar
