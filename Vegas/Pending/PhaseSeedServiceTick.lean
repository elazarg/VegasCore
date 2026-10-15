/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedWaitingWindow
import Vegas.Pending.PhaseSeedRecordedWait

/-! # An original coin service tick bounds the unresolved physical request -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A true original coin, or a protected earlier envelope, prevents a surviving
request from advancing past that service tick. This is derived from actual tick
exhaustion and the complete retained timed packet word. -/
theorem service_tick_bounds_request_time (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon remaining : Nat)
    (players : Player → (app).Policy) (count : Nat) (execution next : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks delay bound priority).family seeds)).Trace
        (some ⟨remaining, none, next⟩))
    {input : graph.Inputs} (valid : execution.application.Invariant input)
    (phases : execution.application.Ordered)
    (wordRecall : PhaseSeedScheduler.WordRecall runtime leaks execution)
    (clean : PhaseCount.CountClean runtime leaks execution)
    (continued : next ∈ ((app).runRounds
      ((controller runtime leaks delay bound priority).family seeds) players count
        execution).support)
    (owner : Player) (coordinate : PhaseSeedAddress graph)
    (requested : execution.application.SeedRequest owner coordinate.1)
    (survives : next.application.SeedRequest owner coordinate.1)
    (entered : Nat)
    (activated : execution.application.current.native.activatedAt coordinate.1.event = some entered)
    (started : entered ≤ execution.application.current.native.clock)
    (serviceTick : Nat)
    (notPast : execution.application.current.native.clock ≤ entered + serviceTick)
    (inTime : serviceTick < runtime.deadline coordinate.1.event)
    (unclosed : (entered + serviceTick, coordinate) ∉
      replayClosed runtime leaks priority seeds.1 execution.environmentRecall)
    (sent : Nat) (message : Message Player (CommitAttemptPacket graph))
    (recorded : (sent, message) ∈
      (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner execution.environmentRecall
        (execution.observeEnvironment app)).emissions)
    (service : sent + bound coordinate.1.event < runtime.deadline coordinate.1.event ∨
      (seeds.2 coordinate).2 (Fin.ofNat (clockLimit runtime delay + 1) serviceTick) = true) :
    execution.application.current.native.clock ≤ next.application.current.native.clock ∧
      next.application.current.native.clock ≤ entered + serviceTick ∧
      next.application.current.native.activatedAt coordinate.1.event = some entered := by
  have timely : execution.application.current.native.clock - entered <
      runtime.deadline coordinate.1.event := by omega
  have initialBound : ClosedCoordinateBound runtime execution.application.current.native.clock
      entered coordinate.1 execution.application :=
    ⟨le_rfl, started, by rw [requested.1], by rw [requested.1],
      fun _ => Or.inr ⟨requested.2.2.1, activated, timely⟩⟩
  have retained := retained_bound_runRounds runtime leaks
    ((controller runtime leaks delay bound priority).family seeds) players count execution next
      valid phases execution.application.current.native.clock entered coordinate.1 initialBound
      continued
  have stamp : next.application.current.native.activatedAt coordinate.1.event = some entered := by
    rcases retained.event survives.1 with completed | active
    · exact (survives.2.2.1.1 completed).elim
    · exact active.2.1
  refine ⟨retained.clock, ?_, stamp⟩
  by_contra later
  have strict : entered + serviceTick < next.application.current.native.clock :=
    Nat.lt_of_not_ge later
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon
    ((controller runtime leaks delay bound priority).family seeds) trace
  have exhausted := history_tickExhaustion runtime leaks delay bound priority seeds plan
    ordered maximal inputs horizon raw ⟨remaining, none, next⟩ rfl
  have closed := exhausted coordinate owner survives entered stamp (entered + serviceTick)
    (Nat.le_add_right _ _) strict
  obtain ⟨laterEntries, recordedLater, _length⟩ :=
    (app).runRounds_environmentRecall_append
      ((controller runtime leaks delay bound priority).family seeds) players count execution next
        continued
  have closure : (entered + serviceTick, coordinate) ∈
      replayClosedFrom runtime leaks priority seeds.1
        (replayClosed runtime leaks priority seeds.1 execution.environmentRecall)
        execution.environmentRecall laterEntries := by
    simpa only [recordedLater, replayClosed, replayClosedFrom_append, List.nil_append] using closed
  rcases replayClosedFrom_origin runtime leaks priority seeds.1
      (replayClosed runtime leaks priority seeds.1 execution.environmentRecall)
      execution.environmentRecall laterEntries (entered + serviceTick) coordinate closure with
    already | ⟨before, entry, after, entries, queryClock, selected, idle⟩
  · exact unclosed already
  · have recordedEntry : next.environmentRecall =
        execution.environmentRecall ++ before ++ entry :: after := by
      rw [recordedLater, entries, List.append_assoc]
    have selectedGlobal : selectOpen runtime leaks
        (replayClosed runtime leaks priority seeds.1 (execution.environmentRecall ++ before))
        entry.beforeView (priority seeds.1 (execution.environmentRecall ++ before)
          entry.beforeView) = some coordinate := by
      simpa only [replayClosed, replayClosedFrom_append, List.nil_append] using selected
    have waitRecord := recorded_wait_of_request runtime leaks delay bound priority seeds bounds
      plan ordered maximal inputs horizon remaining next trace coordinate owner survives
        (execution.environmentRecall ++ before) entry after recordedEntry selectedGlobal idle
    obtain ⟨used, _left, prior, _middle, _length, priorSupported, priorRecall, observed, chosen,
        _moved, _future⟩ := (app).runRounds_recorded_entry
      ((controller runtime leaks delay bound priority).family seeds) players count execution next
        continued before entry after recordedEntry
    have selectedPrior : selectedAt runtime leaks priority seeds.1 prior = some coordinate := by
      unfold selectedAt
      rw [priorRecall, ← observed]
      exact selectedGlobal
    have actualWait : (controller runtime leaks delay bound priority).choose seeds
        prior.environmentRecall (prior.observeEnvironment app) = .wait :=
      ((PMF.mem_support_pure_iff _ _).mp chosen).symm.trans waitRecord.1
    have priorClock : prior.application.current.native.clock = entered + serviceTick := by
      change (prior.observeEnvironment app).application.native.clock = _
      rw [← observed]
      exact queryClock.symm
    have priorStamp : prior.application.current.native.activatedAt coordinate.1.event =
        some entered := by
      change (prior.observeEnvironment app).application.native.activatedAt coordinate.1.event = _
      rw [← observed]
      exact waitRecord.2.trans stamp
    have elapsed : (queryAt runtime leaks prior coordinate owner).elapsed = serviceTick := by
      change prior.application.current.native.clock -
        (prior.application.current.native.activatedAt coordinate.1.event).getD
          prior.application.current.native.clock = _
      rw [priorClock, priorStamp, Option.getD_some]
      omega
    have excluded := runRounds_wait_excludes_earlier_emission runtime leaks delay bound priority
      seeds players used execution prior wordRecall clean priorSupported owner coordinate
        requested.2.2.2.1 selectedPrior sent message recorded actualWait
    rcases service with protection | coin
    · exact excluded.1 protection
    · rw [elapsed] at excluded
      rw [coin] at excluded
      cases excluded.2

/-- All actual closed query tickets are at or before the current physical
clock. Hence every strictly future service tick is genuinely unread. -/
theorem future_tick_unclosed
    (delay : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    {inputs : graph.Inputs} {execution : (app).Execution}
    (safe : TickSafe runtime leaks delay priority seeds inputs execution)
    (coordinate : PhaseSeedAddress graph)
    (openNow : (execution.application.current.native.clock, coordinate) ∉
      replayClosed runtime leaks priority seeds.1 execution.environmentRecall)
    (tick : Nat) (future : execution.application.current.native.clock ≤ tick) :
    (tick, coordinate) ∉
      replayClosed runtime leaks priority seeds.1 execution.environmentRecall := by
  intro member
  obtain ⟨entered, bound⟩ := safe.closed (tick, coordinate) member
  have same : tick = execution.application.current.native.clock :=
    Nat.le_antisymm bound.clock future
  exact openNow (same ▸ member)

end Vegas.EventGraphRuntime.PhaseSeedCalendar
