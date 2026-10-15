/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedUnsentInformation
import Vegas.Pending.PhaseSeedActivationQueries
import Vegas.Pending.PhaseSeedQueryClocks
import Vegas.Pending.PhaseSeedFirstDelay
import Vegas.Pending.PhaseSeedRecordedWait

/-! # The complete candidate-seed filter at an actual unsent activation -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- At a surviving unsent coordinate whose current clock was an actual owner
activation, the full command filter accepts exactly the seeds with its earliest
observed activation delay. Every inclusion-coin word remains possible. -/
theorem unsent_delay_filter_of_recorded_activation (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon remaining : Nat) (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks delay bound priority).family seeds)).Trace
        (some ⟨remaining, none, execution⟩))
    (coordinate : PhaseSeedAddress graph) (owner : Player)
    (request : execution.application.SeedRequest owner coordinate.1)
    (unsent : ∀ message ∈ execution.network.inputs,
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false)
    (observed : (queryAt runtime leaks execution coordinate owner).elapsed ∈
      (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
        (execution.recall owner)).map Prod.fst) :
    ∃ firstClock,
      firstClock ∈ (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
        (execution.recall owner)).map Prod.fst ∧
      (∀ clock ∈ (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
        (execution.recall owner)).map Prod.fst, firstClock ≤ clock) ∧
      ∀ candidate : Seed runtime delay,
        (controller runtime leaks delay bound priority).coordinateConsistentFrom seeds.1
          coordinate candidate [] execution.environmentRecall ↔ candidate.1.val = firstClock := by
  classical
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let driver := controller runtime leaks delay bound priority
  let scheduler := driver.family seeds
  let players := menu.uniformResponses
  have supported := menu.roundSupported_uniform initial horizon scheduler trace
  have rounds : execution ∈ ((app).roundsFrom initial scheduler players
      execution.environmentRecall.length).support := supported.2
  obtain ⟨state, stateSupported, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ rounds)
  obtain ⟨input, _, rfl⟩ := PMF.support_map .. ▸ stateSupported
  have word := PhaseSeedScheduler.initial_wordRecall runtime leaks
    (PhaseRuntimeState.initial plan input)
  have initialValid := PhaseRuntimeState.initial_invariant plan input
  have clocksEq := runRounds_activationTranscript runtime leaks delay bound priority seeds ordered
    coordinate owner request.2.2.2.1 players execution.environmentRecall.length
    (ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan input)) execution
    initialValid.1 word (by rfl) reached
  have commands := ((app).deterministic_transcript_invariant driver.choose seeds).runRounds
    players execution.environmentRecall.length
    (ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan input)) execution
    (by trivial) reached
  have original := ((driver.command_rectangle seeds.1 seeds.2 [] execution.environmentRecall).mp
    commands).2 coordinate
  have empty := queried_emissions_nil_of_unsent runtime leaks delay bound priority seeds.1
    coordinate owner request.2.2.2.1 scheduler players execution.environmentRecall.length
    (PhaseRuntimeState.initial plan input) execution reached unsent
  have recalled := runRounds_queryClocks runtime leaks delay bound priority seeds.1
    coordinate
    owner request.2.2.2.1 scheduler players execution.environmentRecall.length
    (ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan input))
      execution word
    (by intro item impossible; cases impossible) reached
  let clocks := (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
    (execution.recall owner)).map Prod.fst
  have nonempty : clocks.toFinset.Nonempty :=
    ⟨(queryAt runtime leaks execution coordinate owner).elapsed, List.mem_toFinset.mpr observed⟩
  let firstClock := clocks.toFinset.min' nonempty
  have firstMember : firstClock ∈ clocks :=
    List.mem_toFinset.mp (Finset.min'_mem clocks.toFinset nonempty)
  have least : ∀ clock ∈ clocks, firstClock ≤ clock := fun clock member =>
    Finset.min'_le clocks.toFinset clock (List.mem_toFinset.mpr member)
  have positive : ∃ item ∈ driver.coordinateTranscriptFrom seeds.1 coordinate []
      execution.environmentRecall, item.1.elapsed = firstClock ∧ item.2 = .activate owner := by
    have present : firstClock ∈ activationTranscript runtime leaks delay bound priority seeds.1
        coordinate owner execution.environmentRecall := by rw [← clocksEq]; exact firstMember
    obtain ⟨item, member, clockEq⟩ := List.mem_map.mp present
    exact ⟨item, (List.mem_filter.mp member).1, clockEq,
      of_decide_eq_true (List.mem_filter.mp member).2⟩
  have previous : firstClock = 0 ∨ ∃ item ∈ driver.coordinateTranscriptFrom seeds.1 coordinate []
      execution.environmentRecall, item.1.elapsed + 1 = firstClock ∧
        item.1.elapsed ∉ item.1.activationClocks ∧ item.2 = .wait := by
    by_cases zero : firstClock = 0
    · exact Or.inl zero
    · right
      have raw := menu.toRawTrace initial horizon scheduler trace
      obtain ⟨actualInput, valid, _, _⟩ :=
        currentTokenPrerequisites_history runtime leaks plan inputs horizon scheduler raw
      obtain ⟨entered, stamp⟩ := valid.active.activatedAt_eq_some_of_ready_actor coordinate.1.event
        request.2.2.1 (by simp only [request.2.2.2.1, Option.isSome_some])
      have enteredLe := valid.active.activated_le coordinate.1.event entered stamp
      have nowEq : (queryAt runtime leaks execution coordinate owner).elapsed =
          execution.application.current.native.clock - entered := by
        change execution.application.current.native.clock -
          (execution.application.current.native.activatedAt coordinate.1.event).getD
            execution.application.current.native.clock = _
        rw [stamp, Option.getD_some]
      have firstLe := least _ observed
      let tick := entered + (firstClock - 1)
      have started : entered ≤ tick := by omega
      have earlier : tick < execution.application.current.native.clock := by omega
      obtain ⟨query, waited, elapsed⟩ := past_wait_query_of_tickExhaustion runtime leaks delay bound
        priority seeds bounds plan ordered maximal inputs horizon remaining execution trace
        coordinate owner request entered stamp tick started earlier
      have adjacent : query.elapsed + 1 = firstClock := by omega
      have unrecorded : query.elapsed ∉ query.activationClocks := by
        intro present
        have listed := recalled (query, .wait) waited query.elapsed present
        have lower := least query.elapsed listed
        omega
      exact ⟨(query, .wait), waited, adjacent, unrecorded, rfl⟩
  have exactDelay : ∀ candidate : Seed runtime delay,
      driver.coordinateConsistentFrom seeds.1 coordinate candidate [] execution.environmentRecall →
        candidate.1.val = firstClock := fun candidate consistent =>
    first_eq_of_coordinateConsistent_of_bracket runtime leaks delay bound priority seeds.1
      coordinate
      owner request.2.2.2.1 execution.environmentRecall firstClock empty positive previous candidate
      consistent
  have originalDelay := exactDelay (seeds.2 coordinate) original
  refine ⟨firstClock, firstMember, least, fun candidate => ⟨exactDelay candidate, ?_⟩⟩
  intro candidateDelay
  have same : candidate.1 = (seeds.2 coordinate).1 :=
    Fin.ext (candidateDelay.trans originalDelay.symm)
  exact (coordinateConsistent_iff_of_unsent_first_eq runtime leaks delay bound priority seeds.1
    coordinate owner request.2.2.2.1 scheduler players execution.environmentRecall.length
    (PhaseRuntimeState.initial plan input) execution reached unsent candidate (seeds.2 coordinate)
    same).mpr original

end Vegas.EventGraphRuntime.PhaseSeedCalendar
