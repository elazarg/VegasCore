/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedUnsentFiber
import Interaction.ReactiveAddressedCoordinatePosterior
import Interaction.ReactiveSchedulerSeedSupport

/-! # The original local law at a genuine unsent owner callback -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (delay bound : graph.EventId → Nat)
  (priority : RestSeed → List (phaseApplication runtime leaks).EnvironmentEntry →
    (phaseApplication runtime leaks).EnvironmentView → Nat)

local notation "app" => phaseApplication runtime leaks
local notation "driver" => controller runtime leaks delay bound priority
local notation "SeedAt" => ReactiveApplication.AddressedScheduler.CoordinateSeed
  (Address := PhaseSeedAddress graph) (LocalSeed := Seed runtime delay) (RestSeed := RestSeed)

private theorem fixed_trace_of_posterior (laws : PhaseSeedAddress graph → PMF (Seed runtime delay))
    (restLaw : PMF RestSeed) (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon count : Nat) (within : count < horizon)
    (players : Player → (app).Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ (PhaseCount.onePacketMenu runtime leaks bounds).actions who past view)
    (input : graph.Inputs) (inputSupported : input ∈ inputs.support)
    (before current : (app).Execution) (owner : Player)
    (reached : before ∈ ((app).runRounds
      ((driver).coordinateImplementation laws restLaw).scheduler players count
        (ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan input))).support)
    (chosen : (.activate owner : (app).Command) ∈
      (((driver).coordinateImplementation laws restLaw).scheduler before.environmentRecall
        (before.observeEnvironment app)).support)
    (moved : current ∈ (before.environmentStep app (.activate owner)).support)
    (values : (index : Option (PhaseSeedAddress graph)) → SeedAt index)
    (supported : values ∈ (((driver).coordinateImplementation laws restLaw).posterior
      current.environmentRecall).support) :
    values ∈ (independentProduct (ReactiveApplication.AddressedScheduler.coordinateLaws
      laws restLaw)).support ∧
    Nonempty (((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((driver).family (ReactiveApplication.AddressedScheduler.unpack values))).Trace
        (some ⟨horizon - count - 1, some owner, current⟩)) := by
  let prior := independentProduct (ReactiveApplication.AddressedScheduler.coordinateLaws
    laws restLaw)
  let family := fun values : (index : Option (PhaseSeedAddress graph)) → SeedAt index =>
    (driver).family (ReactiveApplication.AddressedScheduler.unpack values)
  obtain ⟨initialSeed, original, originalReached, selected, observed⟩ :=
    (app).schedulerMixture_decision_of_posterior_support prior family players count
      (PhaseRuntimeState.initial plan input) before current (.activate owner) values
      reached chosen moved supported
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have originalSupported : original ∈
      ((app).roundsFrom initial (family values) players count).support := by
    rw [ReactiveApplication.roundsFrom, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨PhaseRuntimeState.initial plan input,
      (PMF.mem_support_map_iff _ _ _).mpr ⟨input, inputSupported, rfl⟩, originalReached⟩
  obtain ⟨priorTrace⟩ := menu.trace_roundsFrom initial horizon (family values) players covered count
    within.le original originalSupported
  have remaining : horizon - count = (horizon - count - 1) + 1 := by omega
  rw [remaining] at priorTrace
  obtain ⟨activeTrace⟩ := menu.trace_environment initial horizon (family values)
    (horizon - count - 1) original current (.activate owner) priorTrace selected observed
  exact ⟨initialSeed, ⟨activeTrace⟩⟩

/-- At a genuine counted unsent callback, the original local seed is filtered
only by its observed first activation delay, independently of every remaining
original coordinate. Actual compatible seed histories discharge the rectangle. -/
theorem unsent_posterior_splitAt (laws : PhaseSeedAddress graph → PMF (Seed runtime delay))
    (restLaw : PMF RestSeed) (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon count : Nat) (within : count < horizon)
    (players : Player → (app).Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ (PhaseCount.onePacketMenu runtime leaks bounds).actions who past view)
    (input : graph.Inputs) (inputSupported : input ∈ inputs.support)
    (before current : (app).Execution) (owner : Player)
    (reached : before ∈ ((app).runRounds
      ((driver).coordinateImplementation laws restLaw).scheduler players count
        (ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan input))).support)
    (chosen : (.activate owner : (app).Command) ∈
      (((driver).coordinateImplementation laws restLaw).scheduler before.environmentRecall
        (before.observeEnvironment app)).support)
    (moved : current ∈ (before.environmentStep app (.activate owner)).support)
    (coordinate : PhaseSeedAddress graph)
    (request : current.application.SeedRequest owner coordinate.1)
    (unsent : ∀ message ∈ (app).outputs (current.recall owner),
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false) :
    ∃ (firstClock : Nat)
      (localPositive : ∃ seed ∈ {seed : Seed runtime delay | seed.1.val = firstClock},
        seed ∈ (laws coordinate).support)
      (residual : PMF ((index : {index : Option (PhaseSeedAddress graph) //
        index ≠ some coordinate}) → SeedAt index)),
      firstClock ∈ inputActivationClocks runtime leaks coordinate.1 owner
        (current.recall owner) (current.observe app owner) ∧
      (∀ clock ∈ inputActivationClocks runtime leaks coordinate.1 owner
        (current.recall owner) (current.observe app owner), firstClock ≤ clock) ∧
      ((((driver).coordinateImplementation laws restLaw).posterior current.environmentRecall).map
        fun values => (values (some coordinate),
          fun index : {index : Option (PhaseSeedAddress graph) // index ≠ some coordinate} =>
            values index)) =
        ((laws coordinate).filter {seed : Seed runtime delay | seed.1.val = firstClock}
          localPositive).bind fun value => residual.map (Prod.mk value) := by
  classical
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let prior := independentProduct (ReactiveApplication.AddressedScheduler.coordinateLaws
    laws restLaw)
  let currentPosterior := ((driver).coordinateImplementation laws restLaw).posterior
    current.environmentRecall
  obtain ⟨reference, referenceSupported⟩ := currentPosterior.support_nonempty
  obtain ⟨referenceInitial, referenceTrace⟩ := fixed_trace_of_posterior runtime leaks delay bound
    priority laws restLaw bounds plan inputs horizon count within players covered input
    inputSupported
    before current owner reached chosen moved reference referenceSupported
  obtain ⟨referenceTrace⟩ := referenceTrace
  obtain ⟨firstClock, firstMember, firstLeast, referenceFilter⟩ := unsent_information_delay_filter
    runtime leaks delay bound priority (ReactiveApplication.AddressedScheduler.unpack reference)
    bounds plan ordered maximal inputs horizon (horizon - count - 1) owner current referenceTrace
    coordinate request unsent
  have compatible : ∀ values ∈ currentPosterior.support,
      (app).commandConsistentFrom
        (fun values => (driver).choose (ReactiveApplication.AddressedScheduler.unpack values))
        values [] current.environmentRecall := by
    intro values supported
    obtain ⟨_, trace⟩ := fixed_trace_of_posterior runtime leaks delay bound priority laws restLaw
      bounds plan inputs horizon count within players covered input inputSupported before current
      owner reached chosen moved values supported
    obtain ⟨trace⟩ := trace
    have raw := menu.toRawTrace initial horizon
      ((driver).family (ReactiveApplication.AddressedScheduler.unpack values)) trace
    have invariant := (app).deterministic_transcript_invariant
      (fun values => (driver).choose (ReactiveApplication.AddressedScheduler.unpack values)) values
    exact invariant.history initial horizon (fun _ _ => trivial) raw
  have positive : ∃ values ∈
      {values : (index : Option (PhaseSeedAddress graph)) → SeedAt index |
        (app).commandConsistentFrom
          (fun values => (driver).choose (ReactiveApplication.AddressedScheduler.unpack values))
          values [] current.environmentRecall}, values ∈ prior.support :=
    ⟨reference, compatible reference referenceSupported, referenceInitial⟩
  have currentEq : currentPosterior = prior.filter
      {values | (app).commandConsistentFrom
        (fun values => (driver).choose (ReactiveApplication.AddressedScheduler.unpack values))
        values [] current.environmentRecall} positive :=
    (app).schedulerMixture_posterior_eq_filter prior
      (fun values => (driver).choose (ReactiveApplication.AddressedScheduler.unpack values))
      current.environmentRecall positive
  obtain ⟨localPositive, residual, product⟩ :=
    (driver).posterior_splitAt_of_coordinate_constraint laws
    restLaw coordinate current.environmentRecall
    {seed : Seed runtime delay | seed.1.val = firstClock} positive (by
      intro rest witnessed candidate
      obtain ⟨values, ⟨follows, restEq⟩, initialSupported⟩ := witnessed
      have supported : values ∈ currentPosterior.support := by
        rw [currentEq]
        exact (PMF.mem_support_filter_iff positive).mpr ⟨follows, initialSupported⟩
      obtain ⟨_, trace⟩ := fixed_trace_of_posterior runtime leaks delay bound priority laws restLaw
        bounds plan inputs horizon count within players covered input inputSupported before current
        owner reached chosen moved values supported
      obtain ⟨trace⟩ := trace
      have common := coordinateConsistent_iff_of_unsent_information_eq runtime leaks delay bound
        priority (ReactiveApplication.AddressedScheduler.unpack reference)
        (ReactiveApplication.AddressedScheduler.unpack values) bounds plan ordered maximal inputs
        horizon (horizon - count - 1) (horizon - count - 1) owner current current
        referenceTrace trace
        coordinate request request rfl unsent candidate
      have result := common.symm.trans (referenceFilter candidate)
      change ((driver).coordinateConsistentFrom rest coordinate candidate []
        current.environmentRecall) ↔ candidate.1.val = firstClock
      simpa only [ReactiveApplication.AddressedScheduler.unpack, restEq] using result)
  exact ⟨firstClock, localPositive, residual, firstMember, firstLeast, product⟩

end Vegas.EventGraphRuntime.PhaseSeedCalendar
