/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceUnsentTranscript
import Vegas.Pending.PhaseSeedPosteriorTrace

/-! # Original filtered local-seed laws at genuine phased owner inputs -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (priority : RestSeed → List (phaseApplication runtime leaks).EnvironmentEntry →
    (phaseApplication runtime leaks).EnvironmentView → Nat)
  (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
    PhaseSeedDecision)

local notation "app" => phaseApplication runtime leaks
local notation "driver" => controller runtime leaks priority decideLocal
local notation "SeedAt" => ReactiveApplication.AddressedScheduler.CoordinateSeed
  (Address := PhaseSeedAddress graph) (LocalSeed := LocalSeed) (RestSeed := RestSeed)

/-- At an actual unsent callback, the ORIGINAL local-seed prior is filtered
by one constraint common to the entire owner-information fiber. It factors
from all remaining original coordinates, with their updated joint law intact. -/
theorem unsent_posterior_splitAt (timed : DeadlineExpiry runtime decideLocal)
    (laws : PhaseSeedAddress graph → PMF LocalSeed) (restLaw : PMF RestSeed)
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
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
    ∃ (event : Set LocalSeed) (localPositive : ∃ seed ∈ event, seed ∈ (laws coordinate).support)
      (residual : PMF ((index : {index : Option (PhaseSeedAddress graph) //
        index ≠ some coordinate}) → SeedAt index)),
      ((((driver).coordinateImplementation laws restLaw).posterior current.environmentRecall).map
        fun values => (values (some coordinate),
          fun index : {index : Option (PhaseSeedAddress graph) // index ≠ some coordinate} =>
            values index)) =
        (((laws coordinate).filter event localPositive).bind fun value =>
          residual.map (Prod.mk value)) ∧
      ∀ (otherSeeds : RestSeed × (PhaseSeedAddress graph → LocalSeed)) (otherRemaining : Nat)
        (other : (app).Execution)
        (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
          (inputs.map (PhaseRuntimeState.initial plan)) horizon
          ((driver).family otherSeeds)).Trace (some ⟨otherRemaining, some owner, other⟩)),
        other.application.SeedRequest owner coordinate.1 →
        (current.recall owner, current.observe app owner) =
          (other.recall owner, other.observe app owner) →
        ∀ candidate, (driver).coordinateConsistentFrom otherSeeds.1 coordinate candidate []
            other.environmentRecall ↔ candidate ∈ event := by
  classical
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let prior := independentProduct (ReactiveApplication.AddressedScheduler.coordinateLaws
    laws restLaw)
  let currentPosterior := ((driver).coordinateImplementation laws restLaw).posterior
    current.environmentRecall
  obtain ⟨reference, referenceSupported⟩ := currentPosterior.support_nonempty
  obtain ⟨referenceInitial, ⟨referenceTrace⟩⟩ :=
    PhaseSeedScheduler.trace_of_posterior_support runtime leaks (driver) laws restLaw bounds plan
      inputs horizon count within players covered input inputSupported before current owner reached
        chosen moved reference referenceSupported
  let event : Set LocalSeed := {candidate | (driver).coordinateConsistentFrom
    (ReactiveApplication.AddressedScheduler.unpack reference).1 coordinate candidate []
      current.environmentRecall}
  have compatible : ∀ values ∈ currentPosterior.support,
      (app).commandConsistentFrom
        (fun values => (driver).choose (ReactiveApplication.AddressedScheduler.unpack values))
        values [] current.environmentRecall := by
    intro values supported
    obtain ⟨_, ⟨trace⟩⟩ := PhaseSeedScheduler.trace_of_posterior_support runtime leaks (driver)
      laws restLaw bounds plan inputs horizon count within players covered input inputSupported
        before current owner reached chosen moved values supported
    have raw := menu.toRawTrace initial horizon
      ((driver).family (ReactiveApplication.AddressedScheduler.unpack values)) trace
    exact ((app).deterministic_transcript_invariant
      (fun values => (driver).choose (ReactiveApplication.AddressedScheduler.unpack values))
        values).history initial horizon (fun _ _ => trivial) raw
  have positive : ∃ values ∈ {values : (index : Option (PhaseSeedAddress graph)) → SeedAt index |
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
    (driver).posterior_splitAt_of_coordinate_constraint laws restLaw coordinate
      current.environmentRecall event positive (by
        intro rest available candidate
        obtain ⟨values, ⟨follows, restEq⟩, initialSupported⟩ := available
        have supported : values ∈ currentPosterior.support := by
          rw [currentEq]
          exact (PMF.mem_support_filter_iff positive).mpr ⟨follows, initialSupported⟩
        obtain ⟨_, ⟨trace⟩⟩ := PhaseSeedScheduler.trace_of_posterior_support runtime leaks (driver)
          laws restLaw bounds plan inputs horizon count within players covered input inputSupported
            before current owner reached chosen moved values supported
        have common := (unsent_information_transcript runtime leaks priority decideLocal timed
          (ReactiveApplication.AddressedScheduler.unpack reference)
          (ReactiveApplication.AddressedScheduler.unpack values) bounds plan ordered maximal inputs
          horizon (horizon - count - 1) (horizon - count - 1) owner current current referenceTrace
            trace coordinate request request rfl unsent).2 candidate
        change (driver).coordinateConsistentFrom rest coordinate candidate []
          current.environmentRecall ↔ candidate ∈ event
        simpa only [event, Set.mem_ofPred_eq, ReactiveApplication.AddressedScheduler.unpack, restEq]
          using common.symm)
  refine ⟨event, localPositive, residual, product, ?_⟩
  intro otherSeeds otherRemaining other otherTrace otherRequest same candidate
  exact ((unsent_information_transcript runtime leaks priority decideLocal timed
    (ReactiveApplication.AddressedScheduler.unpack reference) otherSeeds bounds plan ordered maximal
    inputs horizon (horizon - count - 1) otherRemaining owner current other referenceTrace
      otherTrace coordinate request otherRequest same unsent).2 candidate).symm

end Vegas.EventGraphRuntime.PhaseServiceScheduler
