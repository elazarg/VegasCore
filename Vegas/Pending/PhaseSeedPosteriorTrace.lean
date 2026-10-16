/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedUnsentFiber
import Interaction.ReactiveAddressedCoordinatePosterior
import Interaction.ReactiveSchedulerSeedSupport

/-! # Genuine phased histories for every supported original posterior seed -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed Query : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

variable (driver : ReactiveApplication.AddressedScheduler
  (phaseApplication runtime leaks) (PhaseSeedAddress graph) LocalSeed RestSeed Query)

local notation "SeedAt" => ReactiveApplication.AddressedScheduler.CoordinateSeed
  (Address := PhaseSeedAddress graph) (LocalSeed := LocalSeed) (RestSeed := RestSeed)

/-- The same actual mixture callback has a genuine counted history under every
supported original posterior seed. The initial draw is retained. -/
theorem trace_of_posterior_support (laws : PhaseSeedAddress graph → PMF LocalSeed)
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

end Vegas.EventGraphRuntime.PhaseSeedScheduler
