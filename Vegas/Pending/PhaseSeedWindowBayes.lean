/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedUnsentBayes
import Vegas.Pending.PhaseSeedWindowEquivalence

/-! # Original local-window laws under actual coarse owner Bayes beliefs -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (delay bound : graph.EventId → Nat)
  (priority : RestSeed → List (phaseApplication runtime leaks).EnvironmentEntry →
    (phaseApplication runtime leaks).EnvironmentView → Nat)
  (laws : PhaseSeedAddress graph → PMF (Seed runtime delay)) (restLaw : PMF RestSeed)
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => phaseApplication runtime leaks
local notation "driver" => controller runtime leaks delay bound priority
local notation "mixture" => ReactiveApplication.AddressedScheduler.coordinateImplementation
  (controller runtime leaks delay bound priority) laws restLaw
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "model" => ReactiveApplication.ResponseMenu.information menu initial horizon
  (ReactiveApplication.SchedulerImplementation.scheduler mixture)
local notation "SeedAt" => ReactiveApplication.AddressedScheduler.CoordinateSeed
  (Address := PhaseSeedAddress graph) (LocalSeed := Seed runtime delay) (RestSeed := RestSeed)
local notation "prior" => independentProduct
  (ReactiveApplication.AddressedScheduler.coordinateLaws laws restLaw)
local notation "draws" => fun state : (app).ProtocolState => match state with
  | none => prior
  | some current => ReactiveApplication.SchedulerImplementation.posterior mixture
      (ReactiveApplication.Execution.environmentRecall
        (ReactiveApplication.Control.execution current))

variable [Finite (GameTheory.Protocol.ExecutionProtocol.History
  (ReactiveApplication.ResponseMenu.protocol (PhaseCount.onePacketMenu runtime leaks bounds)
    (PMF.map (PhaseRuntimeState.initial plan) inputs) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler
      (ReactiveApplication.AddressedScheduler.coordinateImplementation
        (controller runtime leaks delay bound priority) laws restLaw))))]

open Classical in
theorem bayesBelief_original_window_law
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (profile : ∀ who, (model).BehavioralPolicy who)
    (owner : Player) (site : (model).InformationSite owner)
    (positive : 0 < (model).informationMass profile owner site)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (siteInfo : site.1 = some (past, view)) (coordinate : PhaseSeedAddress graph)
    (request : PhaseRuntimeState.requests view.application.2 owner coordinate.1)
    (unsent : ∀ message ∈ (app).outputs past,
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false)
    (sent : Nat) :
    ∃ (firstClock : Nat)
      (localPositive : ∃ seed ∈ {seed : Seed runtime delay | seed.1.val = firstClock},
        seed ∈ (laws coordinate).support),
      firstClock ∈ inputActivationClocks runtime leaks coordinate.1 owner past view ∧
      (∀ clock ∈ inputActivationClocks runtime leaks coordinate.1 owner past view,
        firstClock ≤ clock) ∧
      (((((model).bayesBelief profile owner site
        ((menu).decisionInformationAntichain initial horizon (mixture).scheduler owner site)
          positive).map (fun history => history.1.state)).bind fun state =>
        (draws state).map fun values :
          (index : Option (PhaseSeedAddress graph)) → SeedAt index =>
            (values (some coordinate), (state, fun index :
              {index : Option (PhaseSeedAddress graph) // index ≠ some coordinate} =>
                values index))).map fun pair =>
        decide (InclusionWindow runtime delay bound coordinate pair.1 sent)) =
          ((laws coordinate).filter {seed : Seed runtime delay | seed.1.val = firstClock}
            localPositive).map fun seed =>
              decide (InclusionWindow runtime delay bound coordinate seed sent) := by
  obtain ⟨firstClock, localPositive, residual, member, least, product⟩ :=
    bayesBelief_unsent_seed_product runtime leaks delay bound priority laws restLaw bounds plan
      inputs horizon ordered maximal profile owner site positive past view siteInfo coordinate
      request unsent
  refine ⟨firstClock, localPositive, member, least, ?_⟩
  erw [product, PMF.map_bind]
  let localLaw := (laws coordinate).filter
    {seed : Seed runtime delay | seed.1.val = firstClock} localPositive
  change (localLaw.bind fun seed => (residual.map (Prod.mk seed)).map fun pair =>
      decide (InclusionWindow runtime delay bound coordinate pair.1 sent)) =
    localLaw.map (fun seed => decide (InclusionWindow runtime delay bound coordinate seed sent))
  calc
    _ = localLaw.bind (fun seed => PMF.pure
        (decide (InclusionWindow runtime delay bound coordinate seed sent))) := by
      apply congrArg (fun kernel => localLaw.bind kernel)
      funext seed
      apply pmf_eq_pure_of_support_subset_singleton
      intro outcome outcomeSupported
      obtain ⟨pair, pairSupported, pairEq⟩ := PMF.support_map .. ▸ outcomeSupported
      obtain ⟨remaining, _remainingSupported, origin⟩ := PMF.support_map .. ▸ pairSupported
      have sameSeed : pair.1 = seed := by rw [← origin]
      exact Set.mem_singleton_iff.mpr
        (pairEq.symm.trans (decide_eq_decide.mpr (by rw [sameSeed])))
    _ = _ := rfl

end Vegas.EventGraphRuntime.PhaseSeedCalendar
