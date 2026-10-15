/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedFirstCallback
import Vegas.Pending.PhaseSeedUnsentBayes

/-! # Protected first callbacks under the actual original-seed Bayes law -/

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
  (delayLaw : (event : graph.EventId) → PMF (Fin (delay event + 1)))
  (coinLaw : graph.EventId → Fin (clockLimit runtime delay + 1) → PMF Bool)
  (restLaw : PMF RestSeed) (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => phaseApplication runtime leaks
local notation "original" => laws runtime delay delayLaw coinLaw
local notation "mixture" => ReactiveApplication.AddressedScheduler.coordinateImplementation
  (controller runtime leaks delay bound priority) original restLaw
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "model" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon
  (ReactiveApplication.SchedulerImplementation.scheduler mixture)

variable [historiesFinite : Finite (GameTheory.Protocol.ExecutionProtocol.History
  (ReactiveApplication.ResponseMenu.protocol (PhaseCount.onePacketMenu runtime leaks bounds)
    (PMF.map (PhaseRuntimeState.initial plan) inputs) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler
      (ReactiveApplication.AddressedScheduler.coordinateImplementation
        (controller runtime leaks delay bound priority)
        (laws runtime delay delayLaw coinLaw) restLaw))))]

include historiesFinite in
/-- Every positive-mass first response input of the actual mixture leaves the
full protected inclusion window. The original event law supplies the delay bound;
no independent service or chosen-posterior hypothesis is imposed. -/
theorem first_bayes_input_protected
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
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks owner coordinate.1 past)
    (timely : AsyncTimely runtime delay bound) :
    (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner past view).elapsed ≤
        delay coordinate.1.event ∧
      (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner past view).elapsed +
          bound coordinate.1.event < runtime.deadline coordinate.1.event := by
  obtain ⟨clock, supported, _residual, member, _least, _product⟩ :=
    bayesBelief_unsent_seed_product runtime leaks delay bound priority original restLaw bounds plan
      inputs horizon ordered maximal profile owner site positive past view siteInfo coordinate
        request unsent
  rw [inputActivationClocks_of_unrecorded runtime leaks coordinate.1 owner past view first,
    List.mem_singleton] at member
  obtain ⟨seed, equal, possible⟩ := supported
  have bounded := eventLaw_first_delay_le runtime delay delayLaw coinLaw coordinate.1.event seed
    possible
  change seed.1.val = clock at equal
  have fitting := timely coordinate.1.event (by rw [request.2.2.2.1]; rfl)
  constructor <;> omega

end Vegas.EventGraphRuntime.PhaseSeedCalendar
