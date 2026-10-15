/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedUnsentPosterior
import Interaction.ReactiveSchedulerSeedBayes
import Interaction.ReactiveSiteHorizon

/-! # The original event seed in actual unsent owner Bayes fibers -/

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

/-- The actual Bayes law, tagged by the original scheduler seeds, separates the
selected unsent event seed from the entire physical control and every other
original coordinate. Only its observed first delay filters the selected prior. -/
theorem bayesBelief_unsent_seed_product
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
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false) :
    ∃ (firstClock : Nat)
      (localPositive : ∃ seed ∈ {seed : Seed runtime delay | seed.1.val = firstClock},
        seed ∈ (laws coordinate).support)
      (residual : PMF ((app).ProtocolState ×
        ((index : {index : Option (PhaseSeedAddress graph) // index ≠ some coordinate}) →
          SeedAt index))),
      firstClock ∈ inputActivationClocks runtime leaks coordinate.1 owner past view ∧
      (∀ clock ∈ inputActivationClocks runtime leaks coordinate.1 owner past view,
        firstClock ≤ clock) ∧
      ((((model).bayesBelief profile owner site
        ((menu).decisionInformationAntichain initial horizon (mixture).scheduler owner site)
          positive).map (fun history => history.1.state)).bind fun state =>
        (draws state).map fun values :
          (index : Option (PhaseSeedAddress graph)) → SeedAt index => (values (some coordinate),
          (state, fun index : {index : Option (PhaseSeedAddress graph) //
            index ≠ some coordinate} => values index))) =
        ((laws coordinate).filter {seed : Seed runtime delay | seed.1.val = firstClock}
          localPositive).bind fun seed => residual.map (Prod.mk seed) := by
  classical
  have horizonPositive := (menu).informationSite_horizon_pos initial horizon
    (mixture).scheduler owner site
  let : NeZero horizon := ⟨ne_of_gt horizonPositive⟩
  let players := (menu).decodeProfile initial horizon (mixture).scheduler profile
  let occupied := (app).occupationControlLaw (mixture).scheduler players initial horizon
  let beliefs := ((model).bayesBelief profile owner site
    ((menu).decisionInformationAntichain initial horizon (mixture).scheduler owner site)
      positive).map (fun history => history.1.state)
  have present := (menu).occupation_observation_support initial horizon (mixture).scheduler
    profile owner site positive
  have beliefsEq : beliefs = fiberPosterior occupied ((app).observe owner) site.1 :=
    (menu).bayesBelief_state_eq_occupationPosterior initial horizon (mixture).scheduler profile
      owner site ((menu).decisionInformationAntichain initial horizon
        (mixture).scheduler owner site) positive
  have covered : ∀ who previous current action, action ∈ (players who previous current).support →
      action ∈ (menu).actions who previous current := by
    intro who previous current action supported
    exact (menu).decode_embedPolicy_covered initial horizon (mixture).scheduler who
      (profile who) previous current action supported
  have perState : ∀ state ∈ beliefs.support,
      ∃ (clock : Nat) (localPositive : ∃ seed ∈
        {seed : Seed runtime delay | seed.1.val = clock}, seed ∈ (laws coordinate).support)
        (remaining : PMF ((index : {index : Option (PhaseSeedAddress graph) //
          index ≠ some coordinate}) → SeedAt index)),
        clock ∈ inputActivationClocks runtime leaks coordinate.1 owner past view ∧
        (∀ other ∈ inputActivationClocks runtime leaks coordinate.1 owner past view,
          clock ≤ other) ∧
        ((draws state).map fun values :
          (index : Option (PhaseSeedAddress graph)) → SeedAt index => (values (some coordinate),
          fun index : {index : Option (PhaseSeedAddress graph) //
            index ≠ some coordinate} => values index)) =
          ((laws coordinate).filter {seed : Seed runtime delay | seed.1.val = clock}
            localPositive).bind fun seed => remaining.map (Prod.mk seed) := by
    intro state supported
    rw [beliefsEq] at supported
    obtain ⟨observed, actual⟩ := mem_support_fiberPosterior present supported
    unfold ReactiveApplication.occupationControlLaw at actual
    obtain ⟨time, _, actual⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ actual)
    unfold ReactiveApplication.commandControlLaw at actual
    obtain ⟨inputState, initialStateSupported, actual⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ actual)
    obtain ⟨input, inputSupported, rfl⟩ :=
      (PMF.mem_support_map_iff _ _ _).mp initialStateSupported
    obtain ⟨before, reached, actual⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ actual)
    obtain ⟨command, chosen, actual⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ actual)
    obtain ⟨current, moved, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp actual
    have active : command.actor? app = some owner := by
      apply ((app).observe_isSome owner
        (some ⟨horizon - time.val - 1, command.actor? app, current⟩)).mp
      rw [observed, siteInfo]
      rfl
    have commandEq : command = .activate owner := by
      cases command with
      | activate who => exact congrArg ReactiveApplication.Command.activate (Option.some.inj active)
      | «include» id => cases active
      | application command => cases active
      | wait => cases active
    subst command
    have information : (current.recall owner, current.observe app owner) = (past, view) := by
      have exactInfo := observed.trans siteInfo
      change (if (some owner : Option Player) = some owner then
        some (current.recall owner, current.observe app owner) else none) =
          some (past, view) at exactInfo
      rw [ite_eq_left rfl] at exactInfo
      exact Option.some.inj exactInfo
    have pastEq : current.recall owner = past := congrArg Prod.fst information
    have viewEq : current.observe app owner = view := congrArg Prod.snd information
    have invariant := ReactiveApplication.Invariant.policyInvariant app
      (phaseApplication_invariant runtime leaks input) players
    have priorValid := invariant.runRounds (mixture).scheduler time.val
        (ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan input))
          before (PhaseRuntimeState.initial_invariant plan input).1 reached
    have valid := (phaseApplication_invariant runtime leaks input).environmentStep before current
      (.activate owner) priorValid moved
    have requested : current.application.SeedRequest owner coordinate.1 := by
      apply (PhaseRuntimeState.requests_publicView current.application valid owner coordinate.1).mp
      change PhaseRuntimeState.requests
        (current.observe app owner).application.2 owner coordinate.1
      rwa [viewEq]
    obtain ⟨clock, localPositive, remaining, member, least, product⟩ := unsent_posterior_splitAt
      runtime leaks delay bound priority laws restLaw bounds plan ordered maximal inputs horizon
      time.val time.isLt players covered input inputSupported before current owner reached chosen
      moved coordinate requested (by rwa [pastEq])
    refine ⟨clock, localPositive, remaining, ?_, ?_, product⟩
    · simpa only [pastEq, viewEq] using member
    · simpa only [pastEq, viewEq] using least
  obtain ⟨reference, referenceSupported⟩ := beliefs.support_nonempty
  obtain ⟨firstClock, localPositive, _, member, least, _⟩ :=
    perState reference referenceSupported
  have sameFactor : ∀ state ∈ beliefs.support, ∃ remaining : PMF
      ((index : {index : Option (PhaseSeedAddress graph) // index ≠ some coordinate}) →
        SeedAt index),
      ((draws state).map fun values :
          (index : Option (PhaseSeedAddress graph)) → SeedAt index => (values (some coordinate),
        fun index : {index : Option (PhaseSeedAddress graph) // index ≠ some coordinate} =>
          values index)) =
        ((laws coordinate).filter {seed : Seed runtime delay | seed.1.val = firstClock}
          localPositive).bind fun seed => remaining.map (Prod.mk seed) := by
    intro state supported
    obtain ⟨clock, positiveClock, remaining, clockMember, clockLeast, product⟩ :=
      perState state supported
    have same : clock = firstClock := le_antisymm (clockLeast _ member) (least _ clockMember)
    subst clock
    exact ⟨remaining, product⟩
  let remaining := fun state => if supported : state ∈ beliefs.support then
    Classical.choose (sameFactor state supported) else
      independentProduct (fun index : {index : Option (PhaseSeedAddress graph) //
        index ≠ some coordinate} =>
          ReactiveApplication.AddressedScheduler.coordinateLaws laws restLaw index)
  let residual := beliefs.bind fun state => (remaining state).map (Prod.mk state)
  refine ⟨firstClock, localPositive, residual, member, least, ?_⟩
  change (beliefs.bind fun state => (draws state).map fun values :
          (index : Option (PhaseSeedAddress graph)) → SeedAt index =>
    (values (some coordinate), (state, fun index : {index : Option (PhaseSeedAddress graph) //
      index ≠ some coordinate} => values index))) = _
  calc
    _ = beliefs.bind (fun state =>
        ((laws coordinate).filter {seed : Seed runtime delay | seed.1.val = firstClock}
          localPositive).bind fun seed =>
            (remaining state).map fun others => (seed, (state, others))) := by
      apply bind_congr_on_support _
      intro state supported
      have product := Classical.choose_spec (sameFactor state supported)
      have mapped := congrArg (PMF.map fun pair => (pair.1, (state, pair.2))) product
      simpa only [remaining, dite_eq_left supported, PMF.map_bind, PMF.map_comp,
        Function.comp_def] using mapped
    _ = _ := by
      rw [PMF.bind_comm]
      simp only [residual, PMF.map_bind, PMF.map_comp, Function.comp_def]

end Vegas.EventGraphRuntime.PhaseSeedCalendar
