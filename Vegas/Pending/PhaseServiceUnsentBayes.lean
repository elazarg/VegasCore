/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceUnsentPosterior
import Interaction.ReactiveRoundReachability

/-! # Original local-seed laws at genuine unsent owner beliefs -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (priority : RestSeed → List (phaseApplication runtime leaks).EnvironmentEntry →
    (phaseApplication runtime leaks).EnvironmentView → Nat)
  (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
    PhaseSeedDecision)
  (laws : PhaseSeedAddress graph → PMF LocalSeed) (restLaw : PMF RestSeed)
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => phaseApplication runtime leaks
local notation "driver" => controller runtime leaks priority decideLocal
local notation "mixture" => ReactiveApplication.AddressedScheduler.coordinateImplementation
  (controller runtime leaks priority decideLocal) laws restLaw
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "model" => ReactiveApplication.ResponseMenu.information menu initial horizon
  (ReactiveApplication.SchedulerImplementation.scheduler mixture)
local notation "SeedAt" => ReactiveApplication.AddressedScheduler.CoordinateSeed
  (Address := PhaseSeedAddress graph) (LocalSeed := LocalSeed) (RestSeed := RestSeed)
local notation "prior" => independentProduct
  (ReactiveApplication.AddressedScheduler.coordinateLaws laws restLaw)
local notation "draws" => fun state : (app).ProtocolState => match state with
  | none => prior
  | some current => ReactiveApplication.SchedulerImplementation.posterior mixture
      (ReactiveApplication.Execution.environmentRecall
        (ReactiveApplication.Control.execution current))

/-- One original filtered local-seed law separates from the full history and
all remaining seeds for every belief on the actual owner information fiber.
Its seed constraint depends only on the local clock word, across private types.
This includes limiting assessments and sites of zero equilibrium probability. -/
theorem belief_unsent_seed_product
    (timed : DeadlineExpiry runtime decideLocal)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (owner : Player) (site : (model).InformationSite owner)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (siteInfo : site.1 = some (past, view)) (coordinate : PhaseSeedAddress graph)
    (request : PhaseRuntimeState.requests view.application.2 owner coordinate.1)
    (unsent : ∀ message ∈ (app).outputs past,
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false) :
    ∃ (event : Set LocalSeed)
      (localPositive : ∃ seed ∈ event, seed ∈ (laws coordinate).support),
      (∀ (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed)) (left : Nat)
        (other : (app).Execution)
        (_trace : ((menu).protocol initial horizon ((driver).family seeds)).Trace
          (some ⟨left, some owner, other⟩)),
        other.application.SeedRequest owner coordinate.1 →
        (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
          (other.recall owner) (other.observe app owner)).activationClocks ++
          [(PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
            (other.recall owner) (other.observe app owner)).elapsed] =
          (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
            past view).activationClocks ++
            [(PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
              past view).elapsed] →
        (∀ message ∈ (app).outputs (other.recall owner),
          PhaseSeedScheduler.ownPacket coordinate.1 owner message = false) →
        ∀ candidate, (driver).coordinateConsistentFrom seeds.1 coordinate candidate []
          other.environmentRecall ↔ candidate ∈ event) ∧
      ∀ belief : PMF ((model).InformationHistory owner site.1),
      ∃ residual : PMF (((model).InformationHistory owner site.1) ×
        ((index : {index : Option (PhaseSeedAddress graph) // index ≠ some coordinate}) →
          SeedAt index)),
      (belief.bind fun history => (draws history.1.state).map fun values :
          (index : Option (PhaseSeedAddress graph)) → SeedAt index => (values (some coordinate),
          (history, fun index : {index : Option (PhaseSeedAddress graph) //
            index ≠ some coordinate} => values index))) =
        ((laws coordinate).filter event localPositive).bind fun seed =>
          residual.map (Prod.mk seed) := by
  classical
  let players := (menu).uniformResponses
  have covered : ∀ who previous current action, action ∈ (players who previous current).support →
      action ∈ (menu).actions who previous current := by
    intro who previous current action supported
    exact ((menu).uniformResponses_support who previous current action).mp supported
  have perHistory : ∀ history : (model).InformationHistory owner site.1,
      ∃ (event : Set LocalSeed)
        (localPositive : ∃ seed ∈ event, seed ∈ (laws coordinate).support)
        (remaining : PMF ((index : {index : Option (PhaseSeedAddress graph) //
          index ≠ some coordinate}) → SeedAt index)),
        ((draws history.1.state).map fun values :
          (index : Option (PhaseSeedAddress graph)) → SeedAt index => (values (some coordinate),
          fun index : {index : Option (PhaseSeedAddress graph) //
            index ≠ some coordinate} => values index)) =
          (((laws coordinate).filter event localPositive).bind fun seed =>
            remaining.map (Prod.mk seed)) ∧
        (∃ (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed)) (left : Nat)
          (current : (app).Execution),
          Nonempty (((menu).protocol initial horizon ((driver).family seeds)).Trace
            (some ⟨left, some owner, current⟩)) ∧
          current.application.SeedRequest owner coordinate.1 ∧
          (current.recall owner, current.observe app owner) = (past, view)) ∧
        ∀ (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed)) (left : Nat)
          (current : (app).Execution)
          (_trace : ((menu).protocol initial horizon ((driver).family seeds)).Trace
            (some ⟨left, some owner, current⟩)),
          current.application.SeedRequest owner coordinate.1 →
          (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
            (current.recall owner) (current.observe app owner)).activationClocks ++
            [(PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
              (current.recall owner) (current.observe app owner)).elapsed] =
            (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
              past view).activationClocks ++
              [(PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
                past view).elapsed] →
          (∀ message ∈ (app).outputs (current.recall owner),
            PhaseSeedScheduler.ownPacket coordinate.1 owner message = false) →
          ∀ candidate, (driver).coordinateConsistentFrom seeds.1 coordinate candidate []
            current.environmentRecall ↔ candidate ∈ event := by
    intro history
    have observed := ((menu).info initial horizon (mixture).scheduler owner
      history.1.trace).symm.trans (history.2.trans siteInfo)
    obtain ⟨control, controlEq⟩ : ∃ control, history.1.state = some control := by
      cases stateEq : history.1.state with
      | none => rw [stateEq] at observed; cases observed
      | some control => exact ⟨control, rfl⟩
    rw [controlEq] at observed
    rw [controlEq]
    have acting : control.actor = some owner :=
      ((app).observe_isSome owner (some control)).mp (by rw [observed]; rfl)
    have represented := (menu).roundSupported_uniform initial horizon (mixture).scheduler
      (controlEq ▸ history.1.trace)
    dsimp only [ReactiveApplication.RoundSupported] at represented
    rw [acting] at represented
    obtain ⟨accounted, count, before, command, position, priorReached, chosen,
      commandActor, moved⟩ := represented
    have within : count < horizon := by omega
    rw [ReactiveApplication.roundsFrom, PMF.support_bind] at priorReached
    obtain ⟨inputState, initialSupported, reached⟩ := Set.mem_iUnion₂.mp priorReached
    obtain ⟨input, inputSupported, rfl⟩ :=
      (PMF.mem_support_map_iff _ _ _).mp initialSupported
    have commandEq : command = .activate owner := by
      cases command with
      | activate who =>
          exact congrArg ReactiveApplication.Command.activate (Option.some.inj commandActor)
      | «include» id => cases commandActor
      | application operation => cases commandActor
      | wait => cases commandActor
    subst command
    let current := control.execution
    have information : (current.recall owner, current.observe app owner) = (past, view) := by
      change (if control.actor = some owner then
        some (current.recall owner, current.observe app owner) else none) =
          some (past, view) at observed
      rw [ite_eq_left acting] at observed
      exact Option.some.inj observed
    have pastEq : current.recall owner = past := congrArg Prod.fst information
    have viewEq : current.observe app owner = view := congrArg Prod.snd information
    have invariant := ReactiveApplication.Invariant.policyInvariant app
      (phaseApplication_invariant runtime leaks input) players
    have priorValid := invariant.runRounds (mixture).scheduler count
        (ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan input))
          before (PhaseRuntimeState.initial_invariant plan input).1 reached
    have valid := (phaseApplication_invariant runtime leaks input).environmentStep before current
      (.activate owner) priorValid moved
    have requested : current.application.SeedRequest owner coordinate.1 := by
      apply (PhaseRuntimeState.requests_publicView current.application valid owner coordinate.1).mp
      change PhaseRuntimeState.requests
        (current.observe app owner).application.2 owner coordinate.1
      rwa [viewEq]
    obtain ⟨event, localPositive, remaining, product, uniform⟩ := unsent_posterior_splitAt
      runtime leaks priority decideLocal timed laws restLaw bounds plan ordered maximal inputs
      horizon count within players covered input inputSupported before current owner reached
        chosen moved coordinate requested (by rwa [pastEq])
    obtain ⟨values, supported⟩ := ((mixture).posterior current.environmentRecall).support_nonempty
    obtain ⟨_, trace⟩ := PhaseSeedScheduler.trace_of_posterior_support runtime leaks (driver)
      laws restLaw bounds plan inputs horizon count within players covered input
        inputSupported before current owner reached chosen moved values supported
    refine ⟨event, localPositive, remaining, product,
      ⟨ReactiveApplication.AddressedScheduler.unpack values, horizon - count - 1,
        current, trace, requested, information⟩, ?_⟩
    intro seeds left other otherTrace otherRequest otherClocks otherUnsent candidate
    have currentClocks := congrArg (fun pair : List (app).PlayerEntry × (app).PlayerView =>
      let input := PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
        pair.1 pair.2
      input.activationClocks ++ [input.elapsed]) information
    exact uniform seeds left other otherTrace otherRequest
      (currentClocks.trans otherClocks.symm) otherUnsent candidate
  obtain ⟨reference, _rest⟩ := site.2
  obtain ⟨event, localPositive, _, _, witness, uniform⟩ := perHistory reference
  obtain ⟨seeds, left, current, ⟨trace⟩, requested, information⟩ := witness
  have referenceClocks := congrArg (fun pair : List (app).PlayerEntry × (app).PlayerView =>
    let input := PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner pair.1 pair.2
    input.activationClocks ++ [input.elapsed]) information
  have referenceUnsent : ∀ message ∈ (app).outputs (current.recall owner),
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false := by
    have recalled : current.recall owner = past := congrArg Prod.fst information
    rw [recalled]
    exact unsent
  have sameFactor : ∀ history : (model).InformationHistory owner site.1, ∃ remaining : PMF
      ((index : {index : Option (PhaseSeedAddress graph) // index ≠ some coordinate}) →
        SeedAt index),
      ((draws history.1.state).map fun values :
          (index : Option (PhaseSeedAddress graph)) → SeedAt index => (values (some coordinate),
        fun index : {index : Option (PhaseSeedAddress graph) // index ≠ some coordinate} =>
          values index)) =
        ((laws coordinate).filter event localPositive).bind fun seed =>
          remaining.map (Prod.mk seed) := by
    intro history
    obtain ⟨otherEvent, otherPositive, remaining, product, _, otherUniform⟩ :=
      perHistory history
    have same : otherEvent = event := Set.ext fun candidate =>
      (otherUniform seeds left current trace requested referenceClocks referenceUnsent
        candidate).symm.trans
        (uniform seeds left current trace requested referenceClocks referenceUnsent candidate)
    subst otherEvent
    exact ⟨remaining, product⟩
  refine ⟨event, localPositive, uniform, ?_⟩
  intro belief
  let remaining := fun history => Classical.choose (sameFactor history)
  let residual := belief.bind fun history => (remaining history).map (Prod.mk history)
  refine ⟨residual, ?_⟩
  change (belief.bind fun history => (draws history.1.state).map fun values :
          (index : Option (PhaseSeedAddress graph)) → SeedAt index =>
    (values (some coordinate), (history, fun index : {index : Option (PhaseSeedAddress graph) //
      index ≠ some coordinate} => values index))) = _
  calc
    _ = belief.bind (fun history =>
        ((laws coordinate).filter event
          localPositive).bind fun seed =>
            (remaining history).map fun others => (seed, (history, others))) := by
      apply bind_congr_on_support _
      intro history _supported
      have product := Classical.choose_spec (sameFactor history)
      have mapped := congrArg (PMF.map fun pair => (pair.1, (history, pair.2))) product
      simpa only [remaining, PMF.map_bind, PMF.map_comp,
        Function.comp_def] using mapped
    _ = _ := by
      rw [PMF.bind_comm]
      simp only [residual, PMF.map_bind, PMF.map_comp, Function.comp_def]

end Vegas.EventGraphRuntime.PhaseServiceScheduler
