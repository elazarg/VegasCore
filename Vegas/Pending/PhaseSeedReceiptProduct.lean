/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedPosteriorResponse

/-! # Receipt independence from the full hidden current control -/

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
/-- An actual authored receipt is independent of the full current hidden control
under the original owner posterior. Future policies retain their full observations. -/
theorem bayes_receipt_control_product
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (enough : serviceHorizon runtime ≤ horizon)
    (profile : ∀ who, (model).BehavioralPolicy who)
    (owner : Player) (site : (model).InformationSite owner)
    (positive : 0 < (model).informationMass profile owner site)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (siteInfo : site.1 = some (past, view)) (coordinate : PhaseSeedAddress graph)
    (request : PhaseRuntimeState.requests view.application.2 owner coordinate.1)
    (unsent : ∀ message ∈ (app).outputs past,
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false)
    (material : WitnessedSubmission graph)
    (names : material.call.packet.event? graph = some coordinate.1.event)
    (permitted : (⟨some material⟩ : (app).Action) ∈ (menu).actions owner past view)
    (future : Player → (app).Policy)
    (covered : ∀ who previous current action, action ∈ (future who previous current).support →
      action ∈ (menu).actions who previous current) :
    let belief := (((model).bayesBelief profile owner site
      ((menu).decisionInformationAntichain initial horizon (mixture).scheduler owner site)
        positive).map fun history => history.1.state)
    ∃ (firstClock : Nat)
      (localPositive : ∃ seed ∈ {seed : Seed runtime delay | seed.1.val = firstClock},
        seed ∈ (laws coordinate).support),
      firstClock ∈ inputActivationClocks runtime leaks coordinate.1 owner past view ∧
      (∀ clock ∈ inputActivationClocks runtime leaks coordinate.1 owner past view,
        firstClock ≤ clock) ∧
      (belief.bind fun state =>
        (authoredReceiptLaw runtime leaks (mixture).scheduler future owner material state).map
          (fun receipt => (receipt, state))) =
      (((laws coordinate).filter {seed : Seed runtime delay | seed.1.val = firstClock}
        localPositive).map fun seed => some (decide (InclusionWindow runtime delay bound coordinate
          seed (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner past
            view).elapsed))).bind fun receipt => belief.map (Prod.mk receipt) := by
  classical
  dsimp only
  let belief := (((model).bayesBelief profile owner site
    ((menu).decisionInformationAntichain initial horizon (mixture).scheduler owner site)
      positive).map fun history => history.1.state)
  let sent :=
    (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner past view).elapsed
  obtain ⟨firstClock, localPositive, residual, member, least, product⟩ :=
    bayesBelief_unsent_seed_product runtime leaks delay bound priority laws restLaw bounds plan
      inputs horizon ordered maximal profile owner site positive past view siteInfo coordinate
      request unsent
  refine ⟨firstClock, localPositive, member, least, ?_⟩
  let localLaw := (laws coordinate).filter
    {seed : Seed runtime delay | seed.1.val = firstClock} localPositive
  let joint := belief.bind fun state => (draws state).map fun values :
    (index : Option (PhaseSeedAddress graph)) → SeedAt index =>
      (values (some coordinate), (state, fun index :
        {index : Option (PhaseSeedAddress graph) // index ≠ some coordinate} => values index))
  have residualState : residual.map Prod.fst = belief := by
    have states := congrArg (fun law => law.map (fun pair => pair.2.1)) product
    have constant {A : Type} (law : PMF A) (state : (app).ProtocolState) :
        law.map (fun _ => state) = PMF.pure state := PMF.map_const law state
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, constant,
      PMF.bind_const, PMF.bind_pure] at states
    exact states.symm
  have rows : (belief.bind fun state =>
      (authoredReceiptLaw runtime leaks (mixture).scheduler future owner material state).map
        (fun receipt => (receipt, state))) =
      joint.map (fun pair =>
        (some (decide (InclusionWindow runtime delay bound coordinate pair.1 sent)),
          pair.2.1)) := by
    simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
    apply bind_congr_on_support belief
    intro state supported
    obtain ⟨history, _historySupport, stateEq⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    have observed : (app).observe owner state = some (past, view) := by
      rw [← stateEq]
      exact ((menu).info initial horizon (mixture).scheduler owner history.1.trace).symm.trans
        (history.2.trans siteInfo)
    cases state with
    | none => cases observed
    | some current =>
        have acting : current.actor = some owner := by
          apply ((app).observe_isSome owner (some current)).mp
          rw [observed]
          rfl
        have sameInfo : (current.execution.recall owner, current.execution.observe app owner) =
            (past, view) := by
          change (if current.actor = some owner then
            some (current.execution.recall owner, current.execution.observe app owner) else none) =
              some (past, view) at observed
          rw [ite_eq_left acting] at observed
          exact Option.some.inj observed
        have row := bayes_authored_receipt_kernel runtime leaks delay bound priority laws restLaw
          bounds plan inputs horizon ordered maximal enough profile owner site positive past view
          coordinate current acting supported sameInfo request material names permitted future
          covered
        have mapped := congrArg (fun law : PMF (Option Bool) =>
          law.map (fun receipt => (receipt, some current))) row
        simp only [PMF.map_comp, Function.comp_def] at mapped
        exact mapped
  calc
    _ = _ := rows
    _ = localLaw.bind (fun seed => residual.map fun rest =>
        (some (decide (InclusionWindow runtime delay bound coordinate seed sent)), rest.1)) := by
      have mapped := congrArg (fun law => law.map (fun pair =>
        (some (decide (InclusionWindow runtime delay bound coordinate pair.1 sent)), pair.2.1)))
          product
      dsimp only [joint, localLaw, belief, sent]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at mapped ⊢
      exact mapped
    _ = _ := by
      simp only [PMF.bind_map, PMF.map_comp, Function.comp_def]
      apply congrArg (fun kernel => localLaw.bind kernel)
      funext seed
      have mapped := congrArg (fun law => law.map
        (Prod.mk (some (decide (InclusionWindow runtime delay bound coordinate seed sent)))))
          residualState
      dsimp only [belief, sent] at mapped ⊢
      simp only [PMF.map_comp, Function.comp_def] at mapped ⊢
      exact mapped

open Classical in
/-- The natural original-seed response continuation retains independence of its
receipt from the complete hidden control and every other original coordinate. -/
theorem bayes_receipt_original_residual_product
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (enough : serviceHorizon runtime ≤ horizon)
    (profile : ∀ who, (model).BehavioralPolicy who)
    (owner : Player) (site : (model).InformationSite owner)
    (positive : 0 < (model).informationMass profile owner site)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (siteInfo : site.1 = some (past, view)) (coordinate : PhaseSeedAddress graph)
    (request : PhaseRuntimeState.requests view.application.2 owner coordinate.1)
    (unsent : ∀ message ∈ (app).outputs past,
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false)
    (material : WitnessedSubmission graph)
    (names : material.call.packet.event? graph = some coordinate.1.event)
    (permitted : (⟨some material⟩ : (app).Action) ∈ (menu).actions owner past view)
    (future : Player → (app).Policy)
    (covered : ∀ who previous current action, action ∈ (future who previous current).support →
      action ∈ (menu).actions who previous current) :
    ∃ (firstClock : Nat)
      (localPositive : ∃ seed ∈ {seed : Seed runtime delay | seed.1.val = firstClock},
        seed ∈ (laws coordinate).support)
      (residual : PMF ((app).ProtocolState ×
        ((index : {index : Option (PhaseSeedAddress graph) // index ≠ some coordinate}) →
          SeedAt index))),
      firstClock ∈ inputActivationClocks runtime leaks coordinate.1 owner past view ∧
      (∀ clock ∈ inputActivationClocks runtime leaks coordinate.1 owner past view,
        firstClock ≤ clock) ∧
      (((((model).bayesBelief profile owner site
        ((menu).decisionInformationAntichain initial horizon (mixture).scheduler owner site)
          positive).map fun history => history.1.state).bind fun state =>
        (draws state).bind fun values :
          (index : Option (PhaseSeedAddress graph)) → SeedAt index =>
          (authoredReceiptLaw runtime leaks ((driver).family
            (ReactiveApplication.AddressedScheduler.unpack values)) future owner material state).map
            fun receipt => (receipt, (state, fun index :
              {index : Option (PhaseSeedAddress graph) // index ≠ some coordinate} =>
                values index)))) =
      (((laws coordinate).filter {seed : Seed runtime delay | seed.1.val = firstClock}
        localPositive).map fun seed => some (decide (InclusionWindow runtime delay bound coordinate
          seed (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner past
            view).elapsed))).bind fun receipt => residual.map (Prod.mk receipt) := by
  classical
  let belief := (((model).bayesBelief profile owner site
    ((menu).decisionInformationAntichain initial horizon (mixture).scheduler owner site)
      positive).map fun history => history.1.state)
  let sent :=
    (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner past view).elapsed
  obtain ⟨firstClock, localPositive, residual, member, least, product⟩ :=
    bayesBelief_unsent_seed_product runtime leaks delay bound priority laws restLaw bounds plan
      inputs horizon ordered maximal profile owner site positive past view siteInfo coordinate
      request unsent
  refine ⟨firstClock, localPositive, residual, member, least, ?_⟩
  have rows : (belief.bind fun state =>
      (draws state).bind fun values :
        (index : Option (PhaseSeedAddress graph)) → SeedAt index =>
        (authoredReceiptLaw runtime leaks ((driver).family
          (ReactiveApplication.AddressedScheduler.unpack values)) future owner material state).map
          fun receipt => (receipt, (state, fun index :
            {index : Option (PhaseSeedAddress graph) // index ≠ some coordinate} =>
              values index))) =
      ((belief.bind fun state => (draws state).map fun values :
        (index : Option (PhaseSeedAddress graph)) → SeedAt index =>
          (values (some coordinate), (state, fun index :
            {index : Option (PhaseSeedAddress graph) // index ≠ some coordinate} =>
              values index))).map
        fun pair => (some (decide (InclusionWindow runtime delay bound coordinate pair.1 sent)),
          pair.2)) := by
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    apply bind_congr_on_support belief
    intro state supported
    obtain ⟨history, _historySupport, stateEq⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    have observed : (app).observe owner state = some (past, view) := by
      rw [← stateEq]
      exact ((menu).info initial horizon (mixture).scheduler owner history.1.trace).symm.trans
        (history.2.trans siteInfo)
    cases state with
    | none => cases observed
    | some current =>
        have acting : current.actor = some owner := by
          apply ((app).observe_isSome owner (some current)).mp
          rw [observed]
          rfl
        have sameInfo : (current.execution.recall owner, current.execution.observe app owner) =
            (past, view) := by
          change (if current.actor = some owner then
            some (current.execution.recall owner, current.execution.observe app owner) else none) =
              some (past, view) at observed
          rw [ite_eq_left acting] at observed
          exact Option.some.inj observed
        have pastEq : current.execution.recall owner = past := congrArg Prod.fst sameInfo
        have viewEq : current.execution.observe app owner = view := congrArg Prod.snd sameInfo
        have requestView : PhaseRuntimeState.requests
            (current.execution.observe app owner).application.2 owner coordinate.1 := by
          erw [viewEq]
          exact request
        have available : (⟨some material⟩ : (app).Action) ∈ (menu).actions owner
            (current.execution.recall owner) (current.execution.observe app owner) := by
          erw [pastEq, viewEq]
          exact permitted
        have elapsedEq : current.execution.application.current.native.clock -
            (current.execution.application.current.native.activatedAt coordinate.1.event).getD
              current.execution.application.current.native.clock = sent := by
          change (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
            (current.execution.recall owner) (current.execution.observe app owner)).elapsed = sent
          erw [pastEq, viewEq]
        change (((mixture).posterior current.execution.environmentRecall).bind _) =
          (((mixture).posterior current.execution.environmentRecall).bind fun values =>
            PMF.pure (some (decide (InclusionWindow runtime delay bound coordinate
              (values (some coordinate)) sent)), (some current, fun index :
                {index : Option (PhaseSeedAddress graph) // index ≠ some coordinate} =>
                  values index)))
        apply bind_congr_on_support ((mixture).posterior current.execution.environmentRecall)
        intro values valueSupport
        have kernel := bayes_response_receipt_runRounds runtime leaks delay bound priority laws
          restLaw bounds plan inputs horizon ordered maximal enough profile owner site positive
          current acting supported values valueSupport coordinate requestView material names
          available future covered
        have mapped := congrArg (fun law : PMF Bool => law.map some) kernel
        have fixedKernel : authoredReceiptLaw runtime leaks ((driver).family
            (ReactiveApplication.AddressedScheduler.unpack values)) future owner material
              (some current) = PMF.pure (some (decide (InclusionWindow runtime delay bound
                coordinate (values (some coordinate)) sent))) := by
          simpa only [authoredReceiptLaw, PMF.map_comp, Function.comp_def, PMF.pure_map, elapsedEq]
            using mapped
        erw [fixedKernel, PMF.pure_map]
  calc
    _ = _ := rows
    _ = _ := by
      have mapped := congrArg (fun law => law.map (fun pair =>
        (some (decide (InclusionWindow runtime delay bound coordinate pair.1 sent)), pair.2)))
          product
      dsimp only [belief, sent]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_map] at mapped ⊢
      exact mapped

end Vegas.EventGraphRuntime.PhaseSeedCalendar
