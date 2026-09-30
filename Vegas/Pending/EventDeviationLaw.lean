/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPrescribedLaw
import Vegas.Pending.EventReplayEnvironment
import Vegas.Pending.EventServiceCompletion
import Vegas.Pending.EventServicePredraw
import Vegas.Pending.EventServiceReachability

/-! # Deviation law for the actual adaptive event service -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Every focal action completed by one supported transition from a reachable
control is selected by the policy extracted from actual reached actions. -/
theorem reachedFocalPolicy_controlStep
    (runtime : EventGraphRuntime graph)
    (inputs : PMF graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player)
    (functional : ∀ (event : graph.EventId) (observation : graph.PlayerObservation focal)
      (left right : graph.Action event),
      ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation left →
        ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation right → left = right)
    (before after : ServiceControl runtime)
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order before)
    (transition : after ∈
      (runtime.serviceControlStep roster reactionRounds players wire order before).support)
    (event : graph.EventId) (actor : graph.actor? event = some focal)
    (ready : before.execution.native.application.config.cut.Ready event)
    (action : graph.Action event)
    (completion : after.execution.native.application.config ∈
      (before.execution.native.application.config.step event ready action).support) :
    graph.normalizePolicy focal
        (reachedFocalPolicy runtime inputs roster reactionRounds players wire order focal)
        event actor (graph.playerObserve focal before.execution.native.application.config) =
      PMF.pure action := by
  apply runtime.reachedFocalPolicy_eq_of_functional inputs roster reactionRounds players wire
    order focal functional event actor
  exact .realized before after reachable transition actor ready completion rfl

/-- Instruction-level form of `reachedFocalPolicy_controlStep`. -/
theorem reachedFocalPolicy_serviceStep
    (runtime : EventGraphRuntime graph)
    (inputs : PMF graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player)
    (functional : ∀ (event : graph.EventId) (observation : graph.PlayerObservation focal)
      (left right : graph.Action event),
      ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation left →
        ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation right → left = right)
    (epochs : Nat) (instruction : ServiceInstruction graph)
    (rest : List (ServiceInstruction graph))
    (execution next : runtime.application.PolicyExecution)
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order
      ⟨epochs, instruction :: rest, execution⟩)
    (step : next ∈ (runtime.serviceStep players wire instruction execution).support)
    (event : graph.EventId) (actor : graph.actor? event = some focal)
    (ready : execution.native.application.config.cut.Ready event)
    (action : graph.Action event)
    (completion : next.native.application.config ∈
      (execution.native.application.config.step event ready action).support) :
    graph.normalizePolicy focal
        (reachedFocalPolicy runtime inputs roster reactionRounds players wire order focal)
        event actor (graph.playerObserve focal execution.native.application.config) =
      PMF.pure action := by
  let before : ServiceControl runtime := ⟨epochs, instruction :: rest, execution⟩
  let after : ServiceControl runtime := ⟨epochs, rest, next⟩
  apply runtime.reachedFocalPolicy_controlStep inputs roster reactionRounds players wire order
    focal functional before after reachable
  · simp only [before, after, serviceControlStep, PMF.support_map, Set.mem_image]
    exact ⟨next, step, rfl⟩
  · exact completion

/-- The native law of a unilateral deviation follows from two structural
reachability facts: functionality of reached focal actions and the
unchanged-owner activation-age certificate. -/
theorem servicedEventGame_reached_store_law
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered)
    (inputs : PMF graph.Inputs) (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (focal : Player) (replacement : runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    let players := Profile.update
      (sig := MessageApplication.policySignature Player runtime.application)
      (runtime.compileProfile profile) focal replacement
    let extracted :=
      reachedFocalPolicy runtime inputs roster reactionRounds players wire order focal
    (∀ (event : graph.EventId) (observation : graph.PlayerObservation focal)
      (left right : graph.Action event),
      ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation left →
        ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation right → left = right) →
    (∀ (control : ServiceControl runtime),
      ServiceReachable runtime inputs roster reactionRounds players wire order control →
      ∀ owner, owner ≠ focal → ∀ event, graph.actor? event = some owner → ∀ entered,
        control.execution.native.application.activatedAt event = some entered →
        event ∉ control.execution.native.application.config.cut.completed →
        control.execution.native.application.clock - entered ≤ 1) →
    ((runtime.servicedEventGame inputs roster reactionRounds wire order).play players).map
        (fun next => next.native.application.config.store) =
      inputs.bind fun input =>
        (graph.runPolicies graph.canonicalScheduler
          (graph.normalizeProfile
            (Profile.update (sig := graph.gameSignature) profile focal extracted)) input).map
              (fun config => config.store) := by
  dsimp only
  intro functional activationAge
  let players := Profile.update
    (sig := MessageApplication.policySignature Player runtime.application)
    (runtime.compileProfile profile) focal replacement
  let extracted := reachedFocalPolicy runtime inputs roster reactionRounds players wire order focal
  let deviationProfile := Profile.update (sig := graph.gameSignature) profile focal extracted
  have compiled : ∀ owner, owner ≠ focal →
      players owner = runtime.compilePlayerPolicy owner (deviationProfile owner) := by
    intro owner other
    have profileEq : deviationProfile owner = profile owner := Profile.update_of_ne _ _ other
    rw [profileEq]
    exact Profile.update_of_ne _ _ other
  have selected : FreeActionsSelected runtime inputs roster reactionRounds players wire order
      deviationProfile (· ≠ focal) := by
    intro epochs instruction rest execution next reachable step event owner actor free ready action
      completion
    have same : owner = focal := by
      by_contra other
      exact free other
    subst owner
    have focalProfile : deviationProfile focal = extracted := Profile.update_same _ _ _
    rw [focalProfile]
    exact runtime.reachedFocalPolicy_serviceStep inputs roster reactionRounds players wire order
      focal functional epochs instruction rest execution next reachable step event actor ready
      action completion
  have environmentState : ∀ control,
      ServiceReachable runtime inputs roster reactionRounds players wire order control →
      PrescribedEnvironmentState runtime control.execution (· ≠ focal) := by
    intro control reachable
    exact reachable.prescribedEnvironmentState runtime ordered inputs deviationProfile roster
      reactionRounds players wire order (· ≠ focal) control compiled
      (activationAge control reachable)
  change (inputs.bind _).map _ = _
  rw [PMF.map_bind]
  apply bind_congr_on_support _
  intro input inputMem
  exact runtime.runService_store_law feasible ordered inputs input inputMem deviationProfile roster
    reactionRounds players wire order (· ≠ focal) selected compiled environmentState

/-- Joint predrawing of the focal player, wire, and adaptive order turns a
finitely branching native deviation into a finite mixture of graph-policy
deviations. -/
theorem exists_reachedPolicy_mixture_store_law
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered) (finite : graph.FiniteActions)
    (inputs : PMF graph.Inputs) (inputsFinite : inputs.support.Finite)
    (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (focal : Player) (replacement : runtime.application.PlayerPolicy)
    (replacementFinite : replacement.FiniteSupport)
    (wire : runtime.application.WirePolicy) (wireFinite : wire.FiniteSupport)
    (order : runtime.ServiceOrderPolicy) (orderFinite : order.FiniteSupport)
    (functional : ∀ (response : PureServiceResponses runtime) (event : graph.EventId)
      (observation : graph.PlayerObservation focal) (left right : graph.Action event),
      let players := Profile.update
        (sig := MessageApplication.policySignature Player runtime.application)
        (runtime.compileProfile profile) focal response.playerPure
      ReachedFocalAction runtime inputs roster reactionRounds players response.wirePure
          response.orderPure focal event observation left →
        ReachedFocalAction runtime inputs roster reactionRounds players response.wirePure
          response.orderPure focal event observation right → left = right)
    (activationAge : ∀ (response : PureServiceResponses runtime),
      let players := Profile.update
        (sig := MessageApplication.policySignature Player runtime.application)
        (runtime.compileProfile profile) focal response.playerPure
      ∀ (control : ServiceControl runtime),
        ServiceReachable runtime inputs roster reactionRounds players response.wirePure
          response.orderPure control →
        ∀ owner, owner ≠ focal → ∀ event, graph.actor? event = some owner → ∀ entered,
          control.execution.native.application.activatedAt event = some entered →
          event ∉ control.execution.native.application.config.cut.completed →
          control.execution.native.application.clock - entered ≤ 1) :
    ∃ mixture : PMF (graph.BehavioralPolicy focal), mixture.support.Finite ∧
      ((runtime.servicedEventGame inputs roster reactionRounds wire order).play
        (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
          (runtime.compileProfile profile) focal replacement)).map
            (fun next => next.native.application.config.store) =
        mixture.bind fun alternative =>
          inputs.bind fun input =>
            (graph.runPolicies graph.canonicalScheduler
              (graph.normalizeProfile
                (Profile.update (sig := graph.gameSignature) profile focal alternative))
              input).map (fun config => config.store) := by
  obtain ⟨responses, responsesFinite, responseLaw⟩ :=
    runtime.exists_pureServiceResponses_mixture inputs roster reactionRounds
      (runtime.compileProfile profile) wire order focal replacement inputsFinite
      (runtime.compileProfile_finiteSupport (finite.profileFiniteSupport profile)) wireFinite
      orderFinite replacementFinite
  let nativePlayers : PureServiceResponses runtime →
      Player → runtime.application.PlayerPolicy := fun response =>
    Profile.update (sig := MessageApplication.policySignature Player runtime.application)
      (runtime.compileProfile profile) focal response.playerPure
  let alternative : PureServiceResponses runtime → graph.BehavioralPolicy focal :=
    fun response => runtime.reachedFocalPolicy inputs roster reactionRounds
      (nativePlayers response) response.wirePure response.orderPure focal
  let mixture : PMF (graph.BehavioralPolicy focal) := responses.map alternative
  refine ⟨mixture, by rw [PMF.support_map]; exact responsesFinite.image _, ?_⟩
  have projected := congrArg
    (fun measure : PMF runtime.application.PolicyExecution =>
      measure.map fun next => next.native.application.config.store) responseLaw
  rw [PMF.map_bind] at projected
  calc
    _ = responses.bind (fun response =>
          ((runtime.servicedEventGame inputs roster reactionRounds response.wirePure
            response.orderPure).play (nativePlayers response)).map
              (fun next => next.native.application.config.store)) := projected
    _ = responses.bind (fun response =>
          inputs.bind fun input =>
            (graph.runPolicies graph.canonicalScheduler
              (graph.normalizeProfile
                (Profile.update (sig := graph.gameSignature) profile focal
                  (alternative response))) input).map (fun config => config.store)) := by
        apply bind_congr_on_support _
        intro response _
        exact runtime.servicedEventGame_reached_store_law feasible ordered inputs profile roster
          reactionRounds focal response.playerPure response.wirePure response.orderPure
          (functional response) (activationAge response)
    _ = mixture.bind (fun alternative =>
          inputs.bind fun input =>
            (graph.runPolicies graph.canonicalScheduler
              (graph.normalizeProfile
                (Profile.update (sig := graph.gameSignature) profile focal alternative))
              input).map (fun config => config.store)) := by
        simp only [mixture, PMF.bind_map, Function.comp_def]

end Vegas.EventGraphRuntime
