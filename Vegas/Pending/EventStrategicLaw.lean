/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventDeviationLaw
import Vegas.Pending.EventPrescribedReachability
import Vegas.Pending.EventActionLocality

/-! # Strategic reduction for the native event service -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Every native focal replacement has the terminal store law of a finite
mixture of graph-policy replacements against the unchanged opponents. -/
theorem exists_deviation_mixture_store_law
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered)
    (inputs : FinDist graph.Inputs) (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (focal : Player) (replacement : runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ∃ mixture : FinDist (graph.BehavioralPolicy focal),
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
  have functional : ∀ (response : PureServiceResponses runtime) (event : graph.EventId)
      (observation : graph.PlayerObservation focal) (left right : graph.Action event),
      let players := Profile.update
        (sig := MessageApplication.policySignature Player runtime.application)
        (runtime.compileProfile profile) focal response.playerPure
      ReachedFocalAction runtime inputs roster reactionRounds players response.wirePure
          response.orderPure focal event observation left →
        ReachedFocalAction runtime inputs roster reactionRounds players response.wirePure
          response.orderPure focal event observation right → left = right := by
    intro response event observation left right
    dsimp only
    intro leftReached rightReached
    let players := Profile.update
      (sig := MessageApplication.policySignature Player runtime.application)
      (runtime.compileProfile profile) focal response.playerPure
    have fixedFocal : players focal = fun history view =>
        FinDist.pure (response.player history view) := by
      simp only [players, Profile.update_same]
      rfl
    have fixedWire : response.wirePure = fun history view =>
        FinDist.pure (response.wire history view) := rfl
    have fixedOrder : response.orderPure = fun history view =>
        FinDist.pure (response.order history view) := rfl
    have opponentCompiled : ∀ owner, owner ≠ focal →
        players owner = runtime.compilePlayerPolicy owner (profile owner) := by
      intro owner different
      exact Profile.update_of_ne _ _ different
    exact runtime.reachedFocalAction_eq feasible ordered inputs profile roster reactionRounds
      players response.wirePure response.orderPure focal response.player fixedFocal response.wire
      fixedWire response.order fixedOrder opponentCompiled event observation left right
      leftReached rightReached
  apply runtime.exists_reachedPolicy_mixture_store_law feasible ordered inputs profile roster
    reactionRounds focal replacement wire order functional
  intro response
  dsimp only
  intro control reachable owner different event actor entered activated unfinished
  let players := Profile.update
    (sig := MessageApplication.policySignature Player runtime.application)
    (runtime.compileProfile profile) focal response.playerPure
  have prescribed : players owner = runtime.compilePlayerPolicy owner (profile owner) := by
    exact Profile.update_of_ne _ _ different
  have age := ServiceReachable.ownerActivationAgeOne runtime inputs ordered feasible owner
    (profile owner) roster reactionRounds players prescribed response.wirePure response.orderPure
    control reachable
  exact age event actor entered activated unfinished

end Vegas.EventGraphRuntime
