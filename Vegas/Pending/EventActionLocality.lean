/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventReplayCompletion

/-! # Effective-action locality for actual event service -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Two actual focal completions reached at the same normalized observation
have the same effective graph action. All service, wire, opponent, chance, and
expiry transitions are the concrete runtime transitions. -/
theorem reachedFocalAction_eq
    (runtime : EventGraphRuntime graph)
    (feasible : runtime.ServiceFeasible) (ordered : graph.BarrierOrdered)
    (inputs : FinDist graph.Inputs) (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player)
    (focalResponse : List runtime.application.PlayerEntry →
      runtime.application.View → runtime.application.PlayerCommand)
    (fixedFocal : players focal = fun history view =>
      FinDist.pure (focalResponse history view))
    (wireResponse : List runtime.application.EnvironmentEntry →
      runtime.application.EnvironmentObservation → WireCommand Player)
    (fixedWire : wire = fun history view => FinDist.pure (wireResponse history view))
    (orderResponse : List runtime.application.EnvironmentEntry →
      runtime.application.EnvironmentObservation → ServiceOrder graph)
    (fixedOrder : order = fun history view => FinDist.pure (orderResponse history view))
    (opponentCompiled : ∀ owner, owner ≠ focal →
      players owner = runtime.compilePlayerPolicy owner (profile owner))
    (event : graph.EventId) (observation : graph.PlayerObservation focal)
    (leftAction rightAction : graph.Action event)
    (leftReached : ReachedFocalAction runtime inputs roster reactionRounds players wire order
      focal event observation leftAction)
    (rightReached : ReachedFocalAction runtime inputs roster reactionRounds players wire order
      focal event observation rightAction) :
    leftAction = rightAction := by
  have actor : graph.actor? event = some focal := by
    cases leftReached with
    | realized _ _ _ _ actor => exact actor
  have prescribedOthers : ∀ owner, owner ≠ focal →
      ∃ policy : graph.BehavioralPolicy owner,
        players owner = runtime.compilePlayerPolicy owner policy := by
    intro owner different
    exact ⟨profile owner, opponentCompiled owner different⟩
  apply reachedFocalAction_eq_of_pairedStep runtime inputs roster reactionRounds players wire
    order focal event
  · intro left right leftNext rightNext leftEnd rightEnd leftReachable rightReachable replay
      leftSupported rightSupported leftTail rightTail endpoints leftEndReady rightEndReady
    exact replay.pairedControlStep_of_endpoint runtime feasible ordered inputs profile roster
      reactionRounds players wire order focal focalResponse fixedFocal wireResponse fixedWire
      orderResponse fixedOrder opponentCompiled event actor leftReachable rightReachable
      leftSupported rightSupported leftTail rightTail endpoints leftEndReady rightEndReady
  · intro left right leftNext rightNext leftReachable rightReachable replay leftSupported
      rightSupported completion
    exact replay.completionPaired runtime inputs roster reactionRounds players wire order ordered
      focal focalResponse fixedFocal wireResponse fixedWire orderResponse fixedOrder
      prescribedOthers event actor leftReachable rightReachable leftSupported rightSupported
      completion
  · exact leftReached
  · exact rightReached

/-- The canonical extracted focal policy selects every effective action reached
by the actual service under the fixed pure response triple. -/
theorem reachedFocalPolicy_eq
    (runtime : EventGraphRuntime graph)
    (feasible : runtime.ServiceFeasible) (ordered : graph.BarrierOrdered)
    (inputs : FinDist graph.Inputs) (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player)
    (focalResponse : List runtime.application.PlayerEntry →
      runtime.application.View → runtime.application.PlayerCommand)
    (fixedFocal : players focal = fun history view =>
      FinDist.pure (focalResponse history view))
    (wireResponse : List runtime.application.EnvironmentEntry →
      runtime.application.EnvironmentObservation → WireCommand Player)
    (fixedWire : wire = fun history view => FinDist.pure (wireResponse history view))
    (orderResponse : List runtime.application.EnvironmentEntry →
      runtime.application.EnvironmentObservation → ServiceOrder graph)
    (fixedOrder : order = fun history view => FinDist.pure (orderResponse history view))
    (opponentCompiled : ∀ owner, owner ≠ focal →
      players owner = runtime.compilePlayerPolicy owner (profile owner))
    (event : graph.EventId) (actor : graph.actor? event = some focal)
    (observation : graph.PlayerObservation focal) (action : graph.Action event)
    (reached : ReachedFocalAction runtime inputs roster reactionRounds players wire order focal
      event (graph.normalizeObservation event focal observation) action) :
    reachedFocalPolicy runtime inputs roster reactionRounds players wire order focal
      event actor observation = FinDist.pure action := by
  apply reachedFocalPolicy_eq_of_functional runtime inputs roster reactionRounds players wire
    order focal _ event actor observation action reached
  intro query observed left right leftReached rightReached
  exact reachedFocalAction_eq runtime feasible ordered inputs profile roster reactionRounds players
    wire order focal focalResponse fixedFocal wireResponse fixedWire orderResponse fixedOrder
    opponentCompiled query observed left right leftReached rightReached

end Vegas.EventGraphRuntime
