/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Expr.Simple
import Vegas.Pending.EventSequential
import Vegas.Pending.EventStrategicLaw

/-! # Sequential EventGraph runtime regressions

The service deliberately visits the later event first. Sequential dependencies,
not the visit order, nevertheless force semantic completion in source rank.
The common asynchronous strategic theorem applies to the same runtime.
-/

namespace VegasTests.EventSequential

open GameTheory Math.Probability Interaction Vegas Vegas.EventGraph

noncomputable section

private abbrev pairOrder : EventOrder where
  eventCount := 2
  predecessors _ := ∅
  predecessor_lt := by simp

private abbrev pairInputs : Fin 0 → EventField Bool simpleExpr := Fin.elim0

private abbrev pairOutputs : Fin 2 → EventField Bool simpleExpr :=
  fun event => .binding (event.val == 1) .bool

private abbrev pairLayout := fieldLayout pairInputs pairOutputs

private abbrev pairGraph : Vegas.EventGraph Bool simpleExpr where
  inputCount := 0
  order := pairOrder
  inputLayout := pairInputs
  outputLayout := pairOutputs
  nodes event := EventCode.bind (layout := pairLayout) (event.val == 1) .bool
  reads_available := by
    intro event field member
    exact False.elim (Finset.notMem_empty field member)
  payoffs := []

private abbrev sequentialGraph := pairGraph.sequentialize

private def runtime : EventGraphRuntime sequentialGraph where
  deadline _ := 2

private def inputValues : sequentialGraph.Inputs := fun input => nomatch input

private def decreasingOrder : runtime.ServiceOrderPolicy :=
  fun _ _ => FinDist.pure (EventGraphRuntime.ServiceOrder.decreasing sequentialGraph)

private theorem feasible : runtime.ServiceFeasible := by
  intro event
  rfl

/-- Even when every epoch offers event `1` before event `0`, every supported
native play completes the semantic events in order. Players and wire delivery
remain arbitrary. -/
example (players : Bool → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (roster : List Bool)
    (reactionRounds : Nat) (next : runtime.application.PolicyExecution)
    (supported : next ∈
      ((runtime.servicedEventGame (FinDist.pure inputValues) roster reactionRounds
        wire decreasingOrder).play players).support) :
    next.native.application.config.history.map Completion.event = List.finRange 2 := by
  exact runtime.servicedSequentialGame_history
    (FinDist.pure inputValues) roster reactionRounds wire decreasingOrder
      players next supported

/-- Sequential mode consumes the common asynchronous exact-deviation theorem;
it does not introduce a second strategic proof. -/
example (profile : sequentialGraph.BehavioralProfile)
    (roster : List Bool) (reactionRounds : Nat) (focal : Bool)
    (replacement : runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) :
    ∃ mixture : FinDist (sequentialGraph.BehavioralPolicy focal),
      ((runtime.servicedEventGame (FinDist.pure inputValues) roster reactionRounds
        wire decreasingOrder).play
          (Profile.update
            (sig := MessageApplication.policySignature Bool runtime.application)
            (runtime.compileProfile profile) focal replacement)).map
              (fun next => next.native.application.config.store) =
        mixture.bind fun alternative =>
          (sequentialGraph.runPolicies sequentialGraph.canonicalScheduler
            (sequentialGraph.normalizeProfile
              (Profile.update (sig := sequentialGraph.gameSignature)
                profile focal alternative)) inputValues).map
                  (fun config => config.store) := by
  simpa using runtime.exists_deviation_mixture_store_law feasible
    pairGraph.sequentialize_barrierOrdered (FinDist.pure inputValues) profile
      roster reactionRounds focal replacement wire decreasingOrder

end

end VegasTests.EventSequential
