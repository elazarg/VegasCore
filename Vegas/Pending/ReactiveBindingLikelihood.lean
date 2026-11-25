module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveService
public import Vegas.Pending.EventCompletionObservation
public import Vegas.Pending.EventInitialObservation

@[expose] public section

/-! # Actual communication likelihood during an opaque binding window

The auxiliary projection retains the complete network, service recall, and
focal private input. Other players' private submission parameters are absent
from this proof projection. They remain in actual runtime recall. A shared
passive sample couples the silent response windows without an assumption
on the observation rule.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Existing native fields sufficient for the silent window's joint law.
This is a proof readout; it is not a player's observation or extra state. -/
def bindingTraffic (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (focal : Player) (execution : ((reactiveApplication timeouts) leaks).Execution) :=
  (execution.network, execution.receipts, execution.environmentRecall, execution.logs focal,
    execution.application.playerView focal, execution.application.publicView)

/-- The native initial traffic is determined by the focal graph observation,
including the focal player's candidate catalogue. -/
theorem initial_bindingTraffic_eq_of_observation (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (focal : Player) (left right : graph.Inputs)
    (observations : graph.playerObserve focal (EventGraph.Config.initial left) =
      graph.playerObserve focal (EventGraph.Config.initial right)) :
    (bindingTraffic timeouts) leaks focal
        (ReactiveApplication.Execution.initial ((reactiveApplication timeouts) leaks)
          (State.initial left)) =
      (bindingTraffic timeouts) leaks focal
        (ReactiveApplication.Execution.initial ((reactiveApplication timeouts) leaks)
          (State.initial right)) := by
  have publics := State.initial_publicView_eq_of_observation focal left right observations
  have candidates := State.initial_candidates_eq_of_observation focal left right observations
  have views : (State.initial left).playerView focal = (State.initial right).playerView focal := by
    unfold State.playerView
    congr 1
  unfold bindingTraffic
  dsimp only [ReactiveApplication.Execution.initial]
  rw [views, publics]

/-- If the focal graph observation is determined by a view of the hidden
initial state, the joint law of that state and native traffic factors through
the view. The initial draws may be correlated. -/
theorem initial_bindingTraffic_factorization_of_view (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (focal : Player) {Seed State View : Type*}
    (prior : PMF Seed) (inputs : Seed → graph.Inputs)
    (state : Seed → State) (view : State → View)
    (observes : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      view (state left) = view (state right) →
      graph.playerObserve focal (EventGraph.Config.initial (inputs left)) =
        graph.playerObserve focal (EventGraph.Config.initial (inputs right))) :
    let read := fun seed => (bindingTraffic timeouts) leaks focal
      (ReactiveApplication.Execution.initial ((reactiveApplication timeouts) leaks)
        (EventGraphRuntime.State.initial (inputs seed)))
    ∃ traffic : View → PMF _,
      prior.map (fun seed => (state seed, read seed)) =
        (prior.map state).bind fun initial =>
          (traffic (view initial)).map fun extra => (initial, extra) := by
  classical
  intro read
  let traffic := fun observation =>
    if present : ∃ seed ∈ prior.support, view (state seed) = observation then
      PMF.pure (read present.choose)
    else PMF.pure (read prior.support_nonempty.choose)
  refine ⟨traffic, ?_⟩
  rw [PMF.bind_map]
  change prior.bind (fun seed => PMF.pure (state seed, read seed)) = _
  apply bind_congr_on_support _
  intro seed supported
  have present : ∃ other ∈ prior.support, view (state other) = view (state seed) :=
    ⟨seed, supported, rfl⟩
  simp only [traffic, Function.comp_apply, dite_eq_left present, PMF.pure_map]
  rw [show read seed = read present.choose from initial_bindingTraffic_eq_of_observation
    timeouts leaks focal _ _ (observes seed supported present.choose present.choose_spec.1
      present.choose_spec.2.symm)]

/-- Native initial traffic factors through the focal graph observation. -/
theorem initial_bindingTraffic_factorization (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (focal : Player) (prior : PMF graph.Inputs) :
    ∃ traffic : graph.PlayerObservation focal → PMF _,
      prior.map (fun inputs =>
        (EventGraph.Config.initial inputs, (bindingTraffic timeouts) leaks focal
          (ReactiveApplication.Execution.initial ((reactiveApplication timeouts) leaks)
            (State.initial inputs)))) =
        (prior.map EventGraph.Config.initial).bind fun config =>
          (traffic (graph.playerObserve focal config)).map fun extra => (config, extra) :=
  initial_bindingTraffic_factorization_of_view timeouts leaks focal prior id
    EventGraph.Config.initial (graph.playerObserve focal) (fun _ _ _ _ same => same)

/-- Automatic completion preserves equality of the existing native traffic readout. -/
theorem bindingTraffic_drain (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : ((reactiveApplication timeouts) leaks).Execution) (focal : Player)
    (same : (bindingTraffic timeouts) leaks focal left = (bindingTraffic timeouts) leaks focal
      right) :
    (bindingTraffic timeouts) leaks focal {left with application := left.application.drain} =
      (bindingTraffic timeouts) leaks focal {right with application := right.application.drain}
        := by
  have networks := congrArg Prod.fst same
  have receipts := congrArg (fun value => value.2.1) same
  have environments := congrArg (fun value => value.2.2.1) same
  have recalled := congrArg (fun value => value.2.2.2.1) same
  have views := congrArg (fun value => value.2.2.2.2.1) same
  have drained := State.drain_playerView_congr left.application right.application focal views
  exact Prod.ext networks (Prod.ext receipts (Prod.ext environments (Prod.ext recalled
    (Prod.ext drained (congrArg PlayerView.publicView drained)))))

end Vegas.EventGraphRuntime
