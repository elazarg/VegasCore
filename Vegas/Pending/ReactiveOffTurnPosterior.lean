/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePolicyFacts
import GameTheory.Math.Probability.ConditionalObservation

/-! # Prescribed memory across off-turn callbacks -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A callback without an owned turn appends an empty private slot and conveys
no information about prior sampled intentions, even at total posterior fallback. -/
theorem prescribedReactivePosterior_snoc_of_no_turn
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (offTurn : entry.beforeView.application.publicView.ownTurn? who = none) :
    (runtime.prescribedReactiveImplementation leaks who policy).posterior (history ++ [entry]) =
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).map
        (fun intentions => intentions ++ [none]) := by
  rw [ReactiveApplication.Implementation.posterior_snoc]
  have law :
      (((runtime.prescribedReactiveImplementation leaks who policy).posterior history).bind
        fun intentions => (runtime.prescribedReactiveImplementation leaks who policy).respond
          intentions (history, entry.beforeView)) =
      bindPairLaw (PMF.pure (⟨none⟩ : (runtime.reactiveApplication leaks).Action))
        (fun _ =>
          ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).map
          (fun intentions => intentions ++ [none])) := by
    simp only [prescribedReactiveImplementation, prescribedReactiveResponse, offTurn,
      PMF.pure_map, bindPairLaw, PMF.pure_bind, PMF.map_comp, Function.comp_def]
    rfl
  rw [law, fiberPosterior_snd_bindPairLaw_const]

/-- Off-turn callback evidence does not change the law of genuine original
intentions. Empty implementation slots are erased from this readout. -/
theorem prescribedReactivePosterior_intentions_snoc_of_no_turn
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (offTurn : entry.beforeView.application.publicView.ownTurn? who = none) :
    ((runtime.prescribedReactiveImplementation leaks who policy).posterior
      (history ++ [entry])).map (List.filterMap id) =
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).map
        (List.filterMap id) := by
  rw [runtime.prescribedReactivePosterior_snoc_of_no_turn leaks who policy history entry offTurn,
    PMF.map_comp]
  simp only [Function.comp_def, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil, id_eq, List.append_nil]
  rfl

end Vegas.EventGraphRuntime
