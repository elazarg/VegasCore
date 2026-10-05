/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.EventScheduling
import Vegas.Pending.EventHonestLaw
import Vegas.Pending.EventStrategicLaw
import GameTheory.Core.MixtureSimulation

/-! # The public message service as an edge above the canonical graph

Everything the host adds — raw submissions, competing candidates,
delivery before inclusion, adaptive wire choices and epoch ordering — is this
one edge, and so is the mixture a native deviation needs. Below it the graph is
executed canonically; the edge is the only place where the difference between
"what the graph says" and "what a message host does" is argued.

The edge considers finitely branching native deviations. Native commands range
over unbounded identifiers and raw values, so an arbitrary deviation can
reach infinitely many of its own information values, and predrawing it as one
probability mass function over pure responses need not be possible.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Canonical graph execution and the serviced native game form an exact
unilateral-mixture simulation on typed terminal stores, admitting every finitely
branching native player policy. -/
def servicedCanonicalSimulation (runtime : EventGraphRuntime graph)
    (ordered : graph.BarrierOrdered) (finite : graph.FiniteActions)
    (feasible : runtime.ServiceFeasible)
    (inputs : PMF graph.Inputs) (inputsFinite : inputs.support.Finite)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (wireFinite : wire.FiniteSupport)
    (order : runtime.ServiceOrderPolicy) (orderFinite : order.FiniteSupport) :
    GameForm.MixtureSimulationOn (graph.canonicalGame inputs)
      (runtime.servicedEventGame inputs roster reactionRounds wire order)
      graph.terminalStore (fun execution => execution.native.application.config.store)
      (fun _ policy => Interaction.MessageApplication.PlayerPolicy.FiniteSupport policy) where
  compileStrategy := runtime.compilePlayerPolicy
  honest_law profile := by
    change graph.BehavioralProfile at profile
    have compiled : Profile.map (sig := graph.gameSignature)
        (target := Interaction.MessageApplication.policySignature Player runtime.application)
        runtime.compilePlayerPolicy profile = runtime.compileProfile profile := rfl
    unfold Vegas.EventGraph.canonicalGame
    rw [compiled, runtime.servicedEventGame_honest_store_law ordered feasible,
      graph.gameForm_play_map_terminalStore]
    exact bind_congr_on_support _ fun input _ => by
      rw [← graph.runPolicies_canonical_normalize_eq profile input]
  compiled_considered who policy :=
    runtime.compilePlayerPolicy_finiteSupport fun event _ _ =>
      have := finite event
      Set.toFinite _
  deviation_mixture profile who replacement replacementFinite := by
    change graph.BehavioralProfile at profile
    obtain ⟨mixture, _, law⟩ := runtime.exists_deviation_mixture_store_law feasible ordered
      finite inputs inputsFinite profile roster reactionRounds who replacement replacementFinite
      wire wireFinite order orderFinite
    refine ⟨mixture, ?_⟩
    have compiled : Profile.map (sig := graph.gameSignature)
        (target := Interaction.MessageApplication.policySignature Player runtime.application)
        runtime.compilePlayerPolicy profile = runtime.compileProfile profile := rfl
    unfold Vegas.EventGraph.canonicalGame
    rw [compiled, law]
    refine bind_congr_on_support _ fun alternative _ => ?_
    rw [graph.gameForm_play_map_terminalStore]
    exact bind_congr_on_support _ fun input _ => by
      rw [← graph.runPolicies_canonical_normalize_eq
        (Profile.update (sig := graph.gameSignature) profile who alternative) input]

end Vegas.EventGraphRuntime
