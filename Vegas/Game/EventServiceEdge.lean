/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.EventScheduling
import Vegas.Pending.EventHonestLaw
import Vegas.Pending.EventStrategicLaw
import GameTheory.Core.MixtureSimulation

/-! # The public message service as an edge above the canonical graph

Everything the host adds — raw submissions, competing candidates, replay,
delivery before inclusion, adaptive wire choices and epoch ordering — is this
one edge, and so is the mixture a native deviation needs. Below it the graph is
executed canonically; the edge is the only place where the difference between
"what the graph says" and "what a message host does" is argued.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Canonical graph execution and the serviced native game form an exact
unilateral-mixture simulation on typed terminal stores, admitting every native
player policy. -/
def servicedCanonicalSimulation (runtime : EventGraphRuntime graph)
    (ordered : graph.BarrierOrdered) (feasible : runtime.ServiceFeasible)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    GameForm.MixtureSimulationOn (graph.canonicalGame inputs)
      (runtime.servicedEventGame inputs roster reactionRounds wire order)
      graph.terminalStore (fun execution => execution.native.application.config.store)
      (fun _ _ => True) where
  compileStrategy := runtime.compilePlayerPolicy
  honest_law profile := by
    change graph.BehavioralProfile at profile
    have compiled : (fun who => runtime.compilePlayerPolicy who (profile who)) =
        runtime.compileProfile profile := rfl
    unfold Vegas.EventGraph.canonicalGame
    rw [compiled, runtime.servicedEventGame_honest_store_law ordered feasible,
      graph.gameForm_play_map_terminalStore]
    exact FinDist.bind_congr fun input _ => by
      rw [← graph.runPolicies_canonical_normalize_eq profile input]
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    change graph.BehavioralProfile at profile
    obtain ⟨mixture, law⟩ := runtime.exists_deviation_mixture_store_law feasible ordered
      inputs profile roster reactionRounds who replacement wire order
    refine ⟨mixture, ?_⟩
    have compiled : (fun player => runtime.compilePlayerPolicy player (profile player)) =
        runtime.compileProfile profile := rfl
    unfold Vegas.EventGraph.canonicalGame
    rw [compiled, law]
    refine FinDist.bind_congr fun alternative _ => ?_
    rw [graph.gameForm_play_map_terminalStore]
    exact FinDist.bind_congr fun input _ => by
      rw [← graph.runPolicies_canonical_normalize_eq
        (Profile.update (sig := graph.gameSignature) profile who alternative) input]

end Vegas.EventGraphRuntime
