/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPrescribedLaw
import Vegas.Pending.EventPrescribedReachability

/-! # Honest outcome laws of the asynchronous pending-message service

Honest play is the case of the prescribed-continuation argument in which every
player is prescribed, so no player's graph policy has to be matched at an
effective completion.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- One prescribed profile serves every draw of private setup. The complete
typed terminal-store law agrees with canonical normalized graph execution. -/
theorem servicedEventGame_honest_store_law (runtime : EventGraphRuntime graph)
    (ordered : graph.BarrierOrdered) (feasible : runtime.ServiceFeasible)
    (inputs : PMF graph.Inputs) (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ((runtime.servicedEventGame inputs roster reactionRounds wire order).play
      (runtime.compileProfile profile)).map (fun next => next.native.application.config.store) =
      inputs.bind fun input =>
        (graph.runPolicies graph.canonicalScheduler (graph.normalizeProfile profile) input).map
          (fun config => config.store) := by
  let players := runtime.compileProfile profile
  have compiled : ∀ owner, (fun _ => True) owner →
      players owner = runtime.compilePlayerPolicy owner (profile owner) := fun _ _ => rfl
  have selected : FreeActionsSelected runtime inputs roster reactionRounds players wire order
      profile (fun _ => True) := by
    intro _ _ _ _ _ _ _ _ _ _ free
    exact (free trivial).elim
  have environmentState : ∀ control,
      ServiceReachable runtime inputs roster reactionRounds players wire order control →
      PrescribedEnvironmentState runtime control.execution (fun _ => True) := by
    intro control reachable
    refine reachable.prescribedEnvironmentState runtime ordered inputs profile roster
      reactionRounds players wire order (fun _ => True) control compiled ?_
    intro owner _
    exact ServiceReachable.ownerActivationAgeOne runtime inputs ordered feasible owner
      (profile owner) roster reactionRounds players rfl wire order control reachable
  change (inputs.bind _).map _ = _
  rw [PMF.map_bind]
  apply bind_congr_on_support _
  intro input inputMem
  exact runtime.runService_store_law feasible ordered inputs input inputMem profile roster
    reactionRounds players wire order (fun _ => True) selected compiled environmentState

end Vegas.EventGraphRuntime
