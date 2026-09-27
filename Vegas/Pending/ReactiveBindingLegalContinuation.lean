/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingContinuation
import Interaction.ReactiveMenuContinuation

/-! # The repaired binding continuation against the original opponents

The private repair has an actual legal behavioral realization in the retained
menu. Opponents keep their original larger-game policies, with no restrictions
at additional inputs. Profile extension and the structural menu square show
that this repaired run remains a retained continuation. The exact law below
includes the entire execution state, rather than only its public outcome.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (bounds : MessageBounds graph)

theorem MessageBounds.compiledMenu_in_effective :
    (bounds.compiledMenu runtime leaks).IncludedIn (bounds.menu runtime leaks) :=
  bounds.compiledActions_effective runtime leaks

namespace BindingMemory

/-- One fixed legal whole policy realizes the private binding repair against
the unchanged target opponents, from every hidden history at its reference
recall. No continuation rationality or global opponent agreement is assumed. -/
theorem compiledImplementation_legal_continuation
    (initial : FinDist (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (source : ∀ who, ((bounds.compiledMenu runtime leaks).information
      initial horizon scheduler).BehavioralPolicy who)
    (target : ∀ who, ((bounds.menu runtime leaks).information
      initial horizon scheduler).BehavioralPolicy who)
    (agrees : ((bounds.compiledMenu_in_effective runtime leaks).actionRestriction
      initial horizon scheduler).ExtendsProfile source target)
    (who : Player)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy)
    (history : ((bounds.compiledMenu runtime leaks).protocol initial horizon scheduler).History)
    (remaining : Nat) (execution : (runtime.reactiveApplication leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (recalled : execution.recall who = reference)
    (fuel : Nat) (enough : (runtime.reactiveApplication leaks).rank horizon history.state ≤ fuel) :
    let app := runtime.reactiveApplication leaks
    let players := (bounds.menu runtime leaks).decodeProfile initial horizon scheduler target
    let strategy := compiledImplementation runtime leaks bounds who reference policy
    (((bounds.compiledMenu runtime leaks).information initial horizon scheduler).runBehavioralFrom
      (Function.update source who
        (compiledPolicy runtime leaks bounds initial horizon scheduler who reference policy))
      fuel history).map ExecutionProtocol.History.state =
      ((strategy.resume who players (some who) execution (atRecall runtime leaks reference)).bind
        (fun result => strategy.run who players scheduler remaining result.1 result.2)).map
          app.finished := by
  intro app players strategy
  have covered := compiledImplementation_policy_available runtime leaks bounds who reference
    policy
  have legal : (bounds.menu runtime leaks).Admissible initial horizon scheduler who
      strategy.policy := by
    intro control _ _ response supported
    exact bounds.compiledActions_effective runtime leaks who _ _
      (covered _ _ response supported)
  have law := (bounds.compiledMenu_in_effective runtime leaks).runFrom_restrictPolicy_finish
    initial horizon scheduler source target agrees who strategy.policy
    (compiledImplementation_admissible runtime leaks bounds initial horizon scheduler who
      reference policy) legal covered fuel history enough
  change _ = app.finish initial horizon scheduler (Function.update players who strategy.policy)
    history.state at law
  rw [current] at law
  change _ = ((app.resume (Function.update players who strategy.policy) (some who)
    execution).bind (app.runRounds scheduler (Function.update players who strategy.policy)
      remaining)).map app.finished at law
  rw [← compiledImplementation_continuation runtime leaks bounds who reference policy players
    scheduler remaining execution recalled] at law
  exact law

end BindingMemory
end Vegas.EventGraphRuntime
