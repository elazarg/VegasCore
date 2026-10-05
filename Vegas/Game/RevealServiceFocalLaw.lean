/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServicePrefixLaw
import Vegas.Game.RevealServiceSelector

/-! # Exact source-state law after selecting one player's aliases

The selected profile is a legal profile of the same finite native game. It
changes only one player's physical response names and preserves the actual
source-state law at every checkpoint. No support or belief conclusion is
assumed here; information-fiber reflection is a separate obligation.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Selecting recorded aliases keeps the full source protocol-state law,
uniformly over private setup draws and including zero-probability aliases of
the original profile. -/
theorem focal_plan_prefix_law
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program admission)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (who : Player) (notWatcher : who ≠ watcher)
    (reference : List (application setup leaks).PlayerEntry)
    (count : Nat) (within : count ≤ Vegas.eventCount setup.program) :
    let extended := bounds.withInitialValues (initialLaw setup)
    let selected := focalProfile setup leaks extended watcher profile weight nonnegative
      atMostOne who reference
    let players := (menu setup leaks extended watcher).decodeProfile (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher) selected
    ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players ((runtime setup).idleNetwork leaks)
        (planPrefix setup watcher count)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).map
          (fun final => sourcePrefix? setup count final.application.config) =
      ((setup.informationModel admission).runBehavioral
        (fun actor => setup.toProtocolBehavioralPolicy admission actor (profile actor)
          (permitted actor)) (count + 1)).map
        GameTheory.Protocol.ExecutionProtocol.History.state := by
  intro extended selected players
  have focal : players who =
      focalPolicy setup leaks extended profile weight nonnegative atMostOne who reference :=
    focalProfile_decode setup leaks extended watcher profile weight nonnegative atMostOne
      who notWatcher reference
  have other (actor : Player) (different : actor ≠ who) :
      players actor = policy setup leaks extended watcher profile weight nonnegative atMostOne
        actor := by
    change (application setup leaks).decodePolicy
      ((menu setup leaks extended watcher).embedPolicy (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher) actor (selected actor)) = _
    have same := focalProfile_other setup leaks extended watcher profile weight nonnegative
      atMostOne who reference actor different
    exact (congrArg (fun localPolicy => (application setup leaks).decodePolicy
      ((menu setup leaks extended watcher).embedPolicy (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher) actor localPolicy)) same).trans
      (congrFun (decoded_compiledProfile setup leaks extended watcher profile weight
        nonnegative atMostOne) actor)
  apply initialized_prefix_source_law setup leaks bounds watcher reveals observer openable
    admission profile permitted players
  · rw [other watcher (Ne.symm notWatcher)]
    simp only [policy, ↓reduceIte]
  · intro actor ordinary past view response supported
    by_cases same : actor = who
    · subst actor
      rw [focal] at supported
      exact focalPolicy_covered setup leaks extended profile weight nonnegative atMostOne
        who reference past view response supported
    · rw [other actor same, policy, ite_eq_right ordinary] at supported
      exact ordinaryPolicy_covered setup leaks extended profile weight nonnegative atMostOne
        actor past view response supported
  · intro actor ordinary past view opening found covered
    by_cases same : actor = who
    · subst actor
      rw [focal, focalPolicy_projects]
      exact ordinaryPolicy_projects setup leaks extended profile weight nonnegative atMostOne
        who past view opening found covered
    · rw [other actor same, policy, ite_eq_right ordinary]
      exact ordinaryPolicy_projects setup leaks extended profile weight nonnegative atMostOne
        actor past view opening found covered
  · exact within

end Vegas
