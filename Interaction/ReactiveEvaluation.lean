/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactivePolicy
import GameTheory.Protocol.SingleMover
import GameTheory.Protocol.StateKernel

/-! # The canonical protocol executes the reactive policy interface

The state kernel is the projection of canonical randomized history execution.
It is used for concrete execution tests and carries exactly the same policies,
scheduler observations, and network operations as the information model.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def controlStep (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (state : app.ProtocolState) : PMF app.ProtocolState :=
  match app.actor state with
  | none => app.transition initial horizon scheduler state (fun _ => none)
  | some who => match state with
    | none => PMF.pure none
    | some control => (players who (control.execution.recall who)
        (control.execution.observe app who)).bind fun action =>
          app.transition initial horizon scheduler state (fun observer =>
            if observer = who then some action else none)

theorem singleMover (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (state : app.ProtocolState) {first second : Principal}
    (left : (app.protocol initial horizon scheduler).active state first)
    (right : (app.protocol initial horizon scheduler).active state second) : first = second :=
  Option.some.inj (left.symm.trans right)

theorem controlStep_marginals (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (players : Principal → app.Policy) (state : app.ProtocolState)
    (joint : PMF (Principal → Option app.Action))
    (marginal : ∀ who, joint.map (fun actions => actions who) =
      (app.encodePolicy (players who) (app.observe who state)).map Subtype.val) :
    joint.bind (app.transition initial horizon scheduler state) =
      app.controlStep initial horizon scheduler players state := by
  change (joint.bind fun actions => app.transition initial horizon scheduler state actions) = _
  cases state with
  | none => simp [controlStep, actor, transition, PMF.bind_const]
  | some control =>
      rcases control with ⟨remaining, current, execution⟩
      cases current with
      | none =>
          cases remaining <;> simp [controlStep, actor, transition, PMF.bind_const]
      | some who =>
          have law := marginal who
          have observed : app.observe who (some ⟨remaining, some who, execution⟩) =
              some (execution.recall who, execution.observe app who) := by simp [observe]
          rw [observed, encodePolicy, PMF.map_comp] at law
          have selected := congrArg (fun law => law.bind fun action =>
            PMF.pure (some (Control.mk remaining none
              (execution.respond app who (action.getD ⟨none⟩))))) law
          simpa only [PMF.bind_map, Function.comp_def, Option.getD_some, transition,
            controlStep, actor, Option.bind_some, ↓reduceIte] using selected

theorem behavioral_step (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (history : (app.protocol initial horizon scheduler).History)
    (running : ¬ app.terminal history.state) :
    ((app.information initial horizon scheduler).singleMoverJoint
      (app.singleMover initial horizon scheduler) (fun who => app.encodePolicy (players who))
      history running).bind ((app.protocol initial horizon scheduler).step history.state) =
        app.controlStep initial horizon scheduler players history.state := by
  let law := (app.information initial horizon scheduler).singleMoverJoint
    (app.singleMover initial horizon scheduler) (fun who => app.encodePolicy (players who))
    history running
  have marginal (who : Principal) :
      (law.map Subtype.val).map (fun actions => actions who) =
        (app.encodePolicy (players who) (app.observe who history.state)).map Subtype.val := by
    rw [PMF.map_comp]
    change law.map (fun actions => actions.1 who) = _
    rw [InformationModel.singleMoverJoint_marginal]
    change (app.encodePolicy (players who)
      ((app.signals initial horizon scheduler).infoOf who history.trace)).map Subtype.val = _
    rw [app.info]
  have same := app.controlStep_marginals initial horizon scheduler players history.state
    (law.map Subtype.val) marginal
  rw [PMF.bind_map] at same
  exact same

theorem run_map_state (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (fuel : Nat)
    (history : (app.protocol initial horizon scheduler).History) :
    ((app.information initial horizon scheduler).runSingleMoverBehavioralFrom
      (app.singleMover initial horizon scheduler) (fun who => app.encodePolicy (players who))
      fuel history).map ExecutionProtocol.History.state =
        (fun law => law.bind (app.controlStep initial horizon scheduler players))^[fuel]
          (PMF.pure history.state) := by
  apply ExecutionProtocol.runRandomizedFor_map_state
  · intro state stopped
    cases state with
    | none => exact stopped.elim
    | some control =>
        rcases control with ⟨remaining, current, execution⟩
        rcases stopped with ⟨rfl, rfl⟩
        rfl
  · intro current running
    exact app.behavioral_step initial horizon scheduler players current running

end Interaction.ReactiveApplication
