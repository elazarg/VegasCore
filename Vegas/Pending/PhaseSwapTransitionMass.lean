/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSwapTransition
import Interaction.ReactiveEnvironmentMass

/-! # Exact native nature atoms along guarded hidden-swap histories -/

noncomputable section

namespace Vegas.EventGraphRuntime.HiddenSwap

open EventGraph Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {allowed : Set graph.Inputs}

/-- The actual guarded result of a command supplies any inclusion guard needed
to commute its whole environment law. Other commands commute directly. -/
theorem environmentStep_phaseExecution_of_guards (swap : HiddenSwap graph)
    (before after : (phaseApplication runtime leaks).Execution)
    (command : (phaseApplication runtime leaks).Command)
    (moved : after ∈ (before.environmentStep (phaseApplication runtime leaks) command).support)
    (beforeGuard : PhaseSwapGuard runtime leaks swap allowed before)
    (afterGuard : PhaseSwapGuard runtime leaks swap allowed after)
    (expiry : ∀ event, swap.values.ExpiryFixed event) :
    (swap.phaseExecution before).environmentStep (phaseApplication runtime leaks) command =
      (before.environmentStep (phaseApplication runtime leaks) command).map
        swap.phaseExecution := by
  apply swap.environmentStep_phaseExecution_of_admitted before command expiry
  intro id envelope selected found admitted
  subst selected
  have included : PhaseSwapGuard runtime leaks swap allowed
      (before.includePending (phaseApplication runtime leaks) id) := by
    unfold ReactiveApplication.Execution.environmentStep at moved
    rw [PMF.support_map] at moved
    obtain ⟨next, supported, rfl⟩ := moved
    rw [PMF.mem_support_pure_iff] at supported
    subst next
    exact ⟨afterGuard.clear, afterGuard.inputs, afterGuard.compatible,
      afterGuard.completed, afterGuard.active, afterGuard.requests⟩
  exact swap.phaseInclusionFixed_of_guards before id envelope found admitted beforeGuard included

/-- Every realized noninitial transition ending in the primitive guard has
exactly the same native nature mass at its swapped source, action and target.
The initial draw is excluded because its original prior mass is retained. -/
theorem phaseTransition_apply_swap (swap : HiddenSwap graph)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (before after : (phaseApplication runtime leaks).Control)
    (joint : Player → Option (phaseApplication runtime leaks).Action)
    (reached : some after ∈ ((phaseApplication runtime leaks).transition initial horizon scheduler
      (some before) joint).support)
    (native : ∃ draw, before.execution.application.Invariant draw)
    (guarded : PhaseSwapGuard runtime leaks swap allowed after.execution)
    (expiry : ∀ event, swap.values.ExpiryFixed event) :
    ((phaseApplication runtime leaks).transition initial horizon scheduler
      (some (swap.phaseControl before)) (swap.phaseJoint joint))
        (some (swap.phaseControl after)) =
      ((phaseApplication runtime leaks).transition initial horizon scheduler
        (some before) joint) (some after) := by
  classical
  let app := phaseApplication runtime leaks
  have beforeGuard := phaseSwapGuard_of_transition runtime leaks swap allowed initial horizon
    scheduler before after joint reached native guarded
  rcases before with ⟨remaining, actor, current⟩
  cases actor with
  | some who =>
      cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
      change (PMF.pure (some (⟨remaining, none,
        (swap.phaseExecution current).respond app who ((swap.phaseJoint joint who).getD ⟨none⟩)⟩ :
          app.Control))) (some (swap.phaseControl _)) = _
      rw [swap.getD_phaseJoint, swap.respond_phaseExecution current who _
        (swap.phaseRequestFixed_of_respond current who _ guarded)]
      simp only [ReactiveApplication.transition, phaseControl, PMF.pure_apply_self]
  | none =>
      cases remaining with
      | zero =>
          cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
          simp only [ReactiveApplication.transition, phaseControl, PMF.pure_apply_self]
      | succ remaining =>
          rw [ReactiveApplication.transition, PMF.mem_support_bind_iff] at reached
          obtain ⟨command, _scheduled, moved⟩ := reached
          rw [PMF.support_map] at moved
          obtain ⟨next, stepped, nextEq⟩ := moved
          cases Option.some.inj nextEq
          have law := swap.environmentStep_phaseExecution_of_guards current next command
            stepped beforeGuard guarded expiry
          have swapped : swap.phaseExecution next ∈
              ((swap.phaseExecution current).environmentStep app command).support := by
            rw [law, PMF.support_map]
            exact ⟨next, stepped, rfl⟩
          change (app.transition initial horizon scheduler
            (some ⟨remaining + 1, none, swap.phaseExecution current⟩) (swap.phaseJoint joint))
              (some ⟨remaining, command.actor? app, swap.phaseExecution next⟩) = _
          rw [app.transition_environment_apply initial horizon scheduler remaining _ _ command
            swapped _, app.transition_environment_apply initial horizon scheduler remaining _ _
              command stepped _]
          rw [swap.observeEnvironment_phaseExecution, law,
            pmf_map_apply_of_injective _ (swap.phaseExecution_involutive).injective]
          rfl

end Vegas.EventGraphRuntime.HiddenSwap
