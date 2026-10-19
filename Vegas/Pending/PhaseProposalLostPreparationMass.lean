/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalLostRecallReplay
import GameTheoryExtensions.Math.Probability.Support

/-! # Exact intrinsic atoms of actual lost-value environment replay

Environment steps leave all private recalls fixed. Erasing one recall is
therefore injective on each actual environment support, even though it is
not injective on arbitrary executions.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.HiddenSwap

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

local notation "app" => phaseApplication runtime leaks

private theorem environment_eraseRecall_atom
    (before : (app).Execution) (owner : Player) (command : (app).Command)
    (after : (app).Execution) (moved : after ∈ (before.environmentStep app command).support) :
    ((before.environmentStep app command).map (fun next => next.eraseRecall app owner))
        (after.eraseRecall app owner) = (before.environmentStep app command) after := by
  classical
  have recover (next : (app).Execution)
      (supported : next ∈ (before.environmentStep app command).support) :
      ({ next.eraseRecall app owner with «recall» := before.recall } : (app).Execution) = next := by
    change ({ next with «recall» := before.recall } : (app).Execution) = next
    rw [← (app).environmentStep_recall before next command supported]
  rw [← pmf_bind_pure_eq_map]
  have unique : ∀ next ∈ (before.environmentStep app command).support,
      after.eraseRecall app owner ∈ (PMF.pure (next.eraseRecall app owner)).support →
        next = after := by
    intro next supported mapped
    have same := (PMF.mem_support_pure_iff _ _).mp mapped
    exact (recover next supported).symm.trans
      ((congrArg (fun execution : (app).Execution =>
        { execution with «recall» := before.recall }) same.symm).trans (recover after moved))
  rw [bind_apply_of_unique_branch _ _ _ after unique]
  simp only [PMF.pure_apply_self, mul_one]

/-- Every actual matched environment atom has the same intrinsic probability.
The counterpart is an actual supported atom, and equality follows from the
owning physical kernel and support-local injectivity, not a likelihood premise. -/
theorem preparationOnly_environment_atom
    (owner : Player) (slot : CandidateSlot graph) (first second : Raw L)
    (original image : (app).Execution)
    (paired : image.eraseRecall app owner =
      ((preparationOnly (owner, slot) first second).phaseExecution original).eraseRecall app owner)
    (command : (app).Command) (next target : (app).Execution)
    (moved : next ∈ (original.environmentStep app command).support)
    (imageMoved : target ∈ (image.environmentStep app command).support)
    (nextPaired : target.eraseRecall app owner =
      ((preparationOnly (owner, slot) first second).phaseExecution next).eraseRecall app owner)
    (unused : original.application.current.native.HandleUnused (owner, slot))
    (rejected : ∀ id message event, command = .include id →
      original.network.lookup id = some message →
      message.payload.packet.call = .commitment event (owner, slot) →
        original.application.handle runtime message = none) :
    (image.environmentStep app command) target = (original.environmentStep app command) next := by
  let swap := preparationOnly (owner, slot) first second
  have swapped := environmentStep_preparationOnly (owner, slot) first second original command
    unused rejected
  have swapMoved : swap.phaseExecution next ∈
      ((swap.phaseExecution original).environmentStep app command).support := by
    rw [swapped, PMF.support_map]
    exact ⟨next, moved, rfl⟩
  have sameLaw : (image.environmentStep app command).map (fun execution =>
        execution.eraseRecall app owner) =
      ((swap.phaseExecution original).environmentStep app command).map (fun execution =>
        execution.eraseRecall app owner) := by
    rw [ReactiveApplication.eraseRecall_environmentStep, paired,
      ← ReactiveApplication.eraseRecall_environmentStep]
  calc
    _ = ((image.environmentStep app command).map (fun execution =>
        execution.eraseRecall app owner)) (target.eraseRecall app owner) :=
      (environment_eraseRecall_atom image owner command target imageMoved).symm
    _ = ((swap.phaseExecution original).environmentStep app command)
        (swap.phaseExecution next) := by
      rw [sameLaw, nextPaired]
      exact environment_eraseRecall_atom (swap.phaseExecution original) owner command
        (swap.phaseExecution next) swapMoved
    _ = _ := by
      rw [swapped, pmf_map_apply_of_injective _ swap.phaseExecution_involutive.injective]

end Vegas.EventGraphRuntime.HiddenSwap
