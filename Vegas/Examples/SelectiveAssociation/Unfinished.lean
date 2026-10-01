/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SelectiveAssociation.Cursor
import Vegas.Pending.ReactiveServiceFootprint
import Vegas.Pending.ReactiveStateInvariant

/-! # Each reserved native decision precedes its event's completion

All raw player responses are allowed. Only the fixed calendar can include
or expire events, and every such operation is addressed to its current visit.
-/

noncomputable section

namespace Vegas.Examples.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

variable {observation : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph)}

def nativeUntouched (event : nativeGraph.EventId) (count : Nat) : Prop :=
  ∀ index : Fin count, (nativePlan[index.val]?).any (fun instruction =>
    instruction.targets event) = false

private theorem untouched_prior (event : nativeGraph.EventId) (count : Nat)
    (untouched : nativeUntouched event (count + 1)) : nativeUntouched event count :=
  fun index => untouched ⟨index.val, Nat.lt_succ_of_lt index.isLt⟩

private theorem untouched_current (event : nativeGraph.EventId) (count : Nat)
    (untouched : nativeUntouched event (count + 1)) (instruction : ServiceInstruction nativeGraph)
    (selected : nativePlan[count]? = some instruction) : instruction.targets event = false := by
  have absent := untouched ⟨count, Nat.lt_succ_self count⟩
  simpa only [selected, Option.any_some] using absent

private def nativeNoEarlyCompletion : (serviceApp observation).ProtocolState → Prop
  | none => True
  | some control => ∀ event, nativeUntouched event control.execution.environmentRecall.length →
      event ∉ control.execution.application.config.cut.completed

private theorem noEarly_transition (before after : (serviceApp observation).ProtocolState)
    (joint : Player → Option (serviceApp observation).Action)
    (trace : ((serviceApp observation).protocol (PMF.pure nativeInitial)
      nativeHorizon (serviceScheduler observation)).Trace before)
    (valid : nativeNoEarlyCompletion before)
    (reached : after ∈ ((serviceApp observation).transition (PMF.pure nativeInitial)
      nativeHorizon (serviceScheduler observation) before joint).support) : nativeNoEarlyCompletion
        after := by
  cases before with
  | none =>
      obtain ⟨state, stateMem, rfl⟩ := PMF.support_map .. ▸ reached
      cases (PMF.mem_support_pure_iff _ _).mp stateMem
      intro event _
      exact Finset.notMem_empty event
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          intro event untouched
          have prior : nativeUntouched event execution.environmentRecall.length := by
            simpa only [(serviceApp observation).respond_environmentRecall] using untouched
          rw [(nativeRuntime.reactive_respond_application observation execution who _).1]
          exact valid event prior
      | none =>
          cases remaining with
          | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact valid
          | succ remaining =>
              obtain ⟨command, selected, supported⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, moved, rfl⟩ := PMF.support_map .. ▸ supported
              intro event untouched
              have cursor : next.environmentRecall.length =
                  execution.environmentRecall.length + 1 := by
                obtain ⟨updated, _, rfl⟩ := PMF.support_map .. ▸ moved
                simp only [List.length_append, List.length_singleton]
              rw [cursor] at untouched
              have unfinished := valid event
                (untouched_prior event execution.environmentRecall.length untouched)
              cases instruction : nativePlan[execution.environmentRecall.length]? with
              | none =>
                  simp only [serviceScheduler, instruction,
                    PMF.mem_support_pure_iff _ _] at selected
                  subst command
                  simp only [ReactiveApplication.Execution.environmentStep,
                    PMF.pure_map, PMF.mem_support_pure_iff _ _] at moved
                  subst next
                  exact unfinished
              | some step =>
                  have audit := (serviceApp observation).submissionAudit_history
                    ReactivePlayerView.publicView
                    (fun _ _ => rfl) (PMF.pure nativeInitial) nativeHorizon
                      (serviceScheduler observation) trace
                  apply nativeRuntime.reactive_instruction_unfinished observation (serviceNetwork
                    observation)
                    execution next step command event audit.1
                    (untouched_current event _ untouched step instruction) unfinished _ moved
                  simpa only [serviceScheduler, instruction] using selected

private theorem native_no_early_history :
    ∀ {state} (_trace : ((serviceApp observation).protocol (PMF.pure nativeInitial)
      nativeHorizon (serviceScheduler observation)).Trace state), nativeNoEarlyCompletion state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      noEarly_transition _ _ joint prior (native_no_early_history prior) reached

theorem native_response_untouched (event : nativeGraph.EventId) :
    nativeUntouched event ((nativeBeforeResponse event).length + 1) := by
  unfold nativeUntouched
  fin_cases event <;> decide

/-- At every legal decision history, the granted current event is unfinished.
This includes histories outside an assessment's positive-probability play. -/
theorem native_decision_unfinished (event : nativeGraph.EventId) (control : (serviceApp
  observation).Control)
    (trace : (serviceArena observation).Trace (some control)) (who : Player)
    (active : control.actor = some who)
    (granted : NativeTurn event control) :
    event ∉ control.execution.application.config.cut.completed := by
  have cursor := (native_decision_cursor event control trace who active granted).2
  have raw := (serviceMenu observation).toRawTrace (PMF.pure nativeInitial) nativeHorizon
    (serviceScheduler observation) trace
  apply native_no_early_history raw event
  rw [cursor]
  exact native_response_untouched event

end Vegas.Examples.SelectiveAssociation
