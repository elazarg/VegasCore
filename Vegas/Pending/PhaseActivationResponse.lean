/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseOwnerOpportunity
import Vegas.Pending.ReactiveAsyncContract
import Interaction.ReactiveRecordedResponse

/-! # Every completed physical activation retains its actual response view -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseService

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "P" => phaseApplication runtime leaks

/-- An activation at an idle endpoint already has its actual response in full
own recall, with the exact physical public view before that activation. -/
theorem recalled_response_of_activation
    (initial : PMF (P).State) (horizon : Nat) (scheduler : (P).Scheduler)
    (current : (P).Control) (trace : ((P).protocol initial horizon scheduler).Trace (some current))
    (idle : current.actor = none) (activation : (P).EnvironmentEntry)
    (recorded : activation ∈ current.execution.environmentRecall)
    (owner : Player) (chosen : activation.command = .activate owner) :
    ∃ response ∈ current.execution.recall owner,
      response.beforeView.application.2 = activation.beforeView.application := by
  let paired (execution : (P).Execution) (entry : (P).EnvironmentEntry) (owner : Player) : Prop :=
    ∃ response ∈ execution.recall owner,
      response.beforeView.application.2 = entry.beforeView.application
  have origin : ∀ {state} (_history : ((P).protocol initial horizon scheduler).Trace state),
      state.elim True (fun current => ∀ entry ∈ current.execution.environmentRecall,
        ∀ owner, entry.command = .activate owner → paired current.execution entry owner ∨
          (current.actor = some owner ∧ current.execution.application.publicView =
            entry.beforeView.application)) := by
    intro state history
    induction history with
    | start => trivial
    | @extend source target prior joint legal reached ih =>
        cases source with
        | none =>
            obtain ⟨state, _support, rfl⟩ := PMF.support_map .. ▸ reached
            intro entry member
            exact (List.not_mem_nil member).elim
        | some current =>
            rcases current with ⟨remaining, actor, execution⟩
            cases actor with
            | some who =>
                cases (PMF.mem_support_pure_iff _ _).mp reached
                intro entry member owner chosen
                have previous : entry ∈ execution.environmentRecall := by
                  simpa only [(P).respond_environmentRecall] using member
                rcases ih entry previous owner chosen with pairedBefore | waiting
                · obtain ⟨response, retained, viewed⟩ := pairedBefore
                  exact Or.inl ⟨response, (P).respond_recall_mono execution who owner _ retained,
                    viewed⟩
                · have same : who = owner := Option.some.inj waiting.1
                  subst who
                  obtain ⟨emitted, recalled⟩ := (P).respond_recall_entry execution owner
                    ((joint owner).getD ⟨none⟩)
                  refine Or.inl ⟨⟨execution.observe P owner,
                    (joint owner).getD ⟨none⟩, emitted⟩, ?_, waiting.2⟩
                  rw [recalled]
                  exact List.mem_append_right _ (List.mem_singleton_self _)
            | none =>
                cases remaining with
                | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
                | succ remaining =>
                    obtain ⟨selected, _support, moved⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                    obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                    have recalled := (P).environmentStep_recall execution next selected supported
                    have entries : next.environmentRecall = execution.environmentRecall ++
                        [⟨execution.observeEnvironment P, selected⟩] := by
                      unfold ReactiveApplication.Execution.environmentStep at supported
                      obtain ⟨updated, _support, rfl⟩ := PMF.support_map .. ▸ supported
                      rfl
                    intro entry member owner chosen
                    rw [entries, List.mem_append, List.mem_singleton] at member
                    rcases member with previous | rfl
                    · rcases ih entry previous owner chosen with pairedBefore | waiting
                      · obtain ⟨response, retained, viewed⟩ := pairedBefore
                        exact Or.inl ⟨response, recalled ▸ retained, viewed⟩
                      · cases waiting.1
                    · change selected = .activate owner at chosen
                      subst selected
                      refine Or.inr ⟨rfl, ?_⟩
                      unfold ReactiveApplication.Execution.environmentStep at supported
                      obtain ⟨updated, learned, rfl⟩ := PMF.support_map .. ▸ supported
                      obtain ⟨visible, _support, rfl⟩ := PMF.support_map .. ▸ learned
                      rfl
  rcases origin trace activation recorded owner chosen with pairedBefore | waiting
  · exact pairedBefore
  · rw [idle] at waiting
    cases waiting.1

/-- At any due actual physical event, opportunity supplies a retained real
response within the original delay, with its attempt and activation stamp.
This statement concerns physical recall even across earlier resets. -/
theorem due_recalled_response
    (initial : PMF (P).State) (horizon : Nat) (scheduler : (P).Scheduler)
    (delay bound : graph.EventId → Nat)
    (opportunity : Opportunity runtime leaks initial horizon scheduler delay)
    (timely : runtime.AsyncTimely delay bound)
    (current : (P).Control) (trace : ((P).protocol initial horizon scheduler).Trace (some current))
    (idle : current.actor = none) (event : graph.EventId) (owner : Player) (entered : Nat)
    (owned : graph.actor? event = some owner)
    (ready : current.execution.application.current.native.config.cut.Ready event)
    (stamp : current.execution.application.current.native.activatedAt event = some entered)
    (due : runtime.deadline event ≤ current.execution.application.current.native.clock - entered) :
    ∃ response ∈ current.execution.recall owner,
      response.beforeView.application.2.attempt = current.execution.application.attempt ∧
      response.beforeView.application.2.native.EventReady event ∧
      response.beforeView.application.2.native.activatedAt event = some entered ∧
      response.beforeView.application.2.native.clock ≤ entered + delay event := by
  have margin := timely event (by simp only [owned, Option.isSome_some])
  have activated := opportunity current trace event owner entered owned
    ((current.execution.application.current.native.publicView_eventReady event).mpr ready) stamp
      (by omega)
  obtain ⟨activation, recorded, chosen, attempt, wasReady, wasStamp, clock⟩ :=
    recorded_activation_within_delay runtime leaks initial horizon scheduler delay opportunity
      current trace ⟨current.execution.application.attempt, event⟩ owner entered owned activated
  obtain ⟨response, retained, viewed⟩ := recalled_response_of_activation runtime leaks initial
    horizon scheduler current trace idle activation recorded owner chosen
  exact ⟨response, retained, viewed ▸ attempt, viewed ▸ wasReady, viewed ▸ wasStamp,
    viewed ▸ clock⟩

end Vegas.EventGraphRuntime.PhaseService
