/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeNash
import Vegas.Examples.LateOpeningRuntimeServiceReceipt
import Interaction.ReactiveRecallInvariant

/-! # Remembered empty receipts require protected silence

Every clock-zero Alice packet receives a public receipt before any later
Bob callback. The receipt is present in Bob's remembered observation even
if the packet was rejected. Consequently a remembered positive-clock
callback with empty receipts excludes every protected Alice transmission,
at all compatible raw histories and independently of their probabilities.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeProtectedRecall

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

private structure RecallFacts (execution : app.Execution) : Prop where
  clocks : ∀ who entry, entry ∈ execution.recall who →
    entry.beforeView.application.publicView.clock ≤ execution.application.clock
  emissions : ∀ who entry, entry ∈ execution.recall who →
    entry.emitted.isSome = entry.action.transmission.isSome
  receipts : ∀ sender, sender ∈ execution.recall alice →
    sender.beforeView.application.publicView.clock = 0 →
    ∀ receiver, receiver ∈ execution.recall bob →
    0 < receiver.beforeView.application.publicView.clock →
    ∀ message, sender.emitted = some message →
      ∃ accepted, (message.id, accepted) ∈ receiver.beforeView.receipts

private theorem respond_emissions (execution : app.Execution)
    (valid : ∀ who entry, entry ∈ execution.recall who →
      entry.emitted.isSome = entry.action.transmission.isSome)
    (who : Player) (response : app.Action) :
    ∀ observer entry, entry ∈ (execution.respond app who response).recall observer →
      entry.emitted.isSome = entry.action.transmission.isSome := by
  intro observer entry member
  by_cases same : observer = who
  · subst observer
    rcases response with ⟨transmission⟩
    cases transmission with
    | none =>
        simp only [ReactiveApplication.Execution.respond, ↓reduceIte,
          List.mem_append, List.mem_singleton] at member
        rcases member with previous | rfl
        · exact valid who entry previous
        · rfl
    | some submission =>
        simp only [ReactiveApplication.Execution.respond, ↓reduceIte,
          List.mem_append, List.mem_singleton] at member
        rcases member with previous | rfl
        · exact valid who entry previous
        · rfl
  · rw [app.respond_recall_other execution who observer same response] at member
    exact valid observer entry member

private theorem respond_facts (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (valid : RecallFacts control.execution) (who : Player)
    (active : control.actor = some who) (response : app.Action) :
    RecallFacts (control.execution.respond app who response) := by
  have clocks : (control.execution.respond app who response).application.clock =
      control.execution.application.clock := congrArg PublicView.clock
    (LateOpeningRuntimeService.runtime.reactive_respond_application leaks
      control.execution who response).2
  refine ⟨?_, respond_emissions control.execution valid.emissions who response, ?_⟩
  · intro observer entry member
    rw [clocks]
    rcases app.respond_entry_origin control.execution who observer response entry member
      with previous | fresh
    · exact valid.clocks observer entry previous
    · rw [fresh.2]
      exact le_rfl
  · intro sender senderMember clockZero receiver receiverMember later message emitted
    rcases app.respond_entry_origin control.execution who alice response sender senderMember
      with previousSender | freshSender
    · rcases app.respond_entry_origin control.execution who bob response receiver receiverMember
        with previousReceiver | freshReceiver
      · exact valid.receipts sender previousSender clockZero receiver previousReceiver later
          message emitted
      · have receipt := protected_submission_receipt_of_active weight nonnegative control trace
          alice sender previousSender message emitted (Or.inr clockZero) (by rw [active]; simp)
        rw [freshReceiver.2]
        exact receipt
    · rcases app.respond_entry_origin control.execution who bob response receiver receiverMember
        with previousReceiver | freshReceiver
      · have before := valid.clocks bob receiver previousReceiver
        have zero : control.execution.application.clock = 0 := by
          rw [freshSender.2] at clockZero
          exact clockZero
        omega
      · have impossible : alice = bob := freshSender.1.trans freshReceiver.1.symm
        exact ((by decide : alice ≠ bob) impossible).elim

private theorem environment_facts (execution next : app.Execution) (command : app.Command)
    (valid : RecallFacts execution) (grows : execution.application.clock ≤ next.application.clock)
    (supported : next ∈ (execution.environmentStep app command).support) : RecallFacts next := by
  have recalled := app.environmentStep_recall execution next command supported
  refine ⟨?_, ?_, ?_⟩
  · intro who entry member
    rw [recalled] at member
    exact (valid.clocks who entry member).trans grows
  · intro who entry member
    rw [recalled] at member
    exact valid.emissions who entry member
  · rw [recalled]
    exact valid.receipts

private def FactsAt : app.ProtocolState → Prop
  | none => True
  | some control => RecallFacts control.execution

private theorem recall_facts_history :
    ∀ {state} (_trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace state), FactsAt state
  | _, .start => trivial
  | _, @Trace.extend _ _ source target before joint legal realized => by
      have inherited := recall_facts_history before
      have reached : target ∈ (app.transition initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) source joint).support := realized
      cases source with
      | none =>
          obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
          refine ⟨?_, ?_, ?_⟩
          · intro who entry impossible
            exact (List.not_mem_nil impossible).elim
          · intro who entry impossible
            exact (List.not_mem_nil impossible).elim
          · intro sender impossible
            exact (List.not_mem_nil impossible).elim
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              change target ∈ (PMF.pure (some ⟨remaining, none,
                execution.respond app who ((joint who).getD ⟨none⟩)⟩)).support at reached
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact respond_facts weight nonnegative ⟨remaining, some who, execution⟩
                before inherited who rfl _
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  change target ∈ ((LateOpeningRuntimeService.scheduler weight nonnegative
                    execution.environmentRecall (execution.observeEnvironment app)).bind
                      fun command => (execution.environmentStep app command).map
                        (fun next => some ⟨remaining, command.actor? app, next⟩)).support at reached
                  obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  obtain ⟨inputs, invariant⟩ :=
                    (completion_phase_history weight nonnegative
                      ⟨remaining + 1, none, execution⟩ before).invariant
                  have progress := LateOpeningRuntimeService.runtime.reactive_environment_progress
                    leaks inputs execution next command invariant supported
                  have grows : execution.application.clock ≤ next.application.clock := by
                    rw [progress.clock]
                    omega
                  exact environment_facts execution next command inherited grows supported

/-- Silence at every clock-zero Alice response, including its raw action syntax. -/
def ProtectedSilence (execution : app.Execution) : Prop :=
  ∀ entry, entry ∈ execution.recall alice →
    entry.beforeView.application.publicView.clock = 0 → entry.action.transmission = none

/-- Empty receipts in a remembered later Bob callback rule out every protected
Alice packet, including rejected packets and private submission aliases. -/
theorem protected_silence_of_empty_receipt_recall (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (remembered : app.PlayerEntry) (member : remembered ∈ control.execution.recall bob)
    (later : 0 < remembered.beforeView.application.publicView.clock)
    (empty : remembered.beforeView.receipts = []) : ProtectedSilence control.execution := by
  have valid := recall_facts_history weight nonnegative trace
  intro sender senderMember clockZero
  have notEmitted : sender.emitted = none := by
    cases emitted : sender.emitted with
    | none => rfl
    | some message =>
        obtain ⟨accepted, receipt⟩ := valid.receipts sender senderMember clockZero
          remembered member later message emitted
        rw [empty] at receipt
        exact (List.not_mem_nil receipt).elim
  have equal := valid.emissions alice sender senderMember
  rw [notEmitted] at equal
  cases transmitted : sender.action.transmission with
  | none => rfl
  | some material =>
      rw [transmitted] at equal
      cases equal

/-- The same protected silence holds at every native history of the full Bob
information class. Only his actual remembered observation is assumed. -/
theorem information_histories_protected_silent
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob site.1) (control : app.Control)
    (current : representative.1.state = some control) (active : control.actor = some bob)
    (remembered : app.PlayerEntry) (member : remembered ∈ control.execution.recall bob)
    (later : 0 < remembered.beforeView.application.publicView.clock)
    (empty : remembered.beforeView.receipts = [])
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    ∃ compatible : app.Control, history.1.state = some compatible ∧
      ProtectedSilence compatible.execution := by
  have acting := InformationModel.InformationSite.active _ site history
  obtain ⟨compatible, stateEq, compatibleActor⟩ := app.control_of_active initial
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.toRawHistory _ _ _ history.1) bob acting
  change history.1.state = some compatible at stateEq
  have information := representative.2.trans history.2.symm
  change (rawMenu.signals _ _ _).infoOf bob representative.1.trace =
    (rawMenu.signals _ _ _).infoOf bob history.1.trace at information
  rw [rawMenu.info, rawMenu.info, current, stateEq] at information
  simp only [ReactiveApplication.observe, active, compatibleActor, ↓reduceIte] at information
  have sameRecall := congrArg Prod.fst (Option.some.inj information)
  change control.execution.recall bob = compatible.execution.recall bob at sameRecall
  have compatibleMember : remembered ∈ compatible.execution.recall bob := sameRecall ▸ member
  have trace := stateEq ▸ rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) history.1.trace
  exact ⟨compatible, stateEq, protected_silence_of_empty_receipt_recall weight nonnegative
    compatible trace remembered compatibleMember later empty⟩

end Vegas.Examples.LateOpeningRuntimeProtectedRecall
