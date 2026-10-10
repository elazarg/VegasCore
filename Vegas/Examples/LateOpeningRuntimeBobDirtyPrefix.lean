/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Vegas.Examples.LateOpeningRuntimeBobBindingFiber
import Vegas.Examples.LateOpeningRuntimeBobRecallStability
import Vegas.Examples.LateOpeningRuntimeBobSunkAudit
import Vegas.Examples.LateOpeningRuntimeBobSubmissionService

/-!
# Rejected traffic in dirty native binding histories

The full native legal information fiber includes histories in which Alice
published before Bob's first callback. A non-silent earlier Bob response still
yields an actual rejected envelope when his first binding remains ready.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobDirtyPrefix

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobBindingService
  LateOpeningRuntimeBobRecallStability LateOpeningRuntimeBobSunkAudit
  LateOpeningRuntimeBobSubmissionService

/-- Every dirty legal first-binding history contains an actual rejected Bob
envelope, including histories where Alice had already published early. -/
theorem dirty_binding_history_has_rejected_traffic (weight : ℝ) (nonnegative : 0 ≤ weight)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (dirty : ¬ SilentRecall execution) :
    ∃ traffic ∈ app.executionTraffic execution,
      traffic.envelope.sender = bob ∧ (traffic.envelope.id, false) ∈ execution.receipts := by
  classical
  let players := rawMenu.uniformResponses
  have uniform := rawMenu.roundSupported_uniform initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  obtain ⟨budget, count, before, command, length, beforeSupported, selected,
    actor, observed⟩ := uniform
  change execution.environmentRecall.length + 14 = 26 at budget
  have cursor : execution.environmentRecall.length = 12 := by omega
  change execution.environmentRecall.length = count + 1 at length
  have countEq : count = 11 := by omega
  subst count
  have beforeLength := app.roundsFrom_recall initial
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 11 before beforeSupported
  have commandEq : command = .activate bob := by
    change command ∈ (stageChoice weight nonnegative before.environmentRecall.length _).support
      at selected
    rw [beforeLength] at selected
    exact (PMF.mem_support_pure_iff _ _).mp selected
  subst command
  have currentRecall := congrFun (app.environmentStep_recall before execution
    (.activate bob) observed) bob
  unfold ReactiveApplication.roundsFrom at beforeSupported
  obtain ⟨state, stateSupported, beforeReached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ beforeSupported)
  rw [app.runRounds_add (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 5 6] at beforeReached
  obtain ⟨responded, five, six⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ beforeReached)
  rw [app.runRounds_add (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 4 1] at five
  obtain ⟨prior, four, fifth⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ five)
  have priorSupported : prior ∈ (app.roundsFrom initial
      (LateOpeningRuntimeService.scheduler weight nonnegative) players 4).support :=
    by
      change prior ∈ (initial.bind fun state => app.runRounds
        (LateOpeningRuntimeService.scheduler weight nonnegative) players 4
        (ReactiveApplication.Execution.initial app state)).support
      rw [PMF.support_bind]
      exact Set.mem_iUnion₂.mpr ⟨state, stateSupported, four⟩
  have priorLength := app.roundsFrom_recall initial
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 4 prior priorSupported
  have priorEmpty : prior.recall bob = [] := by
    have kept := before_first_callback_recall weight nonnegative players 4
      (ReactiveApplication.Execution.initial app state) prior (by change 4 ≤ 4; omega) four
    exact kept
  simp only [ReactiveApplication.runRounds, PMF.bind_pure] at fifth
  obtain ⟨earlyCommand, earlySelected, earlyDispatched⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ fifth)
  have earlyCommandEq : earlyCommand = .activate bob := by
    change earlyCommand ∈ (stageChoice weight nonnegative prior.environmentRecall.length _).support
      at earlySelected
    rw [priorLength] at earlySelected
    exact (PMF.mem_support_pure_iff _ _).mp earlySelected
  subst earlyCommand
  obtain ⟨early, activated, resumed⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ earlyDispatched)
  have earlyEmpty : early.recall bob = [] := by
    rw [app.environmentStep_recall prior early (.activate bob) activated, priorEmpty]
  obtain ⟨response, _, respondedEq⟩ := PMF.support_map .. ▸ resumed
  subst responded
  have respondedLength := app.round_environmentRecall_length
    (LateOpeningRuntimeService.scheduler weight nonnegative) players prior
    (early.respond app bob response) fifth
  have earlyLength : (early.respond app bob response).environmentRecall.length = 5 := by omega
  have beforeRecall := before_binding_recall weight nonnegative players 6
    (early.respond app bob response) before (by omega) (by omega) six
  have responseActions : (execution.recall bob).map ReactiveApplication.PlayerEntry.action =
      [response] := by
    rw [currentRecall, beforeRecall, app.respond_actions, earlyEmpty]
    rfl
  have nonsilent : response ≠ ⟨none⟩ := by
    intro silent
    apply dirty
    intro entry member
    have present : entry.action ∈
        (execution.recall bob).map ReactiveApplication.PlayerEntry.action :=
      List.mem_map.mpr ⟨entry, member, rfl⟩
    rw [responseActions, silent, List.mem_singleton] at present
    exact present
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact (nonsilent rfl).elim
  | some material =>
    obtain ⟨priorTrace⟩ := app.raw_trace_roundsFrom initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) players 4 (by decide)
      prior priorSupported
    obtain ⟨earlyTrace⟩ := app.raw_trace_environment initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) 21 prior early (.activate bob)
      priorTrace earlySelected activated
    obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) 21 early bob ⟨some material⟩
      earlyTrace
    let message : Message Player app.Payload :=
      ⟨(bob, early.network.nextSerial bob),
        app.packet (app.submit early.application bob material) bob
          (early.network.known bob) material⟩
    have inputs := app.stateTraffic_inputs initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) respondedTrace
    change (app.executionTraffic (early.respond app bob ⟨some material⟩)).map
      ReactiveApplication.TrafficRecord.envelope = early.network.inputs ++ [message] at inputs
    have presentMessage : message ∈
        (app.executionTraffic (early.respond app bob ⟨some material⟩)).map
          ReactiveApplication.TrafficRecord.envelope := by rw [inputs]; simp
    obtain ⟨traffic, present, same⟩ := List.mem_map.mp presentMessage
    have retained := (app.executionTraffic_runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) players 6 _ before six).subset
        present
    have currentTraffic : traffic ∈ app.executionTraffic execution := by
      rw [app.executionTraffic_environment before execution (.activate bob) observed]
      exact retained
    have rest := six
    rw [ReactiveApplication.runRounds] at rest
    obtain ⟨served, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ rest)
    rw [submission_round weight nonnegative 21 early earlyTrace material players,
      PMF.mem_support_pure_iff] at moved
    subst served
    let submitted := early.respond app bob ⟨some material⟩
    let collected := (app.handle submitted.application message).isSome
    have serials := app.serialsBeforeNext_history
      (LateOpeningRuntimeService.scheduler weight nonnegative) initial
      LateOpeningRuntimeService.horizon earlyTrace
    have found := serials.lookup_submit bob
      (app.packet (app.submit early.application bob material) bob
        (early.network.known bob) material)
    change submitted.network.lookup message.id = some message at found
    have receipt : (message.id, collected) ∈ (servicedSubmission early material).receipts := by
      change (message.id, collected) ∈ (submitted.includePending app message.id).receipts
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      rw [found]
      change (message.id, collected) ∈ submitted.receipts ++ [(message.id, collected)]
      simp
    have beforeReceipt := (app.receipt_policyInvariant players (message.id, collected)).runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) 5 _ before receipt continued
    have currentReceipt := (app.environmentStep_receipts_prefix before execution
      (.activate bob) observed).subset beforeReceipt
    have rejected : collected = false := by
      cases value : collected
      · rfl
      · have accepted : ((bob, early.network.nextSerial bob), true) ∈ execution.receipts := by
          simpa only [value] using currentReceipt
        exact (no_accepting_receipt_before_binding weight nonnegative
          ⟨14, some bob, execution⟩ (rawMenu.toRawTrace _ _ _ trace) ready
          (early.network.nextSerial bob) accepted).elim
    refine ⟨traffic, currentTraffic, ?_, ?_⟩
    · rw [same]
      rfl
    · rw [same]
      simpa only [rejected] using currentReceipt

/-- Prior non-silent receiver traffic fixes the full audit deduction throughout
all subsequent native continuations, regardless of later player policies. -/
theorem dirty_binding_continuation_full_charge (weight : ℝ) (nonnegative : 0 ≤ weight)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (dirty : ¬ SilentRecall execution)
    (response : app.Action) (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 (execution.respond app bob response)).support) :
    GameTheory.Enforcement.TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
        (some ⟨0, none, final⟩) bob = 1 := by
  obtain ⟨traffic, present, owner, rejected⟩ :=
    dirty_binding_history_has_rejected_traffic weight nonnegative execution trace ready dirty
  exact LateOpeningRuntimeBobSunkAudit.rejected_prefix_full_charge weight nonnegative
    14 execution (rawMenu.toRawTrace _ _ _ trace) traffic present owner rejected
      response players final reached

/-- Dirty first-binding continuations share one sunk deposit deduction; the
identity does not require a positive deposit or successful sender publication. -/
theorem dirty_binding_payoff_eq_base_sub_deposit (weight : ℝ) (nonnegative : 0 ≤ weight)
    (reward forfeit : ℝ) (deposit : Player → ℝ) (execution : app.Execution)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (dirty : ¬ SilentRecall execution)
    (response : app.Action) (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 (execution.respond app bob response)).support) :
    LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit (some ⟨0, none, final⟩) bob =
        LateOpeningRuntimeUtility.nativeBaseUtility reward forfeit (some ⟨0, none, final⟩) bob -
          deposit bob := by
  unfold LateOpeningRuntimeNash.payoff GameTheory.Enforcement.TerminalAudit.utility
  rw [dirty_binding_continuation_full_charge weight nonnegative execution trace ready dirty
    response players final reached]
  ring
/-- The sunk-charge identity holds at every compatible legal history, including
histories carrying zero posterior belief. -/
theorem dirty_information_history_full_charge (weight : ℝ) (nonnegative : 0 ≤ weight)
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob site.1)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (dirty : ¬ SilentRecall execution)
    (current : representative.1.state = some ⟨14, some bob, execution⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    ∃ other : app.Execution,
      history.1.state = some ⟨14, some bob, other⟩ ∧
      execution.recall bob = other.recall bob ∧ execution.observe app bob = other.observe app bob ∧
      ∀ (response : app.Action) (players : Player → app.Policy) (final : app.Execution),
        final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          players 14 (other.respond app bob response)).support →
        GameTheory.Enforcement.TerminalAudit.charge
          (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
          (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
            (some ⟨0, none, final⟩) bob = 1 := by
  obtain ⟨other, stateEq, sameRecall, sameView⟩ :=
    LateOpeningRuntimeBobBindingFiber.binding_history_same_information weight nonnegative
      site representative execution (rawMenu.toRawTrace _ _ _ trace) ready current history
  have otherReady := LateOpeningRuntimeBobBindingInformation.ready_same_view _ _ sameView ready
  have otherDirty : ¬ SilentRecall other := by
    intro quiet
    apply dirty
    unfold SilentRecall at quiet ⊢
    rw [sameRecall]
    exact quiet
  refine ⟨other, stateEq, sameRecall, sameView, ?_⟩
  intro response players final reached
  exact dirty_binding_continuation_full_charge weight nonnegative other
    (stateEq ▸ history.1.trace) otherReady otherDirty response players final reached
end Vegas.Examples.LateOpeningRuntimeBobDirtyPrefix
