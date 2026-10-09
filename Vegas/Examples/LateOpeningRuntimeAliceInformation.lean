/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceContinuation
import Vegas.Examples.LateOpeningRuntimeNash
import Interaction.ReactiveProvenance
import Interaction.ReactiveMessageIdentity

/-! # Actual information at Alice's remaining late callback

Own recall fixes Alice's previous envelope. Empty public receipts rule out
every earlier Bob envelope, because Bob's author service includes even rejected
calls. Carrier retention and distinct identifiers therefore recover the sole
pending opening throughout the actual information class.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceInformation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeLatePrefix LateOpeningRuntimeLateAcceptance

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- No protected Bob packet can be hidden by the pending sampler at an
active callback with an empty public receipt list. -/
theorem empty_receipts_no_bob_inputs (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (active : control.actor ≠ none) (empty : control.execution.receipts = []) :
    ∀ message ∈ control.execution.network.inputs, message.sender ≠ bob := by
  have origins := app.history_provenance initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  change control.execution.Provenance app at origins
  intro message member owned
  obtain ⟨entry, recalled, material, _transmitted, emitted, _packet⟩ :=
    origins.inputs message member
  rw [owned] at recalled
  obtain ⟨accepted, received⟩ := protected_submission_receipt_of_active weight nonnegative
    control trace bob entry recalled message emitted (Or.inl rfl) active
  rw [empty] at received
  exact List.not_mem_nil received

/-- Alice's actual own record and public receipts determine the complete
carrier input list, including rejected or malformed Bob traffic. -/
theorem first_opening_inputs (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (active : control.actor ≠ none) (empty : control.execution.receipts = [])
    (bit : Bool) (ownOutputs : app.outputs (control.execution.recall alice) =
      [openingMessage bit]) : control.execution.network.inputs = [openingMessage bit] := by
  have noBob := empty_receipts_no_bob_inputs weight nonnegative control trace active empty
  have recalled := app.history_inputRecall initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  change control.execution.InputRecall app at recalled
  have allAlice : ∀ message ∈ control.execution.network.inputs, message.sender = alice := by
    intro message member
    have different := noBob message member
    rcases message with ⟨⟨owner, serial⟩, payload⟩
    fin_cases owner
    · rfl
    · exact (different rfl).elim
  have same : control.execution.network.inputs.filter
      (fun message => message.sender = alice) = control.execution.network.inputs := by
    apply List.filter_eq_self.mpr
    intro message member
    exact decide_eq_true (allAlice message member)
  exact same.symm.trans ((recalled alice).trans ownOutputs)

/-- One retained input and no published input give the exact one-envelope
pending pool at every legal native history. -/
theorem singleton_input_pending (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (message : Message Player app.Payload)
    (inputs : control.execution.network.inputs = [message])
    (ledger : control.execution.network.ledger = []) :
    control.execution.network.pending = [message] := by
  have retained := app.pendingOrPublished_history
    (LateOpeningRuntimeService.scheduler weight nonnegative) initial
      LateOpeningRuntimeService.horizon trace
  change control.execution.network.PendingOrPublished at retained
  have present : message ∈ control.execution.network.pending := by
    rcases retained.inputs message (by rw [inputs]; simp) with pending | published
    · exact pending
    · rw [ledger] at published
      exact (List.not_mem_nil published).elim
  have origins := app.history_provenance initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  change control.execution.Provenance app at origins
  have recalled := app.history_inputRecall initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  change control.execution.InputRecall app at recalled
  have only : ∀ packet ∈ control.execution.network.pending, packet = message := by
    intro packet pending
    obtain ⟨entry, member, _material, _action, emitted, _packet⟩ := origins.pending packet pending
    have output : packet ∈ app.outputs (control.execution.recall packet.sender) := by
      exact List.mem_filterMap.mpr ⟨entry, member, emitted⟩
    rw [← recalled packet.sender] at output
    exact List.mem_singleton.mp (inputs ▸ (List.mem_filter.mp output).1)
  have distinct := app.idsDistinct_history (LateOpeningRuntimeService.scheduler weight nonnegative)
    initial LateOpeningRuntimeService.horizon trace
  change control.execution.network.IdsDistinct at distinct
  unfold MessageNetwork.IdsDistinct at distinct
  rw [ledger, List.append_nil] at distinct
  cases pendingEq : control.execution.network.pending with
  | nil => rw [pendingEq] at present; exact (List.not_mem_nil present).elim
  | cons first rest =>
      have firstEq : first = message := only first (pendingEq ▸ List.mem_cons_self)
      subst first
      have restEmpty : rest = [] := by
        by_contra nonempty
        obtain ⟨second, member⟩ := List.exists_mem_of_ne_nil rest nonempty
        have secondEq := only second (pendingEq ▸ List.mem_cons_of_mem message member)
        rw [pendingEq, List.map_cons] at distinct
        have excluded := (List.nodup_cons.mp distinct).1
        exact excluded (List.mem_map.mpr ⟨second, member, congrArg Message.id secondEq⟩)
      rw [restEmpty]

/-- The clock in Alice's observation identifies her actual final callback. -/
theorem last_alice_cursor (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (active : control.actor = some alice) (clock : control.execution.application.clock = 2) :
    control.execution.environmentRecall.length = 8 ∧ control.remaining = 18 := by
  have located := active_cursor weight nonnegative control trace alice active
  have clocked := clock_history weight nonnegative control trace
  have position : control.execution.environmentRecall.length = 8 := by
    rcases located with ⟨_, positions⟩ | ⟨impossible, _⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at positions
      rcases positions with early | early | last
      · rw [early] at clocked
        have zero : LateOpeningRuntimeService.clockAt 1 = 0 := by decide
        rw [zero] at clocked
        omega
      · rw [early] at clocked
        have one : LateOpeningRuntimeService.clockAt 4 = 1 := by decide
        rw [one] at clocked
        omega
      · exact last
    · exact ((by decide : alice ≠ bob) impossible).elim
  have accounted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  change control.execution.environmentRecall.length + control.remaining = 26 at accounted
  exact ⟨position, by omega⟩

theorem reference_outputs (bit : Bool) (label : Fin 3) (seen : Bool) :
    app.outputs ((secondLateDecision bit label 0 seen).recall alice) = [openingMessage bit] := by
  change app.outputs ((beforeBob bit label 0).recall alice) = _
  change [(⟨(alice, 0), app.packet (firstLateDecision bit label).application alice []
    (disclosureSubmission (.opening aliceEvent aliceCandidate ⟨.bool, bit⟩))⟩ :
      Message Player app.Payload)] = _
  rw [firstLate_opening_packet]
  rfl

/-- Every hidden history of the actual Alice information class has the same
single genuine pending envelope and the same remaining service horizon. -/
theorem information_fiber
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      alice site.1)
    (bit : Bool) (label : Fin 3) (seen : Bool)
    (current : representative.1.state = some ⟨18, some alice,
      secondLateDecision bit label 0 seen⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1) :
    ∃ execution : app.Execution,
      history.1.state = some ⟨18, some alice, execution⟩ ∧
      execution.recall alice = (secondLateDecision bit label 0 seen).recall alice ∧
      execution.observe app alice = (secondLateDecision bit label 0 seen).observe app alice ∧
      execution.network.inputs = [openingMessage bit] ∧
      execution.network.pending = [openingMessage bit] ∧
      execution.receipts = [] ∧ execution.environmentRecall.length = 8 := by
  classical
  have active := InformationModel.InformationSite.active _ site history
  obtain ⟨control, stateEq, actor⟩ := app.control_of_active initial
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.toRawHistory _ _ _ history.1) alice active
  change history.1.state = some control at stateEq
  have trace := stateEq ▸ rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) history.1.trace
  have information := history.2.trans representative.2.symm
  change (rawMenu.signals _ _ _).infoOf alice history.1.trace =
    (rawMenu.signals _ _ _).infoOf alice representative.1.trace at information
  rw [rawMenu.info, rawMenu.info] at information
  change app.observe alice history.1.state = app.observe alice representative.1.state at information
  rw [stateEq, current] at information
  simp only [ReactiveApplication.observe, actor, ↓reduceIte] at information
  have sameRecall := congrArg Prod.fst (Option.some.inj information)
  have sameView := congrArg Prod.snd (Option.some.inj information)
  have empty : control.execution.receipts = [] := congrArg
    ReactiveApplication.PlayerView.receipts sameView
  have ledger : control.execution.network.ledger = [] := congrArg
    (fun view : app.PlayerView => view.messages.ledger) sameView
  have clock : control.execution.application.clock = 2 := congrArg
    (fun view : app.PlayerView => view.application.publicView.clock) sameView
  have cursor := last_alice_cursor weight nonnegative control trace actor clock
  have inputs := first_opening_inputs weight nonnegative control trace
    (by rw [actor]; simp) empty bit
      ((congrArg (app.outputs ·) sameRecall).trans (reference_outputs bit label seen))
  have pending := singleton_input_pending weight nonnegative control trace _ inputs ledger
  have sameControl : control = ⟨18, some alice, control.execution⟩ := by
    cases control
    simp only [ReactiveApplication.Control.mk.injEq] at actor cursor ⊢
    exact ⟨cursor.2, actor, trivial⟩
  exact ⟨control.execution, stateEq.trans (congrArg some sameControl), sameRecall,
    sameView, inputs, pending, empty, cursor.1⟩

end Vegas.Examples.LateOpeningRuntimeAliceInformation
