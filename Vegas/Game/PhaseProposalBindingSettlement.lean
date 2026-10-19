/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseCompletedBindingMeaning
import Vegas.Pending.PhaseRecordedBindingMaterial
import Vegas.Pending.PhaseBindingFreshness
import Vegas.Pending.PhaseAcceptedOrder
import Vegas.Pending.PhaseStoredCheckpoint

/-! # Physical current binding fields retain the original emitted material -/

noncomputable section

namespace Vegas

open EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)

/-- A completed surviving coordinate has the exact private preparation of its
original recorded SEND, for every actual evidence alias. Freshness is derived
at that recorded callback; foreign exclusions and retired catalogue occupancy
are retained. This is a physical-store readback, not a policy support premise. -/
theorem phaseProposal_completed_binding_material
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (lower : control.execution.application.attempt.phase ≤ event.val)
    (completed : event ∈ control.execution.application.current.native.config.cut.completed)
    (surviving : owner ∉ control.execution.application.current.excluded)
    (serial : Nat) (opening : Option (Raw L)) (evidence : EvidenceRequest graph)
    (record : (app).PlayerEntry) (recorded : record ∈ control.execution.recall owner)
    (declared : record.action =
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩)
    (sameAttempt : record.beforeView.application.2.attempt =
      control.execution.application.attempt) :
    (⟨.inr event, binding⟩ : FieldRef graph.layout (.binding owner payload)).get?
        control.execution.application.current.native.config.store =
      some ((opening.bind fun raw => raw.as? payload).elim .failure PublicationResult.success) := by
  let material : WitnessedSubmission graph :=
    ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩
  have transmitted : record.action.transmission = some material := by rw [declared]
  have accepted := PhaseCount.completed_recorded_binding_accepted runtime leaks bounds plan inputs
    horizon scheduler trace owner event payload binding lower completed surviving record recorded
      material transmitted (owner, .prepared serial) rfl sameAttempt
  obtain ⟨before, prior, _prefix, _acting, viewed, offered, _past⟩ :=
    (menu).recorded_response_prefix initial horizon scheduler control trace owner record recorded
  rw [declared] at offered
  have fresh : record.beforeView.application.1.candidates (.prepared serial) = .fresh :=
    viewed ▸ PhaseCount.onePacket_binding_fresh runtime leaks bounds plan inputs horizon scheduler
      prior owner event serial opening evidence offered
  have meaning := phase_recorded_material_binding_result runtime leaks (menu) initial horizon
    scheduler control trace owner event payload serial opening evidence record recorded declared
      fresh
  let raw := (menu).toRawTrace initial horizon scheduler trace
  have bindings :=
    (phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw).active
  have read := bindings.binding_read
    (⟨.inr event, binding⟩ : FieldRef graph.layout (.binding owner payload)) event rfl completed
  rw [accepted, Option.elim_some, meaning] at read
  exact read

/-- An owner excluded on entry cannot acquire an accepted current binding.
Consequently any physically completed current field of that owner is exactly
the automatic failure, independently of all ordinary private values. -/
theorem phaseProposal_completed_inherited_binding
    (ordered : graph.RevealRelaxedOrdered)
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (phase : RuntimePhase graph) (installed : phase ∈ control.execution.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (inside : event ∈ phase.events)
    (completed : event ∈ control.execution.application.current.native.config.cut.completed)
    (inherited : owner ∈ control.execution.application.entry.excluded) :
    (⟨.inr event, binding⟩ : FieldRef graph.layout (.binding owner payload)).get?
        control.execution.application.current.native.config.store = some .failure := by
  let raw := (menu).toRawTrace initial horizon scheduler trace
  have receiptRecord := phaseReceiptRecord_history runtime leaks ordered plan inputs horizon
    scheduler raw
  have receipts := receiptRecord.ordered phase installed commitment
  have missing : control.execution.application.current.native.accepted (.inr event) = none := by
    cases accepted : control.execution.application.current.native.accepted (.inr event) with
    | none => rfl
    | some candidate =>
      exact ((receipts event owner payload candidate ((phase.mem_events event).mp inside).1 binding
        accepted).1 inherited).elim
  have bindings :=
    (phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw).active
  have read := bindings.binding_read
    (⟨.inr event, binding⟩ : FieldRef graph.layout (.binding owner payload)) event rfl completed
  simpa only [missing, Option.elim_none] using read

/-- Primitive retention of the actual emitted binding meanings. This predicate
reads the original signed traffic and its immutable candidate meanings; it
does not mention physical acceptance or prescribe a semantic probability law. -/
def PhaseProposalEmittedBindings
    (execution : (app).Execution) (phase : RuntimePhase graph) (frontier : graph.Config) : Prop :=
  ∀ message ∈ execution.network.inputs,
    message.payload.attempt = execution.application.attempt →
    ∀ event ∈ phase.events, ∀ candidate,
      message.payload.packet.call = .commitment event candidate →
      ∀ owner payload (binding : graph.outputLayout event = .binding owner payload),
        (⟨.inr event, binding⟩ : FieldRef graph.layout (.binding owner payload)).get?
            frontier.store = some (execution.application.current.native.bindingResult
              candidate payload)

/-- A physically completed active binding is present in an emission frontier
that retains the actual signed packet meanings. This does not presuppose any
inclusion of the physical completed cut in that frontier. -/
theorem phaseProposalBinding_active_stored
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (phase : RuntimePhase graph)
    (installed : control.execution.application.phases.head? = some phase)
    (frontier : graph.Config)
    (emissions : PhaseProposalEmittedBindings runtime leaks control.execution phase frontier)
    (event : graph.EventId) (inside : event ∈ phase.events)
    (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (completed : event ∈ control.execution.application.current.native.config.cut.completed)
    (surviving : owner ∉ control.execution.application.current.excluded) :
    (⟨.inr event, binding⟩ : FieldRef graph.layout (.binding owner payload)).get?
        control.execution.application.current.native.config.store =
      (⟨.inr event, binding⟩ : FieldRef graph.layout (.binding owner payload)).get? frontier.store ∧
        event ∈ frontier.cut.completed := by
  let raw := (menu).toRawTrace initial horizon scheduler trace
  have bindings :=
    (phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw).active
  have coverage :=
    (phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler raw).active
  have stamp := phaseLiveBindingStamp_history runtime leaks plan inputs horizon scheduler raw
  have address : control.execution.application.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, Option.map_some, Option.getD_some]
  have present : control.execution.application.current.native.accepted (.inr event) ≠ none := by
    intro missing
    have missed := (control.execution.application.current.native.publicView_missedBinding
      event owner payload binding).mpr ⟨completed, missing⟩
    exact surviving (coverage.covered event owner
      (actor?_of_outputLayout_binding graph binding) (Or.inl missed))
  obtain ⟨candidate, accepted⟩ := Option.ne_none_iff_exists'.mp present
  have read := bindings.binding_read
    (⟨.inr event, binding⟩ : FieldRef graph.layout (.binding owner payload)) event rfl completed
  rw [accepted, Option.elim_some] at read
  rcases stamp event candidate accepted with past |
      ⟨message, authored, _sender, named, attempted⟩
  · have lower := ((phase.mem_events event).mp inside).1
    omega
  · have recalled := (app).history_inputRecall initial horizon scheduler raw
    have input : message ∈ control.execution.network.inputs := by
      change message ∈ (app).outputs (control.execution.recall candidate.1) at authored
      rw [← recalled candidate.1] at authored
      exact (List.mem_filter.mp authored).1
    have emitted := emissions message input attempted event inside candidate named owner payload
      binding
    refine ⟨read.trans emitted.symm, ?_⟩
    apply (frontier.output_available event).mp
    have available {first second : Type} (same : first = second) (item : Option first) :
        (cast (congrArg Option same) item).isSome = item.isSome := by
      cases same
      rfl
    change (frontier.store (.inr event)).isSome = true
    rw [← available (congrArg EventField.Value binding) (frontier.store (.inr event))]
    change ((⟨.inr event, binding⟩ : FieldRef graph.layout
      (.binding owner payload)).get? frontier.store).isSome = true
    rw [emitted]
    rfl

/-- Recorded emissions and the genuine physical receipt invariants imply
agreement on EVERY physically completed field. The current input law is never
conditioned or replaced, and inherited excluded coordinates are handled by
their literal automatic failure rather than a fictitious emission. -/
theorem phaseProposalBinding_completed_agreement
    (ordered : graph.RevealRelaxedOrdered)
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (phase : RuntimePhase graph)
    (installed : control.execution.application.phases.head? = some phase)
    (commitment : phase.kind = .commitment) (frontier : graph.Config)
    (sameExcluded : control.execution.application.current.excluded =
      control.execution.application.entry.excluded)
    (domain : control.execution.application.current.native.config.cut.completed ⊆
      frontier.cut.completed)
    (prior : ∀ event : graph.EventId, event.val < phase.low →
      control.execution.application.entry.native.config.outputs event = frontier.outputs event)
    (emissions : PhaseProposalEmittedBindings runtime leaks control.execution phase frontier)
    (automatic : ∀ event ∈ frontier.cut.completed, event ∈ phase.events →
      ∀ owner ∈ control.execution.application.entry.excluded, ∀ payload,
        ∀ binding : graph.outputLayout event = .binding owner payload,
          (⟨.inr event, binding⟩ : FieldRef graph.layout (.binding owner payload)).get?
            frontier.store = some .failure) :
    control.execution.application.current.native.config.CompletedOutputAgreement frontier := by
  let raw := (menu).toRawTrace initial horizon scheduler trace
  have receipts := phaseReceiptRecord_history runtime leaks ordered plan inputs horizon scheduler
    raw
  have position :
      control.execution.application.entry.native.config.cut.IsPrefix phase.low ∧
      control.execution.application.current.native.config.cut.Within phase.low phase.high := by
    have positioned := receipts.exclusion.frontier.positioned
    cases phases : control.execution.application.phases with
    | nil => simp only [phases, List.head?_nil, reduceCtorEq] at installed
    | cons first rest =>
      have same : first = phase := by simpa only [phases, List.head?_cons, Option.some.injEq]
        using installed
      subst first
      simpa only [PhaseRuntimeState.Positioned, phases] using positioned
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler raw
  intro event completed
  by_cases earlier : event.val < phase.low
  · have saved := (position.1.2 event).mpr earlier
    obtain ⟨value, written⟩ := Option.isSome_iff_exists.mp
      ((control.execution.application.entry.native.config.output_available event).mpr saved)
    have retained := stored (.inr event) value written
    exact retained.trans (written.symm.trans (prior event earlier))
  · have inside : event ∈ phase.events := (phase.mem_events event).mpr
      ⟨by omega, position.2.2 event completed⟩
    have fields := phase.fields event ((phase.mem_events event).mp inside).1
      ((phase.mem_events event).mp inside).2
    rw [commitment] at fields
    obtain ⟨owner, payload, binding⟩ := fields
    let ref : FieldRef graph.layout (.binding owner payload) := ⟨.inr event, binding⟩
    apply (cast_inj (congrArg (fun kind : EventField Player L => Option kind.Value) binding)).mp
    change ref.get? control.execution.application.current.native.config.store =
      ref.get? frontier.store
    by_cases inherited : owner ∈ control.execution.application.entry.excluded
    · exact (phaseProposal_completed_inherited_binding runtime leaks bounds plan inputs horizon
        scheduler ordered control trace phase (Option.mem_def.mpr installed) commitment owner event
          payload binding inside completed inherited).trans
        (automatic event (domain completed) inside owner inherited payload binding).symm
    · have surviving : owner ∉ control.execution.application.current.excluded := by
        rw [sameExcluded]
        exact inherited
      exact (phaseProposalBinding_active_stored runtime leaks bounds plan inputs horizon
        scheduler control trace phase installed frontier emissions event inside owner payload
          binding completed surviving).1

/-- Quiescence of the fixed inherited excluded closure and actual retained
signed emissions derive physical cut inclusion. No environment-step or
physical admission law is supplied as a premise. -/
theorem phaseProposalBinding_settled_domain
    (ordered : graph.RevealRelaxedOrdered)
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (phase : RuntimePhase graph)
    (installed : control.execution.application.phases.head? = some phase)
    (commitment : phase.kind = .commitment) (frontier : graph.Config)
    (sameExcluded : control.execution.application.current.excluded =
      control.execution.application.entry.excluded)
    (prior : ∀ event : graph.EventId, event.val < phase.low →
      control.execution.application.entry.native.config.outputs event = frontier.outputs event)
    (emissions : PhaseProposalEmittedBindings runtime leaks control.execution phase frontier)
    (quiet : ∀ event ∈ phase.events, frontier.cut.Ready event →
      ∀ owner ∈ control.execution.application.entry.excluded,
        graph.actor? event ≠ some owner) :
    control.execution.application.current.native.config.cut.completed ⊆ frontier.cut.completed := by
  let raw := (menu).toRawTrace initial horizon scheduler trace
  have receipts := phaseReceiptRecord_history runtime leaks ordered plan inputs horizon scheduler
    raw
  have position :
      control.execution.application.entry.native.config.cut.IsPrefix phase.low ∧
      control.execution.application.current.native.config.cut.Within phase.low phase.high := by
    have positioned := receipts.exclusion.frontier.positioned
    cases phases : control.execution.application.phases with
    | nil => simp only [phases, List.head?_nil, reduceCtorEq] at installed
    | cons first rest =>
      have same : first = phase := by simpa only [phases, List.head?_cons, Option.some.injEq]
        using installed
      subst first
      simpa only [PhaseRuntimeState.Positioned, phases] using positioned
  have retained : ∀ rank, ∀ event : graph.EventId, event.val = rank →
      event ∈ control.execution.application.current.native.config.cut.completed →
        event ∈ frontier.cut.completed := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
        intro event indexed completed
        by_cases earlier : event.val < phase.low
        · have saved := (position.1.2 event).mpr earlier
          have available := (control.execution.application.entry.native.config.output_available
            event).mpr saved
          rw [prior event earlier] at available
          exact (frontier.output_available event).mp available
        · have inside : event ∈ phase.events := (phase.mem_events event).mpr
            ⟨by omega, position.2.2 event completed⟩
          have fields := phase.fields event ((phase.mem_events event).mp inside).1
            ((phase.mem_events event).mp inside).2
          rw [commitment] at fields
          obtain ⟨owner, payload, binding⟩ := fields
          by_cases inherited : owner ∈ control.execution.application.entry.excluded
          · by_contra missing
            have ready : frontier.cut.Ready event := ⟨missing, fun predecessor member =>
              ih predecessor.val (by have lower := graph.order.predecessor_lt member; omega)
                predecessor rfl
                (control.execution.application.current.native.config.cut.predecessor_closed
                  completed member)⟩
            exact quiet event inside ready owner inherited
              (actor?_of_outputLayout_binding graph binding)
          · have surviving : owner ∉ control.execution.application.current.excluded := by
              rwa [sameExcluded]
            exact (phaseProposalBinding_active_stored runtime leaks bounds plan inputs horizon
              scheduler control trace phase installed frontier emissions event inside owner payload
                binding completed surviving).2
  exact fun event completed => retained event.val event rfl completed

end Vegas
