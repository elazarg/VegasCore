/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCountUniqueness
import Vegas.Pending.ReactiveAssociationEvidence
import Vegas.Pending.ReactiveSignedCommitments
import Vegas.Pending.ReactiveOnePacketMenu
import Vegas.Pending.ReactiveServiceAudit
import Vegas.Pending.ReactiveEventStability
import Interaction.ReactiveMessageIdentity

/-! # Acceptance of authentic counted openings

At a genuine count-clean prefix, a certified opening signed by the owner's
unique binding packet names the currently accepted handle. If the owner has no
public binding omission, readiness and the live deadline therefore suffice for
acceptance, including execution of deferred guards that reject the revealed value.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private theorem initialBindingHandles_history
    (initial : PMF (runtime.reactiveApplication leaks).State)
    (initialized : ∀ state ∈ initial.support, ∃ inputs, state = State.initial inputs)
    (horizon : Nat) (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {control : (runtime.reactiveApplication leaks).Control}
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) :
    ∀ input owner payload, graph.inputLayout input = .binding owner payload →
      control.execution.application.accepted (.inl input) = some (owner, .initial input) := by
  let app := runtime.reactiveApplication leaks
  let property := fun state : State graph => ∀ input owner payload,
    graph.inputLayout input = .binding owner payload →
      state.accepted (.inl input) = some (owner, .initial input)
  have preserved : app.Invariant property := by
    refine ⟨?_, ?_, ?_⟩
    · intro state who material valid input owner payload binding
      rw [(keepsInputHandles_step runtime leaks).submit state who material input]
      exact valid input owner payload binding
    · intro state message next valid accepted input owner payload binding
      rw [(keepsInputHandles_step runtime leaks).handle state message next accepted input]
      exact valid input owner payload binding
    · intro state command next valid reached input owner payload binding
      rw [(keepsInputHandles_step runtime leaks).environment state command next reached input]
      exact valid input owner payload binding
  apply preserved.history initial horizon scheduler ?_ trace
  intro state supported
  obtain ⟨inputs, rfl⟩ := initialized state supported
  exact fun input owner payload binding => State.initial_accepted_binding inputs input owner payload
    binding

private theorem accepted_of_signedBinding
    (execution : (runtime.reactiveApplication leaks).Execution)
    (signed : SignedCommitments runtime leaks execution)
    (clean : runtime.CountClean leaks execution)
    (unique : execution.network.UniqueIds)
    (invariant : execution.application.BindingInvariant)
    (inputs : ∀ input owner payload, graph.inputLayout input = .binding owner payload →
      execution.application.accepted (.inl input) = some (owner, .initial input))
    (message : Message Player (WitnessedPacket graph)) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload)) (candidate : Handle graph)
    (available : (execution.application.config.store binding.field).isSome = true)
    (sender : message.sender = owner)
    (unmissed : execution.application.publicView.missedBindingBy owner = false)
    (signedBinding : SignedBinding (EarlierOwnPacket execution.network.inputs message)
      owner candidate binding.field) :
    execution.application.accepted binding.field = some candidate := by
  cases field : binding.field with
  | inl input =>
      rw [field] at signedBinding
      change candidate = (owner, .initial input) at signedBinding
      rw [signedBinding]
      apply inputs input owner payload
      have kind := binding.layout_eq
      rw [field] at kind
      exact kind
  | inr event =>
      have completed : event ∈ execution.application.config.cut.completed := by
        rw [field] at available
        exact (execution.application.config.output_available event).mp available
      have outputEq : graph.outputLayout event = .binding owner payload := by
        have kind := binding.layout_eq
        rw [field] at kind
        exact kind
      obtain ⟨accepted, associated⟩ :
          ∃ accepted, execution.application.accepted (.inr event) = some accepted := by
        cases ledger : execution.application.accepted (.inr event) with
        | some accepted => exact ⟨accepted, rfl⟩
        | none =>
            have missed := (execution.application.publicView_missedBinding event owner payload
              outputEq).mpr ⟨completed, ledger⟩
            have doomed := execution.application.publicView.missedBindingBy_of_event owner event
              (actor?_of_outputLayout_binding graph outputEq) missed
            rw [unmissed] at doomed
            cases doomed
      have owned : accepted.1 = owner := by
        obtain ⟨acceptedPayload, kind⟩ := invariant.accepted_typed (.inr event) accepted associated
        exact (EventField.binding.inj (outputEq.symm.trans kind)).1.symm
      rw [field] at signedBinding
      obtain ⟨other, ⟨otherInput, otherSender, _⟩, otherCall⟩ := signedBinding
      obtain ⟨actual, actualOutput, actualCall⟩ := signed.acceptedSigned event accepted associated
      rw [owned] at actualOutput
      have actualInput : actual ∈ execution.network.inputs := by
        rw [← clean.1.1 owner] at actualOutput
        exact (List.mem_filter.mp actualOutput).1
      have actualSender : actual.sender = owner := by
        rw [← clean.1.1 owner] at actualOutput
        simpa using (List.mem_filter.mp actualOutput).2
      have same : other = actual := CountPermits.eq_of_same_event
        ((countPermits_eq_true_iff _ _).mp (clean.2 other otherInput))
        ((countPermits_eq_true_iff _ _).mp (clean.2 actual actualInput)) otherInput actualInput
        (fun left leftInput right rightInput ids =>
          (unique.inputs right rightInput).inputs left leftInput ids)
        ((otherSender.trans sender).trans actualSender.symm) (by rw [otherCall, actualCall]; rfl)
      subst other
      have candidateEq : candidate = accepted := by
        rw [otherCall] at actualCall
        exact (Payload.commitment.inj actualCall).2
      rw [candidateEq]
      exact associated

/-- An authentic count-admitted opening is accepted at its live ready event.
Count cleanliness is an explicit restriction on this actual prefix. -/
theorem counted_opening_accepted
    (initial : PMF (runtime.reactiveApplication leaks).State)
    (initialized : ∀ state ∈ initial.support, ∃ inputs, state = State.initial inputs)
    (horizon : Nat) (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {control : (runtime.reactiveApplication leaks).Control}
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control))
    (clean : runtime.CountClean leaks control.execution)
    (message : Message Player (WitnessedPacket graph))
    (authentic : message ∈ control.execution.network.inputs)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (opening : message.payload.call = .opening event candidate raw)
    (unmissed : control.execution.application.publicView.missedBindingBy message.sender = false)
    (ready : control.execution.application.config.cut.Ready event)
    (timely : control.execution.application.WithinDeadline runtime event) :
    ∃ next, (runtime.reactiveApplication leaks).handle control.execution.application message =
      some next := by
  have permitted := (countPermits_eq_true_iff _ _).mp (clean.2 message authentic)
  have correct := permitted.2.1
  rw [CountCallCorrect, opening] at correct
  obtain ⟨certified, resolves⟩ := correct
  cases node : nodeView graph event with
  | bind | sample => simp only [node] at resolves
  | resolve owner payload binding checks outputEq codeEq =>
      rw [node] at resolves
      obtain ⟨sender, typed, signedBinding⟩ := resolves
      rw [sender] at signedBinding
      have invariant := (runtime.reactiveBindingInvariant leaks).history initial horizon scheduler
        (fun state supported => by
          obtain ⟨inputs, rfl⟩ := initialized state supported
          exact State.initial_bindingInvariant inputs) trace
      have signed := signedCommitments_history runtime leaks initial initialized horizon scheduler
        trace
      have unique := (runtime.reactiveApplication leaks).uniqueIds_history scheduler initial horizon
        control trace
      have available : (control.execution.application.config.store binding.field).isSome = true :=
          by
        apply control.execution.application.config.read_available ready
        rw [← EventCode.readFields_cast outputEq (graph.nodes event), codeEq]
        exact Finset.mem_insert_self _ _
      have associated := accepted_of_signedBinding runtime leaks control.execution signed clean
        unique invariant (initialBindingHandles_history runtime leaks initial initialized horizon
          scheduler trace) message owner payload binding candidate available sender
          (sender ▸ unmissed) signedBinding
      have owned : candidate.1 = owner := by
        obtain ⟨acceptedPayload, kind⟩ := invariant.accepted_typed binding.field candidate
          associated
        exact (EventField.binding.inj (binding.layout_eq.symm.trans kind)).1.symm
      have certificate : message.payload.evidence = some ⟨candidate, raw⟩ := by
        unfold certifiedOpening at certified
        rw [opening] at certified
        cases evidence : message.payload.evidence with
        | none => simp only [evidence, Bool.false_eq_true] at certified
        | some fact =>
            simp only [evidence, decide_eq_true_eq] at certified
            exact congrArg some certified
      have sound := (runtime.packetEvidence leaks).history_sound initial horizon scheduler trace
      have verified := sound.inputs message authentic ⟨candidate, raw⟩ (by
        simp only [packetEvidence, certificate, Option.toList_some, List.mem_singleton])
      change control.execution.application.candidates.lookup candidate = .openable raw at verified
      rcases raw with ⟨rawType, value⟩
      change rawType = payload at typed
      subst rawType
      have stored := invariant.opening_stored binding candidate value associated verified
      have defined := EventCode.resolveOutput?_isSome binding checks true
        control.execution.application.config.store (by
          intro field read
          apply control.execution.application.config.read_available ready
          rw [← EventCode.readFields_cast outputEq (graph.nodes event), codeEq]
          exact read)
      obtain ⟨result, resolved⟩ := Option.isSome_iff_exists.mp defined
      rw [reactiveApplication_handle_of_tokenValid runtime leaks _ _ permitted.1, opening]
      exact ⟨_, runtime.handle_opening_eq control.execution.application message.id event candidate
        owner payload binding checks outputEq codeEq node ready timely sender owned associated value
        verified stored result resolved⟩

end Vegas.EventGraphRuntime
