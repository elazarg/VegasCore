/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSignedBindings
import Vegas.Pending.PhaseCountMenu
import Vegas.Pending.PhaseBindingInvariant

/-! # Physical acceptance of count-admitted phased bindings

Freshness is global across archived attempts. A current, ready and timely
binding is accepted before phase closure, including an unusable hidden value.
The exact normalized image is retained because closure may immediately void it.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem commitment_eq_of_handle
    (traffic : List (Message Player (CommitAttemptPacket graph)))
    (first second : Message Player (CommitAttemptPacket graph))
    (firstAllowed : Permits traffic first) (secondAllowed : Permits traffic second)
    (firstInput : first ∈ traffic) (secondInput : second ∈ traffic)
    (identified : ∀ left ∈ traffic, ∀ right ∈ traffic, left.id = right.id → left = right)
    {firstEvent secondEvent : graph.EventId} {candidate : Handle graph}
    (firstCall : first.payload.packet.call = .commitment firstEvent candidate)
    (secondCall : second.payload.packet.call = .commitment secondEvent candidate) :
    first = second := by
  have firstCorrect := firstAllowed.2.1
  have secondCorrect := secondAllowed.2.1
  unfold CountCallCorrect at firstCorrect secondCorrect
  dsimp only [nativeMessage] at firstCorrect secondCorrect
  rw [firstCall] at firstCorrect
  rw [secondCall] at secondCorrect
  obtain ⟨_, _, firstOwner, _, firstUnused⟩ := firstCorrect
  obtain ⟨_, _, secondOwner, _, secondUnused⟩ := secondCorrect
  have sender : first.sender = second.sender := firstOwner.symm.trans secondOwner
  rcases lt_trichotomy first.id.2 second.id.2 with earlier | same | later
  · exact (secondUnused (nativeMessage first)
      ((earlier_native traffic second _).mpr ⟨first, ⟨firstInput, sender, earlier⟩, rfl⟩)
      firstEvent firstCall).elim
  · exact identified first firstInput second secondInput (Prod.ext sender same)
  · exact (firstUnused (nativeMessage second)
      ((earlier_native traffic first _).mpr ⟨second, ⟨secondInput, sender.symm, later⟩, rfl⟩)
      secondEvent secondCall).elim

/-- A permitted prepared handle is absent from every current association,
including associations restored from earlier phase checkpoints. -/
theorem binding_handle_unused (execution : (app).Execution)
    (recalled : execution.InputRecall app) (principal : Player)
    (clean : ∀ message ∈ execution.network.inputs, message.sender = principal →
      permits execution.network.inputs message = true)
    (signed : PhaseRuntimeState.SignedBindings runtime leaks execution)
    (unique : execution.network.UniqueIds)
    (association : execution.application.current.native.AssociationInvariant)
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ execution.network.inputs) (authored : message.sender = principal)
    (event : graph.EventId)
    (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (ready : execution.application.current.native.config.cut.Ready event) :
    execution.application.current.native.HandleUnused candidate := by
  have allowed := (permits_eq_true_iff _ _).mp (clean message member authored)
  have correct := allowed.2.1
  unfold CountCallCorrect at correct
  dsimp only [nativeMessage] at correct
  rw [call] at correct
  obtain ⟨_, _, candidateOwner, ⟨serial, prepared⟩, _⟩ := correct
  intro field accepted
  cases field with
  | inl input =>
      have initial := signed.2.1.1 input candidate accepted
      rw [prepared] at initial
      cases initial
  | inr other =>
      obtain ⟨previous, output, previousSender, previousCall⟩ :=
        signed.2.1.2 other candidate accepted
      have previousInput : previous ∈ execution.network.inputs := by
        change previous ∈ (app).outputs (execution.recall candidate.1) at output
        rw [← recalled candidate.1] at output
        exact (List.mem_filter.mp output).1
      have previousOwner : previous.sender = principal :=
        previousSender.trans (candidateOwner.trans authored)
      have previousAllowed := (permits_eq_true_iff _ _).mp
        (clean previous previousInput previousOwner)
      have same := commitment_eq_of_handle execution.network.inputs message previous allowed
        previousAllowed member previousInput (fun left leftInput right rightInput identified =>
          (unique.inputs right rightInput).inputs left leftInput identified) call previousCall
      have eventEq : event = other := by
        rw [← same, call] at previousCall
        exact (Payload.commitment.inj previousCall).1
      subst other
      exact ready.1 (association.accepted_complete event candidate accepted)

/-- The application accepts a genuine permitted current binding. Completion is
asserted at the raw native edge; the returned state is its exact phase settle,
which may retire that edge when another owner omitted a co-phase binding. -/
theorem binding_accepted (execution : (app).Execution)
    (recalled : execution.InputRecall app) (principal : Player)
    (clean : ∀ message ∈ execution.network.inputs, message.sender = principal →
      permits execution.network.inputs message = true)
    (signed : PhaseRuntimeState.SignedBindings runtime leaks execution)
    (unique : execution.network.UniqueIds)
    (association : execution.application.current.native.AssociationInvariant)
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ execution.network.inputs) (authored : message.sender = principal)
    (event : graph.EventId)
    (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (request : execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, event⟩)
    (timely : execution.application.current.native.WithinDeadline runtime event) :
    ∃ native next,
      handle runtime execution.application.current.native
        ⟨message.id, message.payload.packet.call⟩ = some native ∧
      event ∈ native.config.cut.completed ∧
      native.accepted (.inr event) = some candidate ∧
      next = ({execution.application with current :=
        execution.application.current.inclusionResult message.payload.packet.call native} :
          PhaseRuntimeState graph).normalize ∧
      (app).handle execution.application message = some next := by
  have allowed := (permits_eq_true_iff _ _).mp (clean message member authored)
  have correct := allowed.2.1
  unfold CountCallCorrect at correct
  dsimp only [nativeMessage] at correct
  rw [call] at correct
  obtain ⟨owned, _, candidateOwner, _, _⟩ := correct
  have ready := request.2.2.1
  have unused := binding_handle_unused runtime leaks execution recalled principal clean signed
    unique association message member authored event candidate call ready
  have vacant : execution.application.current.native.accepted (.inr event) = none := by
    cases accepted : execution.application.current.native.accepted (.inr event) with
    | none => rfl
    | some candidate =>
        exact (ready.1 (association.accepted_complete event candidate accepted)).elim
  cases node : nodeView graph event with
  | sample payload law outputEq codeEq =>
      simp only [bindingOwnedBy, outputEq] at owned
      cases owned
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [bindingOwnedBy, outputEq] at owned
      cases owned
  | bind owner payload outputEq codeEq =>
      have sender : message.sender = owner := by
        exact (by simpa only [bindingOwnedBy, outputEq, decide_eq_true_eq, Message.sender]
          using owned :
          owner = message.sender).symm
      have raw := handle_commitment_eq runtime execution.application.current.native message.id
        event candidate owner payload outputEq codeEq node ready timely sender
        (candidateOwner.trans sender) vacant unused
      obtain ⟨native, accepted⟩ : ∃ native, handle runtime execution.application.current.native
          ⟨message.id, message.payload.packet.call⟩ = some native := by
        rw [call]
        exact ⟨_, raw⟩
      obtain ⟨named, addressed, _, completed⟩ := handle_completes runtime _ native _ accepted
      have same : named = event := by
        exact Option.some.inj (addressed.symm.trans (by
          simp only [call, Payload.event?]))
      have stored := (handle_commitment_tables runtime execution.application.current.native native
        message.id event candidate (by simpa only [call] using accepted)).2.1
      have installed : native.accepted (.inr event) = some candidate := by
        rw [stored, Function.update_self]
      let next := ({execution.application with current :=
        execution.application.current.inclusionResult message.payload.packet.call native} :
          PhaseRuntimeState graph).normalize
      refine ⟨native, next, accepted, ?_, installed, rfl, ?_⟩
      · rwa [same] at completed
      · change execution.application.handle runtime message = some next
        have validToken : message.payload.tokenValid execution.application.attempt = true := by
          have current : message.payload.attempt = execution.application.attempt := request.1
          change (decide (message.payload.attempt = execution.application.attempt) &&
            message.payload.packet.tokenValid) = true
          exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true_eq.mpr current, allowed.1⟩
        have validEvent : execution.application.allows message.payload.packet.call = true := by
          obtain ⟨phase, member, inside⟩ := request.2.1
          have head : execution.application.phases.head? = some phase := member
          simp only [PhaseRuntimeState.allows, head, call, Payload.event?, decide_eq_true_eq]
          exact inside
        have active : execution.application.current.excludedCall
            message.payload.packet.call = false := by
          rw [call]
          change (graph.actor? event).any
            (fun owner => decide (owner ∈ execution.application.current.excluded)) = false
          have acting : graph.actor? event = some message.sender := request.2.2.2.1
          rw [acting, Option.any_some]
          exact decide_eq_false (request.2.2.2.2 :
            message.sender ∉ execution.application.current.excluded)
        simp only [PhaseRuntimeState.handle, validToken, validEvent, active, Bool.not_false,
          Bool.and_self, ↓reduceIte, accepted, Option.map_some, next]

end Vegas.EventGraphRuntime.PhaseCount
