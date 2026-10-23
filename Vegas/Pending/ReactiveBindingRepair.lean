/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBinding
import Interaction.ReactiveProvenance
import Vegas.Pending.ReactivePolicyFacts
import Vegas.Pending.ReactiveServiceProgress
import Interaction.ReactiveAllocation
import Vegas.Pending.EventSequentialTiming
import Vegas.Pending.ReactiveHiddenInclusion
import Vegas.EventGraph.Commutation

/-! # Allocation and transport during a hidden binding repair

Replacing an unusable binding by a value changes the owner's private catalog.
It does not consume additional candidate identifiers, change the chosen opaque
handle, or change any other player's input. These facts apply after earlier
repairs as well as at initialization.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- The allocator reads freshness, not the meaning of an already fixed handle. -/
theorem reactiveFreshSlot_congr (left right : PlayerView graph)
    (fresh : ∀ serial, left.candidates (.prepared serial) = .fresh ↔
      right.candidates (.prepared serial) = .fresh) :
    reactiveFreshSlot left = reactiveFreshSlot right := by
  classical
  have predicates : (fun serial => left.candidates (.prepared serial) = .fresh) =
      fun serial => right.candidates (.prepared serial) = .fresh :=
    funext fun serial => propext (fresh serial)
  unfold reactiveFreshSlot
  simp only [predicates]

/-- A binding response consumes its selected candidate and no other slot.
The statement is independent of the value or failure chosen for that binding. -/
theorem reactiveBinding_fresh_iff (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial : Nat) (query : CandidateSlot graph) :
    let next := execution.respond (runtime.reactiveApplication leaks) owner
      (runtime.reactiveBinding leaks owner event payload result serial)
    next.application.candidates.lookup (owner, query) = .fresh ↔
      query ≠ .prepared serial ∧
        execution.application.candidates.lookup (owner, query) = .fresh := by
  let material : Submission graph := ⟨.commitment event (owner, .prepared serial),
    match result with | .failure => none | .success value => some ⟨payload, value⟩⟩
  change (submitStep (material.register execution.application owner) owner
    material.packet).candidates.lookup (owner, query) = .fresh ↔ _
  rw [material.candidateAfter_eq]
  by_cases same : query = .prepared serial
  · subst query
    cases fixed : execution.application.candidates.lookup (owner, .prepared serial) <;>
      cases result <;> simp [material, Submission.candidateAfter, fixed]
  · simp [material, Submission.candidateAfter, same]

private theorem binding_other_view (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (owner observer : Player)
    (different : observer ≠ owner) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial : Nat) :
    (execution.respond (runtime.reactiveApplication leaks) owner
      (runtime.reactiveBinding leaks owner event payload result serial)).application.playerView
        observer = execution.application.playerView observer := by
  let material : Submission graph := ⟨.commitment event (owner, .prepared serial),
    match result with | .failure => none | .success value => some ⟨payload, value⟩⟩
  exact (submitStep_playerView_other (material.register execution.application owner)
    owner observer different material.packet).trans
      (material.register_other execution.application owner observer different)

private theorem binding_public_view (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial : Nat) :
    (execution.respond (runtime.reactiveApplication leaks) owner
      (runtime.reactiveBinding leaks owner event payload result serial)).application.publicView =
        execution.application.publicView := by
  change (submitStep (Submission.register _ execution.application owner) owner _).publicView = _
  rw [submitStep_publicView]
  exact (Submission.register_facts _ owner execution.application).2

/-- Paired submissions extend an existing hidden-owner frame. Foreign recall is
retained exactly; the owner's distinct actions and private meanings remain distinct. -/
theorem reactiveBinding_submit_hidden_congr (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (publicEq : left.application.publicView = right.application.publicView)
    (views : ∀ who, who ≠ owner →
      left.application.playerView who = right.application.playerView who)
    (recall : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (event : graph.EventId) (payload : L.Ty)
    (first second : PublicationResult (L.Val payload)) (serial : Nat) :
    let before := left.respond (runtime.reactiveApplication leaks) owner
      (runtime.reactiveBinding leaks owner event payload first serial)
    let after := right.respond (runtime.reactiveApplication leaks) owner
      (runtime.reactiveBinding leaks owner event payload second serial)
    before.network = after.network ∧ before.receipts = after.receipts ∧
      before.application.publicView = after.application.publicView ∧
      (∀ who, who ≠ owner →
        before.application.playerView who = after.application.playerView who) ∧
      (∀ who, who ≠ owner → before.recall who = after.recall who) := by
  refine ⟨?_, receipts, ?_, ?_, ?_⟩
  · simp only [ReactiveApplication.Execution.respond, reactiveBinding,
      reactiveApplication_packet_none, network, publicEq]
  · exact (binding_public_view runtime leaks left owner event payload first serial).trans
      (publicEq.trans
        (binding_public_view runtime leaks right owner event payload second serial).symm)
  · intro who different
    exact (binding_other_view runtime leaks left owner who different
      event payload first serial).trans
      ((views who different).trans
        (binding_other_view runtime leaks right owner who different
          event payload second serial).symm)
  · intro who different
    exact ((runtime.reactiveApplication leaks).respond_recall_other
      left owner who different _).trans
      ((recall who different).trans
        ((runtime.reactiveApplication leaks).respond_recall_other right owner who different _).symm)

/-- Repeated repairs keep the real candidate allocator aligned. This includes
the unavailable-slot case; no assumption supplies an inexhaustible finite menu. -/
theorem reactiveBinding_fresh_slots_congr (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (fresh : ∀ query, left.application.candidates.lookup (owner, query) = .fresh ↔
      right.application.candidates.lookup (owner, query) = .fresh)
    (event : graph.EventId) (payload : L.Ty)
    (first second : PublicationResult (L.Val payload)) (serial : Nat) :
    let before := left.respond (runtime.reactiveApplication leaks) owner
      (runtime.reactiveBinding leaks owner event payload first serial)
    let after := right.respond (runtime.reactiveApplication leaks) owner
      (runtime.reactiveBinding leaks owner event payload second serial)
    ∀ query,
      before.application.candidates.lookup (owner, query) = .fresh ↔
      after.application.candidates.lookup (owner, query) = .fresh := by
  dsimp only
  intro query
  exact (reactiveBinding_fresh_iff runtime leaks left owner event payload first serial query).trans
    ((and_congr Iff.rfl (fresh query)).trans
      (reactiveBinding_fresh_iff runtime leaks right owner event payload second serial query).symm)

/-- Inclusion freezes a submitted candidate again; it cannot consume any new
slot, whether the application accepts or rejects the packet. -/
theorem reactive_include_fixed_binding_candidates (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (evidence : Option (OpeningFact graph)) {token : Option (ReadinessToken graph)}
    (found : execution.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩)
    (fixed : execution.application.candidates.lookup candidate ≠ .fresh) :
    (execution.includePending (runtime.reactiveApplication leaks) id).application.candidates =
      execution.application.candidates := by
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    found]
  cases accepted : (runtime.reactiveApplication leaks).handle execution.application
      ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩ with
  | none => rfl
  | some next =>
      change next.candidates = execution.application.candidates
      rw [(handle_commitment_tables runtime execution.application next id event candidate
        (reactiveHandle_call accepted)).1]
      exact execution.application.candidates.freeze_eq_self_of_not_fresh candidate fixed

omit [DecidableEq Player] in
private theorem complete_binding_public_congr
    (left right : State graph) (publicEq : left.publicView = right.publicView)
    (owner : Player) (payload : L.Ty) (event : graph.EventId)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (leftReady : left.config.cut.Ready event) (rightReady : right.config.cut.Ready event)
    (leftAction rightAction : graph.Action event)
    (leftValue rightValue : (graph.outputLayout event).Value) :
    (left.complete event leftReady leftAction leftValue).publicView =
      (right.complete event rightReady rightAction rightValue).publicView := by
  classical
  have observations := congrArg PublicView.observation publicEq
  have orders := congrArg EventGraph.PublicObservation.completionOrder observations
  have cuts := EventGraph.cut_eq_of_completionOrder_eq left.config right.config orders
  have observed : graph.publicObserve (left.config.complete event leftReady leftAction leftValue) =
      graph.publicObserve (right.config.complete event rightReady rightAction rightValue) := by
    apply EventGraph.PublicObservation.ext graph
    · simpa only [State.publicView, EventGraph.publicObserve, EventGraph.Config.complete,
        List.map_append, List.map_cons, List.map_nil] using
        congrArg (fun order => order ++ [event]) orders
    · apply graph.publicStore_congr
      intro field visible
      have different : field ≠ .inr event := by
        rintro rfl
        change (graph.outputLayout event).IsPublic at visible
        rw [outputEq] at visible
        exact visible
      rw [EventGraph.store_complete, EventGraph.store_complete,
        Function.update_of_ne different, Function.update_of_ne different]
      have prior := congrFun (congrArg EventGraph.PublicObservation.store observations) field
      simpa only [State.publicView, EventGraph.publicObserve, EventGraph.publicStore_of_public,
        visible] using prior
  have clockEq := congrArg PublicView.clock publicEq
  have activatedEq := congrArg PublicView.activatedAt publicEq
  have acceptedEq := congrArg PublicView.accepted publicEq
  have nextActivated :
      State.refreshActivated (left.config.complete event leftReady leftAction leftValue)
          left.clock left.activatedAt =
        State.refreshActivated (right.config.complete event rightReady rightAction rightValue)
          right.clock right.activatedAt := by
    funext query
    simp only [State.refreshActivated, EventGraph.Config.complete_cut, cuts]
    rw [show left.clock = right.clock from clockEq,
      show left.activatedAt = right.activatedAt from activatedEq]
  unfold State.publicView State.complete
  congr 1

/-- Commitment inclusion preserves the public frame without requiring that
another player exists. The private candidate meanings may differ. -/
theorem reactive_include_binding_public_congr (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : (runtime.reactiveApplication leaks).Execution)
    (network : left.network = right.network)
    (publicEq : left.application.publicView = right.application.publicView)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (id : MessageId Player) (candidate : Handle graph) (evidence : Option (OpeningFact graph))
    (sender : id.1 = owner) (owned : candidate.1 = owner)
    (found : left.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, evidence, some ⟨event⟩⟩⟩)
    (ready : left.application.config.cut.Ready event)
    (timely : left.application.WithinDeadline runtime event)
    (vacant : left.application.accepted (.inr event) = none)
    (unused : left.application.HandleUnused candidate) :
    (left.includePending (runtime.reactiveApplication leaks) id).application.publicView =
      (right.includePending (runtime.reactiveApplication leaks) id).application.publicView := by
  have ready' : right.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← publicEq, State.publicView_eventReady]
    exact ready
  have acceptedEq : left.application.accepted = right.application.accepted :=
    congrArg PublicView.accepted publicEq
  have timely' : right.application.WithinDeadline runtime event := by
    unfold State.WithinDeadline at timely ⊢
    rw [← show left.application.clock = right.application.clock from
      congrArg PublicView.clock publicEq,
      ← show left.application.activatedAt = right.application.activatedAt from
        congrArg PublicView.activatedAt publicEq]
    exact timely
  have vacant' : right.application.accepted (.inr event) = none := by
    exact (congrFun acceptedEq (.inr event)).symm.trans vacant
  have unused' : right.application.HandleUnused candidate := by
    intro field associated
    exact unused field ((congrFun acceptedEq field).trans associated)
  have handled := runtime.handle_commitment_eq left.application id event candidate owner payload
    outputEq codeEq node ready timely sender owned vacant unused
  have handled' := runtime.handle_commitment_eq right.application id event candidate owner payload
    outputEq codeEq node ready' timely' sender owned vacant' unused'
  have found' : right.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, evidence, some ⟨event⟩⟩⟩ := network ▸ found
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    found, found', reactiveApplication_handle, WitnessedPacket.tokenValid_commitment,
    ite_true, handled, handled', Option.getD_some]
  have completed := complete_binding_public_congr left.application right.application publicEq
    owner payload event outputEq ready ready'
    (cast (congrArg EventGraph.EventField.Action outputEq.symm)
      (left.application.bindingResult candidate payload))
    (cast (congrArg EventGraph.EventField.Action outputEq.symm)
      (right.application.bindingResult candidate payload))
    (cast (congrArg EventGraph.EventField.Value outputEq.symm)
      (left.application.bindingResult candidate payload))
    (cast (congrArg EventGraph.EventField.Value outputEq.symm)
      (right.application.bindingResult candidate payload))
  have observed := congrArg PublicView.observation completed
  have activated := congrArg PublicView.activatedAt completed
  have clockEq := congrArg PublicView.clock completed
  unfold State.publicView
  congr 1
  exact congrArg (fun accepted : graph.Field → Option (Handle graph) =>
    Function.update accepted (.inr event) (some candidate)) acceptedEq

end Vegas.EventGraphRuntime
