/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactivePolicyFacts
import Vegas.Pending.EventCompletionObservation
import Vegas.Pending.EventPublicState
import Vegas.EventGraph.ObservationStep

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
      obtain ⟨native, handled, after⟩ := reactiveHandle_call accepted
      rw [← after, (native.drain_tables).2.1,
        (handle_commitment_tables runtime execution.application native id event candidate
          handled).1]
      exact execution.application.candidates.freeze_eq_self_of_not_fresh candidate fixed

private theorem complete_binding_public_congr
    (left right : State graph) (publicEq : left.publicView = right.publicView)
    (owner : Player) (payload : L.Ty) (event : graph.EventId)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (leftReady : left.config.cut.Ready event) (rightReady : right.config.cut.Ready event)
    (leftValue rightValue : PublicationResult (L.Val payload)) :
    (left.complete event leftReady
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) (some leftValue))
      (cast (congrArg EventGraph.EventField.Value outputEq.symm) leftValue)).publicView =
    (right.complete event rightReady
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) (some rightValue))
      (cast (congrArg EventGraph.EventField.Value outputEq.symm) rightValue)).publicView := by
  apply State.complete_publicView_congr left right publicEq event leftReady rightReady
  · intro visible
    change (graph.outputLayout event).IsPublic at visible
    rw [outputEq] at visible
    exact visible.elim
  · rw [left.config.completion_bind_some_defaultEvent event owner payload outputEq codeEq,
      right.config.completion_bind_some_defaultEvent event owner payload outputEq codeEq]

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
  have found' : right.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, evidence, some ⟨event⟩⟩⟩ := network ▸ found
  have defaults : left.application.config.defaulted = right.application.config.defaulted :=
    congrArg (fun view : PublicView graph => view.observation.defaulted) publicEq
  by_cases active : id.1 ∉ left.application.config.defaulted
  swap
  · have inactive : id.1 ∈ left.application.config.defaulted := Classical.not_not.mp active
    have inactive' : id.1 ∈ right.application.config.defaulted := defaults ▸ inactive
    have rejected : handle runtime left.application ⟨id, .commitment event candidate⟩ = none := by
      simp only [handle, Message.sender, ite_eq_left inactive]
    have rejected' : handle runtime right.application ⟨id, .commitment event candidate⟩ = none := by
      simp only [handle, Message.sender, ite_eq_left inactive']
    have actual := reactiveHandle_none (runtime := runtime) (leaks := leaks)
      (message := ⟨id, ⟨.commitment event candidate, evidence, some ⟨event⟩⟩⟩) rejected
    have actual' := reactiveHandle_none (runtime := runtime) (leaks := leaks)
      (message := ⟨id, ⟨.commitment event candidate, evidence, some ⟨event⟩⟩⟩) rejected'
    simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, found', actual, actual', Option.getD_none] using publicEq
  have active' : id.1 ∉ right.application.config.defaulted := defaults ▸ active
  have handled := runtime.handle_commitment_eq left.application id event candidate owner payload
    outputEq codeEq node ready timely active sender owned vacant unused
  have handled' := runtime.handle_commitment_eq right.application id event candidate owner payload
    outputEq codeEq node ready' timely' active' sender owned vacant' unused'
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    found, found', reactiveApplication_handle, WitnessedPacket.tokenValid_commitment,
    ite_true, handled, handled', Option.map_some, Option.getD_some]
  apply State.drain_publicView_congr
  have completed := complete_binding_public_congr left.application right.application publicEq
    owner payload event outputEq codeEq ready ready'
    (left.application.bindingResult candidate payload)
    (right.application.bindingResult candidate payload)
  have observed := congrArg PublicView.observation completed
  have activated := congrArg PublicView.activatedAt completed
  have clockEq := congrArg PublicView.clock completed
  unfold State.publicView
  congr 1
  exact congrArg (fun accepted : graph.Field → Option (Handle graph) =>
    Function.update accepted (.inr event) (some candidate)) acceptedEq

end Vegas.EventGraphRuntime
