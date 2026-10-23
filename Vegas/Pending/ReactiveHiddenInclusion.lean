/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveHiddenResponse
import Vegas.Pending.EventPublicState

/-! # Inclusion steps that preserve a private binding repair

Opaque commitment inclusion and withholding preserve the whole opponent frame.
Opening inclusion needs the additional owner-local validity facts: an arbitrary
attempt to open a repaired unusable handle is not an equivalent transition.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private theorem include_hidden_congr
    (left right : (runtime.reactiveApplication leaks).Execution) (hidden : Player)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (views : ∀ who, who ≠ hidden →
      left.application.playerView who = right.application.playerView who)
    (recall : ∀ who, who ≠ hidden → left.recall who = right.recall who)
    (id : MessageId Player) (packet : WitnessedPacket graph)
    (found : left.network.lookup id = some ⟨id, packet⟩)
    (decision : (handle runtime left.application ⟨id, packet.call⟩).isSome =
      (handle runtime right.application ⟨id, packet.call⟩).isSome)
    (handled : ∀ who, who ≠ hidden →
      (handle runtime left.application ⟨id, packet.call⟩).map (fun next => next.playerView who) =
        (handle runtime right.application ⟨id, packet.call⟩).map
          (fun next => next.playerView who)) :
    let first := left.includePending (runtime.reactiveApplication leaks) id
    let second := right.includePending (runtime.reactiveApplication leaks) id
    first.network = second.network ∧ first.receipts = second.receipts ∧
      (∀ who, who ≠ hidden →
        first.application.playerView who = second.application.playerView who) ∧
      (∀ who, who ≠ hidden → first.recall who = second.recall who) := by
  have rightFound : right.network.lookup id = some ⟨id, packet⟩ := network ▸ found
  dsimp only
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    found, rightFound]
  by_cases valid : packet.tokenValid = true
  swap
  · have rejected (state : State graph) :
        (runtime.reactiveApplication leaks).handle state ⟨id, packet⟩ = none :=
      reactiveApplication_handle_of_not_tokenValid runtime leaks state ⟨id, packet⟩
        (Bool.eq_false_iff.mpr valid)
    simp only [rejected, Option.getD_none, Option.isSome_none]
    exact ⟨by rw [network], by rw [receipts], views, recall⟩
  have handler (state : State graph) :
      (runtime.reactiveApplication leaks).handle state ⟨id, packet⟩ =
        handle runtime state ⟨id, packet.call⟩ :=
    reactiveApplication_handle_of_tokenValid runtime leaks state ⟨id, packet⟩ valid
  simp only [handler]
  refine ⟨by rw [network], by rw [receipts, decision], ?_, recall⟩
  intro who different
  have same := handled who different
  cases first : handle runtime left.application ⟨id, packet.call⟩ <;>
    cases second : handle runtime right.application ⟨id, packet.call⟩ <;>
    simp only [first, second, Option.map_none, Option.map_some, Option.some.injEq,
      Option.getD_none, Option.getD_some] at same ⊢
  · exact views who different
  · cases same
  · cases same
  · exact same

/-- Opaque inclusion preserves all nonowner inputs simultaneously, including
whether the call was accepted. Hidden candidate meanings need not agree. -/
theorem reactive_include_binding_hidden_congr
    (left right : (runtime.reactiveApplication leaks).Execution) (hidden : Player)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (publicEq : left.application.publicView = right.application.publicView)
    (views : ∀ who, who ≠ hidden →
      left.application.playerView who = right.application.playerView who)
    (recall : ∀ who, who ≠ hidden → left.recall who = right.recall who)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (evidence : Option (OpeningFact graph)) {token : Option (ReadinessToken graph)}
    (found : left.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩) :
    let first := left.includePending (runtime.reactiveApplication leaks) id
    let second := right.includePending (runtime.reactiveApplication leaks) id
    first.network = second.network ∧ first.receipts = second.receipts ∧
      (∀ who, who ≠ hidden →
        first.application.playerView who = second.application.playerView who) ∧
      (∀ who, who ≠ hidden → first.recall who = second.recall who) := by
  have decision : (handle runtime left.application ⟨id, .commitment event candidate⟩).isSome =
      (handle runtime right.application ⟨id, .commitment event candidate⟩).isSome := by
    apply Bool.eq_iff_iff.mpr
    rw [← State.publicView_bindingIncludable runtime left.application id event candidate,
      ← State.publicView_bindingIncludable runtime right.application id event candidate, publicEq]
  apply include_hidden_congr runtime leaks left right hidden network receipts
    views recall id ⟨.commitment event candidate, evidence, token⟩ found decision
  intro who different
  exact handle_commitment_playerView_congr runtime left.application right.application who
    id event candidate (views who different)

omit [DecidableEq Player] in
private theorem checks_public_congr {payload : L.Ty}
    (checks : List (GuardCheck graph.layout payload)) (left right : Store graph.layout)
    (publicEq : graph.publicStore left = graph.publicStore right)
    (proposal : PublicationResult (L.Val payload)) :
    GuardCheck.allAccepted? checks left proposal =
      GuardCheck.allAccepted? checks right proposal := by
  induction checks with
  | nil => rfl
  | cons check rest ih =>
      have checked : check.eval? left proposal = check.eval? right proposal := by
        rw [← check.eval?_publicStore left proposal, ← check.eval?_publicStore right proposal,
          publicEq]
      simp only [GuardCheck.allAccepted?, checked, ih]

omit [DecidableEq Player] in
/-- Public service conditions and the checked result transport when the
resolved binding itself has the same successful value. -/
theorem opening_right_facts
    (left right : State graph) (publicEq : left.publicView = right.publicView)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload)) (candidate : Handle graph)
    (ready : left.config.cut.Ready event) (timely : left.WithinDeadline runtime event)
    (associated : left.accepted binding.field = some candidate) (value : L.Val payload)
    (leftStored : binding.get? left.config.store = some (.success value))
    (rightStored : binding.get? right.config.store = some (.success value))
    (result : PublicationResult (L.Val payload))
    (resolved : EventCode.resolveOutput? binding checks true left.config.store = some result) :
    right.config.cut.Ready event ∧ right.WithinDeadline runtime event ∧
      right.accepted binding.field = some candidate ∧
      EventCode.resolveOutput? binding checks true right.config.store = some result := by
  have rightReady : right.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← publicEq, State.publicView_eventReady]
    exact ready
  have clockEq : left.clock = right.clock := congrArg PublicView.clock publicEq
  have activatedEq : left.activatedAt = right.activatedAt :=
    congrArg PublicView.activatedAt publicEq
  have rightTimely : right.WithinDeadline runtime event := by
    unfold State.WithinDeadline at timely ⊢
    rwa [← activatedEq, ← clockEq]
  have acceptedEq : left.accepted = right.accepted := congrArg PublicView.accepted publicEq
  have rightAssociated : right.accepted binding.field = some candidate := by
    rw [← acceptedEq]
    exact associated
  refine ⟨rightReady, rightTimely, rightAssociated, ?_⟩
  have stores : graph.publicStore left.config.store = graph.publicStore right.config.store :=
    congrArg (fun view : PublicView graph => view.observation.store) publicEq
  have same : EventCode.resolveOutput? binding checks true left.config.store =
      EventCode.resolveOutput? binding checks true right.config.store := by
    simp only [EventCode.resolveOutput?, leftStored, rightStored, bind, Option.bind_some,
      ↓reduceIte]
    rw [checks_public_congr checks left.config.store right.config.store stores]
  exact same.symm.trans resolved

end Vegas.EventGraphRuntime
