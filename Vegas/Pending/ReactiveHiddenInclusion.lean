/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveHiddenResponse
import Vegas.Pending.EventHandleObservation
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

/-- Withholding remains coupled even when the hidden owner's remembered
intention and binding meaning differ. Its source-visible result is failure. -/
theorem reactive_include_withhold_hidden_congr
    (left right : (runtime.reactiveApplication leaks).Execution) (hidden : Player)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (publicEq : left.application.publicView = right.application.publicView)
    (views : ∀ who, who ≠ hidden →
      left.application.playerView who = right.application.playerView who)
    (recall : ∀ who, who ≠ hidden → left.recall who = right.recall who)
    (id : MessageId Player) (event : graph.EventId) (evidence : Option (OpeningFact graph))
    {token : Option (ReadinessToken graph)}
    (found : left.network.lookup id = some ⟨id, ⟨.withhold event, evidence, token⟩⟩) :
    let first := left.includePending (runtime.reactiveApplication leaks) id
    let second := right.includePending (runtime.reactiveApplication leaks) id
    first.network = second.network ∧ first.receipts = second.receipts ∧
      (∀ who, who ≠ hidden →
        first.application.playerView who = second.application.playerView who) ∧
      (∀ who, who ≠ hidden → first.recall who = second.recall who) := by
  have ready : left.application.config.cut.Ready event ↔
      right.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← State.publicView_eventReady, publicEq]
  have clockEq : left.application.clock = right.application.clock :=
    congrArg PublicView.clock publicEq
  have activatedEq : left.application.activatedAt = right.application.activatedAt :=
    congrArg PublicView.activatedAt publicEq
  have timely : left.application.WithinDeadline runtime event ↔
      right.application.WithinDeadline runtime event := by
    unfold State.WithinDeadline
    rw [clockEq, activatedEq]
  have decision : (handle runtime left.application ⟨id, .withhold event⟩).isSome =
      (handle runtime right.application ⟨id, .withhold event⟩).isSome := by
    apply Bool.eq_iff_iff.mpr
    rw [handle_withhold_isSome_iff, handle_withhold_isSome_iff, ready, timely]
  apply include_hidden_congr runtime leaks left right hidden network receipts
    views recall id ⟨.withhold event, evidence, token⟩ found decision
  intro who different
  by_cases authored : id.1 = who
  · exact handle_playerView_congr_of_sender runtime left.application right.application who
      ⟨id, .withhold event⟩ (views who different) authored
  · exact handle_withhold_playerView_congr_of_sender_ne runtime left.application right.application
      who id event (views who different) authored

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

/-- An opening of an unchanged, genuinely openable binding is accepted on
both sides with the same checked publication result. Deferred guards may
reject the value; acceptance here does not assert publication success. -/
theorem handle_opening_unrepaired_congr
    (left right : State graph) (focal : Player)
    (views : left.playerView focal = right.playerView focal)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (ready : left.config.cut.Ready event) (timely : left.WithinDeadline runtime event)
    (sender : id.1 = owner) (owned : candidate.1 = owner)
    (associated : left.accepted binding.field = some candidate)
    (value : L.Val payload)
    (leftFixed : left.candidates.lookup candidate = .openable ⟨payload, value⟩)
    (rightFixed : right.candidates.lookup candidate = .openable ⟨payload, value⟩)
    (leftStored : binding.get? left.config.store = some (.success value))
    (rightStored : binding.get? right.config.store = some (.success value))
    (result : PublicationResult (L.Val payload))
    (resolved : EventCode.resolveOutput? binding checks true left.config.store = some result) :
    (handle runtime left ⟨id, .opening event candidate ⟨payload, value⟩⟩).map
        (fun next => next.playerView focal) =
      (handle runtime right ⟨id, .opening event candidate ⟨payload, value⟩⟩).map
        (fun next => next.playerView focal) := by
  have publicEq : left.publicView = right.publicView := congrArg PlayerView.publicView views
  have observed := left.playerView_observation_eq right focal views
  obtain ⟨rightReady, rightTimely, rightAssociated, rightResolved⟩ :=
    opening_right_facts runtime left right publicEq event owner payload binding checks candidate
      ready timely associated value leftStored rightStored result resolved
  rw [handle_opening_eq runtime left id event candidate owner payload binding checks outputEq
      codeEq node ready timely sender owned associated value leftFixed leftStored result resolved,
    handle_opening_eq runtime right id event candidate owner payload binding checks outputEq
      codeEq node rightReady rightTimely sender owned rightAssociated value rightFixed rightStored
      result rightResolved, Option.map_some, Option.map_some]
  apply congrArg some
  exact State.complete_playerView_congr left right focal publicEq observed
    (congrArg PlayerView.remembered views) (congrArg PlayerView.candidates views)
    event ready rightReady _ _ _ _ (fun _ => rfl) (fun _ => rfl)

/-- Including the same valid opening of an unrepaired binding preserves the
joint opponent frame and acceptance receipt. No equality is claimed for an
opening of the binding whose hidden meaning was repaired. -/
theorem reactive_include_opening_hidden_congr
    (left right : (runtime.reactiveApplication leaks).Execution) (hidden : Player)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (publicEq : left.application.publicView = right.application.publicView)
    (views : ∀ who, who ≠ hidden →
      left.application.playerView who = right.application.playerView who)
    (recall : ∀ who, who ≠ hidden → left.recall who = right.recall who)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (ready : left.application.config.cut.Ready event)
    (timely : left.application.WithinDeadline runtime event)
    (sender : id.1 = owner) (owned : candidate.1 = owner)
    (associated : left.application.accepted binding.field = some candidate)
    (value : L.Val payload)
    (leftFixed : left.application.candidates.lookup candidate = .openable ⟨payload, value⟩)
    (rightFixed : right.application.candidates.lookup candidate = .openable ⟨payload, value⟩)
    (leftStored : binding.get? left.application.config.store = some (.success value))
    (rightStored : binding.get? right.application.config.store = some (.success value))
    (result : PublicationResult (L.Val payload))
    (resolved : EventCode.resolveOutput? binding checks true left.application.config.store =
      some result)
    (evidence : Option (OpeningFact graph)) {token : Option (ReadinessToken graph)}
    (found : left.network.lookup id =
      some ⟨id, ⟨.opening event candidate ⟨payload, value⟩, evidence, token⟩⟩) :
    let first := left.includePending (runtime.reactiveApplication leaks) id
    let second := right.includePending (runtime.reactiveApplication leaks) id
    first.network = second.network ∧ first.receipts = second.receipts ∧
      (∀ who, who ≠ hidden →
        first.application.playerView who = second.application.playerView who) ∧
      (∀ who, who ≠ hidden → first.recall who = second.recall who) := by
  obtain ⟨rightReady, rightTimely, rightAssociated, rightResolved⟩ :=
    opening_right_facts runtime left.application right.application publicEq event owner payload
      binding checks candidate ready timely associated value leftStored rightStored result resolved
  have decision :
      (handle runtime left.application ⟨id, .opening event candidate ⟨payload, value⟩⟩).isSome =
        (handle runtime right.application
          ⟨id, .opening event candidate ⟨payload, value⟩⟩).isSome := by
    rw [handle_opening_eq runtime left.application id event candidate owner payload binding checks
        outputEq codeEq node ready timely sender owned associated value leftFixed leftStored result
        resolved,
      handle_opening_eq runtime right.application id event candidate owner payload binding checks
        outputEq codeEq node rightReady rightTimely sender owned rightAssociated value rightFixed
        rightStored result rightResolved]
    rfl
  apply include_hidden_congr runtime leaks left right hidden network receipts
    views recall id ⟨.opening event candidate ⟨payload, value⟩, evidence, token⟩ found decision
  intro who different
  exact handle_opening_unrepaired_congr runtime left.application right.application who
    (views who different) id event candidate owner payload binding checks outputEq codeEq node
    ready timely sender owned associated value leftFixed rightFixed leftStored rightStored result
    resolved

end Vegas.EventGraphRuntime
