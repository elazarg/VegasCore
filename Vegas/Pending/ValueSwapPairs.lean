/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventValueSwap

/-! # Hidden swaps from pairs of values

A family of pairs of values, one optional pair per hidden field, defines a
value swap: the transposition of the pair at each field that has one, and the
transposition of the corresponding results at a binding event's action
(`Vegas.EventGraph.ValueSwap.ofPairs`). Public fields carry no pair, and a pair
at a binding never involves a failure. With one optional pair of prepared values
per handle it defines a hidden swap (`Vegas.EventGraphRuntime.HiddenSwap.ofPairs`).

A handle whose pair is the two typed values of an event's pair is compatible
with the swap at that event; so is a handle without a pair at an event without
one (`Vegas.EventGraphRuntime.HiddenSwap.bindCompatible_ofPairs`,
`Vegas.EventGraphRuntime.HiddenSwap.bindCompatible_ofPairs_none`).
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} {L : IExpr} [R : IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

open EventGraphRuntime

open Classical in
/-- The transposition of an optional pair; the identity without one. -/
def pairSwap {α : Type*} : Option (α × α) → α → α
  | none => id
  | some (left, right) => Equiv.swap left right

theorem pairSwap_involutive {α : Type*} (pair : Option (α × α)) :
    Function.Involutive (pairSwap pair) := by
  classical
  cases pair with
  | none => exact fun _ => rfl
  | some pair => exact fun value => Equiv.swap_apply_self _ _ _

theorem pairSwap_of_ne {α : Type*} (left right value : α) (leftNe : value ≠ left)
    (rightNe : value ≠ right) : pairSwap (some (left, right)) value = value := by
  classical
  exact Equiv.swap_apply_of_ne_of_ne leftNe rightNe

/-- A transposition commutes with an injective map. -/
theorem pairSwap_map {α β : Type*} (map : α → β) (injective : Function.Injective map)
    (left right value : α) :
    pairSwap (some (map left, map right)) (map value) =
      map (pairSwap (some (left, right)) value) := by
  classical
  by_cases isLeft : value = left
  · subst isLeft
    simp [pairSwap, Equiv.swap_apply_left]
  · by_cases isRight : value = right
    · subst isRight
      simp [pairSwap, Equiv.swap_apply_right]
    · rw [pairSwap_of_ne _ _ _ isLeft isRight,
        pairSwap_of_ne _ _ _ (injective.ne isLeft) (injective.ne isRight)]

variable (graph) in
/-- Pairs of values at hidden fields: none at a public field, and no failure at
a binding event. -/
structure SwapPairs where
  /-- The optional pair at each field. -/
  pair : (field : graph.Field) → Option ((graph.layout field).Value × (graph.layout field).Value)
  public_none : ∀ field, graph.fieldPublic field → pair field = none
  binding_success : ∀ event owner payload (outputEq : graph.outputLayout event =
      .binding owner payload) left right, pair (.inr event) = some (left, right) →
    left ≠ cast (congrArg EventField.Value outputEq.symm) .failure ∧
      right ≠ cast (congrArg EventField.Value outputEq.symm) .failure

namespace SwapPairs

variable (pairs : graph.SwapPairs)

/-- The swap of an event's action: at a binding event, the swap of its result. -/
def action (event : graph.EventId) : graph.Action event → graph.Action event :=
  match nodeView graph event with
  | .bind _ _ outputEq _ => fun original =>
      cast (congrArg EventField.Action outputEq.symm)
        (cast (congrArg EventField.Value outputEq)
          (pairSwap (pairs.pair (.inr event)) (cast (congrArg EventField.Value outputEq.symm)
            (cast (congrArg EventField.Action outputEq) original))))
  | .resolve .. | .sample .. => id

theorem action_binding (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (result : PublicationResult (L.Val payload)) :
    pairs.action event (cast (congrArg EventField.Action outputEq.symm) result) =
      cast (congrArg EventField.Action outputEq.symm)
        (cast (congrArg EventField.Value outputEq)
          (pairSwap (pairs.pair (.inr event))
            (cast (congrArg EventField.Value outputEq.symm) result))) := by
  unfold action
  cases view : nodeView graph event with
  | bind otherOwner otherPayload otherEq codeEq =>
      obtain ⟨rfl, rfl⟩ := EventField.binding.inj (otherEq.symm.trans outputEq)
      simp
  | resolve _ _ _ _ otherEq _ => cases otherEq.symm.trans outputEq
  | sample _ _ otherEq _ => cases otherEq.symm.trans outputEq

theorem action_involutive (event : graph.EventId) :
    Function.Involutive (pairs.action event) := by
  intro original
  unfold action
  cases nodeView graph event with
  | bind owner payload outputEq codeEq =>
      simp only [cast_cast, cast_eq]
      rw [pairSwap_involutive]
      simp
  | resolve | sample => rfl

theorem action_publication (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .publication payload) : pairs.action event = id := by
  unfold action
  cases view : nodeView graph event with
  | bind _ _ otherEq _ => cases otherEq.symm.trans outputEq
  | resolve | sample => rfl

end SwapPairs

/-- **The value swap of pairs.** -/
def ValueSwap.ofPairs (pairs : graph.SwapPairs) : graph.ValueSwap where
  value field := pairSwap (pairs.pair field)
  action := pairs.action
  value_involutive field := pairSwap_involutive _
  action_involutive := pairs.action_involutive
  value_public field isPublic := by rw [pairs.public_none field isPublic]; rfl
  action_publication := pairs.action_publication
  action_binding event owner payload outputEq result := pairs.action_binding event owner payload
    outputEq result

/-- **Value swaps of pairs keep failures at binding events**: pairs never pair a
failure there. -/
theorem ValueSwap.ofPairs_expiryFixed (pairs : graph.SwapPairs) (event : graph.EventId) :
    (ValueSwap.ofPairs pairs).ExpiryFixed event := by
  intro owner payload outputEq
  change pairSwap (pairs.pair (.inr event)) _ = _
  cases paired : pairs.pair (.inr event) with
  | none => rfl
  | some pair =>
      obtain ⟨left, right⟩ := pair
      obtain ⟨leftNe, rightNe⟩ := pairs.binding_success event owner payload outputEq left right
        paired
      exact pairSwap_of_ne left right _ (Ne.symm leftNe) (Ne.symm rightNe)

end Vegas.EventGraph

namespace Vegas.EventGraphRuntime

open Interaction Vegas.EventGraph

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- **The hidden swap of pairs**: of field values and of the values prepared at
handles. -/
def HiddenSwap.ofPairs (pairs : graph.SwapPairs)
    (handlePairs : Handle graph → Option (Raw L × Raw L)) : HiddenSwap graph where
  values := ValueSwap.ofPairs pairs
  raw handle := pairSwap (handlePairs handle)
  raw_involutive _ := pairSwap_involutive _

/-- A handle without a pair is compatible at an event without a pair. -/
theorem HiddenSwap.bindCompatible_ofPairs_none (pairs : graph.SwapPairs)
    (handlePairs : Handle graph → Option (Raw L × Raw L)) {event : graph.EventId}
    {handle : Handle graph} (eventNone : pairs.pair (.inr event) = none)
    (handleNone : handlePairs handle = none) :
    BindCompatible (HiddenSwap.ofPairs pairs handlePairs) event handle := by
  intro owner payload outputEq candidate
  change pairSwap (pairs.pair (.inr event)) _ = cast _ (candidateResult
    (swapCandidate (pairSwap (handlePairs handle)) candidate) payload)
  rw [eventNone, handleNone]
  cases candidate <;> rfl

/-- **A handle paired with the typed values of its event's pair is compatible.** -/
theorem HiddenSwap.bindCompatible_ofPairs (pairs : graph.SwapPairs)
    (handlePairs : Handle graph → Option (Raw L × Raw L)) {event : graph.EventId}
    {handle : Handle graph} {owner : Player} {payload : L.Ty}
    (outputEq : graph.outputLayout event = .binding owner payload) (left right : L.Val payload)
    (eventPair : pairs.pair (.inr event) =
      some (cast (congrArg EventField.Value outputEq.symm) (PublicationResult.success left),
        cast (congrArg EventField.Value outputEq.symm) (PublicationResult.success right)))
    (handlePair : handlePairs handle = some (⟨payload, left⟩, ⟨payload, right⟩)) :
    BindCompatible (HiddenSwap.ofPairs pairs handlePairs) event handle := by
  classical
  intro otherOwner otherPayload otherEq candidate
  obtain ⟨ownerEq, payloadEq⟩ := EventField.binding.inj (outputEq.symm.trans otherEq)
  subst ownerEq payloadEq
  change pairSwap (pairs.pair (.inr event)) _ = cast _ (candidateResult
    (swapCandidate (pairSwap (handlePairs handle)) candidate) payload)
  rw [eventPair, handlePair]
  have castInj : Function.Injective
      (cast (congrArg EventField.Value otherEq.symm) :
        PublicationResult (L.Val payload) → (graph.outputLayout event).Value) :=
    fun _ _ same => (cast_inj _).mp same
  have typed : ∀ result : PublicationResult (L.Val payload),
      pairSwap (some (cast (congrArg EventField.Value outputEq.symm)
          (PublicationResult.success left),
        cast (congrArg EventField.Value outputEq.symm) (PublicationResult.success right)))
          (cast (congrArg EventField.Value otherEq.symm) result) =
        cast (congrArg EventField.Value otherEq.symm)
          (pairSwap (some (PublicationResult.success left, PublicationResult.success right))
            result) :=
    fun result => pairSwap_map _ castInj _ _ result
  rw [typed]
  congr 1
  cases candidate with
  | fresh | unopenable =>
      simp only [candidateResult, swapCandidate_fresh, swapCandidate_unopenable]
      exact pairSwap_of_ne _ _ _ (by simp) (by simp)
  | openable raw =>
      simp only [swapCandidate_openable, candidateResult]
      by_cases isLeft : raw = ⟨payload, left⟩
      · subst isLeft
        simp [pairSwap, Equiv.swap_apply_left]
      · by_cases isRight : raw = ⟨payload, right⟩
        · subst isRight
          simp [pairSwap, Equiv.swap_apply_right]
        · rw [pairSwap_of_ne _ _ raw isLeft isRight]
          cases typedRaw : raw.as? payload with
          | none =>
              simp only [Option.elim_none]
              exact pairSwap_of_ne _ _ _ (by simp) (by simp)
          | some value =>
              simp only [Option.elim_some]
              have rawEq : raw = ⟨payload, value⟩ := by
                rcases raw with ⟨rawType, rawValue⟩
                unfold Raw.as? at typedRaw
                split at typedRaw
                · rename_i same
                  subst same
                  simp only [Option.some.injEq] at typedRaw
                  subst typedRaw
                  rfl
                · cases typedRaw
              subst rawEq
              apply pairSwap_of_ne
              · intro same
                exact isLeft (by cases same; rfl)
              · intro same
                exact isRight (by cases same; rfl)

/-- **Swaps of pairs keep every expiry**, so they meet the expiry clause of the
swap guard at every state. -/
theorem HiddenSwap.expired_ofPairs (pairs : graph.SwapPairs)
    (handlePairs : Handle graph → Option (Raw L × Raw L)) (current : State graph) :
    ∀ event, ¬ (HiddenSwap.ofPairs pairs handlePairs).values.ExpiryFixed event →
      event ∈ current.config.cut.completed → current.accepted (.inr event) ≠ none :=
  fun event notFixed => absurd (ValueSwap.ofPairs_expiryFixed pairs event) notFixed

end Vegas.EventGraphRuntime
