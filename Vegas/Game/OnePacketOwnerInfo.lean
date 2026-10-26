/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketOwnerSwap

/-! # The owner swap between two settled states

Take two application states of the supplied runtime and the owner swap between
the views `who` has of them (`Vegas.ownerSwap`). Call a state *settled* for
`who` (`Vegas.OwnerSettled`) when no field private to `who` stores a failure,
every completed binding stores the value its action binds, every completed
reveal of `who` disclosed, and the prepared handles of `who` are fresh exactly
when unnamed and openable when named, while its initial handles carry its
initial inputs.

Fix two settled states naming the same slots, and an earlier state below each
(`Vegas.OwnerEarlier`: stored values and completions persist, a meaning once
fixed stays, and the same slots were named) with equal public views. Then the
owner swap sends the view of `who` at the first earlier state to its view at the
second (`Vegas.EventGraphRuntime.PlayerView.swap_ownerSwap_of_settled`): public
data is fixed, a private field holds, wherever present, its final value, which
the swap transposes, an own completion carries its stored value or its
disclosure, and a fixed meaning is either fresh at both or the final, transposed
meaning.

A recalled response whose emitted envelope, evidence request and preparation
are recorded (`Vegas.RecordedResponse`) is sent to the response recorded at the
second state with the same envelope (`Vegas.EventGraphRuntime.HiddenSwap.action_ownerSwap`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}

section Candidates

/-- Two meanings of one handle are aligned when both are fresh, both are
unopenable, or both are openable. -/
def CandidatesAligned : CommitmentCandidate (Raw L) → CommitmentCandidate (Raw L) → Prop
  | .fresh, .fresh | .unopenable, .unopenable | .openable _, .openable _ => True
  | _, _ => False

variable (who : Player)

/-- The owner swap sends an aligned meaning at a handle of `who` in the first
view to the meaning in the second. -/
theorem swapCandidate_ownerSwap (first second : PlayerView (graph setup))
    (slot : CandidateSlot (graph setup))
    (aligned : CandidatesAligned (first.candidates slot) (second.candidates slot)) :
    swapCandidate ((ownerSwap who first second).raw (who, slot)) (first.candidates slot) =
      second.candidates slot := by
  change swapCandidate (EventGraph.pairSwap (ownerHandlePairs who first second (who, slot))) _ = _
  unfold ownerHandlePairs
  simp only [↓reduceIte]
  generalize first.candidates slot = left at aligned ⊢
  generalize second.candidates slot = right at aligned ⊢
  cases left <;> cases right <;> simp only [CandidatesAligned] at aligned
  · rfl
  · rename_i left right
    by_cases same : left = right
    · subst same
      simp only [↓reduceIte, swapCandidate_openable]
      rfl
    · simp only [same, ↓reduceIte, swapCandidate_openable]
      simp [EventGraph.pairSwap, Equiv.swap_apply_left]
  · rfl

omit [IExpr.ResultTypes L] in
/-- Meanings of the initial handle of `who` for two values of one input field
are aligned when neither value is a failure of a field private to `who`. -/
theorem candidatesAligned_candidateOfValue (kind : EventGraph.EventField Player L)
    (left right : kind.Value)
    (leftOk : kind.VisibleTo who → ¬ kind.IsPublic → ¬ kind.IsFailure left)
    (rightOk : kind.VisibleTo who → ¬ kind.IsPublic → ¬ kind.IsFailure right) :
    CandidatesAligned (State.candidateOfValue who kind left)
      (State.candidateOfValue who kind right) := by
  cases kind with
  | publicData | publication | privateInput => trivial
  | binding owner payload =>
      by_cases same : owner = who
      · subst same
        have leftNe : left ≠ .failure := leftOk rfl id
        have rightNe : right ≠ .failure := rightOk rfl id
        cases left with
        | failure => exact (leftNe rfl).elim
        | success leftValue =>
            cases right with
            | failure => exact (rightNe rfl).elim
            | success rightValue =>
                simp only [State.candidateOfValue, ↓reduceIte]
                trivial
      · simp only [State.candidateOfValue, same, ↓reduceIte]
        trivial

end Candidates

section Values

variable (who : Player)

/-- **The owner swap transposes the two values of a private field** when
neither is a failure. -/
theorem value_ownerSwap (first second : PlayerView (graph setup))
    {field : (graph setup).Field} (privateTo : PrivateTo who field)
    {left right : ((graph setup).layout field).Value}
    (firstStore : first.observation.store field = some left)
    (secondStore : second.observation.store field = some right)
    (leftOk : ¬ ((graph setup).layout field).IsFailure left)
    (rightOk : ¬ ((graph setup).layout field).IsFailure right) :
    (ownerSwap who first second).values.value field left = right := by
  classical
  change EventGraph.pairSwap (ownerValuePair who first second field) left = right
  unfold ownerValuePair
  simp only [privateTo, ↓reduceIte, firstStore, secondStore]
  by_cases same : left = right
  · subst same
    simp only [true_or, ↓reduceIte]
    rfl
  · simp only [same, leftOk, rightOk, or_self, ↓reduceIte]
    exact Equiv.swap_apply_left left right

end Values

section Settled

variable (who : Player)

/-- The prepared slots of `who` named by commitments among some packets. -/
def NamedSlot (packets : List (Message Player (WitnessedPacket (graph setup))))
    (serial : Nat) : Prop :=
  ∃ message ∈ packets, ∃ event,
    message.payload.call = .commitment event (who, .prepared serial)

/-- **A settled state of `who`.** No field private to `who` stores a failure,
every completed binding stores the value its action binds, every completed
reveal of `who` disclosed, a prepared handle of `who` is fresh exactly when its
slot is unnamed and openable when named, and an initial handle of `who` carries
its input. -/
structure OwnerSettled (named : Nat → Prop) (state : EventGraphRuntime.State (graph setup)) :
    Prop where
  noFailure : ∀ field, PrivateTo who field → ∀ value, state.config.store field = some value →
    ¬ ((graph setup).layout field).IsFailure value
  bindAction : ∀ completion ∈ state.config.history, ∀ owner payload
    (outputEq : (graph setup).outputLayout completion.event = .binding owner payload),
    cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes completion.event) = .bind owner payload →
      state.config.outputs completion.event = some (cast (congrArg EventGraph.EventField.Value
        outputEq.symm) (cast (congrArg EventGraph.EventField.Action outputEq) completion.action))
  disclosed : ∀ completion ∈ state.config.history,
    (graph setup).actor? completion.event = some who → ∀ payload
    (outputEq : (graph setup).outputLayout completion.event = .publication payload),
      cast (congrArg EventGraph.EventField.Action outputEq) completion.action = true
  fresh : ∀ serial, state.candidates.lookup (who, .prepared serial) = .fresh ↔ ¬ named serial
  openable : ∀ serial, named serial →
    ∃ raw, state.candidates.lookup (who, .prepared serial) = .openable raw
  initial : ∀ input, state.candidates.lookup (who, .initial input) =
    State.candidateOfValue who ((graph setup).inputLayout input) (state.config.inputs input)

/-- **A state earlier than another for `who`.** Its stored values and
completions persist, a fixed meaning of `who` stays, its prepared handles are
fresh exactly when unnamed, and its initial handles carry its inputs. -/
structure OwnerEarlier (named : Nat → Prop) (before after : EventGraphRuntime.State (graph setup)) :
    Prop where
  store : ∀ field value, before.config.store field = some value →
    after.config.store field = some value
  history : before.config.history <+: after.config.history
  fixed : ∀ slot, before.candidates.lookup (who, slot) ≠ .fresh →
    after.candidates.lookup (who, slot) = before.candidates.lookup (who, slot)
  fresh : ∀ serial, before.candidates.lookup (who, .prepared serial) = .fresh ↔ ¬ named serial
  initial : ∀ input, before.candidates.lookup (who, .initial input) =
    State.candidateOfValue who ((graph setup).inputLayout input) (before.config.inputs input)

/-- A settled state is earlier than itself. -/
theorem OwnerSettled.earlier {named : Nat → Prop} {state : EventGraphRuntime.State (graph setup)}
    (settled : OwnerSettled who named state) : OwnerEarlier who named state state where
  store _ _ stored := stored
  history := List.prefix_refl _
  fixed _ _ := rfl
  fresh := settled.fresh
  initial := settled.initial

end Settled

section Views

variable (who : Player)

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- A filter by a test of the key, mapped by a map that sends each tested entry
of one list to the entry of the other with the same key, is the filter of the
other. -/
private theorem map_filter_of_keys {α β : Type} (map : α → α) (test : α → Bool)
    (key : α → β) (testKey : ∀ left right, key left = key right → test left = test right) :
    ∀ (left right : List α), left.map key = right.map key →
      (∀ x ∈ left, ∀ y ∈ right, key x = key y → test x = true → map x = y) →
      (left.filter test).map map = right.filter test
  | [], [], _, _ => rfl
  | [], _ :: _, keys, _ => by cases keys
  | _ :: _, [], keys, _ => by cases keys
  | x :: xs, y :: ys, keys, pointwise => by
      simp only [List.map_cons, List.cons.injEq] at keys
      have rest := map_filter_of_keys map test key testKey xs ys keys.2
        (fun a member b other => pointwise a (List.mem_cons_of_mem _ member) b
          (List.mem_cons_of_mem _ other))
      have sameTest := testKey x y keys.1
      by_cases tested : test x = true
      · rw [List.filter_cons_of_pos tested, List.filter_cons_of_pos (sameTest ▸ tested),
          List.map_cons, rest, pointwise x List.mem_cons_self y List.mem_cons_self keys.1 tested]
      · have untested : ¬ test y = true := sameTest ▸ tested
        rw [List.filter_cons_of_neg tested, List.filter_cons_of_neg untested, rest]

/-- **An own completion is sent to the completion of the same event** at the
second settled state. -/
theorem completion_ownerSwap_of_settled {named : Nat → Prop}
    {first second : EventGraphRuntime.State (graph setup)}
    (firstSettled : OwnerSettled who named first) (secondSettled : OwnerSettled who named second)
    {left right : (graph setup).Completion} (leftMember : left ∈ first.config.history)
    (rightMember : right ∈ second.config.history) (same : left.event = right.event)
    (own : (graph setup).actor? left.event = some who) :
    (ownerSwap who (first.playerView who) (second.playerView who)).values.completion left =
      right := by
  rcases left with ⟨event, leftAction⟩
  rcases right with ⟨otherEvent, rightAction⟩
  change event = otherEvent at same
  subst same
  change (graph setup).actor? event = some who at own
  suffices actionEq : (ownerSwap who (first.playerView who)
      (second.playerView who)).values.action event leftAction = rightAction by
    change (⟨event, _⟩ : (graph setup).Completion) = _
    rw [actionEq]
  cases view : nodeView (graph setup) event with
  | bind owner payload outputEq codeEq =>
      obtain rfl : owner = who :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans own)
      have leftOut := firstSettled.bindAction _ leftMember owner payload outputEq codeEq
      have rightOut := secondSettled.bindAction _ rightMember owner payload outputEq codeEq
      have privateTo : PrivateTo owner (.inr event) := by
        refine ⟨?_, ?_⟩
        · change ((graph setup).outputLayout event).VisibleTo owner
          rw [outputEq]
          rfl
        · change ¬ ((graph setup).outputLayout event).IsPublic
          rw [outputEq]
          exact id
      have swapped := value_ownerSwap owner (first.playerView owner) (second.playerView owner)
        privateTo
        (by
          change (graph setup).playerStore owner first.config.store (.inr event) = _
          rw [EventGraph.playerStore_of_visible _ _ _ _ privateTo.1]
          exact leftOut)
        (by
          change (graph setup).playerStore owner second.config.store (.inr event) = _
          rw [EventGraph.playerStore_of_visible _ _ _ _ privateTo.1]
          exact rightOut)
        (firstSettled.noFailure _ privateTo _ leftOut)
        (secondSettled.noFailure _ privateTo _ rightOut)
      have actionEq := (ownerSwap owner (first.playerView owner)
        (second.playerView owner)).values.action_binding event owner payload outputEq
          (cast (congrArg EventGraph.EventField.Action outputEq) leftAction)
      simp only [cast_cast, cast_eq] at actionEq
      rw [actionEq]
      simp only [cast_cast] at swapped
      rw [swapped]
      simp only [cast_cast, cast_eq]
  | resolve owner payload binding checks outputEq codeEq =>
      rw [(ownerSwap who (first.playerView who) (second.playerView who)).values.action_publication
        event payload outputEq]
      have leftTrue := firstSettled.disclosed _ leftMember own payload outputEq
      have rightTrue := secondSettled.disclosed _ rightMember own payload outputEq
      exact (cast_inj _).mp (leftTrue.trans rightTrue.symm)
  | sample payload law outputEq codeEq =>
      rw [nodeView_sample_actor outputEq codeEq] at own
      cases own

/-- **Own completions.** The owner swap sends the own completions of `who` at
an earlier state of the first settled state to those at the matching earlier
state of the second. -/
theorem ownActions_ownerSwap_of_settled {named named' : Nat → Prop}
    {first second before after : EventGraphRuntime.State (graph setup)}
    (firstSettled : OwnerSettled who named first) (secondSettled : OwnerSettled who named second)
    (firstEarlier : OwnerEarlier who named' before first)
    (secondEarlier : OwnerEarlier who named' after second)
    (publicEq : before.publicView = after.publicView) :
    ((graph setup).ownCompletions who before.config.history).map
        (ownerSwap who (first.playerView who) (second.playerView who)).values.completion =
      (graph setup).ownCompletions who after.config.history := by
  have orders := congrArg (fun view : PublicView (graph setup) => view.observation.completionOrder)
    publicEq
  change before.config.history.map EventGraph.Completion.event =
    after.config.history.map EventGraph.Completion.event at orders
  unfold EventGraph.ownCompletions
  apply map_filter_of_keys _ _ EventGraph.Completion.event
    (fun left right same => by rw [same]) _ _ orders
  intro left leftMember right rightMember same own
  exact completion_ownerSwap_of_settled who firstSettled secondSettled
    (firstEarlier.history.subset leftMember) (secondEarlier.history.subset rightMember) same
    (of_decide_eq_true own)

/-- **Stores.** The owner swap sends the store `who` sees at an earlier state of
the first settled state to the store it sees at the matching earlier state of
the second. -/
theorem store_ownerSwap_of_settled {named named' : Nat → Prop}
    {first second before after : EventGraphRuntime.State (graph setup)}
    (firstSettled : OwnerSettled who named first) (secondSettled : OwnerSettled who named second)
    (firstEarlier : OwnerEarlier who named' before first)
    (secondEarlier : OwnerEarlier who named' after second)
    (publicEq : before.publicView = after.publicView) :
    (ownerSwap who (first.playerView who) (second.playerView who)).values.store
        ((graph setup).playerStore who before.config.store) =
      (graph setup).playerStore who after.config.store := by
  funext field
  simp only [EventGraph.ValueSwap.store]
  by_cases visible : (graph setup).fieldVisibleTo who field
  · rw [EventGraph.playerStore_of_visible _ _ _ _ visible,
      EventGraph.playerStore_of_visible _ _ _ _ visible]
    by_cases isPublic : (graph setup).fieldPublic field
    · rw [(ownerSwap who (first.playerView who) (second.playerView who)).values.value_public
        field isPublic, Option.map_id, id_eq]
      have stores := congrArg
        (fun view : PublicView (graph setup) => view.observation.store field) publicEq
      change (graph setup).publicStore before.config.store field =
        (graph setup).publicStore after.config.store field at stores
      simpa only [EventGraph.publicStore, isPublic, ↓reduceIte] using stores
    · have privateTo : PrivateTo who field := ⟨visible, isPublic⟩
      have present : (before.config.store field).isSome = (after.config.store field).isSome := by
        cases field with
        | inl input => rfl
        | inr event =>
            have orders := congrArg
              (fun view : PublicView (graph setup) => view.observation.completionOrder) publicEq
            change before.config.history.map EventGraph.Completion.event =
              after.config.history.map EventGraph.Completion.event at orders
            change (before.config.outputs event).isSome = (after.config.outputs event).isSome
            rw [Bool.eq_iff_iff, before.config.output_available, after.config.output_available,
              ← before.config.history_exact, ← after.config.history_exact, orders]
      cases beforeStore : before.config.store field with
      | none =>
          rw [beforeStore] at present
          cases afterStore : after.config.store field with
          | none => rfl
          | some right => rw [afterStore] at present; cases present
      | some left =>
          rw [beforeStore] at present
          cases afterStore : after.config.store field with
          | none => rw [afterStore] at present; cases present
          | some right =>
              have leftStored := firstEarlier.store field left beforeStore
              have rightStored := secondEarlier.store field right afterStore
              refine congrArg some (value_ownerSwap who _ _ privateTo ?_ ?_
                (firstSettled.noFailure field privateTo left leftStored)
                (secondSettled.noFailure field privateTo right rightStored))
              · change (graph setup).playerStore who first.config.store field = _
                rw [EventGraph.playerStore_of_visible _ _ _ _ visible]
                exact leftStored
              · change (graph setup).playerStore who second.config.store field = _
                rw [EventGraph.playerStore_of_visible _ _ _ _ visible]
                exact rightStored
  · rw [EventGraph.playerStore_of_hidden _ _ _ _ visible,
      EventGraph.playerStore_of_hidden _ _ _ _ visible]
    rfl

/-- **Meanings.** The owner swap sends the meaning of a handle of `who` at an
earlier state of the first settled state to its meaning at the matching earlier
state of the second. -/
theorem candidates_ownerSwap_of_settled {named named' : Nat → Prop}
    {first second before after : EventGraphRuntime.State (graph setup)}
    (firstSettled : OwnerSettled who named first) (secondSettled : OwnerSettled who named second)
    (firstEarlier : OwnerEarlier who named' before first)
    (secondEarlier : OwnerEarlier who named' after second)
    (slot : CandidateSlot (graph setup)) :
    swapCandidate ((ownerSwap who (first.playerView who) (second.playerView who)).raw
        (who, slot)) (before.candidates.lookup (who, slot)) =
      after.candidates.lookup (who, slot) := by
  cases slot with
  | prepared serial =>
      by_cases fresh : before.candidates.lookup (who, .prepared serial) = .fresh
      · have afterFresh : after.candidates.lookup (who, .prepared serial) = .fresh :=
          (secondEarlier.fresh serial).mpr ((firstEarlier.fresh serial).mp fresh)
        rw [fresh, afterFresh]
        rfl
      · have afterFixed : after.candidates.lookup (who, .prepared serial) ≠ .fresh :=
          fun afterFresh => fresh ((firstEarlier.fresh serial).mpr
            ((secondEarlier.fresh serial).mp afterFresh))
        rw [← firstEarlier.fixed _ fresh, ← secondEarlier.fixed _ afterFixed]
        have namedSlot : named serial := by
          by_contra unnamed
          apply fresh
          rw [← firstEarlier.fixed _ fresh]
          exact (firstSettled.fresh serial).mpr unnamed
        obtain ⟨leftRaw, leftOpen⟩ := firstSettled.openable serial namedSlot
        obtain ⟨rightRaw, rightOpen⟩ := secondSettled.openable serial namedSlot
        apply swapCandidate_ownerSwap who (first.playerView who) (second.playerView who)
        change CandidatesAligned (first.candidates.lookup (who, .prepared serial))
          (second.candidates.lookup (who, .prepared serial))
        rw [leftOpen, rightOpen]
        trivial
  | initial input =>
      have firstInputs : before.config.inputs input = first.config.inputs input :=
        Option.some.inj (firstEarlier.store (.inl input) _ rfl).symm
      have secondInputs : after.config.inputs input = second.config.inputs input :=
        Option.some.inj (secondEarlier.store (.inl input) _ rfl).symm
      rw [firstEarlier.initial, secondEarlier.initial, firstInputs, secondInputs,
        ← firstSettled.initial, ← secondSettled.initial]
      apply swapCandidate_ownerSwap who (first.playerView who) (second.playerView who)
      change CandidatesAligned (first.candidates.lookup (who, .initial input))
        (second.candidates.lookup (who, .initial input))
      rw [firstSettled.initial, secondSettled.initial]
      exact candidatesAligned_candidateOfValue who _ _ _
        (fun visible notPublic => firstSettled.noFailure (.inl input) ⟨visible, notPublic⟩ _ rfl)
        (fun visible notPublic => secondSettled.noFailure (.inl input) ⟨visible, notPublic⟩ _ rfl)

/-- **The owner swap between two settled states sends the view of `who` at an
earlier state of the first to its view at the matching earlier state of the
second.** -/
theorem EventGraphRuntime.PlayerView.swap_ownerSwap_of_settled {named named' : Nat → Prop}
    {first second before after : EventGraphRuntime.State (graph setup)}
    (firstSettled : OwnerSettled who named first) (secondSettled : OwnerSettled who named second)
    (firstEarlier : OwnerEarlier who named' before first)
    (secondEarlier : OwnerEarlier who named' after second)
    (publicEq : before.publicView = after.publicView) :
    PlayerView.swap (ownerSwap who (first.playerView who) (second.playerView who))
        (before.playerView who) = after.playerView who := by
  have orders := congrArg (fun view : PublicView (graph setup) => view.observation.completionOrder)
    publicEq
  change before.config.history.map EventGraph.Completion.event =
    after.config.history.map EventGraph.Completion.event at orders
  change (⟨who, before.publicView, ⟨before.config.history.map EventGraph.Completion.event,
      (ownerSwap who (first.playerView who) (second.playerView who)).values.store
        ((graph setup).playerStore who before.config.store),
      ((graph setup).ownCompletions who before.config.history).map
        (ownerSwap who (first.playerView who) (second.playerView who)).values.completion⟩,
      fun slot => swapCandidate ((ownerSwap who (first.playerView who)
        (second.playerView who)).raw (who, slot)) (before.candidates.lookup (who, slot))⟩ :
      PlayerView (graph setup)) =
    ⟨who, after.publicView, ⟨after.config.history.map EventGraph.Completion.event,
      (graph setup).playerStore who after.config.store,
      (graph setup).ownCompletions who after.config.history⟩,
      fun slot => after.candidates.lookup (who, slot)⟩
  rw [publicEq, orders,
    store_ownerSwap_of_settled who firstSettled secondSettled firstEarlier secondEarlier publicEq,
    ownActions_ownerSwap_of_settled who firstSettled secondSettled firstEarlier secondEarlier
      publicEq]
  congr 1
  funext slot
  exact candidates_ownerSwap_of_settled who firstSettled secondSettled firstEarlier
    secondEarlier slot

end Views

section Responses

variable {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
variable (who : Player)

/-- **A recorded preparation.** A commitment names a prepared handle of `who`
whose meaning is the supplied value, or unopenable without one; any other call
supplies no value. -/
def PreparationRecorded (state : EventGraphRuntime.State (graph setup))
    (call : Submission (graph setup)) : Prop :=
  match call.packet with
  | .commitment _ handle => ∃ serial, handle = (who, .prepared serial) ∧
      state.candidates.lookup handle = call.opening.elim .unopenable .openable
  | .opening .. | .malformed _ => call.opening = none

/-- **A recorded response.** Silence emits nothing; a transmission emits an
envelope carrying its call, its evidence request is the canonical request of the
emitted evidence among the known packets, and its preparation is recorded. -/
def RecordedResponse (state : EventGraphRuntime.State (graph setup))
    (known : List (Message Player (WitnessedPacket (graph setup))))
    (entry : (application setup runtime leaks).PlayerEntry) : Prop :=
  match entry.action.transmission with
  | none => entry.emitted = none
  | some submission => ∃ message, entry.emitted = some message ∧
      message.payload.call = submission.call.packet ∧
      submission.evidence = EvidenceRequest.canonical known message.payload.evidence ∧
      PreparationRecorded who state submission.call

/-- **The owner swap sends a recorded response to the response recorded with
the same envelope** at the second settled state, when the slots its commitment
names are named. -/
theorem EventGraphRuntime.HiddenSwap.action_ownerSwap {named : Nat → Prop}
    {first second : EventGraphRuntime.State (graph setup)}
    (firstSettled : OwnerSettled who named first) (secondSettled : OwnerSettled who named second)
    {known : List (Message Player (WitnessedPacket (graph setup)))}
    {left right : (application setup runtime leaks).PlayerEntry}
    (leftRecorded : RecordedResponse (runtime := runtime) who first known left)
    (rightRecorded : RecordedResponse (runtime := runtime) who second known right)
    (emitted : left.emitted = right.emitted)
    (namedOf : ∀ message event serial, left.emitted = some message →
      message.payload.call = .commitment event (who, .prepared serial) → named serial) :
    (ownerSwap who (first.playerView who) (second.playerView who)).action left.action =
      right.action := by
  rcases left with ⟨leftView, ⟨leftTransmission⟩, leftEmitted⟩
  rcases right with ⟨rightView, ⟨rightTransmission⟩, rightEmitted⟩
  change leftEmitted = rightEmitted at emitted
  subst emitted
  cases leftTransmission with
  | none =>
      change leftEmitted = none at leftRecorded
      cases rightTransmission with
      | none => rfl
      | some submission =>
          obtain ⟨message, sent, _⟩ := rightRecorded
          change leftEmitted = some message at sent
          rw [leftRecorded] at sent
          cases sent
  | some leftSubmission =>
      obtain ⟨message, sent, leftCall, leftEvidence, leftPrepared⟩ := leftRecorded
      change leftEmitted = some message at sent
      cases rightTransmission with
      | none =>
          change leftEmitted = none at rightRecorded
          rw [rightRecorded] at sent
          cases sent
      | some rightSubmission =>
          obtain ⟨other, otherSent, rightCall, rightEvidence, rightPrepared⟩ := rightRecorded
          change leftEmitted = some other at otherSent
          rw [sent] at otherSent
          cases otherSent
          rcases leftSubmission with ⟨⟨leftPacket, leftOpening⟩, leftRequest⟩
          rcases rightSubmission with ⟨⟨rightPacket, rightOpening⟩, rightRequest⟩
          change message.payload.call = leftPacket at leftCall
          change message.payload.call = rightPacket at rightCall
          change leftRequest = _ at leftEvidence
          change rightRequest = _ at rightEvidence
          subst leftCall rightCall leftEvidence rightEvidence
          generalize packetEq : message.payload.call = packet at leftPrepared rightPrepared ⊢
          cases packet with
          | commitment event handle =>
              obtain ⟨serial, rfl, leftMeaning⟩ := leftPrepared
              obtain ⟨_, sameHandle, rightMeaning⟩ := rightPrepared
              have namedSlot := namedOf message event serial sent packetEq
              obtain ⟨leftRaw, leftOpen⟩ := firstSettled.openable serial namedSlot
              obtain ⟨rightRaw, rightOpen⟩ := secondSettled.openable serial namedSlot
              change first.candidates.lookup (who, .prepared serial) = _ at leftMeaning
              change second.candidates.lookup (who, .prepared serial) = _ at rightMeaning
              rw [leftOpen] at leftMeaning
              rw [rightOpen] at rightMeaning
              cases leftOpening with
              | none => cases leftMeaning
              | some leftValue =>
                  cases rightOpening with
                  | none => cases rightMeaning
                  | some rightValue =>
                      cases leftMeaning
                      cases rightMeaning
                      have aligned := swapCandidate_ownerSwap who (first.playerView who)
                        (second.playerView who) (.prepared serial)
                        (by
                          change CandidatesAligned
                            (first.candidates.lookup (who, .prepared serial))
                            (second.candidates.lookup (who, .prepared serial))
                          rw [leftOpen, rightOpen]
                          trivial)
                      change swapCandidate _ (first.candidates.lookup (who, .prepared serial)) =
                        second.candidates.lookup (who, .prepared serial) at aligned
                      rw [leftOpen, rightOpen, swapCandidate_openable] at aligned
                      cases aligned
                      rfl
          | opening event handle raw =>
              change leftOpening = none at leftPrepared
              change rightOpening = none at rightPrepared
              subst leftPrepared rightPrepared
              rfl
          | malformed raw =>
              change leftOpening = none at leftPrepared
              change rightOpening = none at rightPrepared
              subst leftPrepared rightPrepared
              rfl

/-- **The owner swap sends a view of `who` at an earlier state of the first
settled state to the view with the same operational part at the matching
earlier state of the second.** -/
theorem EventGraphRuntime.HiddenSwap.view_ownerSwap_of_settled {named named' : Nat → Prop}
    {first second before after : EventGraphRuntime.State (graph setup)}
    (firstSettled : OwnerSettled who named first) (secondSettled : OwnerSettled who named second)
    (firstEarlier : OwnerEarlier who named' before first)
    (secondEarlier : OwnerEarlier who named' after second)
    {left right : (application setup runtime leaks).PlayerView}
    (leftApplication : left.application = before.playerView who)
    (rightApplication : right.application = after.playerView who)
    (operational : operationalView setup runtime leaks left = operationalView setup runtime leaks
      right) :
    (ownerSwap who (first.playerView who) (second.playerView who)).view left = right := by
  rcases left with ⟨leftMessages, leftApp, leftReceipts⟩
  rcases right with ⟨rightMessages, rightApp, rightReceipts⟩
  change leftApp = _ at leftApplication
  change rightApp = _ at rightApplication
  subst leftApplication rightApplication
  simp only [operationalView, Prod.mk.injEq] at operational
  obtain ⟨publicEq, messagesEq, receiptsEq⟩ := operational
  subst messagesEq receiptsEq
  change (⟨leftMessages, PlayerView.swap _ (before.playerView who), leftReceipts⟩ :
    (application setup runtime leaks).PlayerView) = _
  rw [EventGraphRuntime.PlayerView.swap_ownerSwap_of_settled who firstSettled secondSettled
    firstEarlier secondEarlier publicEq]

end Responses

end Vegas
