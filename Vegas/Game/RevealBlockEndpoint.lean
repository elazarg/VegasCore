/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealBlockRecords

/-! # The endpoint of a block of concurrent reveals

A block run of concurrent reveals ends in a configuration whose run key is
determined by the key it started from and by the deviator's normalized view at
the end. The deviator sees which events completed, every publication, its own
records and every default entry. An honest block reveal is an accepted opening,
a withholding expiry or an automatic completion, and these differ in the
default entry or in the published output. Every other new record is automatic.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime EventGraph

section Generic

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- **Own records are observed.** Equal normalized views agree on the record of
every event the observer owns. -/
theorem normalize_own_completionOf_congr (who : Player) {left right : graph.Config}
    (same : graph.normalizeObservation who (graph.playerObserve who left) =
      graph.normalizeObservation who (graph.playerObserve who right)) (event : graph.EventId)
    (owned : graph.actor? event = some who) :
    completionOf left event = completionOf right event := by
  have presentEq := normalize_present_congr who same event
  let keep := fun completion : graph.Completion =>
    decide (graph.actor? completion.event = some who ∧ completion.decision.isSome)
  have filtered : (completionOf left event).filter keep =
      (completionOf right event).filter keep := by
    have owns := congrArg
      (fun observation : graph.PlayerObservation who => observation.ownActions) same
    rw [normalizeObservation_playerObserve, normalizeObservation_playerObserve] at owns
    have found := congrArg (fun list : List graph.Completion =>
      list.find? fun completion => completion.event = event) owns
    simp only at found
    rwa [find?_filterMap_tagged _ (completionOf_filter_tagged left keep),
      find?_filterMap_tagged _ (completionOf_filter_tagged right keep)] at found
  cases leftRecord : completionOf left event with
  | none =>
      rw [leftRecord] at presentEq
      cases rightRecord : completionOf right event with
      | none => rfl
      | some record => rw [rightRecord] at presentEq; cases presentEq
  | some first =>
      rw [leftRecord] at presentEq filtered
      cases rightRecord : completionOf right event with
      | none => rw [rightRecord] at presentEq; cases presentEq
      | some second =>
          rw [rightRecord] at filtered
          have firstEvent := completionOf_tagged left event first leftRecord
          have secondEvent := completionOf_tagged right event second rightRecord
          have defaults := normalize_defaultEvent_congr who same event (by rw [leftRecord]; rfl)
          rw [leftRecord, rightRecord] at defaults
          simp only [Option.bind_some] at defaults
          cases firstDecision : first.decision with
          | some action =>
              have kept : keep first = true := by
                simp only [keep, decide_eq_true_eq, firstEvent, owned, firstDecision,
                  Option.isSome_some, and_self]
              by_cases keptSecond : keep second = true
              · simpa only [Option.filter_some, kept, keptSecond, ↓reduceIte,
                  Option.some.injEq] using filtered
              · simp only [Option.filter_some, kept, keptSecond, ↓reduceIte,
                  reduceCtorEq] at filtered
          | none =>
              cases secondDecision : second.decision with
              | some action =>
                  have kept : keep second = true := by
                    simp only [keep, decide_eq_true_eq, secondEvent, owned, secondDecision,
                      Option.isSome_some, and_self]
                  have notKept : keep first = false := by
                    simp only [keep, firstDecision, Option.isSome_none, Bool.false_eq_true,
                      and_false, decide_false]
                  simp only [Option.filter_some, kept, notKept, Bool.false_eq_true,
                    ↓reduceIte, reduceCtorEq] at filtered
              | none =>
                  obtain ⟨firstId, firstChoice, firstDefault⟩ := first
                  obtain ⟨secondId, secondChoice, secondDefault⟩ := second
                  simp only at firstEvent secondEvent firstDecision secondDecision defaults
                  subst firstEvent secondEvent firstDecision secondDecision defaults
                  rfl

end Generic

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode}

/-- Publications are visible to every player. -/
theorem fieldVisibleTo_of_publication (who : Player) {event : (serviceGraph setup mode).EventId}
    (publication : ((serviceGraph setup mode).outputLayout event).IsPublication) :
    (serviceGraph setup mode).fieldVisibleTo who (.inr event) := by
  unfold EventGraph.fieldVisibleTo
  change ((serviceGraph setup mode).outputLayout event).VisibleTo who
  generalize (serviceGraph setup mode).outputLayout event = field at publication ⊢
  cases field <;> simp_all [EventField.IsPublication, EventField.VisibleTo]

/-- The record and output of a new event of a block run, read from the
deviator's view. -/
private theorem block_new_congr {who : Player} {start finish : Nat}
    (publications : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → ((serviceGraph setup mode).outputLayout event).IsPublication)
    {originLeft originRight left right : (serviceGraph setup mode).Config}
    (soundLeft : BlockRecordsSound who start finish originLeft left)
    (soundRight : BlockRecordsSound who start finish originRight right)
    (views : (serviceGraph setup mode).normalizeObservation who
        ((serviceGraph setup mode).playerObserve who left) =
      (serviceGraph setup mode).normalizeObservation who
        ((serviceGraph setup mode).playerObserve who right))
    (event : (serviceGraph setup mode).EventId)
    (freshLeft : event ∉ originLeft.cut.completed) (doneLeft : event ∈ left.cut.completed)
    (freshRight : event ∉ originRight.cut.completed) (doneRight : event ∈ right.cut.completed) :
    completionOf left event = completionOf right event ∧
      left.outputs event = right.outputs event := by
  have stores := congrArg (fun observation : (serviceGraph setup mode).PlayerObservation who =>
    observation.store) views
  rw [normalizeObservation_playerObserve, normalizeObservation_playerObserve] at stores
  simp only at stores
  have published (publication : ((serviceGraph setup mode).outputLayout event).IsPublication) :
      left.outputs event = right.outputs event := by
    have visible := congrFun stores (.inr event)
    rwa [playerStore_of_visible (visible := fieldVisibleTo_of_publication who publication),
      playerStore_of_visible (visible := fieldVisibleTo_of_publication who publication)] at visible
  have defaults := normalize_defaultEvent_congr who views event
    ((completionOf_isSome_iff left event).mpr doneLeft)
  rcases soundLeft event freshLeft doneLeft with
    ⟨silentLeft, failedLeft, _⟩ | ⟨earlyLeft, lateLeft, ownedLeft | openedLeft | expiredLeft⟩ <;>
  rcases soundRight event freshRight doneRight with
    ⟨silentRight, failedRight, _⟩ | ⟨earlyRight, lateRight, ownedRight | openedRight | expiredRight⟩
  · exact ⟨silentLeft.trans silentRight.symm, failedLeft.trans failedRight.symm⟩
  · exact ⟨normalize_own_completionOf_congr who views event ownedRight,
      published (publications event earlyRight lateRight)⟩
  · exfalso
    obtain ⟨owner, payload, binding, checks, outputEq, codeEq, _, node, available, accepted,
      _, stored⟩ := openedRight
    obtain ⟨value, resolved⟩ := resolveOutput_of_accepted node accepted
    have outputs := published (publications event earlyRight lateRight)
    rw [failedLeft, stored, resolved] at outputs
    unfold failureOutput at outputs
    rw [node] at outputs
    simp only [Option.map_some, Option.some.injEq] at outputs
    cases (cast_inj _).mp outputs
  · exfalso
    obtain ⟨owner, _, _, _, _, _, _, _, _, _, recorded, _⟩ := expiredRight
    rw [silentLeft, recorded] at defaults
    cases defaults
  · exact ⟨normalize_own_completionOf_congr who views event ownedLeft,
      published (publications event earlyLeft lateLeft)⟩
  · exact ⟨normalize_own_completionOf_congr who views event ownedLeft,
      published (publications event earlyLeft lateLeft)⟩
  · exact ⟨normalize_own_completionOf_congr who views event ownedLeft,
      published (publications event earlyLeft lateLeft)⟩
  · exact ⟨normalize_own_completionOf_congr who views event ownedLeft,
      published (publications event earlyLeft lateLeft)⟩
  · exfalso
    obtain ⟨owner, payload, binding, checks, outputEq, codeEq, _, node, available, accepted,
      _, stored⟩ := openedLeft
    obtain ⟨value, resolved⟩ := resolveOutput_of_accepted node accepted
    have outputs := published (publications event earlyLeft lateLeft)
    rw [failedRight, stored, resolved] at outputs
    unfold failureOutput at outputs
    rw [node] at outputs
    simp only [Option.map_some, Option.some.injEq] at outputs
    cases (cast_inj _).mp outputs
  · exfalso
    obtain ⟨owner, _, _, _, outputEq, codeEq, different, _⟩ := openedLeft
    exact different (Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans
      ownedRight))
  · obtain ⟨_, _, _, _, _, _, _, nodeLeft, _, _, recordedLeft, _⟩ := openedLeft
    obtain ⟨_, _, _, _, _, _, _, nodeRight, _, _, recordedRight, _⟩ := openedRight
    rw [nodeLeft] at nodeRight
    cases nodeRight
    exact ⟨recordedLeft.trans recordedRight.symm, published (publications event earlyLeft
      lateLeft)⟩
  · exfalso
    obtain ⟨_, _, _, _, _, _, _, _, _, _, recordedLeft, _⟩ := openedLeft
    obtain ⟨_, _, _, _, _, _, _, _, _, _, recordedRight, _⟩ := expiredRight
    rw [recordedLeft, recordedRight] at defaults
    cases defaults
  · exfalso
    obtain ⟨owner, _, _, _, _, _, _, _, _, _, recorded, _⟩ := expiredLeft
    rw [silentRight, recorded] at defaults
    cases defaults
  · exfalso
    obtain ⟨owner, _, _, _, outputEq, codeEq, different, _⟩ := expiredLeft
    exact different (Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans
      ownedRight))
  · exfalso
    obtain ⟨_, _, _, _, _, _, _, _, _, _, recordedLeft, _⟩ := expiredLeft
    obtain ⟨_, _, _, _, _, _, _, _, _, _, recordedRight, _⟩ := openedRight
    rw [recordedLeft, recordedRight] at defaults
    cases defaults
  · obtain ⟨_, _, _, _, _, _, _, nodeLeft, _, _, recordedLeft, _⟩ := expiredLeft
    obtain ⟨_, _, _, _, _, _, _, nodeRight, _, _, recordedRight, _⟩ := expiredRight
    rw [nodeLeft] at nodeRight
    cases nodeRight
    exact ⟨recordedLeft.trans recordedRight.symm, published (publications event earlyLeft
      lateLeft)⟩

/-- **The endpoint of a block.** Two block runs from configurations with equal
run keys end with equal run keys when the deviator's normalized end views are
equal. -/
theorem blockEnd_runKey_congr {who : Player} {start finish : Nat}
    (publications : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → ((serviceGraph setup mode).outputLayout event).IsPublication)
    {originLeft originRight left right : (serviceGraph setup mode).Config}
    (keys : runKey originLeft = runKey originRight)
    (pathLeft : Relation.ReflTransGen Config.Step originLeft left)
    (pathRight : Relation.ReflTransGen Config.Step originRight right)
    (soundLeft : BlockRecordsSound who start finish originLeft left)
    (soundRight : BlockRecordsSound who start finish originRight right)
    (views : (serviceGraph setup mode).normalizeObservation who
        ((serviceGraph setup mode).playerObserve who left) =
      (serviceGraph setup mode).normalizeObservation who
        ((serviceGraph setup mode).playerObserve who right)) :
    runKey left = runKey right := by
  have cuts : originLeft.cut = originRight.cut := congrArg Prod.fst keys
  have stores : originLeft.store = originRight.store := congrArg (fun key => key.2.1) keys
  have records : completionOf originLeft = completionOf originRight :=
    congrArg (fun key => key.2.2) keys
  have doneIff (event : (serviceGraph setup mode).EventId) :
      event ∈ left.cut.completed ↔ event ∈ right.cut.completed := by
    rw [← completionOf_isSome_iff, ← completionOf_isSome_iff,
      normalize_present_congr who views event]
  have each (event : (serviceGraph setup mode).EventId) :
      completionOf left event = completionOf right event ∧
        left.outputs event = right.outputs event := by
    by_cases old : event ∈ originLeft.cut.completed
    · have oldRight : event ∈ originRight.cut.completed := by rw [← cuts]; exact old
      obtain ⟨record, recorded⟩ := Option.isSome_iff_exists.mp
        ((completionOf_isSome_iff originLeft event).mpr old)
      have recordedRight : completionOf originRight event = some record := by
        rw [← records]
        exact recorded
      refine ⟨(Config.Step.path_completionOf_of_some pathLeft event _ recorded).trans
        (Config.Step.path_completionOf_of_some pathRight event _ recordedRight).symm, ?_⟩
      rw [outputs_path pathLeft old, outputs_path pathRight oldRight]
      exact congrFun stores (.inr event)
    have oldRight : event ∉ originRight.cut.completed := by rw [← cuts]; exact old
    by_cases done : event ∈ left.cut.completed
    · exact block_new_congr publications soundLeft soundRight views event old done oldRight
        ((doneIff event).mp done)
    · have doneRight : event ∉ right.cut.completed := fun finished =>
        done ((doneIff event).mpr finished)
      refine ⟨((completionOf_eq_none_iff left event).mpr done).trans
        ((completionOf_eq_none_iff right event).mpr doneRight).symm, ?_⟩
      rw [Option.not_isSome_iff_eq_none.mp (fun stored =>
          done ((left.output_available event).mp stored)),
        Option.not_isSome_iff_eq_none.mp (fun stored =>
          doneRight ((right.output_available event).mp stored))]
  have cutEq : left.cut = right.cut := EventOrder.Cut.ext (Finset.ext doneIff)
  have storeEq : left.store = right.store := by
    funext field
    cases field with
    | inl input =>
        change some (left.inputs input) = some (right.inputs input)
        rw [Config.Step.path_inputs_eq pathLeft, Config.Step.path_inputs_eq pathRight]
        exact congrFun stores (.inl input)
    | inr event => exact (each event).2
  have recordEq : completionOf left = completionOf right := funext fun event => (each event).1
  change (left.cut, (left.store, completionOf left)) =
    (right.cut, (right.store, completionOf right))
  rw [cutEq, storeEq, recordEq]

end Vegas
