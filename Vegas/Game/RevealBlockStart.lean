/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealBlockGraph

/-! # Block starts that may already be done

At a block start the block may already be done, when every block reveal was
completed automatically for a defaulted owner. A run of such a block stays
where it started. The deviator tells such a start from an unfinished one at
the end of the block: a reveal pending at an unfinished start completes with a
decision, a published value, or a recorded default, while at a finished start
it was completed silently.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode}

/-- A finished block start and the end of a run of an unfinished one give the
deviator different normalized views. -/
theorem blockStart_mixed_absurd {who : Player} {start finish : Nat}
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (flat : BlockFlat (graph := serviceGraph setup mode) start finish)
    (publications : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → ((serviceGraph setup mode).outputLayout event).IsPublication)
    {finished origin current : (serviceGraph setup mode).Config}
    (finishedBegin : BlockStart start finish finished) (begin : BlockStart start finish origin)
    (done : BlockDone finish finished) (running : ¬ BlockDone finish origin)
    (path : Relation.ReflTransGen Config.Step origin current)
    (sound : BlockRecordsSound who start finish origin current)
    (owners : DefaultOwners current)
    (views : (serviceGraph setup mode).normalizeObservation who
        ((serviceGraph setup mode).playerObserve who finished) =
      (serviceGraph setup mode).normalizeObservation who
        ((serviceGraph setup mode).playerObserve who current)) : False := by
  unfold BlockDone at running
  push Not at running
  obtain ⟨event, late, pending⟩ := running
  have early : start ≤ event.val := by
    by_contra smaller
    exact pending (begin.earlier event (by omega))
  have finishedDone := done event late
  have quiet := finishedBegin.silent event early late finishedDone
  have failed := finishedBegin.failed event early late finishedDone
  obtain ⟨owner, payload, binding, checks, outputEq, codeEq, node⟩ :=
    exists_resolve_of_publication (publications event early late)
  have owned := nodeView_resolve_actor outputEq codeEq
  by_cases currentDone : event ∈ current.cut.completed
  swap
  · have present := normalize_present_congr who views event
    rw [quiet, (completionOf_eq_none_iff current event).mpr currentDone] at present
    cases present
  by_cases isWho : owner = who
  · subst isWho
    obtain ⟨record, found, decided⟩ := decided_of_pending concurrent flat begin path sound owners
      early late pending currentDone owned
    have own := normalize_own_completionOf_congr owner views event owned
    rw [quiet, found] at own
    have same := Option.some.inj own
    rw [← same] at decided
    cases decided
  rcases sound event pending currentDone with ⟨silent, _, other, otherOwned, inactive⟩ |
    ⟨_, _, whoOwned | opened | expired⟩
  · exact pending_not_silent concurrent flat begin path sound owners early late pending
      otherOwned silent inactive
  · exact isWho (Option.some.inj (owned.symm.trans whoOwned))
  · obtain ⟨_, _, _, _, _, _, _, openedNode, _, accepted, _, stored⟩ := opened
    obtain ⟨value, resolved⟩ := resolveOutput_of_accepted openedNode accepted
    have stores := congrArg (fun observation : (serviceGraph setup mode).PlayerObservation who =>
      observation.store) views
    rw [normalizeObservation_playerObserve, normalizeObservation_playerObserve] at stores
    simp only at stores
    have outputs := congrFun stores (.inr event)
    rw [playerStore_of_visible (visible := fieldVisibleTo_of_publication who
        (publications event early late)),
      playerStore_of_visible (visible := fieldVisibleTo_of_publication who
        (publications event early late))] at outputs
    change finished.outputs event = current.outputs event at outputs
    rw [failed, stored, resolved] at outputs
    unfold failureOutput at outputs
    rw [openedNode] at outputs
    simp only [Option.map_some, Option.some.injEq] at outputs
    cases (cast_inj _).mp outputs
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, recorded, _⟩ := expired
    have defaults := normalize_defaultEvent_congr who views event (by rw [quiet]; rfl)
    rw [quiet, recorded] at defaults
    cases defaults

/-- A block start whose block is done hides no accepted output. -/
theorem blockHidden_of_done {who : Player} {start finish : Nat}
    {config : (serviceGraph setup mode).Config} (done : BlockDone finish config) :
    blockHidden who start finish (runKey config) = fun _ => none := by
  funext event
  unfold blockHidden
  change (if start ≤ event.val ∧ event.val < finish ∧ event ∉ config.cut.completed ∧
    (serviceGraph setup mode).actor? event ≠ some who then acceptedOutput event config.store
    else none) = none
  exact ite_eq_right fun hidden => hidden.2.2.1 (done event hidden.2.1)

/-- **The start of a block is read from a later configuration**, also when a
start is already done and its run stays there. -/
theorem blockStart_reflect_general {who : Player} {start finish : Nat}
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (flat : BlockFlat (graph := serviceGraph setup mode) start finish)
    (publications : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → ((serviceGraph setup mode).outputLayout event).IsPublication)
    {startLeft startRight endLeft endRight : (serviceGraph setup mode).Config}
    (beginLeft : BlockStart start finish startLeft)
    (beginRight : BlockStart start finish startRight)
    (pathLeft : Relation.ReflTransGen Config.Step startLeft endLeft)
    (pathRight : Relation.ReflTransGen Config.Step startRight endRight)
    (soundLeft : BlockRecordsSound who start finish startLeft endLeft)
    (soundRight : BlockRecordsSound who start finish startRight endRight)
    (ownersLeft : DefaultOwners endLeft) (ownersRight : DefaultOwners endRight)
    (honestLeft : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → event ∉ startLeft.cut.completed →
        (serviceGraph setup mode).actor? event ≠ some who → event ∈ endLeft.cut.completed)
    (honestRight : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → event ∉ startRight.cut.completed →
        (serviceGraph setup mode).actor? event ≠ some who → event ∈ endRight.cut.completed)
    (stayLeft : BlockDone finish startLeft → endLeft = startLeft)
    (stayRight : BlockDone finish startRight → endRight = startRight)
    (views : (serviceGraph setup mode).normalizeObservation who
        ((serviceGraph setup mode).playerObserve who endLeft) =
      (serviceGraph setup mode).normalizeObservation who
        ((serviceGraph setup mode).playerObserve who endRight)) :
    (serviceGraph setup mode).normalizeObservation who
        ((serviceGraph setup mode).playerObserve who startLeft) =
      (serviceGraph setup mode).normalizeObservation who
        ((serviceGraph setup mode).playerObserve who startRight) ∧
    blockHidden who start finish (runKey startLeft) =
      blockHidden who start finish (runKey startRight) := by
  by_cases doneLeft : BlockDone finish startLeft
  · by_cases doneRight : BlockDone finish startRight
    · rw [stayLeft doneLeft, stayRight doneRight] at views
      exact ⟨views, by rw [blockHidden_of_done doneLeft, blockHidden_of_done doneRight]⟩
    · rw [stayLeft doneLeft] at views
      exact (blockStart_mixed_absurd concurrent flat publications beginLeft beginRight doneLeft
        doneRight pathRight soundRight ownersRight views).elim
  · by_cases doneRight : BlockDone finish startRight
    · rw [stayRight doneRight] at views
      exact (blockStart_mixed_absurd concurrent flat publications beginRight beginLeft doneRight
        doneLeft pathLeft soundLeft ownersLeft views.symm).elim
    · exact blockStart_reflect_of_honestDone concurrent flat publications beginLeft beginRight
        doneLeft doneRight pathLeft pathRight soundLeft soundRight ownersLeft ownersRight
        honestLeft honestRight views

end Vegas
