/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSwapGuardSite
import Vegas.Game.OnePacketSwapFibers

/-! # The swap between two points of an information site

Fix two intended points `p` and `q` one player `who` observes alike and a table
of accepted handles. The swap between `p` and `q` at the table does not depend on
the order of the points (`Vegas.hiddenSwap_between_comm`). When every accepted
handle belongs to the owner of its field, the swap fixes `who`
(`Vegas.fixes_between`): `who` sees every field and every commitment of its own,
and these agree at the two points. At a state where `who` has a turn, every ready
reveal belongs to `who` (`Vegas.readyOwn_of_ownTurn`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

/-- **At an own turn every ready reveal is own.** -/
theorem readyOwn_of_ownTurn (state : EventGraphRuntime.State (graph setup)) {who : Player}
    {turnEvent : (graph setup).EventId} (turn : state.publicView.ownTurn? who = some turnEvent) :
    ∀ event, state.config.cut.Ready event →
      ∀ owner payload binding checks outputEq codeEq,
        nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq →
          owner = who := by
  intro event ready owner payload binding checks outputEq codeEq _
  obtain ⟨turnReady, turnActor⟩ := PublicView.ownTurn?_spec _ who turnEvent turn
  have same := (soleReady_of_ready setup state ready).2 turnEvent turnReady
  rw [same, nodeView_resolve_actor outputEq codeEq] at turnActor
  exact Option.some.inj turnActor

variable [DecidableEq (CellTy Player L)] {p q : ProtocolState setup.program}

theorem pairSwap_commitmentRawPair_comm (cell : VarId × CellTy Player L) :
    EventGraph.pairSwap (commitmentRawPair setup p q cell) =
      EventGraph.pairSwap (commitmentRawPair setup q p cell) := by
  rcases cell with ⟨name, kind⟩
  cases kind with
  | publicData | privateInput | publication => rfl
  | commitment owner payload =>
      simp only [commitmentRawPair]
      rcases ProtocolState.cell? setup.program p name (.commitment owner payload) with
        _ | _ | left <;>
      rcases ProtocolState.cell? setup.program q name (.commitment owner payload) with
        _ | _ | right
      all_goals try rfl
      by_cases same : left = right
      · subst same
        simp
      · have other : right ≠ left := fun equal => same equal.symm
        simp only [same, other, ↓reduceIte]
        exact EventGraph.pairSwap_comm _ _

/-- **The swap between two points does not depend on their order.** -/
theorem hiddenSwap_between_comm {publicAgree : PublicCellsAgree setup p q}
    {succeed : CommitmentCellsSucceed setup p q} {publicAgree' : PublicCellsAgree setup q p}
    {succeed' : CommitmentCellsSucceed setup q p} (table : AcceptedHandles (graph setup)) :
    HiddenSwap.ofPairs (betweenPairs publicAgree' succeed') (betweenHandlePairs setup q p table) =
      HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
        (betweenHandlePairs setup p q table) := by
  have values := valueSwap_betweenPairs_comm (publicAgree := publicAgree') (succeed := succeed')
    (publicAgree' := publicAgree) (succeed' := succeed)
  have raws : (fun handle => EventGraph.pairSwap (betweenHandlePairs setup q p table handle)) =
      (fun handle => EventGraph.pairSwap (betweenHandlePairs setup p q table handle)) := by
    funext handle
    unfold betweenHandlePairs
    split_ifs
    · exact pairSwap_commitmentRawPair_comm _
    · rfl
  unfold HiddenSwap.ofPairs
  congr 1

variable {publicAgree : PublicCellsAgree setup p q} {succeed : CommitmentCellsSucceed setup p q}

/-- A field a player sees has no pair between two points the player observes
alike. -/
theorem betweenPairs_visible {who : Player}
    (sameView : ProtocolState.observe who setup.program p =
      ProtocolState.observe who setup.program q)
    {field : (graph setup).Field} (visible : (graph setup).fieldVisibleTo who field) :
    (betweenPairs publicAgree succeed).pair field = none := by
  have seen : (cellField (fieldCell setup field).2).VisibleTo who :=
    (layout_fieldCell setup field) ▸ visible
  exact betweenPair_eq_none_of_agree (field := field) rfl
    (visibleCellsAgree_of_observe sameView _ seen)

/-- **The swap between two points a player observes alike fixes the player**
when every accepted handle belongs to the owner of its field. -/
theorem fixes_between {who : Player}
    (sameView : ProtocolState.observe who setup.program p =
      ProtocolState.observe who setup.program q)
    {table : AcceptedHandles (graph setup)}
    (owned : ∀ field handle, table field = some handle →
      ∃ payload, (graph setup).layout field = .binding handle.1 payload) :
    (HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
      (betweenHandlePairs setup p q table)).Fixes who := by
  refine ⟨fun field visible => ?_, fun event acting => ?_, fun slot => ?_⟩
  · change EventGraph.pairSwap ((betweenPairs publicAgree succeed).pair field) = id
    rw [betweenPairs_visible sameView visible]
    rfl
  · change (betweenPairs publicAgree succeed).action event = id
    unfold EventGraph.SwapPairs.action
    cases nodeView (graph setup) event with
    | resolve | sample => rfl
    | bind owner payload outputEq codeEq =>
        rw [nodeView_bind_actor outputEq codeEq] at acting
        cases Option.some.inj acting
        have visible : (graph setup).fieldVisibleTo who (.inr event) := by
          change ((graph setup).outputLayout event).VisibleTo who
          rw [outputEq]
          rfl
        rw [betweenPairs_visible sameView visible]
        funext original
        simp [EventGraph.pairSwap]
  · change EventGraph.pairSwap (betweenHandlePairs setup p q table (who, slot)) = id
    unfold betweenHandlePairs
    split_ifs with found
    · obtain ⟨payload, layoutEq⟩ := owned _ _ found.choose_spec
      have kind := cellField_eq_binding
        ((layout_fieldCell setup found.choose).symm.trans layoutEq)
      have cell : fieldCell setup found.choose =
          ((fieldCell setup found.choose).1, .commitment who payload) := Prod.ext rfl kind
      rw [cell, commitmentRawPair_eq_none_of_agree
        (visibleCellsAgree_of_observe sameView _
          (show (cellField (CellTy.commitment who payload)).VisibleTo who from rfl))]
      rfl
    · rfl

end Vegas
