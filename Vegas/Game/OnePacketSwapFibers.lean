/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSwapRegular

/-! # The swap between two source points is symmetric

Swapping the two points exchanges the pairs, and a transposition does not
depend on the order of its pair, so the value swaps of the pairs between `p`
and `q` and between `q` and `p` agree (`Vegas.valueSwap_betweenPairs_comm`).
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem pairSwap_comm {α : Type*} (left right : α) :
    pairSwap (some (left, right)) = pairSwap (some (right, left)) := by
  classical
  funext value
  exact congrFun (congrArg DFunLike.coe (Equiv.swap_comm left right)) value

/-- Value swaps of pairs with the same transpositions are equal. -/
theorem ValueSwap.ofPairs_congr {first second : graph.SwapPairs}
    (same : ∀ field, pairSwap (first.pair field) = pairSwap (second.pair field)) :
    ValueSwap.ofPairs first = ValueSwap.ofPairs second := by
  have values : (fun field => pairSwap (first.pair field)) =
      (fun field => pairSwap (second.pair field)) := funext same
  have actions : first.action = second.action := by
    funext event
    unfold SwapPairs.action
    cases EventGraphRuntime.nodeView graph event with
    | bind owner payload outputEq codeEq => simp only [same]
    | resolve | sample => rfl
  unfold ValueSwap.ofPairs
  congr 1

end Vegas.EventGraph

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} [DecidableEq (CellTy Player L)]

omit [DecidableEq Player] [IExpr.ResultTypes L] [DecidableEq (CellTy Player L)] in
theorem pairSwap_cellPair_comm {kind : CellTy Player L} (first second : Option (CellVal L kind)) :
    EventGraph.pairSwap (cellPair first second) = EventGraph.pairSwap (cellPair second first) := by
  classical
  funext value
  rw [pairSwap_cellPair, pairSwap_cellPair]
  cases kind <;>
  · cases first <;> cases second <;> simp only [swapFoundField, swapFound]
    exact congrFun (congrArg DFunLike.coe (Equiv.swap_comm _ _)) value

/-- **The value swaps between two points in either order agree.** -/
theorem valueSwap_betweenPairs_comm {first second : ProtocolState setup.program}
    {publicAgree : PublicCellsAgree setup first second}
    {succeed : CommitmentCellsSucceed setup first second}
    {publicAgree' : PublicCellsAgree setup second first}
    {succeed' : CommitmentCellsSucceed setup second first} :
    EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed) =
      EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree' succeed') := by
  apply EventGraph.ValueSwap.ofPairs_congr
  intro field
  change EventGraph.pairSwap (cellPairAt setup first second (fieldCell setup field)
      (layout_fieldCell setup field)) =
    EventGraph.pairSwap (cellPairAt setup second first (fieldCell setup field)
      (layout_fieldCell setup field))
  generalize layout_fieldCell setup field = fieldEq
  generalize fieldCell setup field = found at fieldEq
  rcases found with ⟨name, kind⟩
  unfold cellPairAt
  funext value
  obtain ⟨original, rfl⟩ : ∃ original : (cellField kind).Value,
      value = cast (congrArg EventGraph.EventField.Value fieldEq.symm) original :=
    ⟨cast (congrArg EventGraph.EventField.Value fieldEq) value, by simp⟩
  rw [pairSwap_transportPair, pairSwap_transportPair, pairSwap_cellPair_comm]

end Vegas
