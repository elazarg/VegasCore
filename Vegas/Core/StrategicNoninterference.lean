/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.Noninterference
import Vegas.Core.Strategic

/-!
# Strategic consequences of source non-interference

This module lifts source-history value non-interference to source behavioral
strategy queries.  It records the fact needed by source/frontier strategic
adequacy: if a frontier round is replayed as a sequential source block, hidden
commit values chosen earlier in the block cannot change another player's later
source action law.
-/

namespace Vegas

namespace SourceStrategy

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Querying a source strategy after another player's hidden commit is
independent of the committed value.

The shared prefix reaches a source commit point for `owner`.  The two histories
then take the same commit occurrence with two legal secret values.  For any other
player `who`, any source strategy for `who` sees the same history-local view at
the resulting endpoint, hence returns the same PMF up to the dependent action
type cast. -/
theorem commitSecret_query_heq
    {strategyStart : SourceConfig P L} {who owner : P} (hne : who ≠ owner)
    (strategy : SourceStrategy (L := L) strategyStart who)
    {labels : List (Label P L)}
    {Γ : VCtx P L} {env : VEnv L Γ}
    {x : VarId} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
    {tail : VegasCore P L ((x, .sealed owner b) :: Γ)}
    (prefixRun :
      SourceConfig.LabeledStar strategyStart labels
        { ctx := Γ, env := env, cont := VegasCore.commit x owner guard tail })
    (left right : L.Val b)
    (hleft : evalGuard (Player := P) (L := L) guard left
      ((env.toView owner).eraseEnv) = true)
    (hright : evalGuard (Player := P) (L := L) guard right
      ((env.toView owner).eraseEnv) = true) :
    let leftHistory : SourceHistoryPoint P L :=
      { start := strategyStart
        labels := labels ++ [Label.commit x owner left]
        current :=
          { ctx := (x, .sealed owner b) :: Γ
            env := VEnv.cons left env
            cont := tail }
        run :=
          SourceConfig.LabeledStar.trans prefixRun
            (SourceConfig.LabeledStar.single
              (LStep.commit guard tail left hleft)) }
    let rightHistory : SourceHistoryPoint P L :=
      { start := strategyStart
        labels := labels ++ [Label.commit x owner right]
        current :=
          { ctx := (x, .sealed owner b) :: Γ
            env := VEnv.cons right env
            cont := tail }
        run :=
          SourceConfig.LabeledStar.trans prefixRun
            (SourceConfig.LabeledStar.single
              (LStep.commit guard tail right hright)) }
    ∀ (hchoiceLeft :
        (leftHistory.localHistoryView who).currentView.point.IsChoiceFor who)
      (hchoiceRight :
        (rightHistory.localHistoryView who).currentView.point.IsChoiceFor who),
      HEq
        (strategy
          (SourceReachableInfoState.ofHistory (L := L)
            leftHistory rfl who)
          hchoiceLeft)
        (strategy
          (SourceReachableInfoState.ofHistory (L := L)
            rightHistory rfl who)
          hchoiceRight) := by
  dsimp
  intro hchoiceLeft hchoiceRight
  exact
    query_heq_of_sameHistoryKnowledge (L := L) strategy
      (SourceHistoryPoint.commitSecret_noninterference (L := L)
        hne prefixRun left right hleft hright)
      rfl rfl hchoiceLeft hchoiceRight

end SourceStrategy

end Vegas
