/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.StrategicNoninterference

/-!
# Source/frontier block information facts

Frontier rounds are simultaneous, while source replay consumes ready commits in
source order.  The information theorem needed for that serialization is that
another player's sealed value does not perturb a later source-local strategy
query.
-/

namespace Vegas

namespace SourceFrontier
namespace Information

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- History-level hidden-value noninterference for a source commit block. -/
theorem hiddenCommit_sameHistory
    {who owner : P} (hne : who ≠ owner)
    {start : SourceConfig P L} {labels : List (Label P L)}
    {Γ : VCtx P L} {env : VEnv L Γ}
    {x : VarId} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
    {tail : VegasCore P L ((x, .sealed owner b) :: Γ)}
    (prefixRun :
      SourceConfig.LabeledStar start labels
        { ctx := Γ, env := env, cont := VegasCore.commit x owner guard tail })
    (left right : L.Val b)
    (hleft : evalGuard (Player := P) (L := L) guard left
      ((env.toView owner).eraseEnv) = true)
    (hright : evalGuard (Player := P) (L := L) guard right
      ((env.toView owner).eraseEnv) = true) :
    SourceHistoryPoint.SameHistoryKnowledge (L := L) who
      { start := start
        labels := labels ++ [Label.commit x owner left]
        current :=
          { ctx := (x, .sealed owner b) :: Γ
            env := VEnv.cons left env
            cont := tail }
        run :=
          SourceConfig.LabeledStar.trans prefixRun
            (SourceConfig.LabeledStar.single
              (LStep.commit guard tail left hleft)) }
      { start := start
        labels := labels ++ [Label.commit x owner right]
        current :=
          { ctx := (x, .sealed owner b) :: Γ
            env := VEnv.cons right env
            cont := tail }
        run :=
          SourceConfig.LabeledStar.trans prefixRun
            (SourceConfig.LabeledStar.single
              (LStep.commit guard tail right hright)) } :=
  SourceHistoryPoint.commitSecret_noninterference
    (L := L) hne prefixRun left right hleft hright

/-- Source strategy queries are invariant under replacing another player's
hidden value in a source-order block. -/
theorem hiddenCommit_strategyQuery_heq
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
          hchoiceRight) :=
  SourceStrategy.commitSecret_query_heq
    (L := L) hne strategy prefixRun left right hleft hright

end Information
end SourceFrontier

end Vegas
