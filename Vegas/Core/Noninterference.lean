/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.Epistemic

/-!
# Value non-interference

The epistemic interface in `Vegas.Core.Epistemic` says what a player *can* see.
This module proves the complementary *non-interference* statement: what a player
cannot see does not flow to what they know. Concretely, the value a player
commits in secret is invisible to everyone else — not merely hidden as a value,
but strategically and epistemically inert.

The cornerstone is `commitSecret_noninterference`: at a fixed program point,
replacing the secret bound for `owner` with any other value of the same type
yields a configuration that is *epistemically identical* (`SameKnowledge`) for
every other player `who ≠ owner`. From it, anything `who` knows is invariant
under the secret (`Knows.secret_invariant`).

This is the value-side companion to the schedule-side story in
`Vegas.Core.Schedule`: there the *control* trajectory is value-independent; here
a *hidden value* is observation-independent. Together they isolate exactly what a
player's knowledge depends on — the public/own data and the program point — and
nothing else. The order-only views (`SourcePlayerEvent.otherCommit`) already
record another player's commit as a bare occurrence with no value; this theorem
is the semantic justification that the dropped value was genuinely unobservable.
-/

namespace Vegas

namespace SourceConfig

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- **Value non-interference for secrets.** At a fixed program point just after
`owner` commits, the local view of any other player `who ≠ owner` is independent
of the committed value: the two configurations differing only in `owner`'s secret
are epistemically identical for `who`.

The proof is the semantic content of sealing: a binding the viewer cannot see is
never reached by `VEnv.toView`, so the value placed there is irrelevant to the
projected view. -/
theorem commitSecret_noninterference
    {who owner : P} (hne : who ≠ owner)
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {tail : VegasCore P L ((x, .sealed owner b) :: Γ)}
    {env : VEnv L Γ} (v v' : L.Val b) :
    SameKnowledge (L := L) who
      { ctx := (x, .sealed owner b) :: Γ, env := VEnv.cons v env, cont := tail }
      { ctx := (x, .sealed owner b) :: Γ, env := VEnv.cons v' env,
        cont := tail } := by
  rw [SameKnowledge.same_point_iff_visibleEnv_eq]
  funext x' τ' h'
  have howner := viewVCtx_owner h'
  unfold VEnv.toView
  generalize h'.ofViewVCtx = W
  cases W with
  | here =>
      -- the head is `owner`'s secret, which `who` cannot own
      rw [BindTy.owner_sealed] at howner
      rcases howner with h | h
      · exact absurd h (Option.some_ne_none owner)
      · exact absurd (Option.some.inj h).symm hne
  | there W' => rfl

/-- Anything `who` knows is invariant under replacing another player's secret:
if `who` knows `event` after `owner` commits `v`, they know it after `owner`
commits any `v'`. -/
theorem Knows.secret_invariant
    {who owner : P} (hne : who ≠ owner)
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {tail : VegasCore P L ((x, .sealed owner b) :: Γ)}
    {env : VEnv L Γ} {v v' : L.Val b}
    {event : Set (SourceConfig P L)}
    (hknow :
      Knows (L := L) who
        { ctx := (x, .sealed owner b) :: Γ, env := VEnv.cons v env,
          cont := tail } event) :
    Knows (L := L) who
      { ctx := (x, .sealed owner b) :: Γ, env := VEnv.cons v' env,
        cont := tail } event :=
  hknow.of_sameKnowledge (commitSecret_noninterference hne v v')

end SourceConfig

namespace SourceHistoryPoint

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- **History-level value non-interference for another player's commit.**

If a shared source prefix reaches a commit point for `owner`, then replacing the
committed secret by another legal value yields indistinguishable source histories
for every other player `who`. The visible trace records the same
`otherCommit`, and the endpoint configurations are equal in `who`'s source-local
view by `SourceConfig.commitSecret_noninterference`.

This is the source-side block lemma needed when one frontier round is replayed
sequentially: hidden choices made earlier in the block cannot change later
source-local strategy queries for other players. -/
theorem commitSecret_noninterference
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
    SameHistoryKnowledge (L := L) who
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
              (LStep.commit guard tail right hright)) } := by
  have hcurrent :
      SourceConfig.localView
          { ctx := (x, .sealed owner b) :: Γ
            env := VEnv.cons left env
            cont := tail } who =
        SourceConfig.localView
          { ctx := (x, .sealed owner b) :: Γ
            env := VEnv.cons right env
            cont := tail } who := by
    simpa [SourceConfig.SameKnowledge, Math.ViewKnowledge.Same] using
      SourceConfig.commitSecret_noninterference (L := L) hne left right
  have htrace :
      SourceConfig.playerTraceView (L := L) who
          (labels ++ [Label.commit x owner left]) =
        SourceConfig.playerTraceView (L := L) who
          (labels ++ [Label.commit x owner right]) := by
    simp [SourceConfig.playerTraceView,
      Label.playerEvent_commit_other_value_irrel (L := L) hne x left right]
  unfold SameHistoryKnowledge Math.ViewKnowledge.Same
  simp [SourceHistoryPoint.localHistoryView, htrace, hcurrent]

end SourceHistoryPoint

end Vegas
