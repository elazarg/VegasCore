/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.SmallStep
import Vegas.Core.Scope
import Math.Knowledge

/-!
# Source-level epistemic specification

This module defines the source-facing epistemic interface for `VegasCore`.
It deliberately stays above EventGraph and below game-theoretic solution
concepts.

The key design is:

* knowledge is induced by a player-local view, not postulated directly;
* the local view has an order/program-point component and a value component;
* raw `SmallStep.Label`s remain instrumentation, but can be projected to
  player-visible source events when reasoning about source traces.

Later graph adequacy statements should say that compiled graph/frontier
observations reproduce these source-local views at the chosen strategic
boundary.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## Program points and choice points -/

/-- The source program point of an execution: the current visibility context
and remaining continuation. This is the source-order component that all players
are allowed to know at the source semantic level. -/
structure SourceProgramPoint (P : Type) [DecidableEq P] (L : IExpr) where
  ctx : VCtx P L
  cont : VegasCore P L ctx

/-- Coarse kind of a source program point. This is useful for talking about
where player choices occur without exposing the full continuation. -/
inductive SourcePointKind (P : Type) where
  | terminal
  | sample
  | commit (who : P)
  | reveal (who : P)

namespace SourceProgramPoint

variable (point : SourceProgramPoint P L)

/-- Coarse control kind of a source program point. -/
def kind : SourcePointKind P :=
  match point.cont with
  | .ret _ => .terminal
  | .sample _ _ _ => .sample
  | .commit _ who _ _ => .commit who
  | .reveal _ who _ _ _ => .reveal who

/-- The active strategic player at this source point, if any. In core Vegas,
only `commit` is a player choice; `sample` is nature and `reveal` is
deterministic disclosure. -/
def activePlayer? : Option P :=
  match point.kind with
  | .commit who => some who
  | _ => none

/-- This source program point is a choice point for `who`. -/
def IsChoiceFor (who : P) : Prop :=
  point.activePlayer? = some who

@[simp] theorem activePlayer?_ret
    {Γ : VCtx P L}
    (payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)) :
    (SourceProgramPoint.activePlayer?
      ({ ctx := Γ, cont := VegasCore.ret payoffs } :
        SourceProgramPoint P L)) = none := rfl

@[simp] theorem activePlayer?_sample
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    (dist : L.DistExpr (erasePubVCtx Γ) b)
    (tail : VegasCore P L ((x, .pub b) :: Γ)) :
    (SourceProgramPoint.activePlayer?
      ({ ctx := Γ, cont := VegasCore.sample x dist tail } :
        SourceProgramPoint P L)) = none := rfl

@[simp] theorem activePlayer?_commit
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    (guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((x, .sealed who b) :: Γ)) :
    (SourceProgramPoint.activePlayer?
      ({ ctx := Γ, cont := VegasCore.commit x who guard tail } :
        SourceProgramPoint P L)) = some who := rfl

@[simp] theorem activePlayer?_reveal
    {Γ : VCtx P L} {y x : VarId} {who : P} {b : L.Ty}
    (hx : VHasVar Γ x (.sealed who b))
    (tail : VegasCore P L ((y, .pub b) :: Γ)) :
    (SourceProgramPoint.activePlayer?
      ({ ctx := Γ, cont := VegasCore.reveal y who x hx tail } :
        SourceProgramPoint P L)) = none := rfl

end SourceProgramPoint

namespace SourceConfig

/-- The source program point of a concrete source configuration. -/
def programPoint (cfg : SourceConfig P L) : SourceProgramPoint P L where
  ctx := cfg.ctx
  cont := cfg.cont

/-- Coarse control kind of the source configuration's program point. -/
def pointKind (cfg : SourceConfig P L) : SourcePointKind P :=
  cfg.programPoint.kind

/-- Active strategic player at this source configuration, if any. -/
def activePlayer? (cfg : SourceConfig P L) : Option P :=
  cfg.programPoint.activePlayer?

/-- This source configuration is a choice point for `who`. -/
def IsChoiceFor (cfg : SourceConfig P L) (who : P) : Prop :=
  cfg.activePlayer? = some who

end SourceConfig

/-! ## Value visibility -/

/-- A source binding is visible to `who` in context `Γ` when it appears in
`who`'s projected source view. -/
def BindingVisible (who : P) (Γ : VCtx P L)
    (x : VarId) (τ : BindTy P L) : Prop :=
  Nonempty (VHasVar (viewVCtx who Γ) x τ)

/-- Public head bindings are visible to every player. -/
theorem BindingVisible.pub_head
    (who : P) (Γ : VCtx P L) (x : VarId) (τ : L.Ty) :
    BindingVisible (L := L) who ((x, .pub τ) :: Γ) x (.pub τ) := by
  exact ⟨VHasVar.here⟩

/-- A freshly committed sealed head binding is visible to its owner. -/
theorem BindingVisible.sealed_self_head
    (owner : P) (Γ : VCtx P L) (x : VarId) (τ : L.Ty) :
    BindingVisible (L := L) owner ((x, .sealed owner τ) :: Γ)
      x (.sealed owner τ) := by
  simpa [BindingVisible, viewVCtx, canSee, Visibility.canSee] using
    (show
      Nonempty
        (VHasVar ((x, .sealed owner τ) :: viewVCtx owner Γ)
          x (.sealed owner τ)) from
        ⟨VHasVar.here⟩)

/-- A sealed binding owned by another player is never visible in `who`'s
projected source view. This follows from `viewVCtx_owner`: every binding in a
player's view is either public or sealed to that player. -/
theorem BindingVisible.not_sealed_other
    {who owner : P} (hneq : who ≠ owner)
    {Γ : VCtx P L} {x : VarId} (τ : L.Ty) :
    ¬ BindingVisible (L := L) who Γ x (.sealed owner τ) := by
  intro h
  rcases h with ⟨hvar⟩
  rcases viewVCtx_owner hvar with hpublic | howned
  · simp [BindTy.owner] at hpublic
  · have howner : owner = who := by
      simpa [BindTy.owner] using howned
    exact hneq howner.symm

/-! ## Source choice menus -/

/-- The legal value set for a source commit guard at the current environment.
This is the source-level strategic menu at a commit point before a strategy
chooses a distribution over legal values. -/
def SourceCommitMenu
    (who : P) {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    (guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (env : VEnv L Γ) : Set (L.Val b) :=
  { action |
    evalGuard (Player := P) (L := L) guard action
      (VEnv.eraseEnv (VEnv.toView who env)) = true }

/-- Commit menus are determined by the acting player's visible source
environment. -/
theorem SourceCommitMenu.eq_of_visibleEnv_eq
    {who : P} {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {left right : VEnv L Γ}
    (hview : VEnv.toView who left = VEnv.toView who right) :
    SourceCommitMenu (L := L) who guard left =
      SourceCommitMenu (L := L) who guard right := by
  ext action
  simp [SourceCommitMenu, hview]

/-- A value is legal in the source commit menu exactly when it can fire the
corresponding labeled source commit step. -/
theorem SourceCommitMenu.mem_iff_lstep_commit
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((x, .sealed who b) :: Γ)}
    {env : VEnv L Γ} {value : L.Val b} :
    value ∈ SourceCommitMenu (L := L) who guard env ↔
      LStep
        { ctx := Γ, env := env,
          cont := VegasCore.commit x who guard tail }
        (Label.commit x who value)
        { ctx := (x, .sealed who b) :: Γ, env := env.cons value,
          cont := tail } := by
  constructor
  · intro hguard
    exact LStep.commit guard tail value hguard
  · intro hstep
    cases hstep with
    | commit R k v hguard => exact hguard

namespace SourceConfig

/-- The value component of player `who`'s source-local view at `cfg`. -/
def visibleEnv (cfg : SourceConfig P L) (who : P) :
    VEnv L (viewVCtx who cfg.ctx) :=
  VEnv.toView who cfg.env

end SourceConfig

/-! ## Local views and knowledge -/

/-- Player-local source view: source-order/program-point information plus the
values visible to the player at that point. Equality of this structure is the
source-level indistinguishability relation. -/
structure SourceLocalView (P : Type) [DecidableEq P] (L : IExpr) (who : P) where
  point : SourceProgramPoint P L
  visibleEnv : VEnv L (viewVCtx who point.ctx)

namespace SourceConfig

/-- Player `who`'s complete source-local view of a configuration. -/
def localView (cfg : SourceConfig P L) (who : P) :
    SourceLocalView P L who where
  point := cfg.programPoint
  visibleEnv := cfg.visibleEnv who

@[simp] theorem localView_point (cfg : SourceConfig P L) (who : P) :
    (cfg.localView who).point = cfg.programPoint := rfl

@[simp] theorem localView_visibleEnv (cfg : SourceConfig P L) (who : P) :
    (cfg.localView who).visibleEnv = cfg.visibleEnv who := rfl

/-
The next declarations are source-level names for the generic `ViewKnowledge`
construction instantiated with `fun cfg => cfg.localView who`. The
source-specific content starts at the projection lemmas such as
`SameKnowledge.programPoint_eq`.
-/

/-- Source-level indistinguishability for a player. Two configurations are
epistemically identical for `who` when their source-local views are equal. -/
def SameKnowledge (who : P)
    (left right : SourceConfig P L) : Prop :=
  Math.ViewKnowledge.Same
    (fun cfg : SourceConfig P L => cfg.localView who) left right

theorem SameKnowledge.refl (who : P) (cfg : SourceConfig P L) :
    SameKnowledge (L := L) who cfg cfg :=
  Math.ViewKnowledge.Same.refl
    (fun other : SourceConfig P L => other.localView who) cfg

theorem SameKnowledge.symm {who : P} {left right : SourceConfig P L}
    (h : SameKnowledge (L := L) who left right) :
    SameKnowledge (L := L) who right left :=
  Math.ViewKnowledge.Same.symm h

theorem SameKnowledge.trans {who : P}
    {a b c : SourceConfig P L}
    (hab : SameKnowledge (L := L) who a b)
    (hbc : SameKnowledge (L := L) who b c) :
    SameKnowledge (L := L) who a c :=
  Math.ViewKnowledge.Same.trans hab hbc

/-- Equality of source-local views implies equality of source program points.
Thus source-level knowledge includes the allowed source-order/program-point
component. -/
theorem SameKnowledge.programPoint_eq {who : P}
    {left right : SourceConfig P L}
    (h : SameKnowledge (L := L) who left right) :
    left.programPoint = right.programPoint :=
  congrArg SourceLocalView.point h

/-- Source knowledge equality preserves coarse program-point kind. -/
theorem SameKnowledge.pointKind_eq {who : P}
    {left right : SourceConfig P L}
    (h : SameKnowledge (L := L) who left right) :
    left.pointKind = right.pointKind := by
  exact congrArg SourceProgramPoint.kind h.programPoint_eq

/-- Source knowledge equality preserves the active strategic player. -/
theorem SameKnowledge.activePlayer?_eq {who : P}
    {left right : SourceConfig P L}
    (h : SameKnowledge (L := L) who left right) :
    left.activePlayer? = right.activePlayer? := by
  exact congrArg SourceProgramPoint.activePlayer? h.programPoint_eq

/-- Source knowledge equality preserves whether a given player is at a choice
point. -/
theorem SameKnowledge.isChoiceFor_iff {observer player : P}
    {left right : SourceConfig P L}
    (h : SameKnowledge (L := L) observer left right) :
    left.IsChoiceFor player ↔ right.IsChoiceFor player := by
  unfold IsChoiceFor
  rw [h.activePlayer?_eq]

/-- If two configurations have the same source program point and visible
environment for `who`, then they have the same source knowledge for `who`. -/
theorem SameKnowledge.of_same_point
    {Γ : VCtx P L} {cont : VegasCore P L Γ}
    {left right : VEnv L Γ} {who : P}
    (hview : VEnv.toView who left = VEnv.toView who right) :
    SameKnowledge (L := L) who
      { ctx := Γ, env := left, cont := cont }
      { ctx := Γ, env := right, cont := cont } := by
  simp [SameKnowledge, Math.ViewKnowledge.Same, localView, visibleEnv,
    programPoint, hview]

/-- At a fixed source program point, source knowledge equality is exactly
equality of the player's visible environment. -/
theorem SameKnowledge.same_point_iff_visibleEnv_eq
    {Γ : VCtx P L} {cont : VegasCore P L Γ}
    {left right : VEnv L Γ} {who : P} :
    SameKnowledge (L := L) who
        { ctx := Γ, env := left, cont := cont }
        { ctx := Γ, env := right, cont := cont } ↔
      VEnv.toView who left = VEnv.toView who right := by
  constructor
  · intro h
    simpa [SameKnowledge, Math.ViewKnowledge.Same, localView, visibleEnv,
      programPoint] using h
  · exact SameKnowledge.of_same_point (L := L)

/-- At a fixed source program point, a visible binding has the same visible
value across configurations that are indistinguishable to the player. -/
theorem SameKnowledge.visibleValue_eq
    {Γ : VCtx P L} {cont : VegasCore P L Γ}
    {left right : VEnv L Γ} {who : P}
    {x : VarId} {τ : BindTy P L}
    (hvisible : BindingVisible (L := L) who Γ x τ)
    (h :
      SameKnowledge (L := L) who
        { ctx := Γ, env := left, cont := cont }
        { ctx := Γ, env := right, cont := cont }) :
    (VEnv.toView who left) x τ hvisible.some =
      (VEnv.toView who right) x τ hvisible.some := by
  rw [SameKnowledge.same_point_iff_visibleEnv_eq.mp h]

/-- At the same source commit point, the acting player's legal value menu is
knowledge-local. -/
theorem SameKnowledge.commitMenu_eq
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((x, .sealed who b) :: Γ)}
    {left right : VEnv L Γ}
    (h :
      SameKnowledge (L := L) who
        { ctx := Γ, env := left, cont := VegasCore.commit x who guard tail }
        { ctx := Γ, env := right, cont := VegasCore.commit x who guard tail }) :
    SourceCommitMenu (L := L) who guard left =
      SourceCommitMenu (L := L) who guard right := by
  exact
    SourceCommitMenu.eq_of_visibleEnv_eq
      (SameKnowledge.same_point_iff_visibleEnv_eq.mp h)

/-- The knowledge cell induced by `who`'s source-local view at `cfg`. -/
def KnowledgeCell (who : P) (cfg : SourceConfig P L) :
    Set (SourceConfig P L) :=
  Math.ViewKnowledge.Cell
    (fun other : SourceConfig P L => other.localView who) cfg

@[simp] theorem mem_KnowledgeCell_iff
    (who : P) (cfg other : SourceConfig P L) :
    other ∈ KnowledgeCell (L := L) who cfg ↔
      SameKnowledge (L := L) who cfg other := by
  rfl

/-- The current configuration belongs to its own knowledge cell. -/
theorem KnowledgeCell.self (who : P) (cfg : SourceConfig P L) :
    cfg ∈ KnowledgeCell (L := L) who cfg :=
  Math.ViewKnowledge.Cell.self
    (fun other : SourceConfig P L => other.localView who) cfg

/-- Configurations with the same knowledge have the same knowledge cell. -/
theorem KnowledgeCell.eq_of_sameKnowledge {who : P}
    {left right : SourceConfig P L}
    (h : SameKnowledge (L := L) who left right) :
    KnowledgeCell (L := L) who left = KnowledgeCell (L := L) who right :=
  Math.ViewKnowledge.Cell.eq_of_same h

/-- At a fixed source program point, visible binding values are constant across
the player's source-local knowledge cell. -/
theorem KnowledgeCell.visibleValue_eq
    {Γ : VCtx P L} {cont : VegasCore P L Γ}
    {left right : VEnv L Γ} {who : P}
    {x : VarId} {τ : BindTy P L}
    (hvisible : BindingVisible (L := L) who Γ x τ)
    (hcell :
      { ctx := Γ, env := right, cont := cont } ∈
        KnowledgeCell (L := L) who
          { ctx := Γ, env := left, cont := cont }) :
    (VEnv.toView who left) x τ hvisible.some =
      (VEnv.toView who right) x τ hvisible.some :=
  SameKnowledge.visibleValue_eq hvisible hcell

/-- Player `who` knows event `event` at `cfg` when it holds throughout the
source-local knowledge cell. -/
def Knows (who : P) (cfg : SourceConfig P L)
    (event : Set (SourceConfig P L)) : Prop :=
  Math.ViewKnowledge.Knows
    (fun other : SourceConfig P L => other.localView who) cfg event

/-- Veridicality of source knowledge: known events are true at the current
configuration. -/
theorem Knows.truth {who : P} {cfg : SourceConfig P L}
    {event : Set (SourceConfig P L)}
    (h : Knows (L := L) who cfg event) :
    event cfg :=
  Math.ViewKnowledge.Knows.truth h

/-- Knowledge is monotone in the event. -/
theorem Knows.mono {who : P} {cfg : SourceConfig P L}
    {event stronger : Set (SourceConfig P L)}
    (h : Knows (L := L) who cfg event)
    (hsub : ∀ {other}, event other → stronger other) :
    Knows (L := L) who cfg stronger :=
  Math.ViewKnowledge.Knows.mono h hsub

/-- If an event is known at a configuration, then every indistinguishable
configuration also knows it. -/
theorem Knows.of_sameKnowledge {who : P}
    {cfg other : SourceConfig P L} {event : Set (SourceConfig P L)}
    (hknow : Knows (L := L) who cfg event)
    (hsame : SameKnowledge (L := L) who cfg other) :
    Knows (L := L) who other event :=
  Math.ViewKnowledge.Knows.of_same hknow hsame

/-- A player knows the current source program point under the source
epistemic interface. -/
theorem Knows.programPoint_eq (who : P) (cfg : SourceConfig P L) :
    Knows (L := L) who cfg
      { other | other.programPoint = cfg.programPoint } := by
  intro other hcell
  exact (SameKnowledge.programPoint_eq hcell).symm

/-- A player knows the coarse source point kind under the source epistemic
interface. -/
theorem Knows.pointKind_eq (who : P) (cfg : SourceConfig P L) :
    Knows (L := L) who cfg
      { other | other.pointKind = cfg.pointKind } := by
  intro other hcell
  exact (SameKnowledge.pointKind_eq hcell).symm

/-- A player knows the active strategic player, if any, under the source
epistemic interface. -/
theorem Knows.activePlayer?_eq (who : P) (cfg : SourceConfig P L) :
    Knows (L := L) who cfg
      { other | other.activePlayer? = cfg.activePlayer? } := by
  intro other hcell
  exact (SameKnowledge.activePlayer?_eq hcell).symm

/-- A player knows whether any fixed player is currently at a source choice
point. -/
theorem Knows.isChoiceFor_iff
    (observer player : P) (cfg : SourceConfig P L) :
    Knows (L := L) observer cfg
      { other | other.IsChoiceFor player ↔ cfg.IsChoiceFor player } := by
  intro other hcell
  exact Iff.symm (SameKnowledge.isChoiceFor_iff hcell)

/-- Positive introspection for source knowledge. -/
theorem Knows.positive_introspection {who : P} {cfg : SourceConfig P L}
    {event : Set (SourceConfig P L)}
    (hknow : Knows (L := L) who cfg event) :
    Knows (L := L) who cfg
      { other | Knows (L := L) who other event } :=
  Math.ViewKnowledge.Knows.positive_introspection hknow

/-- Negative introspection for source knowledge. -/
theorem Knows.negative_introspection {who : P} {cfg : SourceConfig P L}
    {event : Set (SourceConfig P L)}
    (hnot : ¬ Knows (L := L) who cfg event) :
    Knows (L := L) who cfg
      { other | ¬ Knows (L := L) who other event } :=
  Math.ViewKnowledge.Knows.negative_introspection hnot

end SourceConfig

/-! ## Player-visible source events -/

/-- Player-visible projection of an instrumented source step label.

For another player's commit, the event records that the commitment occurred,
but not the committed value. Samples and reveals are public; a player's own
commit records the chosen value. This is a source-level order/value projection
for labeled traces, not an implementation scheduler observation. -/
inductive SourcePlayerEvent (P : Type) (L : IExpr) where
  | sample (x : VarId) {b : L.Ty} (value : L.Val b)
  | ownCommit (x : VarId) (owner : P) {b : L.Ty} (value : L.Val b)
  | otherCommit (x : VarId) (owner : P)
  | reveal (y : VarId) (owner : P) (x : VarId) {b : L.Ty}
      (value : L.Val b)

namespace SourcePlayerEvent

/-- Coarse event kind, forgetting all values. -/
inductive Kind (P : Type) where
  | sample
  | ownCommit (owner : P)
  | otherCommit (owner : P)
  | reveal (owner : P)

/-- The order-only part of a player-visible source event. -/
def kind : SourcePlayerEvent P L → Kind P
  | .sample .. => .sample
  | .ownCommit _ owner _ => .ownCommit owner
  | .otherCommit _ owner => .otherCommit owner
  | .reveal _ owner _ _ => .reveal owner

omit [DecidableEq P] in
@[simp] theorem kind_sample
    (x : VarId) {b : L.Ty} (value : L.Val b) :
    kind (P := P) (SourcePlayerEvent.sample x value) =
      Kind.sample := rfl

omit [DecidableEq P] in
@[simp] theorem kind_ownCommit
    (x : VarId) (owner : P) {b : L.Ty} (value : L.Val b) :
    kind (SourcePlayerEvent.ownCommit (L := L) x owner value) =
      Kind.ownCommit owner := rfl

omit [DecidableEq P] in
@[simp] theorem kind_otherCommit
    (x : VarId) (owner : P) :
    kind (L := L) (SourcePlayerEvent.otherCommit x owner) =
      Kind.otherCommit owner := rfl

omit [DecidableEq P] in
@[simp] theorem kind_reveal
    (y : VarId) (owner : P) (x : VarId) {b : L.Ty}
    (value : L.Val b) :
    kind (SourcePlayerEvent.reveal (L := L) y owner x value) =
      Kind.reveal owner := rfl

end SourcePlayerEvent

namespace Label

/-- Project a full instrumented source label to what player `who` may observe
at the source semantic level. -/
def playerEvent (who : P) : Label P L → SourcePlayerEvent P L
  | .sample x value => .sample x value
  | .commit x owner value =>
      if who = owner then
        .ownCommit x owner value
      else
        .otherCommit x owner
  | .reveal y owner x value => .reveal y owner x value

/-- Order-only source observation of an instrumented label. This forgets all
values, including values visible in the full player event. -/
def playerEventKind (who : P) (label : Label P L) :
    SourcePlayerEvent.Kind P :=
  (playerEvent (L := L) who label).kind

@[simp] theorem playerEvent_sample
    (who : P) (x : VarId) {b : L.Ty} (value : L.Val b) :
    playerEvent (L := L) who (Label.sample x value) =
      SourcePlayerEvent.sample x value := rfl

@[simp] theorem playerEvent_commit_self
    (who : P) (x : VarId) {b : L.Ty} (value : L.Val b) :
    playerEvent (L := L) who (Label.commit x who value) =
      SourcePlayerEvent.ownCommit x who value := by
  simp [playerEvent]

@[simp] theorem playerEvent_commit_other
    {who owner : P} (hneq : who ≠ owner)
    (x : VarId) {b : L.Ty} (value : L.Val b) :
    playerEvent (L := L) who (Label.commit x owner value) =
      SourcePlayerEvent.otherCommit x owner := by
  simp [playerEvent, hneq]

@[simp] theorem playerEvent_reveal
    (who : P) (y : VarId) (owner : P) (x : VarId)
    {b : L.Ty} (value : L.Val b) :
    playerEvent (L := L) who (Label.reveal y owner x value) =
      SourcePlayerEvent.reveal y owner x value := rfl

/-- Other-player commit values are erased by the player-visible event
projection. The occurrence and owner remain visible; the value does not. -/
theorem playerEvent_commit_other_value_irrel
    {who owner : P} (hneq : who ≠ owner)
    (x : VarId) {b : L.Ty} (left right : L.Val b) :
    playerEvent (L := L) who (Label.commit x owner left) =
      playerEvent (L := L) who (Label.commit x owner right) := by
  simp [playerEvent_commit_other (L := L) hneq]

/-- The order-only view of a commit event forgets the committed value, even for
the committing player. -/
theorem kind_playerEvent_commit_value_irrel
    (who owner : P) (x : VarId) {b : L.Ty}
    (left right : L.Val b) :
    SourcePlayerEvent.kind
        (playerEvent (L := L) who (Label.commit x owner left)) =
      SourcePlayerEvent.kind
        (playerEvent (L := L) who (Label.commit x owner right)) := by
  by_cases h : who = owner
  · subst h
    simp [playerEvent_commit_self]
  · simp [playerEvent_commit_other (L := L) h]

@[simp] theorem playerEventKind_sample
    (who : P) (x : VarId) {b : L.Ty} (value : L.Val b) :
    playerEventKind (L := L) who (Label.sample x value) =
      SourcePlayerEvent.Kind.sample := rfl

@[simp] theorem playerEventKind_commit_self
    (who : P) (x : VarId) {b : L.Ty} (value : L.Val b) :
    playerEventKind (L := L) who (Label.commit x who value) =
      SourcePlayerEvent.Kind.ownCommit who := by
  simp [playerEventKind]

@[simp] theorem playerEventKind_commit_other
    {who owner : P} (hneq : who ≠ owner)
    (x : VarId) {b : L.Ty} (value : L.Val b) :
    playerEventKind (L := L) who (Label.commit x owner value) =
      SourcePlayerEvent.Kind.otherCommit owner := by
  simp [playerEventKind, playerEvent_commit_other (L := L) hneq]

@[simp] theorem playerEventKind_reveal
    (who : P) (y : VarId) (owner : P) (x : VarId)
    {b : L.Ty} (value : L.Val b) :
    playerEventKind (L := L) who (Label.reveal y owner x value) =
      SourcePlayerEvent.Kind.reveal owner := rfl

/-- Order-only source observation of a commit is independent of the committed
value. -/
theorem playerEventKind_commit_value_irrel
    (who owner : P) (x : VarId) {b : L.Ty}
    (left right : L.Val b) :
    playerEventKind (L := L) who (Label.commit x owner left) =
      playerEventKind (L := L) who (Label.commit x owner right) :=
  kind_playerEvent_commit_value_irrel (L := L) who owner x left right

/-- Order-only source observation of a sample forgets the sampled value. -/
theorem playerEventKind_sample_value_irrel
    (who : P) (x : VarId) {b : L.Ty}
    (left right : L.Val b) :
    playerEventKind (L := L) who (Label.sample x left) =
      playerEventKind (L := L) who (Label.sample x right) := rfl

/-- Order-only source observation of a reveal forgets the revealed value. -/
theorem playerEventKind_reveal_value_irrel
    (who : P) (y : VarId) (owner : P) (x : VarId)
    {b : L.Ty} (left right : L.Val b) :
    playerEventKind (L := L) who (Label.reveal y owner x left) =
      playerEventKind (L := L) who (Label.reveal y owner x right) := rfl

end Label

namespace SourceConfig

/-- Labeled reflexive-transitive source execution. The list is chronological. -/
inductive LabeledStar :
    SourceConfig P L → List (Label P L) → SourceConfig P L → Prop where
  | refl (cfg : SourceConfig P L) : LabeledStar cfg [] cfg
  | cons {a b c : SourceConfig P L} {label : Label P L}
      {labels : List (Label P L)} :
      LStep a label b → LabeledStar b labels c →
        LabeledStar a (label :: labels) c

namespace LabeledStar

/-- Forgetting labels from a labeled source run recovers an ordinary source
run. -/
theorem toStar {start finish : SourceConfig P L}
    {labels : List (Label P L)}
    (h : LabeledStar start labels finish) :
    SmallStep.Star start finish := by
  induction h with
  | refl cfg => exact SmallStep.Star.refl cfg
  | cons hstep _ ih =>
      exact SmallStep.Star.trans
        (SmallStep.Star.single hstep.toSmallStep) ih

/-- An empty labeled run leaves the configuration unchanged. -/
theorem eq_of_nil {start finish : SourceConfig P L}
    (h : LabeledStar start [] finish) : start = finish := by
  cases h
  rfl

/-- A single labeled source step is a one-label source run. -/
theorem single {start finish : SourceConfig P L} {label : Label P L}
    (h : LStep start label finish) :
    LabeledStar start [label] finish :=
  LabeledStar.cons h (LabeledStar.refl finish)

/-- Labeled source runs compose by concatenating their label traces. -/
theorem trans {a b c : SourceConfig P L}
    {left right : List (Label P L)}
    (hab : LabeledStar a left b) (hbc : LabeledStar b right c) :
    LabeledStar a (left ++ right) c := by
  induction hab with
  | refl _ => simpa using hbc
  | cons hstep _ ih =>
      exact LabeledStar.cons hstep (ih hbc)

end LabeledStar

/-! ## Player-visible trace projections -/

/-- Player `who`'s visible projection of a labeled source trace. -/
def playerTraceView (who : P) (labels : List (Label P L)) :
    List (SourcePlayerEvent P L) :=
  labels.map (Label.playerEvent (L := L) who)

/-- Order-only projection of player `who`'s visible source trace. -/
def playerOrderTraceView (who : P) (labels : List (Label P L)) :
    List (SourcePlayerEvent.Kind P) :=
  labels.map (Label.playerEventKind (L := L) who)

end SourceConfig

/-! ## Source histories and history-local knowledge -/

/-- A realized labeled source history from some start configuration to its
current endpoint. This packages the proof that the label trace is executable,
so later adequacy theorems can quantify over source histories rather than raw
lists of labels. -/
structure SourceHistoryPoint (P : Type) [DecidableEq P] (L : IExpr) where
  start : SourceConfig P L
  labels : List (Label P L)
  current : SourceConfig P L
  run : SourceConfig.LabeledStar start labels current

namespace SourceHistoryPoint

/-- The empty source history at a configuration. -/
def refl (cfg : SourceConfig P L) : SourceHistoryPoint P L where
  start := cfg
  labels := []
  current := cfg
  run := SourceConfig.LabeledStar.refl cfg

/-- Extend a source history by one labeled step. -/
def snoc (history : SourceHistoryPoint P L)
    {next : SourceConfig P L} {label : Label P L}
    (step : LStep history.current label next) :
    SourceHistoryPoint P L where
  start := history.start
  labels := history.labels ++ [label]
  current := next
  run :=
    SourceConfig.LabeledStar.trans history.run
      (SourceConfig.LabeledStar.single step)

/-- Forgetting labels from a source history gives an ordinary source run. -/
theorem toStar (history : SourceHistoryPoint P L) :
    SmallStep.Star history.start history.current :=
  history.run.toStar

/-- The current source program point of a history. -/
def programPoint (history : SourceHistoryPoint P L) :
    SourceProgramPoint P L :=
  history.current.programPoint

/-- The starting source program point of a history. This is the source-level
game description that is common knowledge along the history. -/
def startPoint (history : SourceHistoryPoint P L) :
    SourceProgramPoint P L :=
  history.start.programPoint

/-- The coarse source point kind at the current endpoint of a history. -/
def pointKind (history : SourceHistoryPoint P L) : SourcePointKind P :=
  history.current.pointKind

/-- The active strategic player at the current endpoint of a history, if any. -/
def activePlayer? (history : SourceHistoryPoint P L) : Option P :=
  history.current.activePlayer?

/-- This source history is currently at a choice point for `who`. -/
def IsChoiceFor (history : SourceHistoryPoint P L) (who : P) : Prop :=
  history.current.IsChoiceFor who

@[simp] theorem programPoint_current
    (history : SourceHistoryPoint P L) :
    history.programPoint = history.current.programPoint := rfl

@[simp] theorem startPoint_start
    (history : SourceHistoryPoint P L) :
    history.startPoint = history.start.programPoint := rfl

@[simp] theorem pointKind_current
    (history : SourceHistoryPoint P L) :
    history.pointKind = history.current.pointKind := rfl

@[simp] theorem activePlayer?_current
    (history : SourceHistoryPoint P L) :
    history.activePlayer? = history.current.activePlayer? := rfl

@[simp] theorem isChoiceFor_current
    (history : SourceHistoryPoint P L) (who : P) :
    history.IsChoiceFor who ↔ history.current.IsChoiceFor who := by
  rfl

end SourceHistoryPoint

/-- Player-local source history view: the common starting program point, the
visible source trace so far, and the current local view. This is the
source-level object for knowledge that remembers the game being played and
source-visible order facts. -/
structure SourceHistoryLocalView
    (P : Type) [DecidableEq P] (L : IExpr) (who : P) where
  startPoint : SourceProgramPoint P L
  traceView : List (SourcePlayerEvent P L)
  currentView : SourceLocalView P L who

/-- Order-only source history view: visible source event kinds plus current
program point, with the starting program point retained as common knowledge.
This intentionally forgets all values, including currently visible values. -/
structure SourceOrderHistoryView
    (P : Type) [DecidableEq P] (L : IExpr) (who : P) where
  startPoint : SourceProgramPoint P L
  orderTrace : List (SourcePlayerEvent.Kind P)
  currentPoint : SourceProgramPoint P L

namespace SourceOrderHistoryView

/-- Extensionality for order-only history views. -/
theorem ext {who : P}
    {left right : SourceOrderHistoryView P L who}
    (hstart : left.startPoint = right.startPoint)
    (horder : left.orderTrace = right.orderTrace)
    (hpoint : left.currentPoint = right.currentPoint) :
    left = right := by
  cases left
  cases right
  simp only at hstart horder hpoint
  cases hstart
  cases horder
  cases hpoint
  rfl

end SourceOrderHistoryView

namespace SourceHistoryLocalView

/-- Forget values from a full source-history local view, retaining only the
common starting program point, the visible order trace, and the current program
point. -/
def orderView {who : P}
    (view : SourceHistoryLocalView P L who) :
    SourceOrderHistoryView P L who where
  startPoint := view.startPoint
  orderTrace := view.traceView.map SourcePlayerEvent.kind
  currentPoint := view.currentView.point

@[simp] theorem orderView_startPoint {who : P}
    (view : SourceHistoryLocalView P L who) :
    (view.orderView).startPoint = view.startPoint := rfl

@[simp] theorem orderView_orderTrace {who : P}
    (view : SourceHistoryLocalView P L who) :
    (view.orderView).orderTrace =
      view.traceView.map SourcePlayerEvent.kind := rfl

@[simp] theorem orderView_currentPoint {who : P}
    (view : SourceHistoryLocalView P L who) :
    (view.orderView).currentPoint = view.currentView.point := rfl

end SourceHistoryLocalView

namespace SourceHistoryPoint

/-- Player `who`'s source history-local view. -/
def localHistoryView (history : SourceHistoryPoint P L) (who : P) :
    SourceHistoryLocalView P L who where
  startPoint := history.start.programPoint
  traceView := SourceConfig.playerTraceView (L := L) who history.labels
  currentView := history.current.localView who

/-- Player `who`'s order-only source history view. -/
def orderHistoryView (history : SourceHistoryPoint P L) (who : P) :
    SourceOrderHistoryView P L who :=
  (history.localHistoryView who).orderView

@[simp] theorem localHistoryView_startPoint
    (history : SourceHistoryPoint P L) (who : P) :
    (history.localHistoryView who).startPoint =
      history.start.programPoint := rfl

@[simp] theorem localHistoryView_traceView
    (history : SourceHistoryPoint P L) (who : P) :
    (history.localHistoryView who).traceView =
      SourceConfig.playerTraceView (L := L) who history.labels := rfl

@[simp] theorem localHistoryView_currentView
    (history : SourceHistoryPoint P L) (who : P) :
    (history.localHistoryView who).currentView =
      history.current.localView who := rfl

@[simp] theorem orderHistoryView_orderTrace
    (history : SourceHistoryPoint P L) (who : P) :
    (history.orderHistoryView who).orderTrace =
      SourceConfig.playerOrderTraceView (L := L) who history.labels := by
  simp [orderHistoryView, SourceHistoryLocalView.orderView,
    SourceConfig.playerOrderTraceView, SourceConfig.playerTraceView,
    Label.playerEventKind, List.map_map]

@[simp] theorem orderHistoryView_startPoint
    (history : SourceHistoryPoint P L) (who : P) :
    (history.orderHistoryView who).startPoint =
      history.start.programPoint := rfl

@[simp] theorem orderHistoryView_currentPoint
    (history : SourceHistoryPoint P L) (who : P) :
    (history.orderHistoryView who).currentPoint =
      history.current.programPoint := rfl

/-
The full-history and order-history modalities below are named instantiations
of `ViewKnowledge`, respectively with `localHistoryView` and
`orderHistoryView`. The domain-specific layer is the set of projection and
comparison lemmas connecting those views to source traces and program points.
-/

/-- Source-history indistinguishability for a player, including the
player-visible source trace and the current local view. -/
def SameHistoryKnowledge (who : P)
    (left right : SourceHistoryPoint P L) : Prop :=
  Math.ViewKnowledge.Same
    (fun history : SourceHistoryPoint P L => history.localHistoryView who)
    left right

theorem SameHistoryKnowledge.refl
    (who : P) (history : SourceHistoryPoint P L) :
    SameHistoryKnowledge (L := L) who history history :=
  Math.ViewKnowledge.Same.refl
    (fun other : SourceHistoryPoint P L => other.localHistoryView who) history

theorem SameHistoryKnowledge.symm {who : P}
    {left right : SourceHistoryPoint P L}
    (h : SameHistoryKnowledge (L := L) who left right) :
    SameHistoryKnowledge (L := L) who right left :=
  Math.ViewKnowledge.Same.symm h

theorem SameHistoryKnowledge.trans {who : P}
    {a b c : SourceHistoryPoint P L}
    (hab : SameHistoryKnowledge (L := L) who a b)
    (hbc : SameHistoryKnowledge (L := L) who b c) :
    SameHistoryKnowledge (L := L) who a c :=
  Math.ViewKnowledge.Same.trans hab hbc

/-- History knowledge equality implies endpoint source knowledge equality. -/
theorem SameHistoryKnowledge.current
    {who : P} {left right : SourceHistoryPoint P L}
    (h : SameHistoryKnowledge (L := L) who left right) :
    SourceConfig.SameKnowledge (L := L) who left.current right.current :=
  congrArg SourceHistoryLocalView.currentView h

/-- History knowledge equality fixes the starting source program point, i.e.
the game being played is common knowledge at the history level. -/
theorem SameHistoryKnowledge.startPoint_eq
    {who : P} {left right : SourceHistoryPoint P L}
    (h : SameHistoryKnowledge (L := L) who left right) :
    left.startPoint = right.startPoint := by
  change left.start.programPoint = right.start.programPoint
  exact congrArg SourceHistoryLocalView.startPoint h

/-- History knowledge equality implies equality of endpoint source program
points. -/
theorem SameHistoryKnowledge.programPoint_eq
    {who : P} {left right : SourceHistoryPoint P L}
    (h : SameHistoryKnowledge (L := L) who left right) :
    left.programPoint = right.programPoint := by
  change left.current.programPoint = right.current.programPoint
  exact (SameHistoryKnowledge.current h).programPoint_eq

/-- History knowledge equality preserves endpoint source point kind. -/
theorem SameHistoryKnowledge.pointKind_eq
    {who : P} {left right : SourceHistoryPoint P L}
    (h : SameHistoryKnowledge (L := L) who left right) :
    left.pointKind = right.pointKind := by
  change left.current.pointKind = right.current.pointKind
  exact (SameHistoryKnowledge.current h).pointKind_eq

/-- History knowledge equality preserves the endpoint active player. -/
theorem SameHistoryKnowledge.activePlayer?_eq
    {who : P} {left right : SourceHistoryPoint P L}
    (h : SameHistoryKnowledge (L := L) who left right) :
    left.activePlayer? = right.activePlayer? := by
  change left.current.activePlayer? = right.current.activePlayer?
  exact (SameHistoryKnowledge.current h).activePlayer?_eq

/-- History knowledge equality preserves whether a fixed player is at an
endpoint source choice point. -/
theorem SameHistoryKnowledge.isChoiceFor_iff
    {observer player : P} {left right : SourceHistoryPoint P L}
    (h : SameHistoryKnowledge (L := L) observer left right) :
    left.IsChoiceFor player ↔ right.IsChoiceFor player := by
  change left.current.IsChoiceFor player ↔ right.current.IsChoiceFor player
  exact (SameHistoryKnowledge.current h).isChoiceFor_iff

/-- History knowledge equality implies equality of player-visible source
traces. -/
theorem SameHistoryKnowledge.traceView_eq
    {who : P} {left right : SourceHistoryPoint P L}
    (h : SameHistoryKnowledge (L := L) who left right) :
    SourceConfig.playerTraceView (L := L) who left.labels =
      SourceConfig.playerTraceView (L := L) who right.labels :=
  congrArg SourceHistoryLocalView.traceView h

/-- History knowledge equality implies equality of order-only source traces. -/
theorem SameHistoryKnowledge.orderTrace_eq
    {who : P} {left right : SourceHistoryPoint P L}
    (h : SameHistoryKnowledge (L := L) who left right) :
    SourceConfig.playerOrderTraceView (L := L) who left.labels =
      SourceConfig.playerOrderTraceView (L := L) who right.labels := by
  have hk := congrArg (List.map SourcePlayerEvent.kind) h.traceView_eq
  simp only [SourceConfig.playerTraceView, List.map_map] at hk
  exact hk

/-- Order-history indistinguishability for a player. This is weaker than full
history knowledge: it preserves source-visible order facts and current program
point, but forgets all values. -/
def SameOrderKnowledge (who : P)
    (left right : SourceHistoryPoint P L) : Prop :=
  Math.ViewKnowledge.Same
    (fun history : SourceHistoryPoint P L => history.orderHistoryView who)
    left right

theorem SameOrderKnowledge.refl
    (who : P) (history : SourceHistoryPoint P L) :
    SameOrderKnowledge (L := L) who history history :=
  Math.ViewKnowledge.Same.refl
    (fun other : SourceHistoryPoint P L => other.orderHistoryView who) history

theorem SameOrderKnowledge.symm {who : P}
    {left right : SourceHistoryPoint P L}
    (h : SameOrderKnowledge (L := L) who left right) :
    SameOrderKnowledge (L := L) who right left :=
  Math.ViewKnowledge.Same.symm h

theorem SameOrderKnowledge.trans {who : P}
    {a b c : SourceHistoryPoint P L}
    (hab : SameOrderKnowledge (L := L) who a b)
    (hbc : SameOrderKnowledge (L := L) who b c) :
    SameOrderKnowledge (L := L) who a c :=
  Math.ViewKnowledge.Same.trans hab hbc

/-- Order-history knowledge equality implies equality of visible order traces. -/
theorem SameOrderKnowledge.orderTrace_eq
    {who : P} {left right : SourceHistoryPoint P L}
    (h : SameOrderKnowledge (L := L) who left right) :
    SourceConfig.playerOrderTraceView (L := L) who left.labels =
      SourceConfig.playerOrderTraceView (L := L) who right.labels :=
  by simpa using congrArg SourceOrderHistoryView.orderTrace h

/-- Order-history knowledge equality fixes the starting source program point,
i.e. the game being played remains common knowledge even in the order-only
view. -/
theorem SameOrderKnowledge.startPoint_eq
    {who : P} {left right : SourceHistoryPoint P L}
    (h : SameOrderKnowledge (L := L) who left right) :
    left.startPoint = right.startPoint :=
  congrArg SourceOrderHistoryView.startPoint h

/-- Order-history knowledge equality implies equality of endpoint source
program points. -/
theorem SameOrderKnowledge.programPoint_eq
    {who : P} {left right : SourceHistoryPoint P L}
    (h : SameOrderKnowledge (L := L) who left right) :
    left.programPoint = right.programPoint :=
  congrArg SourceOrderHistoryView.currentPoint h

/-- Order-history knowledge equality preserves endpoint source point kind. -/
theorem SameOrderKnowledge.pointKind_eq
    {who : P} {left right : SourceHistoryPoint P L}
    (h : SameOrderKnowledge (L := L) who left right) :
    left.pointKind = right.pointKind := by
  exact congrArg SourceProgramPoint.kind h.programPoint_eq

/-- Order-history knowledge equality preserves the endpoint active player. -/
theorem SameOrderKnowledge.activePlayer?_eq
    {who : P} {left right : SourceHistoryPoint P L}
    (h : SameOrderKnowledge (L := L) who left right) :
    left.activePlayer? = right.activePlayer? := by
  exact congrArg SourceProgramPoint.activePlayer? h.programPoint_eq

/-- Order-history knowledge equality preserves whether a fixed player is at an
endpoint source choice point. -/
theorem SameOrderKnowledge.isChoiceFor_iff
    {observer player : P} {left right : SourceHistoryPoint P L}
    (h : SameOrderKnowledge (L := L) observer left right) :
    left.IsChoiceFor player ↔ right.IsChoiceFor player := by
  change left.activePlayer? = some player ↔ right.activePlayer? = some player
  rw [h.activePlayer?_eq]

/-- Full history knowledge implies order-history knowledge. -/
theorem SameHistoryKnowledge.toOrder
    {who : P} {left right : SourceHistoryPoint P L}
    (h : SameHistoryKnowledge (L := L) who left right) :
    SameOrderKnowledge (L := L) who left right := by
  change Math.ViewKnowledge.Same
    (fun history : SourceHistoryPoint P L =>
      (history.localHistoryView who).orderView) left right
  exact Math.ViewKnowledge.Same.coarsen SourceHistoryLocalView.orderView h

/-- Histories with the same full history knowledge for every player. This is
the natural source-side quotient relation for later graph encodings. -/
def AllPlayersSameHistoryKnowledge
    (left right : SourceHistoryPoint P L) : Prop :=
  ∀ who : P, SameHistoryKnowledge (L := L) who left right

theorem AllPlayersSameHistoryKnowledge.refl
    (history : SourceHistoryPoint P L) :
    AllPlayersSameHistoryKnowledge (L := L) history history := by
  intro who
  exact SameHistoryKnowledge.refl (L := L) who history

theorem AllPlayersSameHistoryKnowledge.symm
    {left right : SourceHistoryPoint P L}
    (h : AllPlayersSameHistoryKnowledge (L := L) left right) :
    AllPlayersSameHistoryKnowledge (L := L) right left := by
  intro who
  exact SameHistoryKnowledge.symm (h who)

theorem AllPlayersSameHistoryKnowledge.trans
    {a b c : SourceHistoryPoint P L}
    (hab : AllPlayersSameHistoryKnowledge (L := L) a b)
    (hbc : AllPlayersSameHistoryKnowledge (L := L) b c) :
    AllPlayersSameHistoryKnowledge (L := L) a c := by
  intro who
  exact SameHistoryKnowledge.trans (hab who) (hbc who)

/-- Histories with the same order-only history knowledge for every player. -/
def AllPlayersSameOrderKnowledge
    (left right : SourceHistoryPoint P L) : Prop :=
  ∀ who : P, SameOrderKnowledge (L := L) who left right

theorem AllPlayersSameOrderKnowledge.refl
    (history : SourceHistoryPoint P L) :
    AllPlayersSameOrderKnowledge (L := L) history history := by
  intro who
  exact SameOrderKnowledge.refl (L := L) who history

theorem AllPlayersSameOrderKnowledge.symm
    {left right : SourceHistoryPoint P L}
    (h : AllPlayersSameOrderKnowledge (L := L) left right) :
    AllPlayersSameOrderKnowledge (L := L) right left := by
  intro who
  exact SameOrderKnowledge.symm (h who)

theorem AllPlayersSameOrderKnowledge.trans
    {a b c : SourceHistoryPoint P L}
    (hab : AllPlayersSameOrderKnowledge (L := L) a b)
    (hbc : AllPlayersSameOrderKnowledge (L := L) b c) :
    AllPlayersSameOrderKnowledge (L := L) a c := by
  intro who
  exact SameOrderKnowledge.trans (hab who) (hbc who)

/-- Full all-player history knowledge equality implies all-player order-only
history knowledge equality. -/
theorem AllPlayersSameHistoryKnowledge.toOrder
    {left right : SourceHistoryPoint P L}
    (h : AllPlayersSameHistoryKnowledge (L := L) left right) :
    AllPlayersSameOrderKnowledge (L := L) left right := by
  intro who
  exact SameHistoryKnowledge.toOrder (h who)

/-- The order-only history knowledge cell induced by a player's source
order-history view. -/
def OrderKnowledgeCell (who : P) (history : SourceHistoryPoint P L) :
    Set (SourceHistoryPoint P L) :=
  Math.ViewKnowledge.Cell
    (fun other : SourceHistoryPoint P L => other.orderHistoryView who) history

@[simp] theorem mem_OrderKnowledgeCell_iff
    (who : P) (history other : SourceHistoryPoint P L) :
    other ∈ OrderKnowledgeCell (L := L) who history ↔
      SameOrderKnowledge (L := L) who history other := by
  rfl

/-- The current history belongs to its own order-only knowledge cell. -/
theorem OrderKnowledgeCell.self
    (who : P) (history : SourceHistoryPoint P L) :
    history ∈ OrderKnowledgeCell (L := L) who history :=
  Math.ViewKnowledge.Cell.self
    (fun other : SourceHistoryPoint P L => other.orderHistoryView who) history

/-- Histories with the same order-only knowledge have the same order-only
knowledge cell. -/
theorem OrderKnowledgeCell.eq_of_sameOrderKnowledge
    {who : P} {left right : SourceHistoryPoint P L}
    (h : SameOrderKnowledge (L := L) who left right) :
    OrderKnowledgeCell (L := L) who left =
      OrderKnowledgeCell (L := L) who right :=
  Math.ViewKnowledge.Cell.eq_of_same h

/-- Player `who` knows an order-history event at `history` when it holds
throughout the order-only knowledge cell. -/
def KnowsOrder (who : P) (history : SourceHistoryPoint P L)
    (event : Set (SourceHistoryPoint P L)) : Prop :=
  Math.ViewKnowledge.Knows
    (fun other : SourceHistoryPoint P L => other.orderHistoryView who)
    history event

/-- Veridicality for order-only history knowledge. -/
theorem KnowsOrder.truth {who : P} {history : SourceHistoryPoint P L}
    {event : Set (SourceHistoryPoint P L)}
    (h : KnowsOrder (L := L) who history event) :
    event history :=
  Math.ViewKnowledge.Knows.truth h

/-- Order-only history knowledge is monotone in the event. -/
theorem KnowsOrder.mono {who : P} {history : SourceHistoryPoint P L}
    {event stronger : Set (SourceHistoryPoint P L)}
    (h : KnowsOrder (L := L) who history event)
    (hsub : ∀ {other}, event other → stronger other) :
    KnowsOrder (L := L) who history stronger :=
  Math.ViewKnowledge.Knows.mono h hsub

/-- If an order-history event is known, then every order-indistinguishable
history also knows it. -/
theorem KnowsOrder.of_sameOrderKnowledge
    {who : P} {history other : SourceHistoryPoint P L}
    {event : Set (SourceHistoryPoint P L)}
    (hknow : KnowsOrder (L := L) who history event)
    (hsame : SameOrderKnowledge (L := L) who history other) :
    KnowsOrder (L := L) who other event :=
  Math.ViewKnowledge.Knows.of_same hknow hsame

/-- A player knows the starting source program point under the order-only
history interface. -/
theorem KnowsOrder.startPoint_eq
    (who : P) (history : SourceHistoryPoint P L) :
    KnowsOrder (L := L) who history
      { other | other.startPoint = history.startPoint } := by
  intro other hcell
  exact (SameOrderKnowledge.startPoint_eq hcell).symm

/-- A player knows the current source program point under the order-only
history interface. -/
theorem KnowsOrder.programPoint_eq
    (who : P) (history : SourceHistoryPoint P L) :
    KnowsOrder (L := L) who history
      { other | other.programPoint = history.programPoint } := by
  intro other hcell
  exact (SameOrderKnowledge.programPoint_eq hcell).symm

/-- A player knows the current coarse source point kind under the order-only
history interface. -/
theorem KnowsOrder.pointKind_eq
    (who : P) (history : SourceHistoryPoint P L) :
    KnowsOrder (L := L) who history
      { other | other.pointKind = history.pointKind } := by
  intro other hcell
  exact (SameOrderKnowledge.pointKind_eq hcell).symm

/-- A player knows the current active player under the order-only history
interface. -/
theorem KnowsOrder.activePlayer?_eq
    (who : P) (history : SourceHistoryPoint P L) :
    KnowsOrder (L := L) who history
      { other | other.activePlayer? = history.activePlayer? } := by
  intro other hcell
  exact (SameOrderKnowledge.activePlayer?_eq hcell).symm

/-- A player knows whether any fixed player is at a source choice point under
the order-only history interface. -/
theorem KnowsOrder.isChoiceFor_iff
    (observer player : P) (history : SourceHistoryPoint P L) :
    KnowsOrder (L := L) observer history
      { other | other.IsChoiceFor player ↔ history.IsChoiceFor player } := by
  intro other hcell
  exact Iff.symm (SameOrderKnowledge.isChoiceFor_iff hcell)

/-- A player knows its own visible order trace under the order-only history
interface. -/
theorem KnowsOrder.orderTrace_eq
    (who : P) (history : SourceHistoryPoint P L) :
    KnowsOrder (L := L) who history
      { other |
        SourceConfig.playerOrderTraceView (L := L) who other.labels =
          SourceConfig.playerOrderTraceView (L := L) who history.labels } := by
  intro other hcell
  exact (SameOrderKnowledge.orderTrace_eq hcell).symm

/-- Positive introspection for order-only history knowledge. -/
theorem KnowsOrder.positive_introspection
    {who : P} {history : SourceHistoryPoint P L}
    {event : Set (SourceHistoryPoint P L)}
    (hknow : KnowsOrder (L := L) who history event) :
    KnowsOrder (L := L) who history
      { other | KnowsOrder (L := L) who other event } :=
  Math.ViewKnowledge.Knows.positive_introspection hknow

/-- Negative introspection for order-only history knowledge. -/
theorem KnowsOrder.negative_introspection
    {who : P} {history : SourceHistoryPoint P L}
    {event : Set (SourceHistoryPoint P L)}
    (hnot : ¬ KnowsOrder (L := L) who history event) :
    KnowsOrder (L := L) who history
      { other | ¬ KnowsOrder (L := L) who other event } :=
  Math.ViewKnowledge.Knows.negative_introspection hnot

/-- The history knowledge cell induced by a player's source history-local view. -/
def HistoryKnowledgeCell (who : P) (history : SourceHistoryPoint P L) :
    Set (SourceHistoryPoint P L) :=
  Math.ViewKnowledge.Cell
    (fun other : SourceHistoryPoint P L => other.localHistoryView who) history

@[simp] theorem mem_HistoryKnowledgeCell_iff
    (who : P) (history other : SourceHistoryPoint P L) :
    other ∈ HistoryKnowledgeCell (L := L) who history ↔
      SameHistoryKnowledge (L := L) who history other := by
  rfl

/-- The current history belongs to its own full history knowledge cell. -/
theorem HistoryKnowledgeCell.self
    (who : P) (history : SourceHistoryPoint P L) :
    history ∈ HistoryKnowledgeCell (L := L) who history :=
  Math.ViewKnowledge.Cell.self
    (fun other : SourceHistoryPoint P L => other.localHistoryView who) history

/-- Histories with the same full history knowledge have the same full history
knowledge cell. -/
theorem HistoryKnowledgeCell.eq_of_sameHistoryKnowledge
    {who : P} {left right : SourceHistoryPoint P L}
    (h : SameHistoryKnowledge (L := L) who left right) :
    HistoryKnowledgeCell (L := L) who left =
      HistoryKnowledgeCell (L := L) who right :=
  Math.ViewKnowledge.Cell.eq_of_same h

/-- Player `who` knows a source-history event at `history` when it holds
throughout the source history-local knowledge cell. -/
def KnowsHistory (who : P) (history : SourceHistoryPoint P L)
    (event : Set (SourceHistoryPoint P L)) : Prop :=
  Math.ViewKnowledge.Knows
    (fun other : SourceHistoryPoint P L => other.localHistoryView who)
    history event

/-- Veridicality for source-history knowledge. -/
theorem KnowsHistory.truth {who : P} {history : SourceHistoryPoint P L}
    {event : Set (SourceHistoryPoint P L)}
    (h : KnowsHistory (L := L) who history event) :
    event history :=
  Math.ViewKnowledge.Knows.truth h

/-- Source-history knowledge is monotone in the event. -/
theorem KnowsHistory.mono {who : P} {history : SourceHistoryPoint P L}
    {event stronger : Set (SourceHistoryPoint P L)}
    (h : KnowsHistory (L := L) who history event)
    (hsub : ∀ {other}, event other → stronger other) :
    KnowsHistory (L := L) who history stronger :=
  Math.ViewKnowledge.Knows.mono h hsub

/-- If a source-history event is known, then every indistinguishable history
also knows it. -/
theorem KnowsHistory.of_sameHistoryKnowledge
    {who : P} {history other : SourceHistoryPoint P L}
    {event : Set (SourceHistoryPoint P L)}
    (hknow : KnowsHistory (L := L) who history event)
    (hsame : SameHistoryKnowledge (L := L) who history other) :
    KnowsHistory (L := L) who other event :=
  Math.ViewKnowledge.Knows.of_same hknow hsame

/-- Anything known from the coarser order-only history view is also known from
the full history view. The converse is not generally available because the full
view can distinguish values that the order-only view forgets. -/
theorem KnowsHistory.of_knowsOrder
    {who : P} {history : SourceHistoryPoint P L}
    {event : Set (SourceHistoryPoint P L)}
    (hknow : KnowsOrder (L := L) who history event) :
    KnowsHistory (L := L) who history event := by
  change Math.ViewKnowledge.Knows
    (fun other : SourceHistoryPoint P L => other.localHistoryView who)
    history event
  change Math.ViewKnowledge.Knows
    (fun other : SourceHistoryPoint P L =>
      (other.localHistoryView who).orderView) history event at hknow
  exact Math.ViewKnowledge.Knows.of_coarser
    SourceHistoryLocalView.orderView hknow

/-- Endpoint source knowledge lifts to full source-history knowledge for
endpoint events. -/
theorem KnowsHistory.current_of_Knows
    {who : P} {history : SourceHistoryPoint P L}
    {event : Set (SourceConfig P L)}
    (hknow : SourceConfig.Knows (L := L) who history.current event) :
    KnowsHistory (L := L) who history
      { other | event other.current } := by
  intro other hcell
  exact hknow (SameHistoryKnowledge.current hcell)

/-- A player knows the starting source program point under the full history
interface. -/
theorem KnowsHistory.startPoint_eq
    (who : P) (history : SourceHistoryPoint P L) :
    KnowsHistory (L := L) who history
      { other | other.startPoint = history.startPoint } := by
  intro other hcell
  exact (SameHistoryKnowledge.startPoint_eq hcell).symm

/-- A player knows the current source program point under the full history
interface. -/
theorem KnowsHistory.programPoint_eq
    (who : P) (history : SourceHistoryPoint P L) :
    KnowsHistory (L := L) who history
      { other | other.programPoint = history.programPoint } := by
  intro other hcell
  exact (SameHistoryKnowledge.programPoint_eq hcell).symm

/-- A player knows the current coarse source point kind under the full history
interface. -/
theorem KnowsHistory.pointKind_eq
    (who : P) (history : SourceHistoryPoint P L) :
    KnowsHistory (L := L) who history
      { other | other.pointKind = history.pointKind } := by
  intro other hcell
  exact (SameHistoryKnowledge.pointKind_eq hcell).symm

/-- A player knows the current active player under the full history interface. -/
theorem KnowsHistory.activePlayer?_eq
    (who : P) (history : SourceHistoryPoint P L) :
    KnowsHistory (L := L) who history
      { other | other.activePlayer? = history.activePlayer? } := by
  intro other hcell
  exact (SameHistoryKnowledge.activePlayer?_eq hcell).symm

/-- A player knows whether any fixed player is at a source choice point under
the full history interface. -/
theorem KnowsHistory.isChoiceFor_iff
    (observer player : P) (history : SourceHistoryPoint P L) :
    KnowsHistory (L := L) observer history
      { other | other.IsChoiceFor player ↔ history.IsChoiceFor player } := by
  intro other hcell
  exact Iff.symm (SameHistoryKnowledge.isChoiceFor_iff hcell)

/-- A player knows its own visible source trace under the full history
interface. -/
theorem KnowsHistory.traceView_eq
    (who : P) (history : SourceHistoryPoint P L) :
    KnowsHistory (L := L) who history
      { other |
        SourceConfig.playerTraceView (L := L) who other.labels =
          SourceConfig.playerTraceView (L := L) who history.labels } := by
  intro other hcell
  exact (SameHistoryKnowledge.traceView_eq hcell).symm

/-- A player knows its own visible order trace under the full history
interface. -/
theorem KnowsHistory.orderTrace_eq
    (who : P) (history : SourceHistoryPoint P L) :
    KnowsHistory (L := L) who history
      { other |
        SourceConfig.playerOrderTraceView (L := L) who other.labels =
          SourceConfig.playerOrderTraceView (L := L) who history.labels } := by
  intro other hcell
  exact (SameHistoryKnowledge.orderTrace_eq hcell).symm

/-- Positive introspection for source-history knowledge. -/
theorem KnowsHistory.positive_introspection
    {who : P} {history : SourceHistoryPoint P L}
    {event : Set (SourceHistoryPoint P L)}
    (hknow : KnowsHistory (L := L) who history event) :
    KnowsHistory (L := L) who history
      { other | KnowsHistory (L := L) who other event } :=
  Math.ViewKnowledge.Knows.positive_introspection hknow

/-- Negative introspection for source-history knowledge. -/
theorem KnowsHistory.negative_introspection
    {who : P} {history : SourceHistoryPoint P L}
    {event : Set (SourceHistoryPoint P L)}
    (hnot : ¬ KnowsHistory (L := L) who history event) :
    KnowsHistory (L := L) who history
      { other | ¬ KnowsHistory (L := L) who other event } :=
  Math.ViewKnowledge.Knows.negative_introspection hnot

end SourceHistoryPoint

namespace SourceConfig

@[simp] theorem playerTraceView_nil (who : P) :
    playerTraceView (L := L) who [] = [] := rfl

@[simp] theorem playerTraceView_cons
    (who : P) (label : Label P L) (labels : List (Label P L)) :
    playerTraceView (L := L) who (label :: labels) =
      Label.playerEvent (L := L) who label ::
        playerTraceView (L := L) who labels := rfl

@[simp] theorem playerOrderTraceView_nil (who : P) :
    playerOrderTraceView (L := L) who [] = [] := rfl

@[simp] theorem playerOrderTraceView_cons
    (who : P) (label : Label P L) (labels : List (Label P L)) :
    playerOrderTraceView (L := L) who (label :: labels) =
      Label.playerEventKind (L := L) who label ::
        playerOrderTraceView (L := L) who labels := rfl

theorem playerTraceView_length
    (who : P) (labels : List (Label P L)) :
    (playerTraceView (L := L) who labels).length = labels.length := by
  simp [playerTraceView]

theorem playerOrderTraceView_length
    (who : P) (labels : List (Label P L)) :
    (playerOrderTraceView (L := L) who labels).length = labels.length := by
  simp [playerOrderTraceView]

/-- Replacing another player's committed value does not change the observer's
visible trace event at that position. -/
theorem playerTraceView_singleton_commit_other_value_irrel
    {who owner : P} (hneq : who ≠ owner)
    (x : VarId) {b : L.Ty} (left right : L.Val b) :
    playerTraceView (L := L) who [Label.commit x owner left] =
      playerTraceView (L := L) who [Label.commit x owner right] := by
  change [Label.playerEvent (L := L) who (Label.commit x owner left)] =
    [Label.playerEvent (L := L) who (Label.commit x owner right)]
  rw [Label.playerEvent_commit_other_value_irrel (L := L) hneq]

/-- Replacing any committed value does not change the order-only trace event at
that position. -/
theorem playerOrderTraceView_singleton_commit_value_irrel
    (who owner : P) (x : VarId) {b : L.Ty}
    (left right : L.Val b) :
    playerOrderTraceView (L := L) who [Label.commit x owner left] =
      playerOrderTraceView (L := L) who [Label.commit x owner right] := by
  change
    [Label.playerEventKind (L := L) who (Label.commit x owner left)] =
    [Label.playerEventKind (L := L) who (Label.commit x owner right)]
  rw [Label.playerEventKind_commit_value_irrel (L := L)]

/-- Replacing any sampled value does not change the order-only trace event at
that position. -/
theorem playerOrderTraceView_singleton_sample_value_irrel
    (who : P) (x : VarId) {b : L.Ty}
    (left right : L.Val b) :
    playerOrderTraceView (L := L) who [Label.sample x left] =
      playerOrderTraceView (L := L) who [Label.sample x right] := rfl

/-- Replacing any revealed value does not change the order-only trace event at
that position. -/
theorem playerOrderTraceView_singleton_reveal_value_irrel
    (who : P) (y : VarId) (owner : P) (x : VarId)
    {b : L.Ty} (left right : L.Val b) :
    playerOrderTraceView (L := L) who [Label.reveal y owner x left] =
      playerOrderTraceView (L := L) who [Label.reveal y owner x right] := rfl

end SourceConfig

end Vegas
