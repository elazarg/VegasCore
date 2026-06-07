/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.Schedule

/-!
# Source traces and program equivalence

Because `VegasCore` is straight-line (`Vegas.Core.Schedule`), the *order* of
events a player observes along a run is fixed by the program text; only the
values vary. This module turns that into a trace-level invariant.

`VegasCore.orderTrace who` is the canonical per-player order-trace skeleton of a
program: a pure structural function of the syntax, listing the event *kinds*
(`SourcePlayerEvent.Kind`) player `who` would observe, with all values dropped.
The central fact `LabeledStar.orderTrace_split` says any run splits the skeleton
as *(visible order trace so far) ++ (skeleton of the remaining program)*. Hence
every terminal run realizes exactly the skeleton (`playerOrderTraceView_eq_of_…`),
and two terminal runs of one program have identical player order traces — the
order trace is a program invariant, the values are run-specific.

`ProgramOrderEquiv` is the induced program equivalence: two programs are
equivalent when they present the same order-trace skeleton to every player. This
is the "same trace structure" relation; it is the source-level object the event
graph's many linearizations must all agree with.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## The canonical order-trace skeleton -/

/-- The per-player order-trace skeleton of a program: the sequence of event
*kinds* `who` observes, dropping every value. A pure structural function of the
syntax — no environment, no run. -/
def VegasCore.orderTrace {Γ : VCtx P L}
    (prog : VegasCore P L Γ) (who : P) : List (SourcePlayerEvent.Kind P) :=
  match prog with
  | .ret _ => []
  | .sample _ _ k => .sample :: k.orderTrace who
  | .commit _ owner _ k =>
      (if who = owner then .ownCommit owner else .otherCommit owner)
        :: k.orderTrace who
  | .reveal _ owner _ _ k => .reveal owner :: k.orderTrace who

@[simp] theorem VegasCore.orderTrace_ret {Γ : VCtx P L}
    (payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)) (who : P) :
    (VegasCore.ret payoffs : VegasCore P L Γ).orderTrace who = [] := rfl

@[simp] theorem VegasCore.orderTrace_sample {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    (dist : L.DistExpr (erasePubVCtx Γ) b)
    (k : VegasCore P L ((x, .pub b) :: Γ)) (who : P) :
    (VegasCore.sample x dist k).orderTrace who =
      SourcePlayerEvent.Kind.sample :: k.orderTrace who := rfl

@[simp] theorem VegasCore.orderTrace_commit {Γ : VCtx P L} {x : VarId} {owner : P}
    {b : L.Ty}
    (guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx owner Γ)) L.bool)
    (k : VegasCore P L ((x, .sealed owner b) :: Γ)) (who : P) :
    (VegasCore.commit x owner guard k).orderTrace who =
      (if who = owner then SourcePlayerEvent.Kind.ownCommit owner
        else SourcePlayerEvent.Kind.otherCommit owner) :: k.orderTrace who := rfl

@[simp] theorem VegasCore.orderTrace_reveal {Γ : VCtx P L} {y : VarId} {owner : P}
    {x : VarId} {b : L.Ty} (hx : VHasVar Γ x (.sealed owner b))
    (k : VegasCore P L ((y, .pub b) :: Γ)) (who : P) :
    (VegasCore.reveal y owner x hx k).orderTrace who =
      SourcePlayerEvent.Kind.reveal owner :: k.orderTrace who := rfl

/-! ## Steps consume one skeleton entry -/

/-- A labeled step peels the head off the order-trace skeleton: the kind it emits
is exactly the player-event kind of its label, and the tail is the skeleton of
the continuation. -/
theorem LStep.orderTrace_cont {who : P} {cfg cfg' : SourceConfig P L}
    {ℓ : Label P L} (h : LStep cfg ℓ cfg') :
    cfg.cont.orderTrace who =
      Label.playerEventKind who ℓ :: cfg'.cont.orderTrace who := by
  cases h with
  | sample D' k v hv => rfl
  | @commit Γ env x owner b R k v hg =>
      by_cases hwho : who = owner
      · subst hwho
        simp [Label.playerEventKind_commit_self]
      · simp [Label.playerEventKind_commit_other hwho, hwho]
  | reveal hx k => rfl

namespace SourceConfig

/-! ## Every run realizes a prefix of the skeleton -/

/-- A run splits the order-trace skeleton: the skeleton of the starting program
equals the player's visible order trace of the run, followed by the skeleton of
the program that remains. -/
theorem LabeledStar.orderTrace_split {cfg d : SourceConfig P L}
    {ls : List (Label P L)}
    (h : SourceConfig.LabeledStar cfg ls d) (who : P) :
    cfg.cont.orderTrace who =
      SourceConfig.playerOrderTraceView who ls ++ d.cont.orderTrace who := by
  induction h with
  | refl c => simp
  | cons step _rest ih =>
      rw [SourceConfig.playerOrderTraceView_cons, step.orderTrace_cont, ih,
        List.cons_append]

/-- Two runs from the same configuration that both reach a terminal state have
identical player order traces: the order trace is determined by the program, not
the values. -/
theorem playerOrderTraceView_eq_of_terminal
    {cfg d₁ d₂ : SourceConfig P L} {ls₁ ls₂ : List (Label P L)}
    (h₁ : SourceConfig.LabeledStar cfg ls₁ d₁)
    (h₂ : SourceConfig.LabeledStar cfg ls₂ d₂)
    (t₁ : d₁.IsTerminal) (t₂ : d₂.IsTerminal) (who : P) :
    SourceConfig.playerOrderTraceView who ls₁ =
      SourceConfig.playerOrderTraceView who ls₂ := by
  have e₁ := h₁.orderTrace_split who
  have e₂ := h₂.orderTrace_split who
  obtain ⟨p₁, hp₁⟩ := t₁
  obtain ⟨p₂, hp₂⟩ := t₂
  rw [hp₁] at e₁
  rw [hp₂] at e₂
  simp only [VegasCore.orderTrace_ret, List.append_nil] at e₁ e₂
  exact e₁.symm.trans e₂

/-- A terminal run from the initial configuration realizes exactly the program's
order-trace skeleton. -/
theorem playerOrderTraceView_initial_eq {prog : VegasCore P L []}
    {ls : List (Label P L)} {d : SourceConfig P L}
    (h : SourceConfig.LabeledStar (SourceConfig.initial prog) ls d)
    (t : d.IsTerminal) (who : P) :
    SourceConfig.playerOrderTraceView who ls = prog.orderTrace who := by
  have e := h.orderTrace_split who
  obtain ⟨p, hp⟩ := t
  rw [hp] at e
  simpa [SourceConfig.initial] using e.symm

end SourceConfig

/-! ## Program equivalence -/

/-- Two closed programs are *order-equivalent* when they present the same
order-trace skeleton to every player. This is the source-level "same trace
structure" relation: it fixes the control/information skeleton while leaving the
realized values free. -/
def ProgramOrderEquiv (prog₁ prog₂ : VegasCore P L []) : Prop :=
  ∀ who : P, prog₁.orderTrace who = prog₂.orderTrace who

namespace ProgramOrderEquiv

theorem refl (prog : VegasCore P L []) : ProgramOrderEquiv prog prog :=
  fun _ => rfl

theorem symm {prog₁ prog₂ : VegasCore P L []}
    (h : ProgramOrderEquiv prog₁ prog₂) : ProgramOrderEquiv prog₂ prog₁ :=
  fun who => (h who).symm

theorem trans {prog₁ prog₂ prog₃ : VegasCore P L []}
    (h₁ : ProgramOrderEquiv prog₁ prog₂) (h₂ : ProgramOrderEquiv prog₂ prog₃) :
    ProgramOrderEquiv prog₁ prog₃ :=
  fun who => (h₁ who).trans (h₂ who)

/-- Order-equivalent programs yield identical player order traces on every pair
of terminal runs: the behavioural meaning of the skeleton equivalence. -/
theorem playerOrderTraceView_eq {prog₁ prog₂ : VegasCore P L []}
    (hequiv : ProgramOrderEquiv prog₁ prog₂)
    {ls₁ ls₂ : List (Label P L)} {d₁ d₂ : SourceConfig P L}
    (h₁ : SourceConfig.LabeledStar (SourceConfig.initial prog₁) ls₁ d₁)
    (h₂ : SourceConfig.LabeledStar (SourceConfig.initial prog₂) ls₂ d₂)
    (t₁ : d₁.IsTerminal) (t₂ : d₂.IsTerminal) (who : P) :
    SourceConfig.playerOrderTraceView who ls₁ =
      SourceConfig.playerOrderTraceView who ls₂ := by
  rw [SourceConfig.playerOrderTraceView_initial_eq h₁ t₁,
    SourceConfig.playerOrderTraceView_initial_eq h₂ t₂, hequiv who]

end ProgramOrderEquiv

end Vegas
