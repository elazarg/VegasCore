import Vegas.SmallStep.Agreement

/-!
# Basic raw small-step properties
-/

namespace Vegas
namespace SmallStep

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Every non-terminal raw world has an outgoing small-step distribution. -/
theorem progress (σ : OmniscientOperationalProfile P L)
    (w : World P L) (hterm : ¬ terminal w) :
    ∃ d, Step σ w d := by
  cases w with
  | mk Γ prog env =>
      cases prog with
      | ret payoffs =>
          exact False.elim (hterm (by simp [terminal]))
      | letExpr x e k =>
          exact ⟨_, Step.letExpr (σ := σ) env⟩
      | sample x D k =>
          exact ⟨_, Step.sample (σ := σ) env⟩
      | commit x who R k =>
          exact ⟨_, Step.commit (σ := σ) env⟩
      | reveal y who x hx k =>
          exact ⟨_, Step.reveal (σ := σ) env⟩

/-- Raw `Step` is functional: the source world determines the outgoing
distribution. -/
theorem step_functional {σ : OmniscientOperationalProfile P L}
    {w : World P L} {d₁ d₂ : FDist (Label P L × World P L)}
    (h₁ : Step σ w d₁) (h₂ : Step σ w d₂) :
    d₁ = d₂ := by
  cases h₁ <;> cases h₂ <;> rfl

/-- Every supported raw step consumes exactly one syntax node. -/
theorem step_syntaxSteps_eq {σ : OmniscientOperationalProfile P L}
    {w : World P L} {d : FDist (Label P L × World P L)}
    {lw : Label P L × World P L}
    (hstep : Step σ w d) (hsupp : lw ∈ d.support) :
    syntaxSteps lw.2.prog + 1 = syntaxSteps w.prog := by
  cases hstep with
  | letExpr env =>
      rw [FDist.mem_support_pure] at hsupp
      subst lw
      simp [syntaxSteps]
  | sample env =>
      rw [FDist.mem_support_bind] at hsupp
      rcases hsupp with ⟨v, _hv, hpure⟩
      rw [FDist.mem_support_pure] at hpure
      subst lw
      simp [syntaxSteps]
  | commit env =>
      rw [FDist.mem_support_bind] at hsupp
      rcases hsupp with ⟨v, _hv, hpure⟩
      rw [FDist.mem_support_pure] at hpure
      subst lw
      simp [syntaxSteps]
  | reveal env =>
      rw [FDist.mem_support_pure] at hsupp
      subst lw
      simp [syntaxSteps]

/-- Every supported raw step strictly decreases the remaining syntax-node
measure. -/
theorem step_syntaxSteps_lt {σ : OmniscientOperationalProfile P L}
    {w : World P L} {d : FDist (Label P L × World P L)}
    {lw : Label P L × World P L}
    (hstep : Step σ w d) (hsupp : lw ∈ d.support) :
    syntaxSteps lw.2.prog < syntaxSteps w.prog := by
  have h := step_syntaxSteps_eq hstep hsupp
  omega

/-- Supported labelled one-step targets consume exactly one syntax node. -/
theorem stepSupport_syntaxSteps_eq
    {σ : OmniscientOperationalProfile P L}
    {w : World P L} {lw : Label P L × World P L}
    (hstep : StepSupport σ w lw) :
    syntaxSteps lw.2.prog + 1 = syntaxSteps w.prog := by
  rcases hstep with ⟨d, hd, hsupp⟩
  exact step_syntaxSteps_eq hd hsupp

/-- Supported labelled one-step targets strictly decrease the syntax-node
measure. -/
theorem stepSupport_syntaxSteps_lt
    {σ : OmniscientOperationalProfile P L}
    {w : World P L} {lw : Label P L × World P L}
    (hstep : StepSupport σ w lw) :
    syntaxSteps lw.2.prog < syntaxSteps w.prog := by
  have h := stepSupport_syntaxSteps_eq hstep
  omega

/-- A supported raw multi-step path consumes exactly its label count from the
source syntax-node measure. -/
theorem steps_length_add_syntaxSteps_eq
    {σ : OmniscientOperationalProfile P L}
    {w dst : World P L} {labels : List (Label P L)}
    (hsteps : Steps σ w labels dst) :
    labels.length + syntaxSteps dst.prog = syntaxSteps w.prog := by
  induction hsteps with
  | nil w =>
      simp
  | @cons w mid dst label labels hstep _ ih =>
      have heq : syntaxSteps mid.prog + 1 = syntaxSteps w.prog :=
        stepSupport_syntaxSteps_eq hstep
      simp only [List.length_cons]
      omega

/-- A supported raw multi-step path cannot consume more labels plus remaining
syntax than the source syntax contains. -/
theorem steps_length_add_syntaxSteps_le
    {σ : OmniscientOperationalProfile P L}
    {w dst : World P L} {labels : List (Label P L)}
    (hsteps : Steps σ w labels dst) :
    labels.length + syntaxSteps dst.prog ≤ syntaxSteps w.prog := by
  have h := steps_length_add_syntaxSteps_eq hsteps
  omega

/-- Bounded-horizon form: the number of supported labels in a raw multi-step
path is bounded by the source syntax size. -/
theorem steps_length_le_syntaxSteps
    {σ : OmniscientOperationalProfile P L}
    {w dst : World P L} {labels : List (Label P L)}
    (hsteps : Steps σ w labels dst) :
    labels.length ≤ syntaxSteps w.prog := by
  have h := steps_length_add_syntaxSteps_le hsteps
  omega

/-- A supported raw multi-step path that reaches a terminal world has consumed
exactly the source syntax size. -/
theorem steps_length_eq_syntaxSteps_of_terminal
    {σ : OmniscientOperationalProfile P L}
    {w dst : World P L} {labels : List (Label P L)}
    (hsteps : Steps σ w labels dst) (hterm : terminal dst) :
    labels.length = syntaxSteps w.prog := by
  have h := steps_length_add_syntaxSteps_eq hsteps
  have hdst := (terminal_iff_syntaxSteps_eq_zero (w := dst)).1 hterm
  omega

/-! ## Small-step evaluator commutation -/

/-- Small-step evaluator form of adjacent independent commit commutation.

The theorem restates `outcomeDist_comm_commit` over packaged small-step worlds.
It is an outcome-level scheduler/permutation fact for `runSmallStep`; the
qualitative `Steps` relation remains the positive-support path relation.

The strategy-agreement hypotheses are explicit because an arbitrary
`OmniscientOperationalProfile` is indexed by both the full erased environment
and the syntactic guard expression. Distinct players and view-scoped guards
are not enough by themselves to identify those raw kernels; a lower-friction
corollary needs an additional coherence predicate for the operational profile. -/
theorem runSmallStep_comm_commit
    {Γ : VCtx P L} {σ : OmniscientOperationalProfile P L} {env : VEnv L Γ}
    {x₁ : VarId} {who₁ : P} {b₁ : L.Ty}
    {R₁ : L.Expr ((x₁, b₁) :: eraseVCtx Γ) L.bool}
    {x₂ : VarId} {who₂ : P} {b₂ : L.Ty}
    {R₂ : L.Expr ((x₂, b₂) :: eraseVCtx
      ((x₁, .hidden who₁ b₁) :: Γ)) L.bool}
    {k : VegasCore P L
      ((x₂, .hidden who₂ b₂) :: (x₁, .hidden who₁ b₁) :: Γ)}
    {R₂' : L.Expr ((x₂, b₂) :: eraseVCtx Γ) L.bool}
    {R₁' : L.Expr ((x₁, b₁) :: eraseVCtx
      ((x₂, .hidden who₂ b₂) :: Γ)) L.bool}
    {k' : VegasCore P L
      ((x₁, .hidden who₁ b₁) :: (x₂, .hidden who₂ b₂) :: Γ)}
    (hk_eq : ∀ (v₁ : L.Val b₁) (v₂ : L.Val b₂)
        (e : VEnv L Γ),
      runSmallStep σ
        ({ Γ := (x₂, .hidden who₂ b₂) :: (x₁, .hidden who₁ b₁) :: Γ
           prog := k
           env := VEnv.cons v₂ (VEnv.cons v₁ e) } : World P L) =
      runSmallStep σ
        ({ Γ := (x₁, .hidden who₁ b₁) :: (x₂, .hidden who₂ b₂) :: Γ
           prog := k'
           env := VEnv.cons v₁ (VEnv.cons v₂ e) } : World P L))
    (hσ₁ : ∀ (v₂ : L.Val b₂) (e : VEnv L Γ),
      σ.commit who₁ x₁ R₁ (VEnv.eraseEnv e) =
      σ.commit who₁ x₁ R₁'
        (VEnv.eraseEnv (VEnv.cons (τ := .hidden who₂ b₂) v₂ e)))
    (hσ₂ : ∀ (v₁ : L.Val b₁) (e : VEnv L Γ),
      σ.commit who₂ x₂ R₂
        (VEnv.eraseEnv (VEnv.cons (τ := .hidden who₁ b₁) v₁ e)) =
      σ.commit who₂ x₂ R₂' (VEnv.eraseEnv e)) :
    runSmallStep σ
      ({ Γ := Γ
         prog := .commit x₁ who₁ R₁
          (.commit x₂ who₂ R₂ k)
         env := env } : World P L) =
    runSmallStep σ
      ({ Γ := Γ
         prog := .commit x₂ who₂ R₂'
          (.commit x₁ who₁ R₁' k')
         env := env } : World P L) := by
  simpa [runSmallStep] using
    outcomeDist_comm_commit
      (σ := σ) (env := env)
      (hk_eq := by
        intro v₁ v₂ e
        simpa [runSmallStep] using hk_eq v₁ v₂ e)
      hσ₁ hσ₂

/-- Small-step evaluator form of adjacent reveal commutation. -/
theorem runSmallStep_comm_reveal
    {Γ : VCtx P L} {σ : OmniscientOperationalProfile P L} {env : VEnv L Γ}
    {y₁ : VarId} {who₁ : P} {x₁ : VarId} {b₁ : L.Ty}
    {hx₁ : VHasVar (L := L) Γ x₁ (.hidden who₁ b₁)}
    {y₂ : VarId} {who₂ : P} {x₂ : VarId} {b₂ : L.Ty}
    {hx₂ : VHasVar (L := L) Γ x₂ (.hidden who₂ b₂)}
    {k : VegasCore P L ((y₂, .pub b₂) :: (y₁, .pub b₁) :: Γ)}
    {k' : VegasCore P L ((y₁, .pub b₁) :: (y₂, .pub b₂) :: Γ)}
    (hk_eq : ∀ (v₁ : L.Val b₁) (v₂ : L.Val b₂)
        (e : VEnv L Γ),
      runSmallStep σ
        ({ Γ := (y₂, .pub b₂) :: (y₁, .pub b₁) :: Γ
           prog := k
           env := VEnv.cons v₂ (VEnv.cons v₁ e) } : World P L) =
      runSmallStep σ
        ({ Γ := (y₁, .pub b₁) :: (y₂, .pub b₂) :: Γ
           prog := k'
           env := VEnv.cons v₁ (VEnv.cons v₂ e) } : World P L)) :
    runSmallStep σ
      ({ Γ := Γ
         prog := .reveal y₁ who₁ x₁ hx₁
          (.reveal y₂ who₂ x₂ hx₂.there k)
         env := env } : World P L) =
    runSmallStep σ
      ({ Γ := Γ
         prog := .reveal y₂ who₂ x₂ hx₂
          (.reveal y₁ who₁ x₁ hx₁.there k')
         env := env } : World P L) := by
  simpa [runSmallStep] using
    outcomeDist_comm_reveal
      (σ := σ) (env := env)
      (hk_eq := by
        intro v₁ v₂ e
        simpa [runSmallStep] using hk_eq v₁ v₂ e)

end SmallStep
end Vegas
