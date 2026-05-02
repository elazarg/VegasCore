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

end SmallStep
end Vegas
