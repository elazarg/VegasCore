import Vegas.SmallStep.Agreement

/-!
# Basic raw small-step properties
-/

namespace Vegas
namespace SmallStep

open FOSGBridge

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

/-- Every supported raw step strictly decreases the remaining syntax-node
measure. This is the bounded-horizon core for raw small-step execution. -/
theorem step_syntaxSteps_lt {σ : OmniscientOperationalProfile P L}
    {w : World P L} {d : FDist (Label P L × World P L)}
    {lw : Label P L × World P L}
    (hstep : Step σ w d) (hsupp : lw ∈ d.support) :
    syntaxSteps lw.2.prog < syntaxSteps w.prog := by
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

end SmallStep
end Vegas
