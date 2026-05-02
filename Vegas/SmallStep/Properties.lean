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

end SmallStep
end Vegas
