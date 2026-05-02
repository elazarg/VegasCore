import Vegas.SmallStep.Defs

/-!
# Agreement for raw small-step semantics
-/

namespace Vegas
namespace SmallStep

open FOSGBridge

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The raw small-step core evaluator is the existing denotational semantics. -/
theorem runSmallStepCore_eq_outcomeDist
    (σ : OmniscientOperationalProfile P L)
    {Γ : VCtx P L} (p : VegasCore P L Γ) (env : VEnv L Γ) :
    runSmallStepCore σ p env = outcomeDist σ p env := by
  induction p with
  | ret payoffs =>
      rfl
  | letExpr x e k ih =>
      exact ih _
  | sample x D k ih =>
      simp only [runSmallStepCore, outcomeDist]
      congr
      funext v
      exact ih _
  | commit x who R k ih =>
      simp only [runSmallStepCore, outcomeDist]
      congr
      funext v
      exact ih _
  | reveal y who x hx k ih =>
      exact ih _

/-- The raw small-step evaluator is the existing denotational semantics,
repackaged over `World`. -/
theorem runSmallStep_eq_outcomeDist
    (σ : OmniscientOperationalProfile P L) (w : World P L) :
    runSmallStep σ w = outcomeDist σ w.prog w.env := by
  exact runSmallStepCore_eq_outcomeDist σ w.prog w.env

/-- The raw evaluator is characterized by one probabilistic `Step` followed by
recursive evaluation of the target world. This makes the `Step` relation, not
just the structural recursion, semantically central. -/
theorem step_bind_runSmallStep
    {σ : OmniscientOperationalProfile P L} {w : World P L}
    {d : FDist (Label P L × World P L)}
    (hstep : Step σ w d) :
    d.bind (fun lw => runSmallStep σ lw.2) = runSmallStep σ w := by
  cases hstep with
  | letExpr env =>
      rw [FDist.pure_bind]
      rfl
  | sample env =>
      rw [FDist.bind_assoc]
      congr
      funext v
      rw [FDist.pure_bind]
      rfl
  | commit env =>
      rw [FDist.bind_assoc]
      congr
      funext v
      rw [FDist.pure_bind]
      rfl
  | reveal env =>
      rw [FDist.pure_bind]
      rfl

end SmallStep
end Vegas
