/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.PassageRestrictionExtension

/-! # Consistent completion with restricted choices at new sites

Retained sites keep a prescribed consistent assessment. Every other information
agent chooses among an embedded nonempty finite menu, with full-menu trembles.
The common limit retains the prescribed beliefs and is optimal among its
restricted local laws, including at histories created by unrestricted trembles.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel.ActionRestriction

open GameTheory.Math.Probability Filter ExecutionProtocol

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E T : ExecutionProtocol ι} {M : InformationModel E} {N : InformationModel T}
  [Finite T.History] [∀ i, DecidableEq (N.InfoState i)]
  (restriction : M.ActionRestriction N)

/-- One common fully mixed approximation of a restricted completion. Every
local law is a tremble of an allowed lottery, with the source lottery retained
at prescribed sites. -/
structure RestrictedExtensionApproximation
    (reference target : N.BehavioralAssessment)
    (antichain : N.DecisionInformationAntichain)
    {Allowed : (who : ι) → N.InfoState who → Type*}
    (allowed : ∀ who info, Allowed who info ↪ N.Choice who info) where
  sequence : ℕ → N.BehavioralAssessment
  index : ℕ → ℕ
  increasing : StrictMono index
  converges : BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) target
  mixed : ∀ n, (sequence n).IsFullyMixed
  bayes : ∀ n, BehavioralAssessment.IsBayesConsistent N (sequence n) antichain
  epsilon : ℕ → ℝ
  positive : ∀ n, 0 < epsilon n
  small : ∀ n, epsilon n < 1
  vanishes : Tendsto epsilon atTop (nhds 0)
  retained : ∀ n who (site : M.InformationSite who),
    ∃ law : PMF (M.Choice who site.1),
      (sequence n).strategy who (restriction.information who site.1) =
        mix (epsilon n) (positive n).le (small n).le
          (reference.strategy who (restriction.information who site.1))
          (law.map (restriction.choice who site.1))
  fresh : ∀ n who (site : N.InformationSite who), ¬ restriction.Retained who site.1 →
    ∃ law : PMF (Allowed who site.1),
      (sequence n).strategy who site.1 =
        mix (epsilon n) (positive n).le (small n).le (reference.strategy who site.1)
          (law.map (allowed who site.1))

end GameTheory.Protocol.InformationModel.ActionRestriction
