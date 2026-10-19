/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryPools

/-! # Quantitative ordinary-domain mass before pooled optimization -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  [Fintype setup.proposalRecoveryProtocol.History]

/-- Every ordinary semantic value has a fixed reference contribution before
the pooled weights are optimized. This bound retains the actual finite menu
cardinality and is independent of both the selected weights and bad rate. -/
theorem proposalRecoveryPooledDomainLaw_lower
    (finite : setup.program.FiniteBindingTypes)
    (floor : ℝ) (nonnegative : 0 ≤ floor) (bounded : floor ≤ 1)
    (pins : (pool : setup.ProposalRecoveryValuePool) →
      Option (PMF (setup.ProposalRecoveryPoolPart pool)))
    (weights : (pool : setup.ProposalRecoveryValuePool) →
      PMF (setup.ProposalRecoveryPoolPart pool))
    (who : Player) (key : setup.ProposalRecoveryComponent who)
    (value : setup.CommitRecoveryValueChoice who key.1) :
    floor / Nat.card (setup.CommitRecoveryValueChoice who key.1) ≤
      (setup.proposalRecoveryPooledDomainLaw finite floor nonnegative bounded
        pins weights who key value).toReal := by
  classical
  let _ := setup.commitRecoveryValueChoice_finite finite who key.1
  let _ := Fintype.ofFinite (setup.CommitRecoveryValueChoice who key.1)
  let _ := setup.commitRecoveryValueChoice_nonempty who key.1
  let rest := if present : key ∈ setup.proposalRecoveryDomainSites who then
      (pins ⟨who, ⟨key, present⟩⟩).getD (weights ⟨who, ⟨key, present⟩⟩)
    else setup.commitRecoveryValueReference finite who key.1
  simpa only [proposalRecoveryPooledDomainLaw, commitRecoveryValueReference,
    Nat.card_eq_fintype_card, rest] using
      div_card_le_mix_uniform_apply floor nonnegative bounded rest value

end Vegas.SourceProgram.Setup
