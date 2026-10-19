/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryPools

/-! # One common consistent assessment sequence on enriched source pools -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  [Fintype setup.proposalRecoveryProtocol.History]

open Classical in
/-- The existing finite component-completion engine selects all free domains
simultaneously. Every approximation is fully mixed and Bayes, rates and floors
remain caller chosen, and a single subsequence supplies all limiting beliefs.
Individual incentive transfer and the intended-law pins are separate proofs. -/
theorem exists_consistent_proposalRecovery_pool
    (finite : setup.program.FiniteBindingTypes)
    (omission bad delivery floor : ℕ → ℝ)
    (omissionPositive : ∀ n, 0 < omission n) (omissionSmall : ∀ n, omission n < 1)
    (badPositive : ∀ n, 0 < bad n) (badSmall : ∀ n, bad n < 1)
    (deliveryPositive : ∀ n, 0 < delivery n) (deliverySmall : ∀ n, delivery n < 1)
    (floorPositive : ∀ n, 0 < floor n) (floorSmall : ∀ n, floor n < 1)
    (pins : ℕ → (pool : setup.ProposalRecoveryValuePool) →
      Option (PMF (setup.ProposalRecoveryPoolPart pool)))
    (fallback : (who : Player) → setup.proposalRecoveryModel.Policy who)
    (payoff : Player → setup.proposalRecoveryProtocol.History → ℝ) :
    let certificate := setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
    let component := fun n => setup.proposalRecoveryPoolComponent finite
      (omission n) (omissionPositive n).le (omissionSmall n).le
      (bad n) (badPositive n).le (badSmall n).le
      (delivery n) (deliveryPositive n).le (deliverySmall n).le
      (floor n) (floorPositive n).le (floorSmall n).le (pins n)
    ∃ (weights : ℕ → (pool : setup.ProposalRecoveryValuePool) →
        PMF (setup.ProposalRecoveryPoolPart pool))
      (sequence : ℕ → setup.proposalRecoveryModel.BehavioralAssessment)
      (limit : setup.proposalRecoveryModel.BehavioralAssessment) (index : ℕ → ℕ),
      (∀ n agent, (sequence n).strategy agent.1 agent.2.val =
        (weights n (setup.proposalRecoveryAgentPool agent)).bind (component n agent)) ∧
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
        setup.proposalRecoveryModel (sequence n) setup.proposalRecoveryModel_decisionAntichain) ∧
      StrictMono index ∧
      InformationModel.BehavioralAssessmentConvergesPointwise
        (fun n => sequence (index n)) limit ∧
      limit.IsSequentiallyConsistent setup.proposalRecoveryModel_decisionAntichain ∧
      (∀ n (alternative : (pool : setup.ProposalRecoveryValuePool) →
          PMF (setup.ProposalRecoveryPoolPart pool)) pool,
        ∑ agent ∈ Finset.univ.filter
            (fun agent => setup.proposalRecoveryAgentPool agent = pool),
          (if decision : setup.proposalRecoveryModel.IsDecisionInfo agent.1 agent.2.val then
            ((sequence n).continuationContext certificate
                ⟨agent.2.val, decision⟩ (payoff agent.1)).value
                (((sequence n).strategy agent.1).withLaw agent.2.val
                  ((alternative (setup.proposalRecoveryAgentPool agent)).bind
                    (component n agent))) -
              ((sequence n).continuationContext certificate
                ⟨agent.2.val, decision⟩ (payoff agent.1)).value ((sequence n).strategy agent.1)
          else 0) ≤ 0) ∧
      (∀ n who (history : setup.proposalRecoveryProtocol.History)
          (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
        (sequence n).strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
          setup.proposalRecoveryNormalizedTrembledProfile
            (omission n) (omissionPositive n).le (omissionSmall n).le
            (bad n) (badPositive n).le (badSmall n).le
            (delivery n) (deliveryPositive n).le (deliverySmall n).le
            (setup.proposalRecoveryPooledDomainLaw finite
              (floor n) (floorPositive n).le (floorSmall n).le (pins n) (weights n))
            who (setup.proposalRecoveryModel.infoOf who history.trace)) ∧
      ∀ who (site : setup.proposalRecoveryModel.InformationSite who)
        (limitComponent : setup.ProposalRecoveryPoolPart
          (setup.proposalRecoveryAgentPool (setup.proposalRecoveryModel.agentAt site)) →
            PMF (setup.proposalRecoveryModel.Choice who site.1)),
        (∀ part, PMFConvergesPointwise
          (fun n => component n (setup.proposalRecoveryModel.agentAt site) part)
          (limitComponent part)) →
        (∃ limitWeights : PMF (setup.ProposalRecoveryPoolPart
            (setup.proposalRecoveryAgentPool (setup.proposalRecoveryModel.agentAt site))),
          limit.strategy who site.1 = limitWeights.bind limitComponent) ∧
        ∀ (error : ℕ → ℝ), Tendsto error atTop (nhds 0) →
          (∀ n (alternative : PMF (setup.ProposalRecoveryPoolPart
              (setup.proposalRecoveryAgentPool (setup.proposalRecoveryModel.agentAt site)))),
            ((sequence n).continuationContext certificate site (payoff who)).value
                (((sequence n).strategy who).withLaw site.1
                  (alternative.bind (component n (setup.proposalRecoveryModel.agentAt site)))) ≤
              ((sequence n).continuationContext certificate site (payoff who)).value
                ((sequence n).strategy who) + error n) →
          ∀ alternative : PMF (setup.ProposalRecoveryPoolPart
              (setup.proposalRecoveryAgentPool (setup.proposalRecoveryModel.agentAt site))),
            (limit.continuationContext certificate site (payoff who)).value
                ((limit.strategy who).withLaw site.1 (alternative.bind limitComponent)) ≤
              (limit.continuationContext certificate site (payoff who)).value
                (limit.strategy who) := by
  classical
  dsimp only
  let _ (pool : setup.ProposalRecoveryValuePool) :
      Finite (setup.ProposalRecoveryPoolPart pool) :=
    setup.commitRecoveryValueChoice_finite finite pool.1 pool.2.val.1
  let _ (pool : setup.ProposalRecoveryValuePool) :
      Nonempty (setup.ProposalRecoveryPoolPart pool) :=
    setup.commitRecoveryValueChoice_nonempty pool.1 pool.2.val.1
  let certificate := setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
  let component := fun n => setup.proposalRecoveryPoolComponent finite
    (omission n) (omissionPositive n).le (omissionSmall n).le
    (bad n) (badPositive n).le (badSmall n).le
    (delivery n) (deliveryPositive n).le (deliverySmall n).le
    (floor n) (floorPositive n).le (floorSmall n).le (pins n)
  have decisionRecall := setup.proposalRecoveryModel.decisionRecall_of_perfectRecall
    setup.proposalRecoveryModel_perfectRecall
  obtain ⟨weights, sequence, limit, index, assembled, full, bayes, increasing,
      converges, consistent, gains, limitOptimal⟩ :=
    setup.proposalRecoveryModel.exists_consistent_pooled_completion decisionRecall fallback
      certificate payoff setup.proposalRecoveryAgentPool component (fun n agent part =>
        setup.proposalRecoveryPoolComponent_fullSupport finite
          (omission n) (omissionPositive n) (omissionSmall n)
          (bad n) (badPositive n) (badSmall n)
          (delivery n) (deliveryPositive n) (deliverySmall n)
          (floor n) (floorPositive n) (floorSmall n) (pins n) agent part)
  have agentLaw n agent : (sequence n).strategy agent.1 agent.2.val =
      (weights n (setup.proposalRecoveryAgentPool agent)).bind (component n agent) := by
    rw [assembled n, InformationModel.agentBehavior_at]
  have actual n who (history : setup.proposalRecoveryProtocol.History)
      (running : ¬ setup.proposalRecoveryProtocol.terminal history.state) :
      (sequence n).strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          (omission n) (omissionPositive n).le (omissionSmall n).le
          (bad n) (badPositive n).le (badSmall n).le
          (delivery n) (deliveryPositive n).le (deliverySmall n).le
          (setup.proposalRecoveryPooledDomainLaw finite
            (floor n) (floorPositive n).le (floorSmall n).le (pins n) (weights n))
          who (setup.proposalRecoveryModel.infoOf who history.trace) := by
    let agent : setup.proposalRecoveryModel.InformationAgent
        setup.proposalRecoveryModel.playedInformation :=
      ⟨who, ⟨_, setup.proposalRecoveryModel.mem_playedInformation running⟩⟩
    exact (agentLaw n agent).trans (setup.proposalRecoveryPoolComponent_bind finite
      (omission n) (omissionPositive n).le (omissionSmall n).le
      (bad n) (badPositive n).le (badSmall n).le
      (delivery n) (deliveryPositive n).le (deliverySmall n).le
      (floor n) (floorPositive n).le (floorSmall n).le (pins n) (weights n) agent)
  exact ⟨weights, sequence, limit, index, agentLaw, full, bayes, increasing,
    converges, consistent, gains, actual, limitOptimal⟩

end Vegas.SourceProgram.Setup
