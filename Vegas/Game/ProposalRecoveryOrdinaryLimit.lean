/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProposalRecoveryAgentGains

/-! # Domain optimality of the same ordinary source limit

Fixed occurrence flags and the domain floor vanish in each actual unpinned
component. The original pooled inequalities therefore pass to individual
ordinary domain comparisons at the same consistent source limit.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

section Components

variable (finite : setup.program.FiniteBindingTypes)
  [Fintype setup.proposalRecoveryProtocol.History]
  (omission bad delivery floor : ℕ → ℝ)
  (omissionNonnegative : ∀ n, 0 ≤ omission n) (omissionBounded : ∀ n, omission n ≤ 1)
  (badNonnegative : ∀ n, 0 ≤ bad n) (badBounded : ∀ n, bad n ≤ 1)
  (deliveryNonnegative : ∀ n, 0 ≤ delivery n) (deliveryBounded : ∀ n, delivery n ≤ 1)
  (floorNonnegative : ∀ n, 0 ≤ floor n) (floorBounded : ∀ n, floor n ≤ 1)
  (pins : ℕ → (pool : setup.ProposalRecoveryValuePool) →
    Option (PMF (setup.ProposalRecoveryPoolPart pool)))
  (omissionVanishes : Tendsto omission atTop (nhds 0))
  (badVanishes : Tendsto bad atTop (nhds 0))
  (deliveryVanishes : Tendsto delivery atTop (nhds 0))
  (floorVanishes : Tendsto floor atTop (nhds 0))

include omissionVanishes badVanishes deliveryVanishes floorVanishes

open Classical in
omit [Fintype Player] in
/-- Actual unpinned components converge to their original domain choice;
the failure flags and domain floor are the prescribed source perturbations. -/
theorem proposalRecoveryPoolComponent_unpinned_converges
    (agent : setup.proposalRecoveryModel.InformationAgent
      setup.proposalRecoveryModel.playedInformation)
    (unpinned : ∀ n, pins n (setup.proposalRecoveryAgentPool agent) = none)
    (part : setup.ProposalRecoveryPoolPart (setup.proposalRecoveryAgentPool agent)) :
    PMFConvergesPointwise
      (fun n => setup.proposalRecoveryPoolComponent finite
        (omission n) (omissionNonnegative n) (omissionBounded n)
        (bad n) (badNonnegative n) (badBounded n)
        (delivery n) (deliveryNonnegative n) (deliveryBounded n)
        (floor n) (floorNonnegative n) (floorBounded n) (pins n) agent part)
      (PMF.pure ((setup.proposalRecoveryComponentChoice agent.1 agent.2.val).symm
        (setup.proposalRecoveryComponentLabelChoice agent.1
          (setup.proposalRecoveryAgentPool agent).2.val false part.val))) := by
  let query := (setup.proposalRecoveryAgentPool agent).2.val
  have omitted := pmfConvergesPointwise_mix_zero omission omissionNonnegative omissionBounded
    omissionVanishes (PMF.pure true) (PMF.pure false)
  have failed := pmfConvergesPointwise_mix_zero bad badNonnegative badBounded
    badVanishes (PMF.pure true) (PMF.pure false)
  have delivered := pmfConvergesPointwise_mix_zero delivery deliveryNonnegative deliveryBounded
    deliveryVanishes (PMF.pure true) (PMF.pure false)
  have flags : PMFConvergesPointwise
      (fun n => commitRecoveryFlagLaw (omission n) (omissionNonnegative n) (omissionBounded n)
        (bad n) (badNonnegative n) (badBounded n)) (PMF.pure (false, false)) := by
    simpa only [commitRecoveryFlagLaw, PMF.pure_bind, PMF.pure_map] using
      omitted.bind (fun bit => failed.map (Prod.mk bit))
  have values := pmfConvergesPointwise_mix_zero floor floorNonnegative floorBounded
    floorVanishes (setup.commitRecoveryValueReference finite agent.1 query.1) (PMF.pure part)
  have semantic := flags.bind (fun bits =>
    values.map (setup.commitRecoveryValueFlags agent.1 query.1 bits.1 bits.2))
  have decoded := (semantic.bind (fun choice =>
    delivered.map (fun requested =>
      setup.proposalRecoveryComponentLabelChoice agent.1 query requested choice))).map
        (setup.proposalRecoveryComponentChoice agent.1 agent.2.val).symm
  simp only [PMF.pure_bind, PMF.pure_map, commitRecoveryValueFlags, Bool.false_eq_true,
    ite_false, Bool.and_false] at decoded
  convert decoded using 1
  funext n
  simp only [proposalRecoveryPoolComponent, proposalRecoveryComponentTrembledLaw,
    unpinned, Option.getD_none]
  rw [← setup.commitRecoveryFlagLaw_choice, PMF.map_bind]

open Classical in
/-- Every domain lottery is optimal at an ordinary unpinned site of the same
actual source limit. The only finite-stage incentive premise is the original
whole-pool completion inequality; failed attachments are removed by the
actual conditional terminal-law comparison. -/
theorem proposalRecovery_pooled_ordinary_limit_domain_optimal
    (sequence : ℕ → setup.proposalRecoveryModel.BehavioralAssessment)
    (limit : setup.proposalRecoveryModel.BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence limit)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.proposalRecoveryModel (sequence n) setup.proposalRecoveryModel_decisionAntichain)
    (weights : ℕ → (pool : setup.ProposalRecoveryValuePool) →
      PMF (setup.ProposalRecoveryPoolPart pool))
    (prescribed : ∀ n who (history : setup.proposalRecoveryProtocol.History)
      (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
      (sequence n).strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          (omission n) (omissionNonnegative n) (omissionBounded n)
          (bad n) (badNonnegative n) (badBounded n)
          (delivery n) (deliveryNonnegative n) (deliveryBounded n)
          (setup.proposalRecoveryPooledDomainLaw finite (floor n) (floorNonnegative n)
            (floorBounded n) (pins n) (weights n)) who
              (setup.proposalRecoveryModel.infoOf who history.trace))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (pooled : ∀ n alternative pool,
      ∑ agent ∈ Finset.univ.filter (fun agent => setup.proposalRecoveryAgentPool agent = pool),
        setup.proposalRecoveryComponentGain finite (sequence n)
          (omission n) (omissionNonnegative n) (omissionBounded n)
          (bad n) (badNonnegative n) (badBounded n)
          (delivery n) (deliveryNonnegative n) (deliveryBounded n)
          (floor n) (floorNonnegative n) (floorBounded n) (pins n)
          alternative utility excludedPayoff agent ≤ 0)
    (focal : Player) (source : setup.proposalRecoveryModel.InformationSite focal)
    (first : CommitRecoveryState setup.program)
    (firstTrace : setup.proposalRecoveryProtocol.Trace (some first))
    (sourceAt : setup.proposalRecoveryModel.infoOf focal firstTrace = source.1)
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (ordinary : first.excluded = first.entryExcluded)
    (unpinned : ∀ n, pins n (setup.proposalRecoveryAgentPool
      (setup.proposalRecoveryModel.agentAt source)) = none)
    (law : PMF (setup.ProposalRecoveryPoolPart
      (setup.proposalRecoveryAgentPool (setup.proposalRecoveryModel.agentAt source)))) :
    (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories source
      (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw source.1
          (law.map (fun part => (setup.proposalRecoveryComponentChoice focal source.1).symm
            (setup.proposalRecoveryComponentLabelChoice focal
              (setup.proposalRecoveryQuery focal source.1) false part.val)))) ≤
      (limit.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories source
        (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
          (limit.strategy focal) := by
  classical
  let agent := setup.proposalRecoveryModel.agentAt source
  let component := fun n => setup.proposalRecoveryPoolComponent finite
    (omission n) (omissionNonnegative n) (omissionBounded n)
    (bad n) (badNonnegative n) (badBounded n)
    (delivery n) (deliveryNonnegative n) (deliveryBounded n)
    (floor n) (floorNonnegative n) (floorBounded n) (pins n) agent
  have current : PMFConvergesPointwise (fun n => law.bind (component n))
      (law.map (fun part => (setup.proposalRecoveryComponentChoice focal source.1).symm
        (setup.proposalRecoveryComponentLabelChoice focal
          (setup.proposalRecoveryQuery focal source.1) false part.val))) := by
    have result := (pmfConvergesPointwise_const law).bind
      (kernel := component) (fun part => setup.proposalRecoveryPoolComponent_unpinned_converges
        finite omission bad delivery floor omissionNonnegative omissionBounded
        badNonnegative badBounded deliveryNonnegative deliveryBounded
        floorNonnegative floorBounded pins omissionVanishes badVanishes
        deliveryVanishes floorVanishes
        agent unpinned part)
    convert result using 1
    rfl
  have bound (n : ℕ) :
      ((sequence n).continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
        source (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
          (((sequence n).strategy focal).withLaw source.1 (law.bind (component n))) ≤
      ((sequence n).continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
        source (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value
          ((sequence n).strategy focal) := by
    let alternative := Function.update (weights n) (setup.proposalRecoveryAgentPool agent) law
    have single := setup.proposalRecovery_pooled_ordinary_component_optimal finite (sequence n)
      (omission n) (omissionNonnegative n) (omissionBounded n)
      (bad n) (badNonnegative n) (badBounded n)
      (delivery n) (deliveryNonnegative n) (deliveryBounded n)
      (floor n) (floorNonnegative n) (floorBounded n) (pins n) alternative utility excludedPayoff
      (mixed n) (bayes n) (weights n) (prescribed n) focal source first firstTrace
      sourceAt committing ordinary
      (pooled n alternative (setup.proposalRecoveryAgentPool agent))
    simp only [proposalRecoveryComponentGain, agent, source.property, dite_eq_left,
      alternative, Function.update_self] at single
    change _ - _ ≤ 0 at single
    convert sub_nonpos.mp single using 1
    all_goals rfl
  let payoff := setup.proposalRecoveryPayoff utility excludedPayoff focal
  let total := ∑ history : setup.proposalRecoveryProtocol.History, |payoff history|
  have totalBound (history : setup.proposalRecoveryProtocol.History) : |payoff history| ≤ total :=
    Finset.single_le_sum (fun other _ => abs_nonneg (payoff other)) (Finset.mem_univ history)
  have value (replacement : ℕ → setup.proposalRecoveryModel.BehavioralPolicy focal)
      (target : setup.proposalRecoveryModel.BehavioralPolicy focal)
      (policies : ∀ decision : setup.proposalRecoveryModel.InformationSite focal,
        PMFConvergesPointwise (fun n => replacement n decision.1) (target decision.1)) :=
    setup.proposalRecoveryModel.continuationContext_value_tendsto_of_bounded_terminal
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
      (fun who decision => converges.strategy who decision) focal source
      (converges.belief focal source) policies payoff total
      ((abs_nonneg _).trans (totalBound setup.proposalRecoveryProtocol.initHistory))
      (fun final _ => totalBound final)
  have installed (decision : setup.proposalRecoveryModel.InformationSite focal) :
      PMFConvergesPointwise
        (fun n => ((sequence n).strategy focal).withLaw source.1
          (law.bind (component n)) decision.1)
        (((limit.strategy focal).withLaw source.1
          (law.map (fun part => (setup.proposalRecoveryComponentChoice focal source.1).symm
            (setup.proposalRecoveryComponentLabelChoice focal
              (setup.proposalRecoveryQuery focal source.1) false part.val)))) decision.1) := by
    by_cases same : decision.1 = source.1
    · have equal : decision = source := Subtype.ext same
      subst decision
      simpa only [InformationModel.BehavioralPolicy.withLaw_self] using current
    · simpa only [InformationModel.BehavioralPolicy.withLaw_of_ne _ _ _ same] using
        converges.strategy focal decision
  exact le_of_tendsto_of_tendsto' (value _ _ installed)
    (value _ _ (converges.strategy focal)) bound

end Components

end Vegas.SourceProgram.Setup
