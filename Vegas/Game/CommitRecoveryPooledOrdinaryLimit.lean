/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryPooledAgentGains

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

variable (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
  [Fintype setup.commitRecoveryProtocol.History]
  (omission bad floor : ℕ → ℝ)
  (omissionNonnegative : ∀ n, 0 ≤ omission n) (omissionBounded : ∀ n, omission n ≤ 1)
  (badNonnegative : ∀ n, 0 ≤ bad n) (badBounded : ∀ n, bad n ≤ 1)
  (floorNonnegative : ∀ n, 0 ≤ floor n) (floorBounded : ∀ n, floor n ≤ 1)
  (pins : ℕ → (pool : setup.CommitRecoveryValuePool finite) →
    Option (PMF (setup.CommitRecoveryPoolPart finite pool)))
  (omissionVanishes : Tendsto omission atTop (nhds 0))
  (badVanishes : Tendsto bad atTop (nhds 0))
  (floorVanishes : Tendsto floor atTop (nhds 0))

include omissionVanishes badVanishes floorVanishes

open Classical in
/-- Actual unpinned components converge to their original domain choice;
the failure flags and domain floor are the prescribed source perturbations. -/
theorem commitRecoveryPoolComponent_unpinned_converges
    (agent : setup.commitRecoveryModel.InformationAgent setup.commitRecoveryModel.playedInformation)
    (unpinned : ∀ n, pins n (setup.commitRecoveryAgentPool finite agent) = none)
    (part : setup.CommitRecoveryPoolPart finite (setup.commitRecoveryAgentPool finite agent)) :
    PMFConvergesPointwise
      (fun n => setup.commitRecoveryPoolComponent finite
        (omission n) (omissionNonnegative n) (omissionBounded n)
        (bad n) (badNonnegative n) (badBounded n)
        (floor n) (floorNonnegative n) (floorBounded n) (pins n) agent part)
      (PMF.pure ((setup.commitRecoveryNoMissErasedChoice agent.1 agent.2.val).symm part.val)) := by
  let query := (setup.commitRecoveryAgentPool finite agent).2.val
  have omitted := pmfConvergesPointwise_mix_zero omission omissionNonnegative omissionBounded
    omissionVanishes (PMF.pure true) (PMF.pure false)
  have failed := pmfConvergesPointwise_mix_zero bad badNonnegative badBounded
    badVanishes (PMF.pure true) (PMF.pure false)
  have flags : PMFConvergesPointwise
      (fun n => commitRecoveryFlagLaw (omission n) (omissionNonnegative n) (omissionBounded n)
        (bad n) (badNonnegative n) (badBounded n)) (PMF.pure (false, false)) := by
    simpa only [commitRecoveryFlagLaw, PMF.pure_bind, PMF.pure_map] using
      omitted.bind (fun bit => failed.map (Prod.mk bit))
  have values := pmfConvergesPointwise_mix_zero floor floorNonnegative floorBounded
    floorVanishes (setup.commitRecoveryValueReference finite agent.1 query) (PMF.pure part)
  have decoded := (flags.bind (fun bits =>
    values.map (setup.commitRecoveryValueFlags agent.1 query bits.1 bits.2))).map
      (setup.commitRecoveryNoMissErasedChoice agent.1 agent.2.val).symm
  simp only [PMF.pure_bind, PMF.pure_map, commitRecoveryValueFlags, Bool.false_eq_true,
    ↓reduceIte, Bool.and_false] at decoded
  convert decoded using 1
  funext n
  simp only [commitRecoveryPoolComponent, unpinned, Option.getD_none]
  rw [← setup.commitRecoveryFlagLaw_choice, PMF.map_bind]

open Classical in
/-- Every domain lottery is optimal at an ordinary unpinned site of the same
actual source limit. The only finite-stage incentive premise is the original
whole-pool completion inequality; failed attachments are removed by the
actual conditional terminal-law comparison. -/
theorem commitRecovery_pooled_ordinary_limit_domain_optimal
    (sequence : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
    (limit : setup.commitRecoveryModel.BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence limit)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.commitRecoveryModel (sequence n) setup.commitRecoveryModel_decisionAntichain)
    (weights : ℕ → (pool : setup.CommitRecoveryValuePool finite) →
      PMF (setup.CommitRecoveryPoolPart finite pool))
    (prescribed : ∀ n who (history : setup.commitRecoveryProtocol.History)
      (_running : ¬ setup.commitRecoveryProtocol.terminal history.state),
      (sequence n).strategy who (setup.commitRecoveryModel.infoOf who history.trace) =
        setup.commitRecoveryNormalizedTrembledProfile
          (omission n) (omissionNonnegative n) (omissionBounded n)
          (bad n) (badNonnegative n) (badBounded n)
          (setup.commitRecoveryPooledDomainLaw finite (floor n) (floorNonnegative n)
            (floorBounded n) (pins n) (weights n)) who
              (setup.commitRecoveryModel.infoOf who history.trace))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (pooled : ∀ n alternative pool,
      ∑ agent ∈ Finset.univ.filter (fun agent => setup.commitRecoveryAgentPool finite agent = pool),
        setup.commitRecoveryComponentGain finite (sequence n)
          (omission n) (omissionNonnegative n) (omissionBounded n)
          (bad n) (badNonnegative n) (badBounded n)
          (floor n) (floorNonnegative n) (floorBounded n) (pins n)
          alternative utility excludedPayoff agent ≤ 0)
    (focal : Player) (source : setup.commitRecoveryModel.InformationSite focal)
    (committing : source.1.1.1.1.elim false (ProtocolView.atCommit focal setup.program) = true)
    (ordinary : source.1.1.1.2.1 = setup.commitRecoverySavedExclusions focal source.1)
    (unpinned : ∀ n, pins n (setup.commitRecoveryAgentPool finite
      (setup.commitRecoveryModel.agentAt source)) = none)
    (law : PMF (setup.CommitRecoveryPoolPart finite
      (setup.commitRecoveryAgentPool finite (setup.commitRecoveryModel.agentAt source)))) :
    (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories source
      (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
        ((limit.strategy focal).withLaw source.1
          (law.map (fun part => (setup.commitRecoveryNoMissErasedChoice focal source.1).symm
            part.val))) ≤
      (limit.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories source
        (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          (limit.strategy focal) := by
  classical
  let agent := setup.commitRecoveryModel.agentAt source
  let component := fun n => setup.commitRecoveryPoolComponent finite
    (omission n) (omissionNonnegative n) (omissionBounded n)
    (bad n) (badNonnegative n) (badBounded n)
    (floor n) (floorNonnegative n) (floorBounded n) (pins n) agent
  have current : PMFConvergesPointwise (fun n => law.bind (component n))
      (law.map (fun part => (setup.commitRecoveryNoMissErasedChoice focal source.1).symm
        part.val)) := by
    have result := (pmfConvergesPointwise_const law).bind
      (kernel := component) (fun part => setup.commitRecoveryPoolComponent_unpinned_converges
        finite omission bad floor omissionNonnegative omissionBounded badNonnegative badBounded
        floorNonnegative floorBounded pins omissionVanishes badVanishes floorVanishes
        agent unpinned part)
    convert result using 1
    rfl
  have bound (n : ℕ) :
      ((sequence n).continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        source (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          (((sequence n).strategy focal).withLaw source.1 (law.bind (component n))) ≤
      ((sequence n).continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        source (setup.commitRecoveryPayoff utility excludedPayoff focal)).value
          ((sequence n).strategy focal) := by
    let alternative := Function.update (weights n) (setup.commitRecoveryAgentPool finite agent) law
    have single := setup.commitRecovery_pooled_ordinary_component_optimal finite (sequence n)
      (omission n) (omissionNonnegative n) (omissionBounded n)
      (bad n) (badNonnegative n) (badBounded n)
      (floor n) (floorNonnegative n) (floorBounded n) (pins n) alternative utility excludedPayoff
      (mixed n) (bayes n) (weights n) (prescribed n) focal source committing ordinary
      (pooled n alternative (setup.commitRecoveryAgentPool finite agent))
    simp only [commitRecoveryComponentGain, agent, source.property, dite_eq_left,
      alternative, Function.update_self] at single
    change _ - _ ≤ 0 at single
    convert sub_nonpos.mp single using 1
    all_goals rfl
  let payoff := setup.commitRecoveryPayoff utility excludedPayoff focal
  let total := ∑ history : setup.commitRecoveryProtocol.History, |payoff history|
  have totalBound (history : setup.commitRecoveryProtocol.History) : |payoff history| ≤ total :=
    Finset.single_le_sum (fun other _ => abs_nonneg (payoff other)) (Finset.mem_univ history)
  have value (replacement : ℕ → setup.commitRecoveryModel.BehavioralPolicy focal)
      (target : setup.commitRecoveryModel.BehavioralPolicy focal)
      (policies : ∀ decision : setup.commitRecoveryModel.InformationSite focal,
        PMFConvergesPointwise (fun n => replacement n decision.1) (target decision.1)) :=
    setup.commitRecoveryModel.continuationContext_value_tendsto_of_bounded_terminal
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories
      (fun who decision => converges.strategy who decision) focal source
      (converges.belief focal source) policies payoff total
      ((abs_nonneg _).trans (totalBound setup.commitRecoveryProtocol.initHistory))
      (fun final _ => totalBound final)
  have installed (decision : setup.commitRecoveryModel.InformationSite focal) :
      PMFConvergesPointwise
        (fun n => ((sequence n).strategy focal).withLaw source.1
          (law.bind (component n)) decision.1)
        (((limit.strategy focal).withLaw source.1
          (law.map (fun part => (setup.commitRecoveryNoMissErasedChoice focal source.1).symm
            part.val))) decision.1) := by
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
