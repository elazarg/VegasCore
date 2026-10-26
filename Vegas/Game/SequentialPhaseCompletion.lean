/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseComponents
import Vegas.Game.PhaseExclusionPayoff
import GameTheoryExtensions.Analysis.Protocol.ComponentCompletion
import Interaction.ReactiveOwnPlay

/-! # Common pooled completion on the actual singleton phase game

All operational pool weights and richer free information sites are optimized
together for the original phase payoff. One common mixed Bayes sequence and
its consistent limit are retained; source comparisons at forced sites remain
separate obligations.
-/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (Vegas.graph setup))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  [(phaseApplication runtime leaks).FiniteNature (phaseInitialLaw setup) scheduler]

local notation "M" => model setup runtime leaks bounds horizon scheduler

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

open Classical in
/-- The actual phase game selects one simultaneous free/keyed pooled
completion. Its original parameterized ordinary terminal utility is unchanged. -/
theorem exists_consistent_completion {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (sourceSequence : ℕ → setup.intendedModel.BehavioralAssessment) (slots : Nat)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (vanishes : Tendsto scale atTop (nhds 0)) :
    let parts := Part setup runtime leaks bounds horizon scheduler slots
    let pools := pool setup runtime leaks bounds horizon scheduler
    let laws := fun n => component setup runtime leaks bounds horizon scheduler (sourceSequence n)
      (slots := slots) (scale n) (positive n).le (le_one n)
    let fallback : ∀ who, (M).Policy who := fun _ _ => Classical.arbitrary _
    let certificate := (menu setup runtime leaks bounds).bounded (phaseInitialLaw setup) horizon
      scheduler
      |>.wellFoundedHistories
    let payoff := fun who (final : (menu setup runtime leaks bounds).protocol (phaseInitialLaw
      setup)
        horizon
        scheduler |>.History) => phaseExclusionBase setup .sequential runtime leaks
      (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
        final.state who
    ∃ (weights : ℕ → ∀ p, PMF (parts p)) (sequence : ℕ → (M).BehavioralAssessment)
      (limit : (M).BehavioralAssessment) (index : ℕ → ℕ),
      (∀ n, (sequence n).strategy = (M).agentBehavior (M).playedInformation fallback
        fun agent => (weights n (pools agent)).bind (laws n agent)) ∧
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, BehavioralAssessment.IsBayesConsistent (M) (sequence n)
        ((menu setup runtime leaks bounds).decisionRecall (phaseInitialLaw setup) horizon
          scheduler).decisionInformationAntichain) ∧
      StrictMono index ∧
      BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit ∧
      limit.IsSequentiallyConsistent
        ((menu setup runtime leaks bounds).decisionRecall (phaseInitialLaw setup) horizon
          scheduler).decisionInformationAntichain ∧
      (∀ n (alternative : ∀ p, PMF (parts p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => pools agent = p),
          (if decision : (M).IsDecisionInfo agent.1 agent.2.1 then
            ((sequence n).continuationContext certificate ⟨agent.2.1, decision⟩
                (payoff agent.1)).value
                (((sequence n).strategy agent.1).withLaw agent.2.1
                  ((alternative (pools agent)).bind (laws n agent))) -
              ((sequence n).continuationContext certificate ⟨agent.2.1, decision⟩
                (payoff agent.1)).value ((sequence n).strategy agent.1)
          else 0) ≤ 0) ∧
      (∀ who (site : (M).InformationSite who)
        (limitComponent : parts (pools ((M).agentAt site)) → PMF ((M).Choice who site.1)),
        (∀ part, PMFConvergesPointwise (fun n => laws n ((M).agentAt site) part)
          (limitComponent part)) →
        (∃ limitWeights : PMF (parts (pools ((M).agentAt site))),
          limit.strategy who site.1 = limitWeights.bind limitComponent) ∧
        ∀ (error : ℕ → ℝ), Tendsto error atTop (nhds 0) →
          (∀ n (alternative : PMF (parts (pools ((M).agentAt site)))),
            ((sequence n).continuationContext certificate site (payoff who)).value
                (((sequence n).strategy who).withLaw site.1
                  (alternative.bind (laws n ((M).agentAt site)))) ≤
              ((sequence n).continuationContext certificate site (payoff who)).value
                ((sequence n).strategy who) + error n) →
          ∀ alternative : PMF (parts (pools ((M).agentAt site))),
            (limit.continuationContext certificate site (payoff who)).value
                ((limit.strategy who).withLaw site.1 (alternative.bind limitComponent)) ≤
              (limit.continuationContext certificate site (payoff who)).value
                (limit.strategy who)) ∧
      ∀ who (site : (M).InformationSite who),
        FreeAgent setup runtime leaks bounds horizon scheduler ((M).agentAt site) →
          ∀ law : PMF ((M).Choice who site.1),
            (limit.continuationContext certificate site (payoff who)).value
                ((limit.strategy who).withLaw site.1 law) ≤
              (limit.continuationContext certificate site (payoff who)).value
                (limit.strategy who) := by
  classical
  intro parts pools laws fallback certificate payoff
  obtain ⟨weights, sequence, limit, index, assembled, mixed, bayes, increasing, converges,
      consistent, pooled, limits⟩ :=
    (M).exists_consistent_pooled_completion
      ((menu setup runtime leaks bounds).decisionRecall (phaseInitialLaw setup) horizon scheduler)
      fallback certificate payoff pools laws
      (fun n agent part => component_fullSupport setup runtime leaks bounds horizon scheduler
        (sourceSequence n) (positive n) (le_one n) agent part)
  refine ⟨weights, sequence, limit, index, assembled, mixed, bayes, increasing, converges,
    consistent, pooled, limits, ?_⟩
  intro who site isFree law
  let identify := freeIdentify
    (keyed := KeyedAgent setup runtime leaks bounds horizon scheduler)
    (key := agentKey setup runtime leaks bounds horizon scheduler) (Opt := LateOption slots) isFree
  let limitComponent := fun part => PMF.pure (identify part)
  have componentsConverge (part : parts (pools ((M).agentAt site))) :
      PMFConvergesPointwise (fun n => laws n ((M).agentAt site) part) (limitComponent part) := by
    have same : (fun n => laws n ((M).agentAt site) part) = fun n =>
        freeLaw setup runtime leaks bounds horizon scheduler (scale n) (positive n).le (le_one n)
          ((M).agentAt site) (identify part) := by
      funext n
      exact freeKeyedComponent_of_free _ _ _ isFree part
    rw [same]
    exact freeLaw_converges setup runtime leaks bounds horizon scheduler scale positive le_one
      vanishes
      ((M).agentAt site) (identify part)
  have finiteOptimal (n : ℕ) (alternative : PMF (parts (pools ((M).agentAt site)))) :
      ((sequence n).continuationContext certificate site (payoff who)).value
          (((sequence n).strategy who).withLaw site.1
            (alternative.bind (laws n ((M).agentAt site)))) ≤
        ((sequence n).continuationContext certificate site (payoff who)).value
          ((sequence n).strategy who) + 0 := by
    have single : Finset.univ.filter (fun agent => pools agent = pools ((M).agentAt site)) =
        {(M).agentAt site} := by
      ext agent
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro same
        dsimp only [pools, pool] at same
        rw [freeKeyedPool_of_free isFree] at same
        exact eq_of_freeKeyedPool_eq_inl same
      · rintro rfl
        rfl
    have bound := pooled n (Function.update (weights n) (pools ((M).agentAt site)) alternative)
      (pools ((M).agentAt site))
    rw [single, Finset.sum_singleton, dite_eq_left site.2] at bound
    simp only [Function.update_self] at bound
    change ((sequence n).continuationContext certificate site (payoff who)).value
        (((sequence n).strategy who).withLaw site.1
          (alternative.bind (laws n ((M).agentAt site)))) -
      ((sequence n).continuationContext certificate site (payoff who)).value
        ((sequence n).strategy who) ≤ 0 at bound
    simpa only [add_zero] using sub_nonpos.mp bound
  have spanning : (law.map identify.symm).bind limitComponent = law := by
    rw [PMF.bind_map]
    have same : limitComponent ∘ identify.symm = PMF.pure := by
      funext choice
      simp only [limitComponent, Function.comp_apply, Equiv.apply_symm_apply]
    rw [same, PMF.bind_pure]
  have optimal := (limits who site limitComponent componentsConverge).2
    (fun _ => 0) tendsto_const_nhds finiteOptimal (law.map identify.symm)
  simpa only [spanning] using optimal

end Vegas.SequentialPhase
