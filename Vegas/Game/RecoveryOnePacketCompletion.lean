/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryPublicCompletion

/-! # A common consistent completion of recovery operational components

The actual finite recovery game chooses all free and keyed pool weights
together. Its common approximating sequence, Bayes beliefs, and mixture limit
are retained for the later continuation estimates.
-/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (initial : PMF (RecoveryState (graph setup)))
  (horizon : Nat) (scheduler : (recoveryApplication runtime leaks).Scheduler)
  [Fintype ((Recovery.onePacketMenu runtime leaks bounds).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq ((model setup runtime leaks bounds initial horizon scheduler).InfoState who)]

local notation "N" => model setup runtime leaks bounds initial horizon scheduler
local notation "menu" => Recovery.onePacketMenu runtime leaks bounds

open Classical in
/-- Simultaneous pooled completion on the actual recovery runtime. The result
retains one common witness for all clear operational and post-exclusion choices;
local estimates for nonfree agents remain explicit later proof obligations. -/
theorem exists_consistent_completion {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (sourceSequence : ℕ → setup.intendedModel.BehavioralAssessment) (slots : Nat)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (vanishes : Tendsto scale atTop (nhds 0)) :
    let parts := Part setup runtime leaks bounds initial horizon scheduler slots
    let pools := pool setup runtime leaks bounds initial horizon scheduler
    let laws := fun n => component setup runtime leaks bounds initial horizon scheduler
      (sourceSequence n)
      (slots := slots) (scale n) (positive n).le (le_one n)
    let fallback : ∀ who, (N).Policy who := fun _ _ => Classical.arbitrary _
    let certificate := (menu).bounded initial horizon scheduler |>.wellFoundedHistories
    let payoff := fun who (final : (menu).protocol initial horizon scheduler |>.History) =>
      recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff final.state who
    ∃ (weights : ℕ → ∀ p, PMF (parts p)) (sequence : ℕ → (N).BehavioralAssessment)
      (limit : (N).BehavioralAssessment) (index : ℕ → ℕ),
      (∀ n, (sequence n).strategy = (N).agentBehavior (N).playedInformation fallback
        fun agent => (weights n (pools agent)).bind (laws n agent)) ∧
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, BehavioralAssessment.IsBayesConsistent (N) (sequence n)
        ((menu).decisionRecall initial horizon scheduler).decisionInformationAntichain) ∧
      StrictMono index ∧
      BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit ∧
      limit.IsSequentiallyConsistent
        ((menu).decisionRecall initial horizon scheduler).decisionInformationAntichain ∧
      (∀ n (alternative : ∀ p, PMF (parts p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => pools agent = p),
          (if decision : (N).IsDecisionInfo agent.1 agent.2.1 then
            ((sequence n).continuationContext certificate ⟨agent.2.1, decision⟩
                (payoff agent.1)).value
                (((sequence n).strategy agent.1).withLaw agent.2.1
                  ((alternative (pools agent)).bind (laws n agent))) -
              ((sequence n).continuationContext certificate ⟨agent.2.1, decision⟩
                (payoff agent.1)).value ((sequence n).strategy agent.1)
          else 0) ≤ 0) ∧
      (∀ who (site : (N).InformationSite who)
        (limitComponent : parts (pools ((N).agentAt site)) → PMF ((N).Choice who site.1)),
        (∀ part, PMFConvergesPointwise (fun n => laws n ((N).agentAt site) part)
          (limitComponent part)) →
        (∃ limitWeights : PMF (parts (pools ((N).agentAt site))),
          limit.strategy who site.1 = limitWeights.bind limitComponent) ∧
        ∀ (error : ℕ → ℝ), Tendsto error atTop (nhds 0) →
          (∀ n (alternative : PMF (parts (pools ((N).agentAt site)))),
            ((sequence n).continuationContext certificate site (payoff who)).value
                (((sequence n).strategy who).withLaw site.1
                  (alternative.bind (laws n ((N).agentAt site)))) ≤
              ((sequence n).continuationContext certificate site (payoff who)).value
                ((sequence n).strategy who) + error n) →
          ∀ alternative : PMF (parts (pools ((N).agentAt site))),
            (limit.continuationContext certificate site (payoff who)).value
                ((limit.strategy who).withLaw site.1 (alternative.bind limitComponent)) ≤
              (limit.continuationContext certificate site (payoff who)).value
                (limit.strategy who)) ∧
      (∀ who (site : (N).InformationSite who),
        FreeAgent setup runtime leaks bounds initial horizon scheduler ((N).agentAt site) →
          ∀ law : PMF ((N).Choice who site.1),
            (limit.continuationContext certificate site (payoff who)).value
                ((limit.strategy who).withLaw site.1 law) ≤
              (limit.continuationContext certificate site (payoff who)).value
                (limit.strategy who)) ∧
      ∀ who (site : (N).InformationSite who), PublicExclusion setup runtime leaks site.1 →
        limit.IsSequentiallyRationalAt site
          (limit.continuationContext certificate site (payoff who)) := by
  intro parts pools laws fallback certificate payoff
  obtain ⟨weights, sequence, limit, index, assembled, mixed, bayes, increasing, converges,
      consistent, pooled, limits⟩ :=
    (N).exists_consistent_pooled_completion ((menu).decisionRecall initial horizon scheduler)
      fallback certificate payoff pools laws
      (fun n agent part => component_fullSupport setup runtime leaks bounds initial horizon
        scheduler
        (sourceSequence n) (positive n) (le_one n) agent part)
  have freeOptimal : ∀ who (site : (N).InformationSite who),
      FreeAgent setup runtime leaks bounds initial horizon scheduler ((N).agentAt site) →
        ∀ law : PMF ((N).Choice who site.1),
          (limit.continuationContext certificate site (payoff who)).value
              ((limit.strategy who).withLaw site.1 law) ≤
            (limit.continuationContext certificate site (payoff who)).value
              (limit.strategy who) := by
    intro who site isFree law
    let identify := freeIdentify
      (keyed := KeyedAgent setup runtime leaks bounds initial horizon scheduler)
      (key := agentKey setup runtime leaks bounds initial horizon scheduler) (Opt := LateOption
        slots)
      isFree
    let limitComponent := fun part => PMF.pure (identify part)
    have componentsConverge (part : parts (pools ((N).agentAt site))) :
        PMFConvergesPointwise (fun n => laws n ((N).agentAt site) part) (limitComponent part) := by
      have same : (fun n => laws n ((N).agentAt site) part) = fun n =>
          freeLaw setup runtime leaks bounds initial horizon scheduler (scale n) (positive
            n).le (le_one n)
            ((N).agentAt site) (identify part) := by
        funext n
        exact freeKeyedComponent_of_free _ _ _ isFree part
      rw [same]
      exact freeLaw_converges setup runtime leaks bounds initial horizon scheduler scale
        positive le_one
        vanishes ((N).agentAt site) (identify part)
    have finiteOptimal (n : ℕ) (alternative : PMF (parts (pools ((N).agentAt site)))) :
        ((sequence n).continuationContext certificate site (payoff who)).value
            (((sequence n).strategy who).withLaw site.1
              (alternative.bind (laws n ((N).agentAt site)))) ≤
          ((sequence n).continuationContext certificate site (payoff who)).value
            ((sequence n).strategy who) + 0 := by
      have single : Finset.univ.filter (fun agent => pools agent = pools ((N).agentAt site)) =
          {(N).agentAt site} := by
        ext agent
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro same
          dsimp only [pools, pool] at same
          rw [freeKeyedPool_of_free isFree] at same
          exact eq_of_freeKeyedPool_eq_inl same
        · rintro rfl
          rfl
      have bound := pooled n (Function.update (weights n) (pools ((N).agentAt site)) alternative)
        (pools ((N).agentAt site))
      rw [single, Finset.sum_singleton, dite_eq_left site.2] at bound
      simp only [Function.update_self] at bound
      change ((sequence n).continuationContext certificate site (payoff who)).value
          (((sequence n).strategy who).withLaw site.1
            (alternative.bind (laws n ((N).agentAt site)))) -
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
  refine ⟨weights, sequence, limit, index, assembled, mixed, bayes, increasing, converges,
    consistent, pooled, limits, freeOptimal, ?_⟩
  intro who site excluded
  apply (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _)
    (fun _ _ => payoffIntegrable_of_finite _ _)).mpr
  intro alternative _allowed
  exact wholePolicyOptimal_of_publicExclusion setup runtime leaks bounds initial horizon scheduler
    certificate payoff limit consistent freeOptimal who site excluded alternative

end Vegas.RecoveryOnePacket
