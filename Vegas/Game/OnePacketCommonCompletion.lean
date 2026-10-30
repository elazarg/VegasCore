/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketComponents
import Vegas.Game.OnePacketExclusionPayoff
import GameTheoryExtensions.Analysis.Protocol.ComponentCompletion

/-! # A common consistent completion of native operational components

One finite native game chooses all free and keyed pool weights together. Its
common approximating sequence, Bayes beliefs and limit are retained for every
local comparison. Free components give local optimality, and the persistent
public-default region gives whole-policy sequential rationality there.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (initial : PMF (application setup runtime leaks).State)
  (horizon : Nat) (scheduler : (application setup runtime leaks).Scheduler)
  [Fintype ((bounds.onePacketMenu runtime leaks).protocol initial horizon
    scheduler).History]
  [infoEq : ∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds initial horizon
    scheduler).InfoState who)]

local notation "N" => onePacketModel setup runtime leaks bounds initial horizon scheduler
local notation "menu" => bounds.onePacketMenu runtime leaks

open Classical in
/-- Singleton free pools turn pooled optimality and component limits into
local optimality of every free decision. -/
private theorem freeOptimal_of_pooled_limits
    (sourceSequence : ℕ → setup.intendedModel.BehavioralAssessment) (slots : Nat)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (vanishes : Tendsto scale atTop (nhds 0)) :
    let parts := OnePacketPart setup runtime leaks bounds initial horizon scheduler slots
    let pools := onePacketPool setup runtime leaks bounds initial horizon scheduler
    let laws := fun n => onePacketComponent setup runtime leaks bounds initial horizon scheduler
      (sourceSequence n) (slots := slots) (scale n) (positive n).le (le_one n)
    ∀ (_weights : ℕ → ∀ p, PMF (parts p)) (sequence : ℕ → (N).BehavioralAssessment)
      (limit : (N).BehavioralAssessment)
      (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories)
      (payoff : Player → ((menu).protocol initial horizon scheduler).History → ℝ),
      (∀ n (alternative : ∀ p, PMF (parts p)) p,
              ∑ agent ∈ Finset.univ.filter (fun agent => pools agent = p),
                (if decision : (N).IsDecisionInfo agent.1 agent.2.1 then
                  ((sequence n).continuationContext certificate ⟨agent.2.1, decision⟩
                      (payoff agent.1)).value
                      (((sequence n).strategy agent.1).withLaw agent.2.1
                        ((alternative (pools agent)).bind (laws n agent))) -
                    ((sequence n).continuationContext certificate ⟨agent.2.1, decision⟩
                      (payoff agent.1)).value ((sequence n).strategy agent.1)
                else 0) ≤ 0) →
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
                      (limit.strategy who)) →
      ∀ who (site : (N).InformationSite who),
            FreeAgent setup runtime leaks bounds initial horizon scheduler ((N).agentAt site) →
              ∀ law : PMF ((N).Choice who site.1),
                (limit.continuationContext certificate site (payoff who)).value
                    ((limit.strategy who).withLaw site.1 law) ≤
                  (limit.continuationContext certificate site (payoff who)).value
                    (limit.strategy who) := by
  intro parts pools laws weights sequence limit certificate payoff pooled limits who site isFree law
  let identify := freeIdentify
    (keyed := LateDeliveryAgent setup runtime leaks bounds initial horizon scheduler)
    (key := agentLateKey setup runtime leaks bounds initial horizon scheduler) (Opt := LateOption
      slots)
    isFree
  let limitComponent := fun part => PMF.pure (identify part)
  have componentsConverge (part : parts (pools ((N).agentAt site))) :
      PMFConvergesPointwise (fun n => laws n ((N).agentAt site) part) (limitComponent part) := by
    have same : (fun n => laws n ((N).agentAt site) part) = fun n =>
        unforcedLaw setup runtime leaks bounds initial horizon scheduler (scale n) (positive
          n).le (le_one n)
          ((N).agentAt site) (identify part) := by
      funext n
      exact freeKeyedComponent_of_free _ _ _ isFree part
    rw [same]
    exact unforcedLaw_converges setup runtime leaks bounds initial horizon scheduler scale
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
        dsimp only [pools, onePacketPool] at same
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

open Classical in
/-- Simultaneous pooled completion on the native runtime retains a common
witness for every clear operational and public-default choice. Local estimates
for nonfree agents remain separate proof obligations. -/
theorem SourceProgram.Setup.exists_onePacket_consistent_completion {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (sourceSequence : ℕ → setup.intendedModel.BehavioralAssessment) (slots : Nat)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (vanishes : Tendsto scale atTop (nhds 0)) :
    let parts := OnePacketPart setup runtime leaks bounds initial horizon scheduler slots
    let pools := onePacketPool setup runtime leaks bounds initial horizon scheduler
    let laws := fun n => onePacketComponent setup runtime leaks bounds initial horizon scheduler
      (sourceSequence n)
      (slots := slots) (scale n) (positive n).le (le_one n)
    let fallback : ∀ who, (N).Policy who := fun _ _ => Classical.arbitrary _
    let certificate := (menu).bounded initial horizon scheduler |>.wellFoundedHistories
    let payoff := fun who (final : (menu).protocol initial horizon scheduler |>.History) =>
      exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who
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
      ∀ who (site : (N).InformationSite who), runtime.PublicDefaultInput leaks site.1 →
        limit.IsSequentiallyRationalAt site
          (limit.continuationContext certificate site (payoff who)) := by
  intro parts pools laws fallback certificate payoff
  let Pool := FreeKeyedPool (FreeAgent setup runtime leaks bounds initial horizon scheduler)
    (LateDeliveryAgent setup runtime leaks bounds initial horizon scheduler)
    (agentLateKey setup runtime leaks bounds initial horizon scheduler)
  have componentFull : ∀ (n : ℕ) (agent : (N).InformationAgent (N).playedInformation)
      (part : parts (pools agent)), FullSupport (laws n agent part) := by
    intro n agent part
    exact onePacketComponent_fullSupport setup runtime leaks bounds initial horizon scheduler
      (sourceSequence n) (positive n) (le_one n) agent part
  let core :=
    (N).exists_consistent_pooled_completion ((menu).decisionRecall initial horizon scheduler)
      fallback certificate payoff (Pool := Pool) (Part := parts) pools laws componentFull
  rcases core with ⟨weights, sequence, limit, index, assembled, mixed, bayes, increasing, converges,
    consistent, pooled, limits⟩
  have freeOptimal : ∀ who (site : (N).InformationSite who),
      FreeAgent setup runtime leaks bounds initial horizon scheduler ((N).agentAt site) →
        ∀ law : PMF ((N).Choice who site.1),
          (limit.continuationContext certificate site (payoff who)).value
              ((limit.strategy who).withLaw site.1 law) ≤
            (limit.continuationContext certificate site (payoff who)).value
              (limit.strategy who) := by
    exact freeOptimal_of_pooled_limits setup runtime leaks bounds initial horizon scheduler
      sourceSequence slots scale positive le_one vanishes weights sequence limit certificate payoff
      pooled limits
  have localDefaultOptimal : ∀ player (site : (N).InformationSite player),
      runtime.PublicDefaultInput leaks site.1 → ∀ law : PMF ((N).Choice player site.1),
        (limit.continuationContext certificate site (payoff player)).value
            (@BehavioralPolicy.withLaw Player ((menu).protocol initial horizon scheduler)
              (N) player (Classical.typeDecidableEq ((N).InfoState player))
              (limit.strategy player) site.1 law) ≤
          (limit.continuationContext certificate site (payoff player)).value
            (limit.strategy player) := by
    intro player site flagged law
    have equality : infoEq player =
        Classical.typeDecidableEq ((N).InfoState player) := Subsingleton.elim _ _
    have comparison := freeOptimal player site
      (freeAgent_of_publicDefault setup runtime leaks bounds initial horizon scheduler
        ((N).agentAt site) flagged) law
    rw [equality] at comparison
    exact comparison
  have publicOptimal : ∀ who (site : (N).InformationSite who),
      runtime.PublicDefaultInput leaks site.1 →
        limit.IsSequentiallyRationalAt site
          (limit.continuationContext certificate site (payoff who)) := by
    intro who site flagged
    let ctx : Context ((N).BehavioralPolicy who)
        ((menu).protocol initial horizon scheduler).History :=
      limit.continuationContext certificate site (payoff who)
    have integrable (alternative : (N).BehavioralPolicy who) :
        ctx.IntegrableAt alternative :=
      payoffIntegrable_of_finite (ctx.outcome alternative) ctx.continuation
    have compare (alternative : (N).BehavioralPolicy who) :
        ctx.value alternative ≤ ctx.value (limit.strategy who) :=
      runtime.wholePolicyOptimal_of_publicDefault leaks (bounds.onePacketMenu runtime leaks)
        initial horizon scheduler certificate payoff limit consistent localDefaultOptimal
        who site flagged alternative
    change ctx.IsLocallyOptimal Set.univ (limit.strategy who)
    exact (Context.isLocallyOptimal_iff_of_integrable
      (ctx := ctx) (allowed := Set.univ) (choice := limit.strategy who)
      (integrable (limit.strategy who)) (fun alternative _ => integrable alternative)).mpr
        (fun alternative _ => compare alternative)
  exact ⟨weights, sequence, limit, index, assembled, mixed, bayes, increasing, converges,
    consistent, pooled, limits, freeOptimal, publicOptimal⟩

end Vegas
