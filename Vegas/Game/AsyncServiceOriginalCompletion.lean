/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceInformationWaitDomination
import Vegas.Game.SourceServiceChoiceSupport
import Vegas.Game.SourceInformation
import Vegas.Game.SourceServiceCompletedRationality
import Vegas.Game.SourceServiceFreeRationality
import Vegas.Game.SourceServiceCompatiblePinValue
import Vegas.Game.SourceServiceCompatibleChargedComparison
import Vegas.Game.SourceServiceMissBranchComparison
import Vegas.Game.SourceServiceCompatibleBindingResponse
import Vegas.Game.AsyncServiceBindingBayesResponse
import Vegas.Game.AsyncServiceResolutionBayesResponse
import Vegas.Game.SourceContinuation
import GameTheoryExtensions.Analysis.Protocol.BehavioralContinuity
import GameTheoryExtensions.Analysis.Protocol.AgentPayoffCompletion

/-! # Full effective completion along actual original source assessments

The original consistent source assessment supplies a complete supported Bayes
sequence through the actual source-choice producer before the waiting and
error rates are selected. Normalized source policies
may have different limits at transcripts of zero source probability.
The completion retains their actual information-dependent
WAIT and full effective uniform pin sequence, selecting one common native
assessment subsequence. Prescribed uniform trembles and free-agent reference trembles
have independent rates. Uniform initialized history domination preserves the
original source joint law in that limit without assuming global continuity of
disclosure normalization.

Finite residual selection may use uniformly vanishing auxiliary terminal
bonuses. Bayes beliefs, limiting free rationality and every displayed sampled
payoff use the original audited utility.

The result gives consistency, whole-policy rational free sites, rational
completed compatible sites with nonnegative deposits, classified charged first-choice
comparisons with arbitrary focal continuations under actual backend coverage, and the initialized
typed outcome and sampled settlement law. Uncharged prescribed-site comparisons and
conditional escape relative to rare observations remain separate obligations.
Valid configured rate bounds also compare each positive-mass terminal
public-miss fiber with the same assessment's pin-derived value floor.
This leaves its actual no-miss continuation fiber unbounded here.
The returned native sequence also has an actual binding response law at
compatible initialized inputs, keeping the normalized compiler draw and WAIT
tag beside the same full post-response execution. Its current response is also
averaged under the same native sequence's Bayes belief: the actual initial
parameter, effective prefix, typed draw and complete
traffic are retained jointly, with counterfactual history weights including
foreign waits and full-menu excursions. Original source restoration and
source-posterior transport remain separate from this conditional draw law.
The same native sequence also has the conditional resolution law, retaining
separate effective FALSE/TRUE response traffic through actual source residuals.
The uniform maximum bound controls only initialized loss; it does not assert
that the information-dependent waiting rates enforce those comparisons.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
private abbrev originalCompletionMenu : (app).ResponseMenu :=
  service.bounds.menu (runtime service.setup) service.leaks

local notation "menu" => originalCompletionMenu service
local notation "model" => ReactiveApplication.ResponseMenu.information
  (service.bounds.menu (runtime service.setup) service.leaks)
  (initialLaw service.setup) service.horizon service.scheduler
local notation "sourceModel" => service.setup.informationModel
  (CommitmentInterface.values service.setup.program)

omit [DecidableEq Player] in
private theorem completion_loss_vanishes
    (bound delta : Nat → ℝ)
    (boundVanishes : Tendsto bound atTop (nhds 0))
    (deltaVanishes : Tendsto delta atTop (nhds 0)) (fuel : Nat) :
    Tendsto (fun n => 1 - ((1 - delta n) * (1 - bound n)) ^ (Fintype.card Player * fuel))
      atTop (nhds 0) := by
  have one : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  convert one.sub (((one.sub deltaVanishes).mul (one.sub boundVanishes)).pow
    (Fintype.card Player * fuel)) using 1
  simp only [sub_zero, one_mul, one_pow, sub_self]

omit [Fintype Player] in
private theorem original_run_converges [Finite Player]
    (source : (sourceModel).BehavioralAssessment)
    (sequence : Nat → (sourceModel).BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence source) :
    PMFConvergesPointwise
      (fun n => (service.setup.run (service.setup.decodeBehavioralProfile
        (CommitmentInterface.values service.setup.program) (sequence n).strategy)).map some)
      ((service.setup.run (service.setup.decodeBehavioralProfile
        (CommitmentInterface.values service.setup.program) source.strategy)).map some) := by
  let _ := Fintype.ofFinite Player
  let admission := CommitmentInterface.values service.setup.program
  let certificate := (service.setup.protocol_bounded admission).wellFoundedHistories
  have laws (assessment : (sourceModel).BehavioralAssessment) :
      ((sourceModel).runBehavioralTerminalFrom certificate assessment.strategy
        (service.setup.executionProtocol admission).initHistory).map
          (fun final => service.setup.protocolReadout final.state) =
        (service.setup.run (service.setup.decodeBehavioralProfile admission
          assessment.strategy)).map some := by
    let profile := service.setup.decodeBehavioralProfile admission assessment.strategy
    have permitted who := ((service.setup.behavioralPolicyEquiv admission who).symm
      (assessment.strategy who)).2
    have encoded : (fun who => service.setup.toProtocolBehavioralPolicy admission who
        (profile who) (permitted who)) = assessment.strategy :=
      funext fun who => (service.setup.behavioralPolicyEquiv admission who).apply_symm_apply
        (assessment.strategy who)
    rw [(sourceModel).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
      (service.setup.protocol_bounded admission)]
    have actual := service.setup.protocol_runBehavioral_eq admission profile permitted
    rw [(sourceModel).runSingleMoverBehavioralFrom_eq_runBehavioralFrom, encoded] at actual
    exact actual
  have actual := ((sourceModel).runBehavioralTerminalFrom_convergesPointwise certificate
    converges.strategy (service.setup.executionProtocol admission).initHistory).map
      (fun final => service.setup.protocolReadout final.state)
  simpa only [laws] using actual

open Classical in
/-- A consistent original source assessment supplies its complete supported
source sequence and one consistent native completion in the full effective
game, with the real normalized pin limits of that same source sequence.
Free information sites are optimal against whole-policy deviations; completed
compatible sites under nonnegative deposits are rational; actual backend coverage
bounds arbitrary continuations after classified charged choices; typed outcomes and sampled
payoffs agree exactly. -/
theorem exists_consistent_original_sequence_completion
    (source : (sourceModel).BehavioralAssessment)
    (sourceConsistent : source.IsSequentiallyConsistent
      (service.setup.decision_antichain (CommitmentInterface.values service.setup.program))) :
    ∃ sourceSequence : Nat → (sourceModel).BehavioralAssessment,
      (∀ n who info, FullSupport ((sourceSequence n).strategy who info)) ∧
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent (sourceModel)
        (sourceSequence n) (service.setup.decision_antichain
          (CommitmentInterface.values service.setup.program))) ∧
      InformationModel.BehavioralAssessmentConvergesPointwise sourceSequence source ∧
      (∀ n who, (normalizeDisclosureProfile service.setup.program []
        (Revelations.initial service.setup.context)
        (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
          (sourceSequence n).strategy) who).SupportsEffectiveChoices service.setup.program
            (CommitmentInterface.values service.setup.program) []
              (Revelations.initial service.setup.context)) ∧
    ∀ (weight : Nat → Player → (app).Info → ℝ)
    (weightNonnegative : ∀ n who info, 0 ≤ weight n who info)
    (weightSmall : ∀ n who info, weight n who info ≤ 1)
    (bound : Nat → ℝ) (_boundNonnegative : ∀ n, 0 ≤ bound n)
    (_boundSmall : ∀ n, bound n ≤ 1)
    (_bounded : ∀ n who info, service.sourceCompatibleInfo who info → weight n who info ≤ bound n)
    (_boundVanishes : Tendsto bound atTop (nhds 0))
    (delta : Nat → ℝ) (deltaPositive : ∀ n, 0 < delta n)
    (deltaSmall : ∀ n, delta n < 1)
    (_deltaVanishes : Tendsto delta atTop (nhds 0))
    (freeTremble : Nat → ℝ) (_freePositive : ∀ n, 0 < freeTremble n)
    (_freeSmall : ∀ n, freeTremble n < 1)
    (_freeVanishes : Tendsto freeTremble atTop (nhds 0))
    (utility : State L service.setup.program.terminalCtx → Player → ℝ)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (_authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ)
    (selectionBonus : Nat → Player →
      ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).History → ℝ)
    (selectionError : Nat → ℝ)
    (_selectionVanishes : Tendsto selectionError atTop (nhds 0))
    (_selectionBounded : ∀ n who final,
      ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).terminal
        final.state → |selectionBonus n who final| ≤ selectionError n),
    let certificate := (menu).bounded (initialLaw service.setup) service.horizon service.scheduler
      |>.wellFoundedHistories
    let base := baseUtility service.setup service.leaks utility
    let payoff := fun who (final : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).History) => TerminalAudit.utility base
        ((runtime service.setup).serviceAuditObservation service.leaks)
        (sourceServiceAudit service.setup service.leaks sample)
        (service.auditDeposit base probability) final.state who
    ∃ (nativeSequence : Nat → (model).BehavioralAssessment)
      (assessment : (model).BehavioralAssessment) (index : Nat → Nat),
      (∀ n, (nativeSequence n).IsFullyMixed) ∧
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent (model) (nativeSequence n)
        ((menu).decisionInformationAntichain (initialLaw service.setup) service.horizon
          service.scheduler)) ∧
      StrictMono index ∧
      InformationModel.BehavioralAssessmentConvergesPointwise
        (fun n => nativeSequence (index n)) assessment ∧
      assessment.IsSequentiallyConsistent ((menu).decisionInformationAntichain
        (initialLaw service.setup) service.horizon service.scheduler) ∧
      (∀ n who (site : (model).InformationSite who),
        service.sourceCompatibleInfo who site.1 →
        (nativeSequence n).strategy who site.1 =
          mix (delta n) (deltaPositive n).le (deltaSmall n).le
            ((menu).uniformPolicy (initialLaw service.setup) service.horizon service.scheduler who
              site.1)
            (mix (weight n who site.1) (weightNonnegative n who site.1)
              (weightSmall n who site.1)
              (((menu).restrictPolicy (initialLaw service.setup) service.horizon service.scheduler
                who (app).silentPolicy) site.1)
              (service.effectiveImmediateComparator (normalizeDisclosureProfile
                service.setup.program []
                (Revelations.initial service.setup.context) (service.setup.decodeBehavioralProfile
                  (CommitmentInterface.values service.setup.program) (sourceSequence n).strategy))
                    who site.1))) ∧
      (∀ n,
        let currentProfile := normalizeDisclosureProfile service.setup.program []
          (Revelations.initial service.setup.context)
          (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
            (sourceSequence n).strategy)
        ∀ event (execution : (app).Execution)
          (binding : BindingSource service.setup currentProfile event execution.application.config)
          remaining,
          ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
            (some ⟨remaining, some binding.owner, execution⟩) →
          service.sourceCompatibleInfo binding.owner
            (some (execution.recall binding.owner, execution.observe (app) binding.owner)) →
          execution.application.publicView.ownTurn? binding.owner = some event →
          (runtime service.setup).eventRecorded service.leaks (execution.recall binding.owner)
            event = false →
          let info := some (execution.recall binding.owner, execution.observe (app) binding.owner)
          let read := fun choice : (model).Choice binding.owner info =>
            let response := choice.1.getD (⟨none⟩ : (app).Action)
            (bindingResponseResult? binding.owner binding.payload execution response,
              execution.respond (app) binding.owner response)
          ((nativeSequence n).strategy binding.owner info).map read =
            mix (delta n) (deltaPositive n).le (deltaSmall n).le
              (((menu).uniformPolicy (initialLaw service.setup) service.horizon service.scheduler
                binding.owner info).map read)
              (mix (weight n binding.owner info) (weightNonnegative n binding.owner info)
                (weightSmall n binding.owner info)
                (PMF.pure (none, execution.respond (app) binding.owner ⟨none⟩))
                ((commitKernel binding.residual (binding.source.view binding.owner)).map
                  fun value => (some value, execution.respond (app) binding.owner
                    ((runtime service.setup).reactiveBinding service.leaks binding.owner event
                      binding.payload value
                      (execution.application.publicView.bindingCount binding.owner)))))) ∧
      (∀ n,
        let currentProfile := normalizeDisclosureProfile service.setup.program []
          (Revelations.initial service.setup.context)
          (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
            (sourceSequence n).strategy)
        ∀ (Parameter : Type) (parameter : State L service.setup.context → Parameter)
          who payload event
          (binding : (graph service.setup).outputLayout event = .binding who payload)
          (site : (model).InformationSite who) past view,
          site.1 = some (past, view) → service.sourceCompatibleInfo who site.1 →
          view.application.publicView.ownTurn? who = some event →
          (runtime service.setup).eventRecorded service.leaks past event = false →
          service.BindingConditionalResponseLaw parameter currentProfile who payload event binding
            site past view (weight n) (weightNonnegative n) (weightSmall n) (delta n)
              (deltaPositive n).le (deltaSmall n).le (nativeSequence n)) ∧
      (∀ n,
        let currentProfile := normalizeDisclosureProfile service.setup.program []
          (Revelations.initial service.setup.context)
          (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
            (sourceSequence n).strategy)
        ∀ (Parameter : Type) (parameter : State L service.setup.context → Parameter)
          who payload event
          (_publication : (graph service.setup).outputLayout event = .publication payload)
          (site : (model).InformationSite who) past view,
          site.1 = some (past, view) → service.sourceCompatibleInfo who site.1 →
          view.application.publicView.ownTurn? who = some event →
          (runtime service.setup).eventRecorded service.leaks past event = false →
          service.ResolutionConditionalResponseLaw parameter currentProfile who payload event
            site past view (weight n) (weightNonnegative n) (weightSmall n) (delta n)
              (deltaPositive n).le (deltaSmall n).le (nativeSequence n)) ∧
      (∀ who (site : (model).InformationSite who), ¬ service.sourceCompatibleInfo who site.1 →
        ∀ law : PMF ((model).Choice who site.1),
          (assessment.continuationContext certificate site (payoff who)).value
              ((assessment.strategy who).withLaw site.1 law) ≤
            (assessment.continuationContext certificate site (payoff who)).value
              (assessment.strategy who)) ∧
      (∀ who (site : (model).InformationSite who), ¬ service.sourceCompatibleInfo who site.1 →
        (assessment.continuationContext certificate site (payoff who)).IsLocallyOptimal
          Set.univ (assessment.strategy who)) ∧
      (∀ who (site : (model).InformationSite who),
        0 ≤ service.auditDeposit base probability who →
        service.sourceCompatibleInfo who site.1 →
        ∀ (past : List (app).PlayerEntry) (view : (app).PlayerView),
          site.1 = some (past, view) →
          (∀ event, event ∈ view.application.publicView.observation.completionOrder) →
          (assessment.continuationContext certificate site (payoff who)).IsLocallyOptimal
            Set.univ (assessment.strategy who)) ∧
      (∀ (backend : EvidenceReportService (SettledEvidence service.setup))
        (observationRate deliveryRate : Player → ℝ), sample = backend.sample →
        probability = (fun player => observationRate player * deliveryRate player) →
        (∀ player, 0 ≤ deliveryRate player) →
        FinalForbiddenEvidenceCoverage backend observationRate deliveryRate →
        ∀ who (site : (model).InformationSite who),
          service.sourceCompatibleInfo who site.1 → 0 < observationRate who * deliveryRate who →
          ∀ choice : (model).Choice who site.1,
            (auditableServiceChoice service.setup service.leaks (menu) service.horizon
              service.scheduler who site.1 choice ∨
              recordedServiceChoice service.setup service.leaks (menu) service.horizon
                service.scheduler who site.1 choice) →
            ∀ alternative : (model).BehavioralPolicy who,
            (assessment.continuationContext certificate site (payoff who)).value
                (alternative.commit site.1 choice) ≤
              (assessment.continuationContext certificate site (payoff who)).value
                (assessment.strategy who)) ∧
      (∀ observationRate deliveryRate : Player → ℝ,
        probability = (fun player => observationRate player * deliveryRate player) →
        ∀ who (site : (model).InformationSite who),
          service.sourceCompatibleInfo who site.1 → observationRate who ≤ 1 →
          0 ≤ deliveryRate who → deliveryRate who ≤ 1 →
          0 < observationRate who * deliveryRate who →
          ∀ alternative : (model).BehavioralPolicy who,
            let context := assessment.continuationContext certificate site (payoff who)
            let law := context.outcome alternative
            let missing := fun final : ((menu).protocol (initialLaw service.setup)
              service.horizon service.scheduler).History => (final.state.map fun control =>
                control.execution.application.publicView.missedDecisionBy who).getD false
            true ∈ (law.map missing).support →
              expect (fiberPosterior law missing true) (payoff who) ≤
                context.value (assessment.strategy who)) ∧
      (∀ fuel history, history ∈ ((model).runBehavioral assessment.strategy fuel).support →
        ∀ who, ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).active
          history.state who → service.sourceCompatibleInfo who ((model).infoOf who history.trace)) ∧
      (PMF.bind ((model).runBehavioralTerminalFrom certificate assessment.strategy
        ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).initHistory)
          fun final =>
            (TerminalAudit.settlement base
              ((runtime service.setup).serviceAuditObservation service.leaks)
              (sourceServiceAudit service.setup service.leaks sample)
              (service.auditDeposit base probability) final.state).map fun payoffs =>
                (sourceReadout service.setup service.leaks final.state, payoffs)) =
        (service.setup.run (service.setup.decodeBehavioralProfile
          (CommitmentInterface.values service.setup.program) source.strategy)).map
            (fun state => (some state, utility state)) := by
  classical
  let admission := CommitmentInterface.values service.setup.program
  have approximation := sourceConsistent
  obtain ⟨_witness, approximates, _⟩ := approximation
  let _ : Finite (service.setup.executionProtocol admission).History :=
    (approximates 0).1.finite_history (service.setup.protocol_bounded admission)
      (fun who info =>
        have := service.setup.finite_choice
          (sourceService_finiteBindingTypes service.setup service.bounds service.values)
          admission who info
        Set.toFinite _)
      (fun draw => service.setup.protocolStep_support_finite _ draw.1)
  obtain ⟨sourceSequence, sourceFull, sourceBayes, sourceConverges, sourceChoices⟩ :=
    sourceService_consistent_supported_sequence service.setup service.bounds service.values
      source (service.setup.decision_antichain admission) sourceConsistent
  refine ⟨sourceSequence, sourceFull, sourceBayes, sourceConverges, sourceChoices, ?_⟩
  intro weight weightNonnegative weightSmall bound boundNonnegative boundSmall bounded
    boundVanishes delta deltaPositive deltaSmall deltaVanishes freeTremble freePositive freeSmall
    freeVanishes utility sample authentic probability selectionBonus selectionError
    selectionVanishes selectionBounded certificate base payoff
  let original n := service.setup.decodeBehavioralProfile
    (CommitmentInterface.values service.setup.program) (sourceSequence n).strategy
  have originalAdmitted (n : Nat) (who : Player) : (original n who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program) :=
    ((service.setup.behavioralPolicyEquiv
      (CommitmentInterface.values service.setup.program) who).symm
      ((sourceSequence n).strategy who)).2
  let normalized n := normalizeDisclosureProfile service.setup.program []
    (Revelations.initial service.setup.context) (original n)
  have permitted (n : Nat) (who : Player) : (normalized n who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program) :=
    (original n who).normalizeDisclosureFrom_admitted service.setup.program
      (CommitmentInterface.values service.setup.program) (originalAdmitted n who) []
      (Revelations.initial service.setup.context) (fun view => PMF.pure view.2)
  have effective (n : Nat) (who : Player) : (normalized n who).EffectiveDisclosures
      service.setup.program [] (Revelations.initial service.setup.context) :=
    (original n who).normalizeDisclosureFrom_effective service.setup.program []
      (Revelations.initial service.setup.context) (fun view => PMF.pure view.2)
  let fallback : ∀ who, (model).Policy who := fun who info => Classical.choice inferInstance
  let free : Finset ((model).InformationAgent (model).playedInformation) :=
    Finset.univ.filter fun agent => ¬ service.sourceCompatibleInfo agent.1 agent.2.1
  let reference : Profile ((model).agentForm fallback certificate).sig.mixed := fun agent =>
    (menu).uniformPolicy (initialLaw service.setup) service.horizon service.scheduler agent.1
      agent.2.1
  let pinned n : Profile ((model).agentForm fallback certificate).sig.mixed := fun agent =>
    mix (delta n) (deltaPositive n).le (deltaSmall n).le (reference agent)
      (mix (weight n agent.1 agent.2.1) (weightNonnegative n agent.1 agent.2.1)
        (weightSmall n agent.1 agent.2.1)
        (((menu).restrictPolicy (initialLaw service.setup) service.horizon service.scheduler
          agent.1 (app).silentPolicy) agent.2.1)
        (service.effectiveImmediateComparator (normalized n) agent.1 agent.2.1))
  have referenceFull (agent : (model).InformationAgent (model).playedInformation) :
      FullSupport (reference agent) := by
    intro choice
    let := Fintype.ofFinite ((model).Choice agent.1 agent.2.1)
    change choice ∈ (PMF.uniformOfFintype ((model).Choice agent.1 agent.2.1)).support
    exact PMF.mem_support_uniformOfFintype (α := (model).Choice agent.1 agent.2.1) choice
  have pinnedFull (n : Nat) (agent : (model).InformationAgent (model).playedInformation)
      (_kept : agent ∉ free) : FullSupport (pinned n agent) := by
    intro choice
    exact mem_support_mix_left _ _ _ (deltaPositive n) (referenceFull agent choice)
  let selectionPayoff (n : Nat) (who : Player) (final :
      ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).History) :=
    payoff who final + selectionBonus n who final
  have payoffClose (n : Nat) (who : Player) (final :
      ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).History)
      (terminal : ((menu).protocol (initialLaw service.setup) service.horizon
        service.scheduler).terminal final.state) :
      |selectionPayoff n who final - payoff who final| ≤ selectionError n := by
    simpa only [selectionPayoff, add_sub_cancel_left] using selectionBounded n who final terminal
  obtain ⟨_residual, nativeSequence, assessment, index, played, mixed, bayes, increasing,
    converges, consistent, freeOptimal⟩ := (model).exists_consistent_free_agent_payoff_completion
      ((menu).decisionRecall (initialLaw service.setup) service.horizon service.scheduler)
      fallback certificate payoff selectionPayoff selectionError selectionVanishes payoffClose
        free pinned reference pinnedFull referenceFull freeTremble freePositive freeSmall
          freeVanishes
  have kept (n : Nat) (who : Player) (site : (model).InformationSite who)
      (compatible : service.sourceCompatibleInfo who site.1) :
      (nativeSequence n).strategy who site.1 = pinned n ((model).agentAt site) := by
    rw [played]
    exact ((model).agentBehavior_at (model).playedInformation fallback _
      ((model).agentAt site)).trans
      (ite_eq_right (by
        simpa only [free, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using compatible))
  have constructed (n : Nat) (who : Player) (site : (model).InformationSite who) :
      (nativeSequence n).strategy who site.1 =
        service.completedInformationWaitProfile (normalized n) (weight n) (weightNonnegative n)
          (weightSmall n) (delta n) (deltaPositive n).le (deltaSmall n).le
            (nativeSequence n).strategy who site.1 := by
    by_cases compatible : service.sourceCompatibleInfo who site.1
    · simp only [completedInformationWaitProfile, compatible, ↓reduceIte]
      exact kept n who site compatible
    · simp only [completedInformationWaitProfile, compatible, ↓reduceIte]
  have initialized (n fuel : Nat) :
      (model).runBehavioral (nativeSequence n).strategy fuel =
        (model).runBehavioral (service.completedInformationWaitProfile (normalized n) (weight n)
          (weightNonnegative n) (weightSmall n) (delta n) (deltaPositive n).le (deltaSmall n).le
            (nativeSequence n).strategy) fuel := by
    apply (model).runBehavioralFrom_congr_on_support
    intro _ _ history _ running who
    by_cases active : ((menu).protocol (initialLaw service.setup) service.horizon
        service.scheduler).active history.state who
    · obtain ⟨site, observed⟩ := (model).exists_informationSite_of_active who history running active
      rw [← observed]
      exact constructed n who site
    · exact (model).behavioral_eq_of_not_active _ _ history.trace active
  let budget := 2 * service.horizon + 1
  let loss n := 1 - ((1 - delta n) * (1 - bound n)) ^ (Fintype.card Player * budget)
  have lossVanishes : Tendsto loss atTop (nhds 0) :=
    completion_loss_vanishes bound delta boundVanishes deltaVanishes budget
  have close (n : Nat) : PMF.WithinTV (loss n)
      ((model).runBehavioral
        (fun player => service.effectiveImmediateComparator (normalized n) player) budget)
      ((model).runBehavioral (nativeSequence n).strategy budget) := by
    rw [initialized]
    exact service.completedInformationWaitProfile_initialized_close (normalized n) (permitted n)
      (effective n) (weight n) (weightNonnegative n) (weightSmall n) (delta n) (deltaPositive n).le
        (deltaSmall n).le (nativeSequence n).strategy (bound n) (boundNonnegative n)
          (boundSmall n) (bounded n) budget
  have nativeLimit := (model).runBehavioralTerminalFrom_convergesPointwise certificate
    converges.strategy ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).initHistory
  have compatiblePlay (fuel : Nat)
      (history : ((menu).protocol (initialLaw service.setup) service.horizon
        service.scheduler).History)
      (reached : history ∈ ((model).runBehavioral assessment.strategy fuel).support)
      (who : Player)
      (active :
        ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).active
          history.state who) :
      service.sourceCompatibleInfo who ((model).infoOf who history.trace) := by
    by_contra escaped
    have absent (n : Nat) :
        (((model).runBehavioral
          (fun player => service.effectiveImmediateComparator (normalized n) player) fuel)
            history).toReal = 0 := by
      apply pmf_toReal_eq_zero_iff.mpr
      intro supported
      exact escaped (service.effectiveImmediateProfile_sourceCompatibleInfo service.horizon
        (normalized n)
        (permitted n) (effective n) fuel history supported who active)
    let prefixLoss n := 1 - ((1 - delta n) * (1 - bound n)) ^ (Fintype.card Player * fuel)
    have prefixVanishes : Tendsto prefixLoss atTop (nhds 0) :=
      completion_loss_vanishes bound delta boundVanishes deltaVanishes fuel
    have pointBound (n : Nat) :
        (((model).runBehavioral (nativeSequence n).strategy fuel) history).toReal ≤ prefixLoss n :=
      by
      have estimate := service.completedInformationWaitProfile_initialized_close (normalized n)
        (permitted n) (effective n) (weight n) (weightNonnegative n) (weightSmall n) (delta n)
        (deltaPositive n).le (deltaSmall n).le (nativeSequence n).strategy (bound n)
        (boundNonnegative n) (boundSmall n) (bounded n) fuel
      rw [← initialized] at estimate
      have point := estimate.apply history
      rw [absent] at point
      simpa only [zero_sub, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg] using point
    have massLimit := (model).runBehavioralFrom_expect_tendsto (.of_finite_history)
      (fun n => (nativeSequence (index n)).strategy) assessment.strategy converges.strategy
      (fun final => if history = final then (1 : ℝ) else 0) fuel
      ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).initHistory
    simp only [expect_ite_eq, mul_one] at massLimit
    have nonpositive := le_of_tendsto_of_tendsto massLimit
      (prefixVanishes.comp increasing.tendsto_atTop)
      (Eventually.of_forall fun n => pointBound (index n))
    have vanished : (((model).runBehavioral assessment.strategy fuel) history).toReal = 0 :=
      le_antisymm nonpositive ENNReal.toReal_nonneg
    exact (pmf_toReal_eq_zero_iff.mp vanished) reached
  have baselineLimit : PMFConvergesPointwise (fun n =>
      (model).runBehavioralTerminalFrom certificate
        (fun player => service.effectiveImmediateComparator (normalized (index n)) player)
          ((menu).protocol (initialLaw service.setup) service.horizon
            service.scheduler).initHistory)
      ((model).runBehavioralTerminalFrom certificate assessment.strategy
        ((menu).protocol (initialLaw service.setup) service.horizon
          service.scheduler).initHistory) := by
    apply pmfConvergesPointwise_iff_toReal.mpr
    intro final
    apply (nativeLimit.toReal final).congr_dist
    apply squeeze_zero (fun _ => dist_nonneg) _
      (lossVanishes.comp increasing.tendsto_atTop)
    intro n
    rw [(model).runBehavioralTerminalFrom_initHistory certificate _
        ((menu).bounded (initialLaw service.setup) service.horizon service.scheduler),
      (model).runBehavioralTerminalFrom_initHistory certificate _
        ((menu).bounded (initialLaw service.setup) service.horizon service.scheduler)]
    simpa only [Real.dist_eq, abs_sub_comm, budget, Function.comp_def] using
      (close (index n)).apply final
  let readout (final : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).History) :=
    (TerminalAudit.settlement base ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample)
      (service.auditDeposit base probability) final.state).map fun payoffs =>
        (sourceReadout service.setup service.leaks final.state, payoffs)
  have nativeJoint := baselineLimit.bind (fun final => pmfConvergesPointwise_const (readout final))
  have referenceJoint (n : Nat) :
      ((model).runBehavioralTerminalFrom certificate
        (fun player => service.effectiveImmediateComparator (normalized n) player)
          ((menu).protocol (initialLaw service.setup) service.horizon
            service.scheduler).initHistory).bind readout =
        (service.setup.run (original n)).map (fun state => (some state, utility state)) := by
    rw [service.effectiveImmediateProfile_terminal_history (normalized n) (permitted n),
      PMF.bind_map]
    exact service.normalizedFirstTurnProfile_joint_law service.horizon (original n)
      (originalAdmitted n) utility sample authentic probability
  have sourceRuns : PMFConvergesPointwise (fun n => service.setup.run (original n))
      (service.setup.run (service.setup.decodeBehavioralProfile
        (CommitmentInterface.values service.setup.program) source.strategy)) := by
    intro state
    have limit := original_run_converges service source sourceSequence sourceConverges (some state)
    simpa only [pmf_map_apply_of_injective _
      (Option.some_injective (State L service.setup.program.terminalCtx))] using limit
  have sourceTarget := sourceRuns.map (fun state => (some state, utility state))
  refine ⟨nativeSequence, assessment, index, mixed, bayes, increasing, converges, consistent,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, compatiblePlay, ?_⟩
  · intro n who site compatible
    exact kept n who site compatible
  · intro n currentProfile event execution binding remaining trace compatible turn unrecorded
      info read
    let history : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).History := ⟨some ⟨remaining, some binding.owner, execution⟩, trace⟩
    have running : ¬ ((menu).protocol (initialLaw service.setup) service.horizon
        service.scheduler).terminal history.state := by
      change ¬ (app).terminal (some ⟨remaining, some binding.owner, execution⟩)
      simp only [ReactiveApplication.terminal, reduceCtorEq, and_false, not_false_eq_true]
    have acting : ((menu).protocol (initialLaw service.setup) service.horizon
        service.scheduler).active history.state binding.owner := rfl
    obtain ⟨current, observed⟩ := (model).exists_informationSite_of_active binding.owner history
      running acting
    have siteInfo : current.1 = info := by
      have atState := observed.trans ((menu).info (initialLaw service.setup) service.horizon
        service.scheduler binding.owner history.trace)
      simpa only [history, info, ReactiveApplication.observe, ↓reduceIte] using atState
    have actualPinned := constructed n binding.owner current
    rw [siteInfo] at actualPinned
    rw [actualPinned]
    exact service.completedInformationWaitProfile_binding_joint_response currentProfile event
      execution binding (permitted n binding.owner) remaining trace compatible turn unrecorded
      (weight n) (weightNonnegative n) (weightSmall n) (delta n) (deltaPositive n).le
      (deltaSmall n).le (nativeSequence n).strategy
  · intro n currentProfile Parameter parameter who payload event binding site past view
      observed compatible turn unrecorded
    have positive := (model).informationMass_pos_of_fullSupport (nativeSequence n).strategy
      (mixed n) who site
    exact service.information_wait_binding_bayes_joint_response parameter currentProfile who
      payload (permitted n who) event binding site past view observed compatible turn unrecorded
      (weight n) (weightNonnegative n) (weightSmall n) (delta n) (deltaPositive n).le
      (deltaSmall n).le (nativeSequence n) (bayes n) (constructed n who site) positive
  · intro n currentProfile Parameter parameter who payload event publication site past view
      observed compatible turn unrecorded
    have positive := (model).informationMass_pos_of_fullSupport (nativeSequence n).strategy
      (mixed n) who site
    exact service.information_wait_resolution_bayes_joint_response parameter currentProfile who
      payload (permitted n who) (effective n) event publication site past view observed compatible
      turn unrecorded (weight n) (weightNonnegative n) (weightSmall n) (delta n)
      (deltaPositive n).le (deltaSmall n).le (nativeSequence n) (bayes n)
      (constructed n who site) positive
  · intro who site incompatible law
    exact freeOptimal who site (Finset.mem_filter.mpr ⟨Finset.mem_univ _, incompatible⟩) law
  · intro who site incompatible
    exact service.sourceCompatibleInfo_free_optimal (menu) assessment consistent certificate payoff
      (fun player current missed law => freeOptimal player current
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, missed⟩) law) who site incompatible
  · intro who site nonnegative compatible past view observed completed
    have silence player earlier atView :
        (⟨none⟩ : (app).Action) ∈ (menu).actions player earlier atView :=
      service.bounds.canonicalActions_effective (runtime service.setup) service.leaks
        player earlier atView
        (service.bounds.silence_canonical (runtime service.setup) service.leaks player
          earlier atView)
    apply service.sourceCompatibleInfo_completed_optimal (menu) silence assessment consistent
      utility sample authentic (service.auditDeposit base probability) _ _ who site nonnegative
        compatible past view observed completed
    · intro player current currentCompatible currentPast currentView currentObserved currentComplete
      exact service.sourceCompatibleInfo_completed_pin_limit (menu) silence normalized weight
        weightNonnegative weightSmall delta (fun n => (deltaPositive n).le)
        (fun n => (deltaSmall n).le) deltaVanishes nativeSequence assessment index increasing
        converges (fun n player current currentCompatible => kept n player current
          currentCompatible)
        player current currentCompatible currentPast currentView currentObserved currentComplete
    · intro player current incompatible law
      exact freeOptimal player current (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, incompatible⟩) law
  · intro backend observationRate deliveryRate sampling rates deliveryNonnegative coverage
      who site compatible positive choice classified alternative
    subst sample probability
    have lower := service.sourceCompatibleInfo_pin_value_lower normalized permitted weight
      weightNonnegative weightSmall bound bounded boundVanishes delta
      (fun n => (deltaPositive n).le) (fun n => (deltaSmall n).le) deltaVanishes
      nativeSequence assessment index increasing converges consistent
      (fun n player current currentCompatible => kept n player current currentCompatible)
      base backend.sample backend.sample_authentic
      (service.auditDeposit base (fun player => observationRate player * deliveryRate player))
      (fun player current incompatible law => freeOptimal player current
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, incompatible⟩) law) who site compatible
    have charged := service.charged_expected_utility_le_lower base backend observationRate
      deliveryRate deliveryNonnegative coverage who positive
      (Profile.update (sig := (model).behavioralSignature) assessment.strategy who alternative)
      site compatible
      choice classified (assessment.belief who site)
    simp only [Profile.update_same, Profile.update_idem] at charged
    have tower := assessment.continuationContextWith_value_tower
      ((model).runBehavioralTerminalFrom certificate) site (payoff who)
      (alternative.commit site.1 choice) (payoffIntegrable_of_finite _ _)
    change (assessment.continuationContextWith ((model).runBehavioralTerminalFrom certificate)
      site (payoff who)).value (alternative.commit site.1 choice) ≤ _
    rw [tower]
    exact charged.trans lower
  · intro observationRate deliveryRate rates who site compatible observationSmall
      deliveryNonnegative deliverySmall positive alternative context law missing possible
    subst probability
    have lower := service.sourceCompatibleInfo_pin_value_lower normalized permitted weight
      weightNonnegative weightSmall bound bounded boundVanishes delta
      (fun n => (deltaPositive n).le) (fun n => (deltaSmall n).le) deltaVanishes
      nativeSequence assessment index increasing converges consistent
      (fun n player current currentCompatible => kept n player current currentCompatible)
      base sample authentic
      (service.auditDeposit base (fun player => observationRate player * deliveryRate player))
      (fun player current incompatible actionLaw => freeOptimal player current
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, incompatible⟩) actionLaw) who site compatible
    have split := service.public_miss_continuation_decomposition base sample observationRate
      deliveryRate who observationSmall deliveryNonnegative deliverySmall positive assessment
        site alternative
    exact (split.2 possible).trans lower
  · have sourceAlong := sourceTarget.subseq increasing
    have aligned := nativeJoint
    simp only [referenceJoint] at aligned
    exact aligned.unique sourceAlong

end Vegas.AsyncServiceSpec
