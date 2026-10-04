/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceTrueGuessBayes
import Vegas.Game.SourceServiceInitialGuessPayoff
import GameTheoryExtensions.Analysis.Protocol.UniformPolicyLimit

/-! # Actual native guessing incentives after retained waiting

The continuation payoff reads the same immutable initial parameter at the real
terminal configuration. A LOW commitment has the genuine LOW-type upper bound;
a protected HIGH comparator has the genuine HIGH-type value. The incumbent's
actual probability of choosing something other than LOW remains explicit.
All counterfactual masses retain foreign waiting, uniform and free-menu paths.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory GameTheory.Math.Probability
  GameTheory.Enforcement GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
local notation "runtime" => runtime service.setup
local notation "menu" => service.bounds.menu (runtime) service.leaks
local notation "guessModel" => ReactiveApplication.ResponseMenu.information
  (service.bounds.menu (Vegas.runtime service.setup) service.leaks) (initialLaw service.setup)
    service.horizon service.scheduler

/-- This fixed terminal utility reads actual initial inputs and the public
publication, then subtracts the actual expected sampled charge. -/
def initialGuessPayoff
    (parameter : State L service.setup.context → Bool) (event : (graph service.setup).EventId)
    (payload : L.Ty) (outputEq : (graph service.setup).outputLayout event = .publication payload)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (deposit : Player → ℝ) (who : Player)
    (final : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).History) : ℝ :=
  TerminalAudit.utility (fun state _ => sourceInitialPublicationGuessValue service.setup
    service.leaks parameter event payload outputEq state)
    ((runtime).serviceAuditObservation service.leaks)
    (sourceServiceAudit service.setup service.leaks sample) deposit final.state who

open Classical in
/-- Every actual information history transports the fixed terminal parameter
to the same starting-history parameter, under every whole continuation. -/
theorem initialGuess_continuationContext_value
    (parameter : State L service.setup.context → Bool) (event : (graph service.setup).EventId)
    (payload : L.Ty) (outputEq : (graph service.setup).outputLayout event = .publication payload)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (deposit : Player → ℝ) (assessment : (guessModel).BehavioralAssessment) (who : Player)
    (site : (guessModel).InformationSite who) (alternative : (guessModel).BehavioralPolicy who) :
    (assessment.continuationContext
      ((menu).bounded (initialLaw service.setup) service.horizon
        service.scheduler).wellFoundedHistories site
      (service.initialGuessPayoff parameter event payload outputEq sample deposit who)).value
        alternative =
    expect (assessment.belief who site) (fun history =>
      expect ((guessModel).runBehavioralTerminalFrom
        ((menu).bounded (initialLaw service.setup) service.horizon
          service.scheduler).wellFoundedHistories
        (Profile.update (sig := (guessModel).behavioralSignature) assessment.strategy who
          alternative) history.1)
        (fun final => TerminalAudit.utility
          (fun state _ => sourcePublicationGuessValue service.setup service.leaks event payload
            outputEq (service.initialGuessParameter (menu) parameter history.1) state)
          ((runtime).serviceAuditObservation service.leaks)
          (sourceServiceAudit service.setup service.leaks sample) deposit final.state who)) := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    expect_bind_of_finite]
  change expect (assessment.belief who site) (fun history =>
    expect ((guessModel).runBehavioralTerminalFrom
      ((menu).bounded (initialLaw service.setup) service.horizon
        service.scheduler).wellFoundedHistories
      (Profile.update (sig := (guessModel).behavioralSignature) assessment.strategy who
        alternative) history.1)
      (fun final => TerminalAudit.utility
        (fun state _ => sourceInitialPublicationGuessValue service.setup service.leaks parameter
          event payload outputEq state) ((runtime).serviceAuditObservation service.leaks)
        (sourceServiceAudit service.setup service.leaks sample) deposit final.state who)) = _
  apply expect_congr_on_support
  intro history _supported
  have active := InformationModel.InformationSite.active (guessModel) site history
  cases current : history.1.state with
  | none => rw [current] at active; cases active
  | some control =>
      have transported := sourceInitialPublicationGuess_continuation_value_eq service.setup
        service.leaks (menu) service.horizon service.scheduler parameter event payload outputEq
        (Profile.update (sig := (guessModel).behavioralSignature) assessment.strategy who
          alternative) history.1 control current sample deposit who
      simpa only [initialGuessParameter, current, Option.elim_some]
        using transported

/-- Arbitrary native future behavior has guess utility at most one under a
nonnegative deposit. This uses the real audit marginal, without independence. -/
theorem initialGuessPayoff_le_one
    (parameter : State L service.setup.context → Bool) (event : (graph service.setup).EventId)
    (payload : L.Ty) (outputEq : (graph service.setup).outputLayout event = .publication payload)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (deposit : Player → ℝ) (who : Player) (nonnegative : 0 ≤ deposit who)
    (final : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).History) :
    service.initialGuessPayoff parameter event payload outputEq sample deposit who final ≤ 1 := by
  have base := (sourcePublicationGuessValue_mem_Icc service.setup service.leaks event payload
    outputEq (final.state.elim false fun control =>
      (sourceInitialReadout service.setup control.execution.application.config).elim false
        parameter) final.state).2
  have collected := (TerminalAudit.charge_mem_Icc ((runtime).serviceAuditObservation service.leaks)
    (sourceServiceAudit service.setup service.leaks sample) final.state who).1
  exact (sub_le_self _ (mul_nonneg collected nonnegative)).trans base

open Classical in
/-- The real native LOW commitment has the fixed public-payoff upper bound
given by its actual LOW-type counterfactual probability. -/
theorem initialGuess_context_withhold_le
    (parameter : State L service.setup.context → Bool)
    (assessment : (guessModel).BehavioralAssessment) (who : Player)
    (site : (guessModel).InformationSite who)
    (positive : 0 < (guessModel).informationMass assessment.strategy who site)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent (guessModel) assessment
      ((menu).decisionInformationAntichain
      (initialLaw service.setup) service.horizon service.scheduler))
    (choice : (guessModel).Choice who site.1) (material : (app).Submission)
    (selected : choice.1 = some ⟨some material⟩)
    (event : (graph service.setup).EventId) (payload : L.Ty)
    (outputEq : (graph service.setup).outputLayout event = .publication payload)
    (withheld : material.call.packet = .withhold event)
    (backend : EvidenceReportService (SettledEvidence service.setup))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate)
    (deposit : Player → ℝ) (nonnegative : 0 ≤ deposit who)
    (sufficient : 1 ≤ observationRate who * deliveryRate who * deposit who) :
    (assessment.continuationContext
      ((menu).bounded (initialLaw service.setup) service.horizon
        service.scheduler).wellFoundedHistories site
      (service.initialGuessPayoff parameter event payload outputEq backend.sample
        deposit who)).value
        ((assessment.strategy who).commit site.1 choice) ≤
      service.counterfactualInformationMass (menu) assessment.strategy who site
        {history | service.initialGuessParameter (menu) parameter history.1 = false} /
      service.counterfactualInformationMass (menu) assessment.strategy who site Set.univ := by
  rw [service.initialGuess_continuationContext_value]
  have belief := (assessment.isBayesConsistentAt_iff (guessModel) who site
    ((menu).decisionInformationAntichain (initialLaw service.setup) service.horizon
      service.scheduler who site) positive).mp (bayes who site positive)
  rw [belief]
  exact service.bayes_withhold_guess_committed_le (menu) parameter assessment.strategy who site
    positive choice material selected event payload outputEq withheld backend observationRate
    deliveryRate delivery_nonnegative coverage deposit nonnegative sufficient

open Classical in
/-- The actual LOW atom controls the whole incumbent continuation; every
other current response retains its real continuation and has utility at most one. -/
theorem initialGuess_context_incumbent_le_low_add_defect
    (parameter : State L service.setup.context → Bool)
    (assessment : (guessModel).BehavioralAssessment) (who : Player)
    (site : (guessModel).InformationSite who)
    (positive : 0 < (guessModel).informationMass assessment.strategy who site)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent (guessModel) assessment
      ((menu).decisionInformationAntichain
      (initialLaw service.setup) service.horizon service.scheduler))
    (choice : (guessModel).Choice who site.1) (material : (app).Submission)
    (selected : choice.1 = some ⟨some material⟩)
    (event : (graph service.setup).EventId) (payload : L.Ty)
    (outputEq : (graph service.setup).outputLayout event = .publication payload)
    (withheld : material.call.packet = .withhold event)
    (backend : EvidenceReportService (SettledEvidence service.setup))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate)
    (deposit : Player → ℝ) (nonnegative : 0 ≤ deposit who)
    (sufficient : 1 ≤ observationRate who * deliveryRate who * deposit who) :
    (assessment.continuationContext
      ((menu).bounded (initialLaw service.setup) service.horizon
        service.scheduler).wellFoundedHistories site
      (service.initialGuessPayoff parameter event payload outputEq backend.sample
        deposit who)).value
        (assessment.strategy who) ≤
      service.counterfactualInformationMass (menu) assessment.strategy who site
        {history | service.initialGuessParameter (menu) parameter history.1 = false} /
      service.counterfactualInformationMass (menu) assessment.strategy who site Set.univ +
        (1 - (assessment.strategy who site.1 choice).toReal) := by
  let certificate := ((menu).bounded (initialLaw service.setup) service.horizon
    service.scheduler).wellFoundedHistories
  let payoff := service.initialGuessPayoff parameter event payload outputEq backend.sample
    deposit who
  let ctx := assessment.continuationContext certificate site payoff
  let law := assessment.strategy who site.1
  let value := fun action => ctx.value ((assessment.strategy who).commit site.1 action)
  let low := service.counterfactualInformationMass (menu) assessment.strategy who site
    {history | service.initialGuessParameter (menu) parameter history.1 = false} /
      service.counterfactualInformationMass (menu) assessment.strategy who site Set.univ
  have lowNonnegative : 0 ≤ low := div_nonneg
    (service.counterfactualInformationMass_nonnegative (menu) assessment.strategy who site _)
    (service.counterfactualInformationMass_pos (menu) assessment.strategy who site positive).le
  have lowBound : value choice ≤ low := service.initialGuess_context_withhold_le parameter
    assessment who site positive bayes choice material selected event payload outputEq withheld
    backend observationRate deliveryRate delivery_nonnegative coverage deposit nonnegative
    sufficient
  have upper (action : (guessModel).Choice who site.1) : value action ≤ 1 :=
    expect_le_const _ _ (payoffIntegrable_of_finite _ _) 1 fun final _ =>
      service.initialGuessPayoff_le_one parameter event payload outputEq backend.sample deposit
        who nonnegative final
  have contextEq := assessment.continuationContext_eq_truncated_of_bounded
    certificate ((menu).bounded (initialLaw service.setup) service.horizon service.scheduler)
    site payoff
  have affine := assessment.truncatedContinuationContext_withLaw_eq_expect (guessModel)
    ((menu).decisionRecall (initialLaw service.setup) service.horizon
      service.scheduler).actsOnceWhereItMatters site (assessment.strategy who) law payoff
        (2 * service.horizon) (payoffIntegrable_of_finite _ _) value (fun _ _ => by
          rw [← contextEq])
  have ownLaw : (assessment.strategy who).withLaw site.1 law = assessment.strategy who :=
    (assessment.strategy who).withLaw_eq_self site.1
  have expectation : ctx.value (assessment.strategy who) = expect law value := by
    simpa only [← contextEq, ownLaw] using affine.2
  have bound (action : (guessModel).Choice who site.1) :
      value action ≤ low + if choice = action then 0 else 1 := by
    by_cases same : choice = action
    · subst action
      rw [ite_eq_left (show choice = choice from rfl), add_zero]
      exact lowBound
    · rw [ite_eq_right same]
      exact (upper action).trans (by linarith)
  have defect : expect law (fun action => if choice = action then (0 : ℝ) else 1) =
      1 - (law choice).toReal := by
    have identity (action : (guessModel).Choice who site.1) :
        (if choice = action then (0 : ℝ) else 1) =
          1 - (if choice = action then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    simp_rw [identity]
    rw [expect_sub (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _),
      expect_constant, expect_ite_eq, mul_one]
  change ctx.value (assessment.strategy who) ≤ low + (1 - (law choice).toReal)
  rw [expectation]
  calc
    _ ≤ expect law (fun action => low + if choice = action then 0 else 1) :=
      expect_mono (fun action _ => bound action)
        (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
    _ = _ := by
      rw [expect_add (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _),
        expect_constant, defect]

open Classical in
/-- Protected HIGH has exactly the actual HIGH-type counterfactual value for
the fixed terminal payoff, after its same whole immediate continuation. -/
theorem initialGuess_context_true_eq
    (parameter : State L service.setup.context → Bool)
    (source : BehavioralProfile service.setup.program) (who : Player)
    (permitted : (source who).Admitted service.setup.program (CommitmentInterface.values _))
    (supports : ∀ player, (source player).SupportsEffectiveChoices service.setup.program
      (CommitmentInterface.values service.setup.program) []
      (Revelations.initial service.setup.context))
    (assessment : (guessModel).BehavioralAssessment) (site : (guessModel).InformationSite who)
    (positive : 0 < (guessModel).informationMass assessment.strategy who site)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent (guessModel) assessment
      ((menu).decisionInformationAntichain
      (initialLaw service.setup) service.horizon service.scheduler))
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (observed : site.1 = some (past, view))
    (compatible : service.sourceCompatibleInfo who site.1)
    (event : (graph service.setup).EventId) (payload : L.Ty)
    (binding : FieldRef (graph service.setup).layout (.binding who payload))
    (checks : List (GuardCheck (graph service.setup).layout payload))
    (outputEq : (graph service.setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph service.setup).layout) outputEq)
      ((graph service.setup).nodes event) = .resolve who payload binding checks)
    (turn : view.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime).eventRecorded service.leaks past event = false)
    (value : L.Val payload)
    (successful : EventCode.resolveOutput? binding checks true view.application.observation.store =
      some (.success value))
    (choice : (guessModel).Choice who site.1)
    (selected : choice.1 = some ((runtime).canonicalServiceDecision service.leaks who past view
      event (cast (congrArg EventField.Action outputEq.symm) true)))
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual sampled, sampled ∈ (sample actual).support → sampled ⊆ actual)
    (deposit : Player → ℝ) :
    (assessment.continuationContext
      ((menu).bounded (initialLaw service.setup) service.horizon
        service.scheduler).wellFoundedHistories site
      (service.initialGuessPayoff parameter event payload outputEq sample deposit who)).value
        ((service.effectiveImmediateComparator source who).commit site.1 choice) =
      service.counterfactualInformationMass (menu) assessment.strategy who site
        {history | service.initialGuessParameter (menu) parameter history.1 = true} /
      service.counterfactualInformationMass (menu) assessment.strategy who site Set.univ := by
  rw [service.initialGuess_continuationContext_value]
  have belief := (assessment.isBayesConsistentAt_iff (guessModel) who site
    ((menu).decisionInformationAntichain (initialLaw service.setup) service.horizon
      service.scheduler who site) positive).mp (bayes who site positive)
  rw [belief]
  exact service.bayes_true_guess_comparator_eq parameter source who permitted supports
    assessment.strategy site positive past view observed compatible event payload binding checks
    outputEq codeEq turn unrecorded value successful choice selected sample authentic deposit

open Classical in
/-- Ordinary whole-policy rationality forces the actual native HIGH probability
below the LOW probability plus the incumbent's actual non-LOW response mass.
No incoming source-posterior equation or local optimality wrapper is assumed. -/
theorem rational_initialGuess_counterfactual_le
    (parameter : State L service.setup.context → Bool)
    (source : BehavioralProfile service.setup.program) (who : Player)
    (permitted : (source who).Admitted service.setup.program (CommitmentInterface.values _))
    (supports : ∀ player, (source player).SupportsEffectiveChoices service.setup.program
      (CommitmentInterface.values service.setup.program) []
      (Revelations.initial service.setup.context))
    (assessment : (guessModel).BehavioralAssessment) (site : (guessModel).InformationSite who)
    (positive : 0 < (guessModel).informationMass assessment.strategy who site)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent (guessModel) assessment
      ((menu).decisionInformationAntichain
      (initialLaw service.setup) service.horizon service.scheduler))
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (observed : site.1 = some (past, view))
    (compatible : service.sourceCompatibleInfo who site.1)
    (event : (graph service.setup).EventId) (payload : L.Ty)
    (binding : FieldRef (graph service.setup).layout (.binding who payload))
    (checks : List (GuardCheck (graph service.setup).layout payload))
    (outputEq : (graph service.setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph service.setup).layout) outputEq)
      ((graph service.setup).nodes event) = .resolve who payload binding checks)
    (turn : view.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime).eventRecorded service.leaks past event = false)
    (value : L.Val payload)
    (successful : EventCode.resolveOutput? binding checks true view.application.observation.store =
      some (.success value))
    (highChoice lowChoice : (guessModel).Choice who site.1)
    (highSelected : highChoice.1 = some ((runtime).canonicalServiceDecision service.leaks who
      past view event (cast (congrArg EventField.Action outputEq.symm) true)))
    (material : (app).Submission) (lowSelected : lowChoice.1 = some ⟨some material⟩)
    (withheld : material.call.packet = .withhold event)
    (backend : EvidenceReportService (SettledEvidence service.setup))
    (authentic : ∀ actual sampled, sampled ∈ (backend.sample actual).support → sampled ⊆ actual)
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate)
    (deposit : Player → ℝ) (nonnegative : 0 ≤ deposit who)
    (sufficient : 1 ≤ observationRate who * deliveryRate who * deposit who)
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext
        ((menu).bounded (initialLaw service.setup) service.horizon
          service.scheduler).wellFoundedHistories site
        (service.initialGuessPayoff parameter event payload outputEq backend.sample deposit who))) :
    let total := service.counterfactualInformationMass (menu) assessment.strategy who site Set.univ
    let high := service.counterfactualInformationMass (menu) assessment.strategy who site
      {history | service.initialGuessParameter (menu) parameter history.1 = true}
    let low := service.counterfactualInformationMass (menu) assessment.strategy who site
      {history | service.initialGuessParameter (menu) parameter history.1 = false}
    let defect := 1 - (assessment.strategy who site.1 lowChoice).toReal
    high / total ≤ low / total + defect ∧ high ≤ low + total * defect := by
  intro total high low defect
  let certificate := ((menu).bounded (initialLaw service.setup) service.horizon
    service.scheduler).wellFoundedHistories
  let payoff := service.initialGuessPayoff parameter event payload outputEq backend.sample
    deposit who
  let ctx := assessment.continuationContext certificate site payoff
  let alternative := (service.effectiveImmediateComparator source who).commit site.1 highChoice
  have highValue : ctx.value alternative = high / total := service.initialGuess_context_true_eq
    parameter source who permitted supports assessment site positive bayes past view observed
    compatible event payload binding checks outputEq codeEq turn unrecorded value successful
    highChoice highSelected backend.sample authentic deposit
  have lowBound : ctx.value (assessment.strategy who) ≤ low / total + defect :=
    service.initialGuess_context_incumbent_le_low_add_defect parameter assessment who site
      positive bayes lowChoice material lowSelected event payload outputEq withheld backend
      observationRate deliveryRate delivery_nonnegative coverage deposit nonnegative sufficient
  have optimal := (Context.isLocallyOptimal_iff_of_integrable
    (payoffIntegrable_of_finite _ _) (fun _ _ => payoffIntegrable_of_finite _ _)).mp rational
      alternative (Set.mem_univ _)
  have normalized : high / total ≤ low / total + defect := by
    rw [← highValue]
    exact optimal.trans lowBound
  refine ⟨normalized, ?_⟩
  have totalPositive := service.counterfactualInformationMass_pos (menu) assessment.strategy
    who site positive
  have multiplied := (div_le_iff₀ totalPositive).mp normalized
  rwa [add_mul, div_mul_cancel₀ _ totalPositive.ne', mul_comm defect total] at multiplied

open Classical Filter in
/-- A rational LOW limit of the same fully mixed native Bayes sequence forces
a vanishing conditional HIGH-versus-LOW counterfactual gap. Positivity comes
from actual full mixing; the error comes from actual assessment convergence
and the observable non-LOW atom, without dividing an unconditional error. -/
theorem convergent_lowGuess_counterfactual_le
    (parameter : State L service.setup.context → Bool)
    (source : Nat → BehavioralProfile service.setup.program) (who : Player)
    (permitted : ∀ n, (source n who).Admitted service.setup.program (CommitmentInterface.values _))
    (supports : ∀ n player, (source n player).SupportsEffectiveChoices service.setup.program
      (CommitmentInterface.values service.setup.program) []
      (Revelations.initial service.setup.context))
    (sequence : Nat → (guessModel).BehavioralAssessment)
    (target : (guessModel).BehavioralAssessment)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent (guessModel)
      (sequence n) ((menu).decisionInformationAntichain
      (initialLaw service.setup) service.horizon service.scheduler))
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence target)
    (site : (guessModel).InformationSite who)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (observed : site.1 = some (past, view))
    (compatible : service.sourceCompatibleInfo who site.1)
    (event : (graph service.setup).EventId) (payload : L.Ty)
    (binding : FieldRef (graph service.setup).layout (.binding who payload))
    (checks : List (GuardCheck (graph service.setup).layout payload))
    (outputEq : (graph service.setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph service.setup).layout) outputEq)
      ((graph service.setup).nodes event) = .resolve who payload binding checks)
    (turn : view.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime).eventRecorded service.leaks past event = false)
    (value : L.Val payload)
    (successful : EventCode.resolveOutput? binding checks true view.application.observation.store =
      some (.success value))
    (highChoice lowChoice : (guessModel).Choice who site.1)
    (highSelected : highChoice.1 = some ((runtime).canonicalServiceDecision service.leaks who
      past view event (cast (congrArg EventField.Action outputEq.symm) true)))
    (material : (app).Submission) (lowSelected : lowChoice.1 = some ⟨some material⟩)
    (withheld : material.call.packet = .withhold event)
    (lowLimit : target.strategy who site.1 = PMF.pure lowChoice)
    (backend : EvidenceReportService (SettledEvidence service.setup))
    (authentic : ∀ actual sampled, sampled ∈ (backend.sample actual).support → sampled ⊆ actual)
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate)
    (deposit : Player → ℝ) (nonnegative : 0 ≤ deposit who)
    (sufficient : 1 ≤ observationRate who * deliveryRate who * deposit who)
    (rational : target.IsSequentiallyRationalAt site
      (target.continuationContext
        ((menu).bounded (initialLaw service.setup) service.horizon
          service.scheduler).wellFoundedHistories site
        (service.initialGuessPayoff parameter event payload outputEq backend.sample deposit who))) :
    ∃ error : Nat → ℝ, (∀ n, 0 ≤ error n) ∧ Tendsto error atTop (nhds 0) ∧
      ∀ n,
        let total := service.counterfactualInformationMass (menu) (sequence n).strategy
          who site Set.univ
        let high := service.counterfactualInformationMass (menu) (sequence n).strategy who site
          {history | service.initialGuessParameter (menu) parameter history.1 = true}
        let low := service.counterfactualInformationMass (menu) (sequence n).strategy who site
          {history | service.initialGuessParameter (menu) parameter history.1 = false}
        high / total ≤ low / total + error n ∧ high ≤ low + total * error n := by
  let certificate := ((menu).bounded (initialLaw service.setup) service.horizon
    service.scheduler).wellFoundedHistories
  let payoff := service.initialGuessPayoff parameter event payload outputEq backend.sample
    deposit who
  have targetContext := target.continuationContext_eq_truncated_of_bounded
    certificate ((menu).bounded (initialLaw service.setup) service.horizon service.scheduler)
    site payoff
  have rationalFinite : target.IsSequentiallyRationalAt site
      (target.truncatedContinuationContext site payoff (2 * service.horizon + 1)) := by
    rw [← targetContext]
    exact rational
  obtain ⟨regret, regretNonnegative, regretVanishes, gain⟩ :=
    converges.exists_uniform_policy_gain_bound_at_site who site payoff
      (2 * service.horizon + 1) rationalFinite
  let defect := fun n => 1 - ((sequence n).strategy who site.1 lowChoice).toReal
  have defectNonnegative (n : Nat) : 0 ≤ defect n :=
    sub_nonneg.mpr (pmf_toReal_apply_le_one _ _)
  have atom := (converges.strategy who site).toReal lowChoice
  rw [lowLimit, PMF.pure_apply_self, ENNReal.toReal_one] at atom
  have defectVanishes : Tendsto defect atTop (nhds 0) := by
    simpa only [sub_self] using (tendsto_const_nhds.sub atom :
      Tendsto (fun n => 1 - ((sequence n).strategy who site.1 lowChoice).toReal)
        atTop (nhds (1 - 1)))
  refine ⟨fun n => defect n + regret n,
    (fun n => add_nonneg (defectNonnegative n) (regretNonnegative n)),
    by simpa only [zero_add] using defectVanishes.add regretVanishes, ?_⟩
  intro n total high low
  have positive := (guessModel).informationMass_pos_of_fullSupport (sequence n).strategy
    (mixed n) who site
  let ctx := (sequence n).continuationContext certificate site payoff
  let alternative := (service.effectiveImmediateComparator (source n) who).commit site.1 highChoice
  have highValue : ctx.value alternative = high / total := service.initialGuess_context_true_eq
    parameter (source n) who (permitted n) (supports n) (sequence n) site positive (bayes n)
    past view observed compatible event payload binding checks outputEq codeEq turn unrecorded
    value successful highChoice highSelected backend.sample authentic deposit
  have lowBound : ctx.value ((sequence n).strategy who) ≤ low / total + defect n :=
    service.initialGuess_context_incumbent_le_low_add_defect parameter (sequence n) who site
      positive (bayes n) lowChoice material lowSelected event payload outputEq withheld backend
      observationRate deliveryRate delivery_nonnegative coverage deposit nonnegative sufficient
  have currentContext := (sequence n).continuationContext_eq_truncated_of_bounded
    certificate ((menu).bounded (initialLaw service.setup) service.horizon service.scheduler)
    site payoff
  have currentGain := gain n alternative
  rw [← currentContext] at currentGain
  have normalized : high / total ≤ low / total + (defect n + regret n) := by
    rw [← highValue]
    linarith
  refine ⟨normalized, ?_⟩
  have totalPositive := service.counterfactualInformationMass_pos (menu) (sequence n).strategy
    who site positive
  have multiplied := (div_le_iff₀ totalPositive).mp normalized
  rwa [add_mul, div_mul_cancel₀ _ totalPositive.ne', mul_comm (defect n + regret n) total]
    at multiplied

end Vegas.AsyncServiceSpec
