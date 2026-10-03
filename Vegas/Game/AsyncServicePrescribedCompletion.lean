/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceEffectiveImmediateComparator
import Interaction.ReactiveMenuContinuation
import Vegas.Game.AsyncServiceSourceSites
import Vegas.Game.SourceServiceImmediatePolicy
import Vegas.Game.SourceServiceProtectedDecisionLaw
import Vegas.Game.SourceServiceCompletedRationality
import Vegas.Game.SourceServiceFreeRationality
import GameTheoryExtensions.Analysis.Protocol.PrescribedCompletion
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Actual native completion of protected source decisions

The fixed admitted effective source profile decides immediately at every
source-compatible protected unrecorded input, including after earlier waits.
The classifier keeps its actual risk-menu witness. Menu inclusion carries the
immediate reference into the full effective game, where geometric timing and
uniform trembles derive the prescribed limits. Initialized whole-history and
sampled settlement laws agree with exact first-turn source execution.

Free information sites receive a consistent completion optimal against every
whole owner continuation policy.
Completed source-compatible sites are also rational when the owner's deposit
is nonnegative. Comparisons at unfinished prescribed sites and compatibility
with a varying original source assessment sequence are not asserted. In
particular, normalization at zero-mass private transcripts is not assumed
continuous.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
private abbrev completionMenu : (app).ResponseMenu :=
  service.bounds.riskMenu (runtime service.setup) service.leaks service.bound

local notation "menu" => completionMenu service
local notation "model" => ReactiveApplication.ResponseMenu.information
  (service.bounds.riskMenu (runtime service.setup) service.leaks service.bound)
  (initialLaw service.setup) service.horizon service.scheduler

/-- At compatible inputs the owner decides now, regardless of earlier waits.
At other inputs this total profile uses the actual locally admitted immediate
policy; its behavior there is replaced by the free-site completion. -/
def immediateProfile (profile : BehavioralProfile service.setup.program) :
    ∀ who, (model).BehavioralPolicy who := fun who =>
  (menu).restrictPolicy (initialLaw service.setup) service.horizon service.scheduler who
    (sourceServiceImmediatePolicy service.setup service.leaks service.bound profile who)

omit [Fintype Player] in
/-- A recorded event makes the actual owner turn policy silent for every
timing lottery and source profile. -/
theorem sourceServiceTurnPolicy_recorded_silent
    (turns : Nat) (timing : TurnTiming service.setup turns)
    (profile : BehavioralProfile service.setup.program) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (event : (graph service.setup).EventId)
    (turn : view.application.publicView.ownTurn? who = some event)
    (recorded : (runtime service.setup).eventRecorded service.leaks past event = true) :
    sourceServiceTurnPolicy service.setup service.leaks service.bound turns timing profile who
        past view = PMF.pure ⟨none⟩ := by
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  rw [sourceServiceTurnPolicy_turn service.setup service.leaks service.bound turns timing
    profile who past view event owned turn, ReactiveApplication.policyMixture_policy]
  have same (slot : Fin (turns + 1)) :
      sourceServiceTurnFamily service.setup service.leaks service.bound profile who event turns
        slot past view = PMF.pure ⟨none⟩ := by
    unfold sourceServiceTurnFamily ReactiveApplication.turnScheduledPolicy
    dsimp only
    split
    · simp only [sourceServiceCanonicalOpportunity, recorded, ↓reduceIte,
        ReactiveApplication.silentPolicy]
    · rfl
  simp_rw [same]
  exact PMF.bind_const _ _

omit [Fintype Player] in
/-- Only actual initialized support is needed to identify immediate play
with exact first-turn play. Its recorded past cannot contain an unsent old
own turn. -/
theorem sourceServiceImmediatePolicy_firstTurn_roundSupported
    (turns : Nat) (profile : BehavioralProfile service.setup.program)
    (control : (app).Control) (who : Player)
    (actual : (app).RoundSupported (initialLaw service.setup) service.horizon service.scheduler
      (sourceServiceTurnPolicy service.setup service.leaks service.bound turns
        (firstTurnTiming service.setup turns) profile) (some control)) :
    sourceServiceImmediatePolicy service.setup service.leaks service.bound profile who
        (control.execution.recall who) (control.execution.observe (app) who) =
      sourceServiceTurnPolicy service.setup service.leaks service.bound turns
        (firstTurnTiming service.setup turns) profile who (control.execution.recall who)
          (control.execution.observe (app) who) := by
  have clear := sourceServiceFirstTurn_serviceRisk_clear_roundSupported service.contract
    service.timely _ who turns profile rfl control actual
  cases turn : (control.execution.observe (app) who).application.publicView.ownTurn? who with
  | none => simp only [sourceServiceImmediatePolicy, clear, ↓reduceIte, turn,
      sourceServiceTurnPolicy]
  | some event =>
      rw [sourceServiceImmediatePolicy_at_event clear turn]
      by_cases recorded : (runtime service.setup).eventRecorded service.leaks
          (control.execution.recall who) event = true
      · rw [sourceServiceTurnPolicy_recorded_silent service turns
          (firstTurnTiming service.setup turns) profile who _ _ event turn recorded]
        simp only [sourceServiceCanonicalOpportunity, recorded, ↓reduceIte,
          ReactiveApplication.silentPolicy]
      · have unrecorded : (runtime service.setup).eventRecorded service.leaks
            (control.execution.recall who) event = false := Bool.eq_false_of_not_eq_true recorded
        have turned := (sourceServiceFirstTurn_recallFacts_roundSupported service.contract
          service.timely _ who turns profile rfl control actual).1
        have first : sourceServiceTurn service.setup service.leaks who event
            (control.execution.recall who) (control.execution.observe (app) who) = some 0 := by
          simp only [sourceServiceTurn, turn, ↓reduceIte]
          apply congrArg some
          apply List.countP_eq_zero.mpr
          intro entry member seen
          have sent := turned entry member event (of_decide_eq_true seen)
          rw [unrecorded] at sent
          cases sent
        exact (sourceServiceTurnPolicy_firstTurn
          (PublicView.ownTurn?_spec _ who event turn).2 first).symm

/-- The immediate profile has the same initialized complete history law as
exact first-turn play, including all private recall and pending traffic. -/
theorem immediateProfile_initialized_history (turns : Nat)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program)) (fuel : Nat) :
    (model).runBehavioral (service.immediateProfile profile) fuel =
      (model).runBehavioral (service.firstTurnProfile turns profile) fuel := by
  classical
  symm
  apply (model).runBehavioralFrom_congr_on_support
  intro elapsed _ history reached running who
  by_cases active : (menu).protocol (initialLaw service.setup) service.horizon service.scheduler
      |>.active history.state who
  · have actual := service.firstTurnProfile_initialized_roundSupported turns profile permitted
      elapsed history reached
    have atState : (model).infoOf who history.trace = (app).observe who history.state :=
      (menu).info (initialLaw service.setup) service.horizon service.scheduler who history.trace
    obtain ⟨state, trace⟩ := history
    cases state with
    | none => cases active
    | some control =>
        have acting : control.actor = some who := active
        have input : (model).infoOf who trace =
            some (control.execution.recall who, control.execution.observe (app) who) := by
          rw [atState]
          simp only [ReactiveApplication.observe, acting, ↓reduceIte]
        rw [input]
        unfold immediateProfile firstTurnProfile
        apply pmf_map_injective (f := Subtype.val) Subtype.val_injective
        rw [(menu).restrictPolicy_map_val (initialLaw service.setup) service.horizon
          service.scheduler who _ _ _ (fun response chosen =>
            service.firstTurnProfile_response_covered turns profile permitted who control trace
              actual response chosen),
          (menu).restrictPolicy_map_val (initialLaw service.setup) service.horizon
            service.scheduler who _ _ _ (fun response chosen =>
              sourceServiceImmediatePolicy_risk_retained service.bounds service.values
                service.initialValues service.capacity service.bound profile who (permitted who)
                  control trace response chosen)]
        exact congrArg (PMF.map some)
          (sourceServiceImmediatePolicy_firstTurn_roundSupported service turns profile control who
            actual).symm
  · exact (model).behavioral_eq_of_not_active _ _ history.trace active

local notation "effectiveMenu" => service.bounds.menu (runtime service.setup) service.leaks
local notation "effectiveModel" => ReactiveApplication.ResponseMenu.information
  (service.bounds.menu (runtime service.setup) service.leaks)
  (initialLaw service.setup) service.horizon service.scheduler

/-- The full effective immediate pin agrees with the risk reference at every
actual risk decision site, including sites after earlier deferrals. -/
theorem immediateProfile_extends_effective
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program)) :
    ((service.bounds.riskMenu_in_effective (runtime service.setup) service.leaks
      service.bound).actionRestriction (initialLaw service.setup) service.horizon
        service.scheduler).ExtendsProfile (service.immediateProfile profile)
      (fun who => service.effectiveImmediateComparator profile who) := by
  exact (service.bounds.riskMenu_in_effective (runtime service.setup) service.leaks
    service.bound).restrictProfile_extends_of_admissible (initialLaw service.setup)
      service.horizon service.scheduler
      (sourceServiceImmediatePolicy service.setup service.leaks service.bound profile)
      (fun who => sourceServiceImmediatePolicy_risk_admissible service.bounds service.values
        service.initialValues service.capacity service.bound profile who (permitted who)
          service.horizon service.scheduler)

/-- Full effective immediate play has the embedded initialized first-turn
history law. The embedding preserves every actual state and own input. -/
theorem effectiveImmediateProfile_initialized_history (turns : Nat)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program)) (fuel : Nat) :
    (effectiveModel).runBehavioral (fun who => service.effectiveImmediateComparator profile who)
        fuel =
      ((model).runBehavioral (service.firstTurnProfile turns profile) fuel).map
        ((service.bounds.riskMenu_in_effective (runtime service.setup) service.leaks
          service.bound).history (initialLaw service.setup) service.horizon service.scheduler) := by
  have law := InformationModel.ActionRestriction.initialized_law
    ((service.bounds.riskMenu_in_effective (runtime service.setup) service.leaks
      service.bound).actionRestriction (initialLaw service.setup) service.horizon
        service.scheduler) (service.immediateProfile profile)
        (fun who => service.effectiveImmediateComparator profile who)
        (service.immediateProfile_extends_effective profile permitted) fuel
  change ((model).runBehavioral (service.immediateProfile profile) fuel).map _ = _ at law
  rw [service.immediateProfile_initialized_history turns profile permitted] at law
  exact law.symm

/-- Every actual decision visited by initialized full effective immediate
play has the existing clean source-compatible witness. -/
theorem effectiveImmediateProfile_sourceCompatibleInfo (turns : Nat)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (fuel : Nat)
    (history : ((effectiveMenu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).History)
    (reached : history ∈ ((effectiveModel).runBehavioral
      (fun who => service.effectiveImmediateComparator profile who) fuel).support)
    (who : Player)
    (active : ((effectiveMenu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).active history.state who) :
    service.sourceCompatibleInfo who ((effectiveModel).infoOf who history.trace) := by
  rw [service.effectiveImmediateProfile_initialized_history turns profile permitted fuel,
    PMF.support_map] at reached
  obtain ⟨original, supported, rfl⟩ := reached
  have retainedActive : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).active original.state who := active
  have compatible := service.firstTurnProfile_sourceCompatibleInfo turns profile permitted
    effective fuel original supported who retainedActive
  rw [(service.bounds.riskMenu_in_effective (runtime service.setup) service.leaks
    service.bound).observed]
  exact compatible

/-- The actual full effective terminal pin law is the embedded risk first-turn
law. This preserves one terminal state before any settlement sampling. -/
theorem effectiveImmediateProfile_terminal_history
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program)) :
    (effectiveModel).runBehavioralTerminalFrom
        ((effectiveMenu).bounded (initialLaw service.setup) service.horizon
          service.scheduler).wellFoundedHistories
        (fun who => service.effectiveImmediateComparator profile who)
        ((effectiveMenu).protocol (initialLaw service.setup) service.horizon
          service.scheduler).initHistory =
      ((model).runBehavioralTerminalFrom
        ((menu).bounded (initialLaw service.setup) service.horizon
          service.scheduler).wellFoundedHistories
        (service.firstTurnProfile service.horizon profile)
        ((menu).protocol (initialLaw service.setup) service.horizon
          service.scheduler).initHistory).map
        ((service.bounds.riskMenu_in_effective (runtime service.setup) service.leaks
          service.bound).history (initialLaw service.setup) service.horizon service.scheduler) := by
  rw [InformationModel.runBehavioralTerminalFrom_initHistory (effectiveModel) _ _
      ((effectiveMenu).bounded (initialLaw service.setup) service.horizon service.scheduler),
    InformationModel.runBehavioralTerminalFrom_initHistory (model) _ _
      ((menu).bounded (initialLaw service.setup) service.horizon service.scheduler)]
  exact service.effectiveImmediateProfile_initialized_history service.horizon profile permitted _

/-- The full effective pin preserves typed source outcomes and the complete
actual sampled settlement vector jointly, without a new audit assumption. -/
theorem effectiveImmediateProfile_joint_law
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (utility : State L service.setup.program.terminalCtx → Player → ℝ)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) :
    ((effectiveModel).runBehavioralTerminalFrom
      ((effectiveMenu).bounded (initialLaw service.setup) service.horizon
        service.scheduler).wellFoundedHistories
      (fun who => service.effectiveImmediateComparator profile who)
      ((effectiveMenu).protocol (initialLaw service.setup) service.horizon
        service.scheduler).initHistory).bind (fun final =>
          (TerminalAudit.settlement (baseUtility service.setup service.leaks utility)
            ((runtime service.setup).serviceAuditObservation service.leaks)
            (sourceServiceAudit service.setup service.leaks sample)
            (service.auditDeposit (baseUtility service.setup service.leaks utility) probability)
            final.state).map fun payoffs =>
              (sourceReadout service.setup service.leaks final.state, payoffs)) =
      (service.setup.run profile).map (fun source => (some source, utility source)) := by
  rw [service.effectiveImmediateProfile_terminal_history profile permitted, PMF.bind_map]
  exact service.firstTurnProfile_joint_law service.horizon profile permitted effective utility
    sample authentic probability

private def completionWeight (n : Nat) : ℝ := (1 / ((n : ℝ) + 1)) / 2

private theorem completionWeight_positive (n : Nat) : 0 < completionWeight n := by
  unfold completionWeight
  positivity

private theorem completionWeight_small (n : Nat) : completionWeight n < 1 := by
  have bound : 1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  unfold completionWeight
  linarith

private theorem completionWeight_vanishes : Tendsto completionWeight atTop (nhds 0) := by
  change Tendsto (fun n : Nat => (1 / ((n : ℝ) + 1)) / 2) atTop (nhds 0)
  simpa only [zero_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2

/-- The actual timing family converges at every compatible input to the
immediate source decision, rather than to the literal slot-zero policy. -/
private theorem compatible_geometric_immediate_limit
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (who : Player) (info : (app).Info) (compatible : service.sourceCompatibleInfo who info) :
    PMFConvergesPointwise (fun n =>
      (menu).restrictPolicy (initialLaw service.setup) service.horizon service.scheduler who
        (sourceServiceTurnPolicy service.setup service.leaks service.bound service.horizon
          (geometricTiming service.setup service.horizon (completionWeight n)
            (completionWeight_positive n).le (completionWeight_small n).le) profile who) info)
      (service.immediateProfile profile who info) := by
  classical
  obtain ⟨_witnessProfile, _turns, _timing, _admitted, _effective, history, remaining, execution,
    current, observed, _actual, allClear, clear⟩ := compatible
  have trace : ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  have input : info = some (execution.recall who, execution.observe (app) who) := by
    have stateInfo : (model).infoOf who history.trace = (app).observe who history.state :=
      (menu).info (initialLaw service.setup) service.horizon service.scheduler who history.trace
    rw [stateInfo, current] at observed
    simpa only [ReactiveApplication.observe, ↓reduceIte] using observed.symm
  rw [input]
  have physical : PMFConvergesPointwise (fun n => sourceServiceTurnPolicy service.setup
      service.leaks service.bound service.horizon (geometricTiming service.setup service.horizon
        (completionWeight n) (completionWeight_positive n).le (completionWeight_small n).le)
          profile who (execution.recall who) (execution.observe (app) who))
      (sourceServiceImmediatePolicy service.setup service.leaks service.bound profile who
        (execution.recall who) (execution.observe (app) who)) := by
    cases turn : (execution.observe (app) who).application.publicView.ownTurn? who with
    | none =>
        simp only [sourceServiceTurnPolicy, sourceServiceImmediatePolicy, clear, turn,
          ↓reduceIte]
        exact pmfConvergesPointwise_const _
    | some event =>
        rw [sourceServiceImmediatePolicy_at_event clear turn]
        by_cases recorded : (runtime service.setup).eventRecorded service.leaks
            (execution.recall who) event = true
        · simp_rw [sourceServiceTurnPolicy_recorded_silent service _ _ profile who _ _ event turn
            recorded]
          simp only [sourceServiceCanonicalOpportunity, recorded, ↓reduceIte,
            ReactiveApplication.silentPolicy]
          exact pmfConvergesPointwise_const _
        · exact sourceServiceDecision_clear_geometric_limit service.bounds service.bound profile
            who execution trace allClear event (Bool.eq_false_of_not_eq_true recorded) turn
              completionWeight completionWeight_positive completionWeight_small
                completionWeight_vanishes
  have maps (n : Nat) :
      (((menu).restrictPolicy (initialLaw service.setup) service.horizon service.scheduler who
        (sourceServiceTurnPolicy service.setup service.leaks service.bound service.horizon
          (geometricTiming service.setup service.horizon (completionWeight n)
            (completionWeight_positive n).le (completionWeight_small n).le) profile who)
              (some (execution.recall who, execution.observe (app) who))).map Subtype.val) =
        (sourceServiceTurnPolicy service.setup service.leaks service.bound service.horizon
          (geometricTiming service.setup service.horizon (completionWeight n)
            (completionWeight_positive n).le (completionWeight_small n).le) profile who
              (execution.recall who) (execution.observe (app) who)).map some :=
    (menu).restrictPolicy_map_val (initialLaw service.setup) service.horizon service.scheduler
      who _ _ _ (fun response chosen => sourceServiceTurnPolicy_risk_retained service.bounds
        service.values service.initialValues service.capacity service.bound service.horizon _
          profile who (permitted who) _ trace clear response chosen)
  have targetMap : ((service.immediateProfile profile who
      (some (execution.recall who, execution.observe (app) who))).map Subtype.val) =
      (sourceServiceImmediatePolicy service.setup service.leaks service.bound profile who
        (execution.recall who) (execution.observe (app) who)).map some :=
    (menu).restrictPolicy_map_val (initialLaw service.setup) service.horizon service.scheduler
      who _ _ _ (fun response chosen => sourceServiceImmediatePolicy_risk_retained service.bounds
        service.values service.initialValues service.capacity service.bound profile who
          (permitted who) _ trace response chosen)
  intro choice
  have convergence := physical.map some (choice.1)
  have same (n : Nat) := congrArg (fun law => law choice.1) (maps n)
  have target := congrArg (fun law => law choice.1) targetMap
  simp only [pmf_map_apply_of_injective _ Subtype.val_injective] at same target
  have atoms := convergence.congr (fun n => (same n).symm)
  exact target.symm ▸ atoms

private theorem compatible_is_risk_decision
    (who : Player) (info : (app).Info)
    (compatible : service.sourceCompatibleInfo who info) : (model).IsDecisionInfo who info := by
  obtain ⟨_profile, _turns, _timing, _permitted, _effective, history, remaining, execution,
    current, observed, _actual, _allClear, _clear⟩ := compatible
  have input : info = some (execution.recall who, execution.observe (app) who) := by
    have actualInfo : (model).infoOf who history.trace = (app).observe who history.state :=
      (menu).info (initialLaw service.setup) service.horizon service.scheduler who history.trace
    rw [actualInfo, current] at observed
    simpa only [ReactiveApplication.observe, ↓reduceIte] using observed.symm
  refine ⟨⟨history, observed⟩, ?_, ⟨none⟩, ?_⟩
  · rw [current]
    simp only [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.terminal,
      reduceCtorEq, and_false, not_false_eq_true]
  · rw [input]
    exact ⟨⟨none⟩, service.bounds.canonicalActions_subset_risk (runtime service.setup)
      service.leaks service.bound who _ _
        (service.bounds.silence_canonical (runtime service.setup) service.leaks who _ _), rfl⟩

private theorem compatible_geometric_effective_limit
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (who : Player) (info : (app).Info) (compatible : service.sourceCompatibleInfo who info) :
    PMFConvergesPointwise (fun n =>
      ((menu).restrictPolicy (initialLaw service.setup) service.horizon service.scheduler who
        (sourceServiceTurnPolicy service.setup service.leaks service.bound service.horizon
          (geometricTiming service.setup service.horizon (completionWeight n)
            (completionWeight_positive n).le (completionWeight_small n).le) profile who) info).map
        ((service.bounds.riskMenu_in_effective (runtime service.setup) service.leaks
          service.bound).choice (initialLaw service.setup) service.horizon service.scheduler who
            info)) (service.effectiveImmediateComparator profile who info) := by
  let retainedSite : (model).InformationSite who :=
    ⟨info, compatible_is_risk_decision service who info compatible⟩
  have agreement := service.immediateProfile_extends_effective profile permitted who retainedSite
  change service.effectiveImmediateComparator profile who info =
    (service.immediateProfile profile who info).map
      ((service.bounds.riskMenu_in_effective (runtime service.setup) service.leaks
        service.bound).choice (initialLaw service.setup) service.horizon service.scheduler who
          info) at agreement
  have deciding := (compatible_geometric_immediate_limit service profile permitted who info
    compatible).map ((service.bounds.riskMenu_in_effective (runtime service.setup) service.leaks
      service.bound).choice (initialLaw service.setup) service.horizon service.scheduler who info)
  rw [← agreement] at deciding
  exact deciding

open Classical in
/-- A fixed admitted effective source profile has a consistent full effective
native completion. Free sites are optimal against every whole continuation;
completed compatible sites with nonnegative deposits are rational. Protected
sites keep the source decision and the same initialized history and sampled
settlement laws as exact first-turn play. -/
theorem exists_consistent_source_completion
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (utility : State L service.setup.program.terminalCtx → Player → ℝ)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) :
    let certificate := (effectiveMenu).bounded (initialLaw service.setup) service.horizon
      service.scheduler |>.wellFoundedHistories
    let base := baseUtility service.setup service.leaks utility
    let payoff := fun who (final : ((effectiveMenu).protocol (initialLaw service.setup)
      service.horizon service.scheduler).History) => TerminalAudit.utility base
        ((runtime service.setup).serviceAuditObservation service.leaks)
        (sourceServiceAudit service.setup service.leaks sample)
        (service.auditDeposit base probability) final.state who
    ∃ assessment : (effectiveModel).BehavioralAssessment,
      assessment.IsSequentiallyConsistent ((effectiveMenu).decisionInformationAntichain
        (initialLaw service.setup) service.horizon service.scheduler) ∧
      (∀ who (site : (effectiveModel).InformationSite who),
        service.sourceCompatibleInfo who site.1 →
        assessment.strategy who site.1 = service.effectiveImmediateComparator profile who site.1) ∧
      (∀ who (site : (effectiveModel).InformationSite who),
        ¬ service.sourceCompatibleInfo who site.1 →
        ∀ law : PMF ((effectiveModel).Choice who site.1),
          (assessment.continuationContext certificate site (payoff who)).value
              ((assessment.strategy who).withLaw site.1 law) ≤
            (assessment.continuationContext certificate site (payoff who)).value
              (assessment.strategy who)) ∧
      (∀ who (site : (effectiveModel).InformationSite who),
        ¬ service.sourceCompatibleInfo who site.1 →
          (assessment.continuationContext certificate site (payoff who)).IsLocallyOptimal
            Set.univ (assessment.strategy who)) ∧
      (∀ who (site : (effectiveModel).InformationSite who),
        0 ≤ service.auditDeposit base probability who →
        service.sourceCompatibleInfo who site.1 →
        ∀ past view, site.1 = some (past, view) →
          (∀ event, event ∈ view.application.publicView.observation.completionOrder) →
          (assessment.continuationContext certificate site (payoff who)).IsLocallyOptimal
            Set.univ (assessment.strategy who)) ∧
      (effectiveModel).runBehavioralTerminalFrom certificate assessment.strategy
          ((effectiveMenu).protocol (initialLaw service.setup) service.horizon
            service.scheduler).initHistory =
        (effectiveModel).runBehavioralTerminalFrom certificate
          (fun player => service.effectiveImmediateComparator profile player)
          ((effectiveMenu).protocol (initialLaw service.setup) service.horizon
            service.scheduler).initHistory ∧
      (PMF.bind ((effectiveModel).runBehavioralTerminalFrom certificate assessment.strategy
        ((effectiveMenu).protocol (initialLaw service.setup) service.horizon
          service.scheduler).initHistory)
          fun final =>
            (TerminalAudit.settlement base
              ((runtime service.setup).serviceAuditObservation service.leaks)
              (sourceServiceAudit service.setup service.leaks sample)
              (service.auditDeposit base probability) final.state).map fun payoffs =>
                (sourceReadout service.setup service.leaks final.state, payoffs)) =
        (service.setup.run profile).map (fun source => (some source, utility source)) := by
  classical
  intro certificate base payoff
  let fallback : ∀ who, (effectiveModel).Policy who := fun who info =>
    Classical.choice inferInstance
  let free : Finset ((effectiveModel).InformationAgent (effectiveModel).playedInformation) :=
    Finset.univ.filter fun agent => ¬ service.sourceCompatibleInfo agent.1 agent.2.1
  let reference : Profile ((effectiveModel).agentForm fallback certificate).sig.mixed :=
    fun agent =>
      (effectiveMenu).uniformPolicy (initialLaw service.setup) service.horizon
        service.scheduler agent.1 agent.2.1
  let timingProfile (n : Nat) : ∀ who, (effectiveModel).BehavioralPolicy who := fun who info =>
    ((menu).restrictPolicy (initialLaw service.setup) service.horizon service.scheduler who
      (sourceServiceTurnPolicy service.setup service.leaks service.bound service.horizon
        (geometricTiming service.setup service.horizon (completionWeight n)
          (completionWeight_positive n).le (completionWeight_small n).le) profile who) info).map
        ((service.bounds.riskMenu_in_effective (runtime service.setup) service.leaks
          service.bound).choice (initialLaw service.setup) service.horizon service.scheduler who
            info)
  let pinned (n : Nat) : Profile ((effectiveModel).agentForm fallback certificate).sig.mixed :=
    fun agent =>
      mix (completionWeight n) (completionWeight_positive n).le (completionWeight_small n).le
        (reference agent) (timingProfile n agent.1 agent.2.1)
  have referenceFull
      (agent : (effectiveModel).InformationAgent (effectiveModel).playedInformation) :
      FullSupport (reference agent) := by
    intro choice
    let := Fintype.ofFinite ((effectiveModel).Choice agent.1 agent.2.1)
    change choice ∈ (PMF.uniformOfFintype ((effectiveModel).Choice agent.1 agent.2.1)).support
    exact PMF.mem_support_uniformOfFintype (α := (effectiveModel).Choice agent.1 agent.2.1) choice
  have pinnedFull (n : Nat)
      (agent : (effectiveModel).InformationAgent (effectiveModel).playedInformation)
      (_kept : agent ∉ free) : FullSupport (pinned n agent) := by
    intro choice
    exact mem_support_mix_left _ _ _ (completionWeight_positive n) (referenceFull agent choice)
  have pinnedConverges (who : Player) (site : (effectiveModel).InformationSite who)
      (kept : (effectiveModel).agentAt site ∉ free) :
      PMFConvergesPointwise (fun n => pinned n ((effectiveModel).agentAt site))
        (service.effectiveImmediateComparator profile who site.1) := by
    have compatible : service.sourceCompatibleInfo who site.1 := by
      simpa only [free, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using kept
    have deciding := compatible_geometric_effective_limit service profile permitted who site.1
      compatible
    change PMFConvergesPointwise (fun n => timingProfile n who site.1)
      (service.effectiveImmediateComparator profile who site.1) at deciding
    apply pmfConvergesPointwise_iff_toReal.mpr
    intro choice
    change Tendsto (fun n => (mix (completionWeight n) (completionWeight_positive n).le
      (completionWeight_small n).le (reference ((effectiveModel).agentAt site))
        (timingProfile n who site.1) choice).toReal) atTop _
    simp only [mix_apply_toReal]
    have first := completionWeight_vanishes.mul_const
      ((reference ((effectiveModel).agentAt site) choice).toReal)
    have constant : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have second := (constant.sub completionWeight_vanishes).mul
      (deciding.toReal choice)
    convert first.add second using 1
    all_goals simp only [zero_mul, sub_zero, one_mul, zero_add]
    rfl
  have protectedPlay (elapsed : Nat)
      (history : ((effectiveMenu).protocol (initialLaw service.setup) service.horizon
        service.scheduler).History)
      (reached : history ∈ ((effectiveModel).runBehavioralFrom
        (fun player => service.effectiveImmediateComparator profile player) elapsed
          ((effectiveMenu).protocol (initialLaw service.setup) service.horizon
            service.scheduler).initHistory).support)
      (_running : ¬ ((effectiveMenu).protocol (initialLaw service.setup) service.horizon
        service.scheduler).terminal history.state)
      (who : Player) (site : (effectiveModel).InformationSite who)
      (observed : (effectiveModel).infoOf who history.trace = site.1) :
      (effectiveModel).agentAt site ∉ free := by
    have active := InformationModel.InformationSite.active (effectiveModel) site
      ⟨history, observed⟩
    have compatible := service.effectiveImmediateProfile_sourceCompatibleInfo service.horizon
      profile permitted effective elapsed history reached who active
    simpa only [free, Finset.mem_filter, Finset.mem_univ, true_and, not_not, observed] using
      compatible
  obtain ⟨assessment, consistent, agrees, freeOptimal, histories⟩ :=
    (effectiveModel).exists_consistent_prescribed_completion
      ((effectiveMenu).decisionRecall (initialLaw service.setup) service.horizon service.scheduler)
      fallback certificate payoff free pinned reference pinnedFull referenceFull completionWeight
      completionWeight_positive completionWeight_small completionWeight_vanishes
      (fun player => service.effectiveImmediateComparator profile player) pinnedConverges
      protectedPlay
  have initializedHistories :
      (effectiveModel).runBehavioralTerminalFrom certificate assessment.strategy
          ((effectiveMenu).protocol (initialLaw service.setup) service.horizon
            service.scheduler).initHistory =
        (effectiveModel).runBehavioralTerminalFrom certificate
          (fun player => service.effectiveImmediateComparator profile player)
          ((effectiveMenu).protocol (initialLaw service.setup) service.horizon
            service.scheduler).initHistory := histories
  refine ⟨assessment, consistent, ?_, ?_, ?_, ?_, initializedHistories, ?_⟩
  · intro who site compatible
    apply agrees who site
    simpa only [free, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using compatible
  · intro who site incompatible law
    apply freeOptimal who site _ law
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, incompatible⟩
  · intro who site incompatible
    apply service.sourceCompatibleInfo_free_optimal (effectiveMenu) assessment consistent
      certificate payoff _ who site incompatible
    intro player current currentFree law
    exact freeOptimal player current (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, currentFree⟩) law
  · intro who site nonnegative compatible past view observed completed
    have silence player earlier atView :
        (⟨none⟩ : (app).Action) ∈ (effectiveMenu).actions player earlier atView :=
      service.bounds.canonicalActions_effective (runtime service.setup) service.leaks
        player earlier atView
        (service.bounds.silence_canonical (runtime service.setup) service.leaks player
          earlier atView)
    apply service.sourceCompatibleInfo_completed_optimal (effectiveMenu) silence assessment
      consistent
      utility sample authentic (service.auditDeposit base probability) _ _ who site nonnegative
        compatible past view observed completed
    · intro player current currentCompatible currentPast currentView currentObserved currentComplete
      have agreement := agrees player current (by
        simpa only [free, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using
          currentCompatible)
      rw [agreement, currentObserved]
      exact service.sourceServiceImmediatePolicy_completed_profile (effectiveMenu) silence profile
        player currentPast currentView currentComplete
    · intro player current incompatible law
      exact freeOptimal player current (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, incompatible⟩) law
  · rw [initializedHistories]
    exact service.effectiveImmediateProfile_joint_law profile permitted effective utility
      sample authentic probability

end Vegas.AsyncServiceSpec
