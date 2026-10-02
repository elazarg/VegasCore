/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceFirstTurnLaw
import Vegas.Game.SourceServiceFirstTurnSafe
import Vegas.Game.SourceServiceRiskPolicy
import Interaction.ReactiveSupportedMenuPolicy

/-! # Initialized first-turn play in the finite risk-menu game

The exact first-turn physical policy has a total behavioral representation in
the finite risk menu. At every supported initialized control, its owner risk
is clear and the actual prescribed response is admitted. Coverage at risky or
inconsistent counterfactual inputs is unnecessary for the initialized law.

The represented profile preserves the typed source outcome jointly with the
actual sampled terminal settlement vector. This is an execution bridge, not
a sequential-rationality or belief-transport result.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

/-- The finite information model retains the owner's complete actual recall
and current view. Its total fallback is irrelevant on initialized support. -/
def firstTurnProfile (turns : Nat) (profile : BehavioralProfile service.setup.program) :
    ∀ who,
      ((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).information
        (initialLaw service.setup) service.horizon service.scheduler).BehavioralPolicy who :=
  fun who =>
    (service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).restrictPolicy
      (initialLaw service.setup) service.horizon service.scheduler who
      (sourceServiceTurnPolicy service.setup service.leaks service.bound turns
        (firstTurnTiming service.setup turns) profile who)

/-- Only coverage on the original physical initialized support is required.
The supplied history is legal in the actual finite risk menu. -/
theorem firstTurnProfile_response_covered (turns : Nat)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (who : Player) (control : (application service.setup service.leaks).Control)
    (trace : ((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).protocol
      (initialLaw service.setup) service.horizon service.scheduler).Trace (some control))
    (actual : (application service.setup service.leaks).RoundSupported (initialLaw service.setup)
      service.horizon service.scheduler
      (sourceServiceTurnPolicy service.setup service.leaks service.bound turns
        (firstTurnTiming service.setup turns) profile) (some control))
    (response : (application service.setup service.leaks).Action)
    (chosen : response ∈ (sourceServiceTurnPolicy service.setup service.leaks service.bound turns
      (firstTurnTiming service.setup turns) profile who (control.execution.recall who)
        (control.execution.observe (application service.setup service.leaks) who)).support) :
    response ∈ (service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).actions
      who (control.execution.recall who)
        (control.execution.observe (application service.setup service.leaks) who) := by
  have clear := sourceServiceFirstTurn_serviceRisk_clear_roundSupported service.contract
    service.timely _ who turns profile rfl control actual
  exact sourceServiceTurnPolicy_risk_retained service.bounds service.values service.initialValues
    service.capacity service.bound turns (firstTurnTiming service.setup turns) profile who
      (permitted who) control trace clear response chosen

/-- Every finite initialized behavioral prefix has the actual complete
control law. This also covers pending activations before their responses. -/
theorem firstTurnProfile_initialized_controlSteps (turns : Nat)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program)) (fuel : Nat) :
    let menu := service.bounds.riskMenu (runtime service.setup) service.leaks service.bound
    let initial := initialLaw service.setup
    ((menu.information initial service.horizon service.scheduler).runBehavioral
      (service.firstTurnProfile turns profile) fuel).map History.state =
      (fun law => law.bind ((application service.setup service.leaks).controlStep initial
        service.horizon service.scheduler (sourceServiceTurnPolicy service.setup service.leaks
          service.bound turns (firstTurnTiming service.setup turns) profile)))^[fuel]
            (PMF.pure none) := by
  intro menu initial
  exact menu.run_restrict_supported_controlSteps initial service.horizon service.scheduler
    (sourceServiceTurnPolicy service.setup service.leaks service.bound turns
      (firstTurnTiming service.setup turns) profile)
    (fun who control trace actual _ response chosen =>
      service.firstTurnProfile_response_covered turns profile permitted who control trace actual
        response chosen) fuel

/-- An actual initialized behavioral prefix is supported by the original
physical evaluator, including a pending owner activation. -/
theorem firstTurnProfile_initialized_roundSupported (turns : Nat)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program)) (fuel : Nat)
    (history :
      ((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).protocol
        (initialLaw service.setup) service.horizon service.scheduler).History)
    (reached : history ∈
      (((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).information
        (initialLaw service.setup) service.horizon service.scheduler).runBehavioral
          (service.firstTurnProfile turns profile) fuel).support) :
    (application service.setup service.leaks).RoundSupported (initialLaw service.setup)
      service.horizon service.scheduler (sourceServiceTurnPolicy service.setup service.leaks
        service.bound turns (firstTurnTiming service.setup turns) profile) history.state := by
  have physical : history.state ∈
      ((((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).information
        (initialLaw service.setup) service.horizon service.scheduler).runBehavioral
          (service.firstTurnProfile turns profile) fuel).map History.state).support :=
    PMF.support_map .. ▸ ⟨history, reached, rfl⟩
  rw [service.firstTurnProfile_initialized_controlSteps turns profile permitted fuel] at physical
  exact (application service.setup service.leaks).roundSupported_iterate_controlStep
    (initialLaw service.setup) service.horizon service.scheduler _ fuel history.state physical

/-- The finite behavioral representation has the exact physical terminal
control law, including all network state, receipts and private recall. -/
theorem firstTurnProfile_initialized_control_law (turns : Nat)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program)) :
    let menu := service.bounds.riskMenu (runtime service.setup) service.leaks service.bound
    let initial := initialLaw service.setup
    let certificate := (menu.bounded initial service.horizon service.scheduler).wellFoundedHistories
    ((menu.information initial service.horizon service.scheduler).runBehavioralTerminalFrom
      certificate (service.firstTurnProfile turns profile)
        (menu.protocol initial service.horizon service.scheduler).initHistory).map History.state =
      ((application service.setup service.leaks).roundsFrom initial service.scheduler
        (sourceServiceTurnPolicy service.setup service.leaks service.bound turns
          (firstTurnTiming service.setup turns) profile) service.horizon).map
            (application service.setup service.leaks).finished := by
  intro menu initial certificate
  have represented := menu.terminal_restrict_supported_finish initial service.horizon
    service.scheduler (sourceServiceTurnPolicy service.setup service.leaks service.bound turns
      (firstTurnTiming service.setup turns) profile)
    (fun who control trace actual _ response chosen =>
      service.firstTurnProfile_response_covered turns profile permitted who control trace actual
        response chosen) certificate
  change ((menu.information initial service.horizon service.scheduler).runBehavioralTerminalFrom
    certificate (fun who => menu.restrictPolicy initial service.horizon service.scheduler who
      (sourceServiceTurnPolicy service.setup service.leaks service.bound turns
        (firstTurnTiming service.setup turns) profile who))
    (menu.protocol initial service.horizon service.scheduler).initHistory).map History.state = _
  rw [represented]
  simp only [ReactiveApplication.finish, ReactiveApplication.roundsFrom, PMF.map_bind]

/-- The represented initialized strategy preserves the complete typed source
terminal law. This statement does not assert sequential equilibrium. -/
theorem firstTurnProfile_initialized_readout (turns : Nat)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context)) :
    let menu := service.bounds.riskMenu (runtime service.setup) service.leaks service.bound
    let initial := initialLaw service.setup
    let certificate := (menu.bounded initial service.horizon service.scheduler).wellFoundedHistories
    ((menu.information initial service.horizon service.scheduler).runBehavioralTerminalFrom
      certificate (service.firstTurnProfile turns profile)
        (menu.protocol initial service.horizon service.scheduler).initHistory).map
          (fun final => sourceReadout service.setup service.leaks final.state) =
      (service.setup.run profile).map some := by
  intro menu initial certificate
  have states := congrArg (PMF.map (sourceReadout service.setup service.leaks))
    (service.firstTurnProfile_initialized_control_law turns profile permitted)
  simp only [PMF.map_comp, Function.comp_def] at states
  exact states.trans (sourceServiceFirstTurn_initialized_readout service.contract service.timely
    profile effective)

/-- One actual terminal audit draw preserves the source outcome and the entire
realized payoff vector jointly in the finite risk-menu behavioral game. -/
theorem firstTurnProfile_joint_law (turns : Nat)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (utility : State L service.setup.program.terminalCtx → Player → ℝ)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) :
    let menu := service.bounds.riskMenu (runtime service.setup) service.leaks service.bound
    let initial := initialLaw service.setup
    let certificate := (menu.bounded initial service.horizon service.scheduler).wellFoundedHistories
    (((menu.information initial service.horizon service.scheduler).runBehavioralTerminalFrom
      certificate (service.firstTurnProfile turns profile)
        (menu.protocol initial service.horizon service.scheduler).initHistory).bind fun final =>
          (TerminalAudit.settlement (baseUtility service.setup service.leaks utility)
            ((runtime service.setup).serviceAuditObservation service.leaks)
            (sourceServiceAudit service.setup service.leaks sample)
            (service.auditDeposit (baseUtility service.setup service.leaks utility) probability)
            final.state).map fun payoffs =>
              (sourceReadout service.setup service.leaks final.state, payoffs)) =
      (service.setup.run profile).map (fun source => (some source, utility source)) := by
  intro menu initial certificate
  have states := congrArg (fun law => law.bind fun final =>
    (TerminalAudit.settlement (baseUtility service.setup service.leaks utility)
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample)
      (service.auditDeposit (baseUtility service.setup service.leaks utility) probability)
      final).map fun payoffs => (sourceReadout service.setup service.leaks final, payoffs))
        (service.firstTurnProfile_initialized_control_law turns profile permitted)
  simp only [PMF.bind_map] at states
  exact states.trans (service.firstTurn_joint_law turns profile effective utility sample authentic
    probability)

/-- Initial parameters, public outcomes and the actual settlement vector use
the same terminal draw; no independent parameter resampling is introduced. -/
theorem firstTurnProfile_parameter_joint_law {Parameter : Type} (turns : Nat)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) :
    let menu := service.bounds.riskMenu (runtime service.setup) service.leaks service.bound
    let initial := initialLaw service.setup
    let certificate := (menu.bounded initial service.horizon service.scheduler).wellFoundedHistories
    let base := baseUtility service.setup service.leaks
      (fun source => utility (service.setup.parameterOutcome parameter source))
    (((menu.information initial service.horizon service.scheduler).runBehavioralTerminalFrom
      certificate (service.firstTurnProfile turns profile)
        (menu.protocol initial service.horizon service.scheduler).initHistory).bind fun final =>
          (TerminalAudit.settlement base
            ((runtime service.setup).serviceAuditObservation service.leaks)
            (sourceServiceAudit service.setup service.leaks sample)
            (service.auditDeposit base probability) final.state).map fun payoffs =>
              ((sourceReadout service.setup service.leaks final.state).map
                (service.setup.parameterOutcome parameter), payoffs)) =
      (service.setup.parameterRun parameter profile).map
        (fun outcome => (some outcome, utility outcome)) := by
  intro menu initial certificate base
  have joint := congrArg (PMF.map (fun pair =>
    (pair.1.map (service.setup.parameterOutcome parameter), pair.2)))
      (service.firstTurnProfile_joint_law turns profile permitted effective
        (fun source => utility (service.setup.parameterOutcome parameter source)) sample authentic
          probability)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Option.map_some] at joint
  rw [← service.setup.run_map_parameterOutcome parameter profile, PMF.map_comp]
  exact joint

/-- Every value-admitted source profile preserves its initialized joint law
when its effective disclosure normalization is represented behaviorally. -/
theorem normalizedFirstTurnProfile_joint_law (turns : Nat)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (utility : State L service.setup.program.terminalCtx → Player → ℝ)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) :
    let menu := service.bounds.riskMenu (runtime service.setup) service.leaks service.bound
    let initial := initialLaw service.setup
    let certificate := (menu.bounded initial service.horizon service.scheduler).wellFoundedHistories
    let normalized := normalizeDisclosureProfile service.setup.program []
      (Revelations.initial service.setup.context) profile
    (((menu.information initial service.horizon service.scheduler).runBehavioralTerminalFrom
      certificate (service.firstTurnProfile turns normalized)
        (menu.protocol initial service.horizon service.scheduler).initHistory).bind fun final =>
          (TerminalAudit.settlement (baseUtility service.setup service.leaks utility)
            ((runtime service.setup).serviceAuditObservation service.leaks)
            (sourceServiceAudit service.setup service.leaks sample)
            (service.auditDeposit (baseUtility service.setup service.leaks utility) probability)
            final.state).map fun payoffs =>
              (sourceReadout service.setup service.leaks final.state, payoffs)) =
      (service.setup.run profile).map (fun source => (some source, utility source)) := by
  intro menu initial certificate normalized
  have states := congrArg (fun law => law.bind fun final =>
    (TerminalAudit.settlement (baseUtility service.setup service.leaks utility)
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample)
      (service.auditDeposit (baseUtility service.setup service.leaks utility) probability)
      final).map fun payoffs => (sourceReadout service.setup service.leaks final, payoffs))
        (service.firstTurnProfile_initialized_control_law turns normalized
          (normalized_sourceService_admitted service.setup profile permitted))
  simp only [PMF.bind_map] at states
  exact states.trans (service.normalizedFirstTurn_joint_law turns profile utility sample authentic
    probability)

/-- The normalized representation preserves each initial parameter/public
outcome together with the actual entire settlement vector. -/
theorem normalizedFirstTurnProfile_parameter_joint_law {Parameter : Type} (turns : Nat)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) :
    let menu := service.bounds.riskMenu (runtime service.setup) service.leaks service.bound
    let initial := initialLaw service.setup
    let certificate := (menu.bounded initial service.horizon service.scheduler).wellFoundedHistories
    let normalized := normalizeDisclosureProfile service.setup.program []
      (Revelations.initial service.setup.context) profile
    let base := baseUtility service.setup service.leaks
      (fun source => utility (service.setup.parameterOutcome parameter source))
    (((menu.information initial service.horizon service.scheduler).runBehavioralTerminalFrom
      certificate (service.firstTurnProfile turns normalized)
        (menu.protocol initial service.horizon service.scheduler).initHistory).bind fun final =>
          (TerminalAudit.settlement base
            ((runtime service.setup).serviceAuditObservation service.leaks)
            (sourceServiceAudit service.setup service.leaks sample)
            (service.auditDeposit base probability) final.state).map fun payoffs =>
              ((sourceReadout service.setup service.leaks final.state).map
                (service.setup.parameterOutcome parameter), payoffs)) =
      (service.setup.parameterRun parameter profile).map
        (fun outcome => (some outcome, utility outcome)) := by
  intro menu initial certificate normalized base
  have joint := congrArg (PMF.map (fun pair =>
    (pair.1.map (service.setup.parameterOutcome parameter), pair.2)))
      (service.normalizedFirstTurnProfile_joint_law turns profile permitted
        (fun source => utility (service.setup.parameterOutcome parameter source)) sample authentic
          probability)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Option.map_some] at joint
  rw [← service.setup.run_map_parameterOutcome parameter profile, PMF.map_comp]
  exact joint

end Vegas.AsyncServiceSpec
