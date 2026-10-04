/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceDeposit
import Vegas.Game.SourceServiceFirstTurnCompletes
import Vegas.Game.SourceServiceFirstTurnAudit
import Vegas.Game.SourceServiceSiteBridge
import Vegas.Source.InitialState
import Vegas.Source.DisclosureBehavioral

/-! # Joint initialized outcome and settlement under asynchronous first-turn play

Exact first-turn play has the source's complete typed terminal law under any
asynchronous service contract. Authentic evidence sampling collects no charge
on its supported executions, so the same terminal audit draw gives precisely
the source outcome and the entire realized base-payoff vector jointly.

Initial private parameters remain correlated with public outcomes. Disclosure
normalization extends the initialized-law statement to every source profile.
These are execution and actual settlement laws, not equilibrium comparisons.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability GameTheory.Enforcement
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Finite Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The physical initialized first-turn execution preserves the complete typed
source law. A native missing readout consequently has probability zero. -/
theorem sourceServiceFirstTurn_initialized_readout {horizon turns : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context)) :
    (((application setup leaks).roundsFrom (initialLaw setup) scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      horizon).map fun final => sourceReadout setup leaks
        ((application setup leaks).finished final)) = (setup.run profile).map some := by
  let app := application setup leaks
  let players := sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
    profile
  have within := sourceServiceTurnPolicy_boundaryContinuationWithin
    (sourceServiceTurnPolicy_firstTurnCompletes contract timely (firstTurnTiming setup turns)
      profile effective)
  have law := BoundaryContinuationWithin.law setup leaks within (fun _ =>
    Finset.sum_eq_zero fun _ _ => firstTurnTiming_deferral setup turns _)
  rw [← initialLaw_bind_sourceContinuation setup profile]
  change ((initialLaw setup).bind fun state =>
    app.runRounds scheduler players horizon (ReactiveApplication.Execution.initial app state)).map
      (fun final => sourceReadout setup leaks (app.finished final)) = _
  rw [PMF.map_bind]
  apply bind_congr_on_support _
  intro state supported
  have exactLaw := law 0 (ReactiveApplication.Execution.initial app state)
    (initial_completionBoundary setup leaks scheduler players state supported) (Nat.zero_le _)
  simpa only [ReactiveApplication.runToHorizon, ReactiveApplication.Execution.initial,
    List.length_nil, Nat.sub_zero, sourceContinuation] using exactLaw

/-- The typed source outcome and all realized audited payoffs are preserved
jointly. The audit sample may correlate players' verdicts in any way. -/
theorem sourceServiceFirstTurn_initialized_settlement {horizon turns : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) :
    (((application setup leaks).roundsFrom (initialLaw setup) scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      horizon).bind fun final =>
        (TerminalAudit.settlement (baseUtility setup leaks utility)
          ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
          deposit ((application setup leaks).finished final)).map fun payoffs =>
            (sourceReadout setup leaks ((application setup leaks).finished final), payoffs)) =
      (setup.run profile).map (fun source => (some source, utility source)) := by
  let app := application setup leaks
  let players := sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
    profile
  let law := app.roundsFrom (initialLaw setup) scheduler players horizon
  have clean (final : app.Execution) (reached : final ∈ law.support) :
      TerminalAudit.settlement (baseUtility setup leaks utility)
        ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
        deposit (app.finished final) = PMF.pure (baseUtility setup leaks utility
          (app.finished final)) := by
    have length := app.roundsFrom_recall (initialLaw setup) scheduler players horizon final reached
    have supported : app.RoundSupported (initialLaw setup) horizon scheduler players
        (app.finished final) := by
      change final.environmentRecall.length + 0 = horizon ∧
        final ∈ (app.roundsFrom (initialLaw setup) scheduler players
          final.environmentRecall.length).support
      rw [length]
      exact ⟨Nat.add_zero _, reached⟩
    exact sourceServiceFirstTurn_settlement contract timely players turns profile (fun _ => rfl)
      sample authentic (baseUtility setup leaks utility) deposit (app.finished final) supported
  calc
    _ = law.map (fun final => (sourceReadout setup leaks (app.finished final),
        baseUtility setup leaks utility (app.finished final))) := by
      rw [← PMF.bind_pure_comp]
      apply bind_congr_on_support _
      intro final reached
      rw [clean final reached, PMF.pure_map]
      rfl
    _ = ((setup.run profile).map some).map (fun outcome =>
        (outcome, fun who => outcome.elim 0 (fun source => utility source who))) := by
      rw [← sourceServiceFirstTurn_initialized_readout (turns := turns) contract timely profile
        effective, PMF.map_comp]
      rfl
    _ = _ := by rw [PMF.map_comp]; rfl

namespace AsyncServiceSpec

variable [Fintype Player] (service : AsyncServiceSpec Player L)

/-- The general service's initialized execution preserves the full typed
outcome and actual sampled settlement vector. Its deposit is fixed beforehand. -/
theorem firstTurn_joint_law (turns : Nat)
    (profile : BehavioralProfile service.setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (utility : State L service.setup.program.terminalCtx → Player → ℝ)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) :
    (((application service.setup service.leaks).roundsFrom (initialLaw service.setup)
      service.scheduler (sourceServiceTurnPolicy service.setup service.leaks service.bound turns
        (firstTurnTiming service.setup turns) profile) service.horizon).bind fun final =>
          (TerminalAudit.settlement (baseUtility service.setup service.leaks utility)
            ((runtime service.setup).serviceAuditObservation service.leaks)
            (sourceServiceAudit service.setup service.leaks sample)
            (service.auditDeposit (baseUtility service.setup service.leaks utility) probability)
            ((application service.setup service.leaks).finished final)).map fun payoffs =>
              (sourceReadout service.setup service.leaks
                ((application service.setup service.leaks).finished final), payoffs)) =
      (service.setup.run profile).map (fun source => (some source, utility source)) :=
  sourceServiceFirstTurn_initialized_settlement service.contract service.timely profile effective
    utility sample authentic _

/-- Recover initial parameters and public results from the same terminal
state, retaining their joint law with the complete realized payoff vector. -/
theorem firstTurn_parameter_joint_law {Parameter : Type} (turns : Nat)
    (profile : BehavioralProfile service.setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) :
    let base := baseUtility service.setup service.leaks
      (fun source => utility (service.setup.parameterOutcome parameter source))
    (((application service.setup service.leaks).roundsFrom (initialLaw service.setup)
      service.scheduler (sourceServiceTurnPolicy service.setup service.leaks service.bound turns
        (firstTurnTiming service.setup turns) profile) service.horizon).bind fun final =>
          (TerminalAudit.settlement base
            ((runtime service.setup).serviceAuditObservation service.leaks)
            (sourceServiceAudit service.setup service.leaks sample)
            (service.auditDeposit base probability)
            ((application service.setup service.leaks).finished final)).map fun payoffs =>
              ((sourceReadout service.setup service.leaks
                ((application service.setup service.leaks).finished final)).map
                  (service.setup.parameterOutcome parameter), payoffs)) =
      (service.setup.parameterRun parameter profile).map
        (fun outcome => (some outcome, utility outcome)) := by
  intro base
  have joint := congrArg (PMF.map (fun pair =>
    (pair.1.map (service.setup.parameterOutcome parameter), pair.2)))
      (service.firstTurn_joint_law turns profile effective
        (fun source => utility (service.setup.parameterOutcome parameter source)) sample authentic
          probability)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Option.map_some] at joint
  rw [← service.setup.run_map_parameterOutcome parameter profile, PMF.map_comp]
  exact joint

/-- Every source profile has the same initialized outcome and actual joint
settlement law after its effective disclosure normalization is compiled. -/
theorem normalizedFirstTurn_joint_law (turns : Nat)
    (profile : BehavioralProfile service.setup.program)
    (utility : State L service.setup.program.terminalCtx → Player → ℝ)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) :
    let normalized := normalizeDisclosureProfile service.setup.program []
      (Revelations.initial service.setup.context) profile
    (((application service.setup service.leaks).roundsFrom (initialLaw service.setup)
      service.scheduler (sourceServiceTurnPolicy service.setup service.leaks service.bound turns
        (firstTurnTiming service.setup turns) normalized) service.horizon).bind fun final =>
          (TerminalAudit.settlement (baseUtility service.setup service.leaks utility)
            ((runtime service.setup).serviceAuditObservation service.leaks)
            (sourceServiceAudit service.setup service.leaks sample)
            (service.auditDeposit (baseUtility service.setup service.leaks utility) probability)
            ((application service.setup service.leaks).finished final)).map fun payoffs =>
              (sourceReadout service.setup service.leaks
                ((application service.setup service.leaks).finished final), payoffs)) =
      (service.setup.run profile).map (fun source => (some source, utility source)) := by
  intro normalized
  have effective (who : Player) : (normalized who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context) :=
    (profile who).normalizeDisclosureFrom_effective service.setup.program []
      (Revelations.initial service.setup.context) _
  have same : service.setup.run normalized = service.setup.run profile := by
    unfold Setup.run
    apply bind_congr_on_support _
    intro initial _
    exact normalizeDisclosureProfile_runFrom service.setup.program profile
      (service.setup.initialConfig initial)
  rw [← same]
  exact service.firstTurn_joint_law turns normalized effective utility sample authentic probability

end AsyncServiceSpec

end Vegas
