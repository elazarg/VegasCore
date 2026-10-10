/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.IntendedPreservation
import Vegas.Game.RevealServicePayoffs
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # The audited outcome shared by the intended game and the runtime

Comparing the intended game with an audited runtime needs one outcome type and
one utility on it. The audited outcome is the typed terminal store, if any,
together with every player's collection probability
(`Vegas.SourceProgram.Setup.AuditedOutcome`). Its utility is the forfeited
utility of the store minus each player's collection probability times its
deposit (`Vegas.SourceProgram.Setup.auditedUtility`).

The intended game charges nobody (`Vegas.SourceProgram.Setup.intendedOutcome`),
and no reveal of it fails, so on every intended history the audited utility is
the intended payoff (`Vegas.SourceProgram.Setup.intended_auditedUtility`). Every
sequential equilibrium of the intended game is therefore sequentially rational
against the audited utility, at the intended game's horizon, and is the limit of
a fully mixed Bayes-consistent sequence
(`Vegas.SourceProgram.Setup.intended_auditedSource`). On the runtime side the
audited utility of the readout and the collection probabilities is the audited
terminal utility of the forfeited base payoff
(`Vegas.SourceProgram.Setup.auditedUtility_runtime`). A law equality on audited
outcomes with the intended law then rules out charges on the runtime's paths and
gives its joint law of store and settlement
(`GameTheory.Enforcement.TerminalAudit.clean_of_law_eq`).
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability GameTheory.Enforcement Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- The audited outcome: the typed terminal store, if any, and every player's
collection probability. -/
abbrev AuditedOutcome := Option (State L setup.program.terminalCtx) × (Player → ℝ)

/-- The utility of an audited outcome: the forfeited utility of the store, or
zero without one, minus each player's collection probability times its
deposit. -/
def auditedUtility {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (deposit : Player → ℝ) (outcome : setup.AuditedOutcome) (who : Player) : ℝ :=
  outcome.1.elim 0 (fun state => forfeitUtility setup.program forfeit utility
    (setup.parameterOutcome parameter state) who) - outcome.2 who * deposit who

/-- The intended game's audited outcome: its readout, charging nobody. -/
def intendedOutcome (history : setup.intendedProtocol.History) : setup.AuditedOutcome :=
  (setup.protocolReadout history.state, 0)

/-- On every history of the intended game the audited utility is the intended
payoff: nobody is charged and no reveal fails. -/
theorem intended_auditedUtility (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (deposit : Player → ℝ) (history : setup.intendedProtocol.History) (who : Player) :
    setup.auditedUtility parameter utility forfeit deposit (setup.intendedOutcome history) who =
      (setup.protocolReadout history.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who) := by
  unfold auditedUtility intendedOutcome
  simp only [Pi.zero_apply, zero_mul, sub_zero]
  cases read : setup.protocolReadout history.state with
  | none => rfl
  | some terminal =>
      have zero := setup.failedReveals_eq_zero_of_intendedState
        (setup.intendedState_trace wellFormed history.trace) who read
      simp only [Option.elim_some, forfeitUtility, parameterOutcome] at zero ⊢
      simp [zero]

/-- **The intended equilibrium as the source of the audited comparison.** Every
sequential equilibrium of the intended game of a well-formed setup is the
pointwise limit of fully mixed Bayes-consistent assessments, and is sequentially
rational against the audited utility of the intended outcome for play cut off at
the intended game's horizon, whatever the forfeit and the deposits. -/
theorem intended_auditedSource [Fintype Player] (wellFormed : setup.WellFormed)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (deposit : Player → ℝ) (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who))) :
    ∃ sequence : ℕ → setup.intendedModel.BehavioralAssessment,
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent setup.intendedModel
        (sequence n) setup.intended_decision_antichain) ∧
      InformationModel.BehavioralAssessmentConvergesPointwise sequence intended ∧
      intended.IsSequentiallyRationalFor (fun who site =>
        intended.truncatedContinuationContext site
          (fun history => setup.auditedUtility parameter utility forfeit deposit
            (setup.intendedOutcome history) who)
          (instructionCount setup.program + 1)) := by
  have truncated := (intended.isSequentialEquilibrium_iff_truncated_of_bounded setup.intendedModel
    setup.intended_decision_antichain setup.intended_bounded.wellFoundedHistories
    setup.intended_bounded _).mp equilibrium
  obtain ⟨sequence, regular, converges⟩ := truncated.2
  refine ⟨sequence, fun n => (regular n).1, fun n => (regular n).2, converges, ?_⟩
  intro who site
  have same : (fun history : setup.intendedProtocol.History =>
      setup.auditedUtility parameter utility forfeit deposit (setup.intendedOutcome history) who) =
      (fun final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)) :=
    funext fun history =>
      setup.intended_auditedUtility wellFormed parameter utility forfeit deposit history who
  beta_reduce
  rw [same]
  exact truncated.1 who site

/-- The finite history type of the intended game, for finite commitment payload
types and a finite initial law. -/
theorem intended_finite_history [Finite Player] (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] : Finite setup.intendedProtocol.History :=
  have : Finite (setup.executionProtocol (CommitmentInterface.values setup.program)).History :=
    setup.finite_history finite _
  Finite.of_injective (setup.intendedRestriction (CommitmentInterface.values
    setup.program)).history (setup.intendedRestriction (CommitmentInterface.values
    setup.program)).history.injective

/-- On the runtime, the audited utility of the readout and the collection
probabilities is the audited terminal utility of the forfeited base payoff. -/
theorem auditedUtility_runtime {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (deposit : Player → ℝ)
    (leaks : MessageNetwork.ObservationRule Player
      (EventGraphRuntime.WitnessedPacket (graph setup)))
    {Observation : Type} (observe : (application setup leaks).ProtocolState → Observation)
    (audit : Observation → PMF (Player → Bool))
    (state : (application setup leaks).ProtocolState) (who : Player) :
    setup.auditedUtility parameter utility forfeit deposit
        (sourceReadout setup leaks state,
          fun who => TerminalAudit.charge observe audit state who) who =
      TerminalAudit.utility (baseUtility setup leaks (fun terminal =>
          forfeitUtility setup.program forfeit utility (setup.parameterOutcome parameter terminal)))
        observe audit deposit state who :=
  rfl

end Vegas.SourceProgram.Setup
