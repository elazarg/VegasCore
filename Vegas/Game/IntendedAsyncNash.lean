/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.IntendedNash
import Vegas.Game.AsyncServiceNash

/-! # Approximate Nash equilibria of the intended game under a contract builder

Composing Nash preservation for the intended game
(`Vegas.SourceProgram.Setup.intended_isεNash_preserved`) with the forward
transfer to turn-counted clients
(`Vegas.AsyncServiceSpec.isεNash_clientProfile_of_firstTurn_bounds`) and their
honest execution (`Vegas.sourceServiceClients_settlement_lawError`), at the
forfeited utility: if every native policy against the first-turn clients is
bounded by a source deviation, the turn-counted clients of every source profile
extending an `ε`-Nash equilibrium of the intended game are an
`(ε + 2 * δ * R)`-Nash equilibrium of every admitting response menu, and their
joint law of typed outcome and realized settlement is within `δ` of the
intended joint law of terminal store and payoff.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace AsyncServiceSpec

variable (service : AsyncServiceSpec Player L)

/-- **Intended approximate Nash equilibria under a contract builder, from the
first-turn bound.** For a well-formed setup and a forfeit no smaller than the
payoff range, if every native policy of one player against the first-turn
clients is bounded in audited expected payoff by a source deviation, the
turn-counted clients of a source profile extending an `ε`-Nash equilibrium of
the intended game are an `(ε + 2 * δ * R)`-Nash equilibrium of every admitting
response menu under the forfeit pass, and their joint law of typed outcome and
realized settlement is within `δ` in total variation of the intended joint law
of terminal store and payoff. -/
theorem intended_clientProfile_isεNash_of_firstTurn_bounds {Parameter : Type}
    (wellFormed : service.setup.WellFormed)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (forfeit : ℝ) (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (menu : (serviceApplication service.setup service.mode service.deadline
      service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (covered : ∀ (source : Profile (service.sourceModel (CommitmentInterface.values
      service.setup.program)).behavioralSignature) who,
      menu.Admissible (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler who
        (serviceClientPolicy service.setup service.mode service.deadline service.leaks
          service.bound turns timing
          (sourceServiceClientProfile service.setup (service.setup.decodeBehavioralProfile
            (CommitmentInterface.values service.setup.program) source)) who))
    (low : Player → ℝ) (spread : ℝ)
    (within : ∀ who (output : Option (State L service.setup.program.terminalCtx))
      (charged : Bool),
      low who ≤ output.elim 0 (fun state => forfeitUtility service.setup.program forfeit utility
          (service.setup.parameterOutcome parameter state) who) -
            (if charged then deposit who else 0) ∧
        output.elim 0 (fun state => forfeitUtility service.setup.program forfeit utility
          (service.setup.parameterOutcome parameter state) who) -
            (if charged then deposit who else 0) ≤ low who + spread)
    (intended : Profile service.setup.intendedModel.behavioralSignature)
    (source : Profile (service.sourceModel (CommitmentInterface.values
      service.setup.program)).behavioralSignature)
    (agrees : (service.setup.intendedRestriction (CommitmentInterface.values
      service.setup.program)).ExtendsProfile intended source)
    (terminal : FirstTurnSourceLaw service.setup service.mode service.deadline service.leaks
      service.horizon service.scheduler service.bound turns
      (sourceServiceClientProfile service.setup (service.setup.decodeBehavioralProfile
        (CommitmentInterface.values service.setup.program) source))) (ε : ℝ)
    (equilibrium : IsεNash (service.setup.intendedModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
      (fun final who => (service.setup.protocolReadout final.state).elim 0
        (fun state => utility (service.setup.parameterOutcome parameter state) who)) ε
      intended) :
    let forfeited := forfeitUtility service.setup.program forfeit utility
    let base := serviceBaseUtility service.setup service.mode service.deadline service.leaks
      (fun state => forfeited (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit
    let settle := TerminalAudit.settlement base
      ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit
    let clients := sourceServiceClientProfile service.setup
      (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
        source)
    (∀ who (alternative : (serviceApplication service.setup service.mode service.deadline
      service.leaks).Policy),
      ∃ deviation : (service.sourceModel (CommitmentInterface.values
        service.setup.program)).BehavioralPolicy who,
        expect (((serviceApplication service.setup service.mode service.deadline
          service.leaks).roundsFrom (serviceInitialLaw service.setup service.mode)
            service.scheduler (deviatedTurnProfile service.bound turns
              (firstTurnTiming service.setup turns service.mode) clients who alternative)
            service.horizon).map (serviceApplication service.setup service.mode service.deadline
              service.leaks).finished)
          (fun final => payoff final who) ≤
        expect ((service.sourceModel (CommitmentInterface.values
          service.setup.program)).runBehavioral (Profile.update source who deviation)
          (instructionCount service.setup.program + 1))
          (fun final => (service.setup.protocolReadout final.state).elim 0
            (fun state => forfeited (service.setup.parameterOutcome parameter state) who))) →
    IsεNash ((menu.information (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who)
        (ε + 2 * (∑ event, timing.deferral event) * spread)
        (service.clientProfile (CommitmentInterface.values service.setup.program) menu timing
          source) ∧
      PMF.WithinTV (∑ event, timing.deferral event)
        (((menu.information (serviceInitialLaw service.setup service.mode) service.horizon
          service.scheduler).runBehavioral (service.clientProfile (CommitmentInterface.values
            service.setup.program) menu timing source)
            (2 * service.horizon + 1)).bind (fun final =>
              (settle final.state).map fun payoffs =>
                (serviceSourceReadout service.setup service.mode service.deadline service.leaks
                  final.state, payoffs)))
        ((service.setup.intendedModel.runBehavioral intended
            (instructionCount service.setup.program + 1)).map
          (fun final => (service.setup.protocolReadout final.state,
            fun who => (service.setup.protocolReadout final.state).elim 0
              (fun state => utility (service.setup.parameterOutcome parameter state) who)))) := by
  intro forfeited base payoff settle clients firstTurn
  obtain ⟨sourceNash, _, sourceLaw⟩ := service.setup.intended_isεNash_preserved
    (sourceService_finiteBindingTypes service.setup service.bounds service.values)
    wellFormed parameter utility forfeit range intended source agrees ε equilibrium
  refine ⟨service.isεNash_clientProfile_of_firstTurn_bounds (CommitmentInterface.values
    service.setup.program) parameter forfeited
    sample authentic
    deposit menu timing covered low spread within ε source terminal firstTurn sourceNash, ?_⟩
  let decoded := service.setup.decodeBehavioralProfile
    (CommitmentInterface.values service.setup.program) source
  let stateUtility := fun state : State L service.setup.program.terminalCtx =>
    forfeited (service.setup.parameterOutcome parameter state)
  have close := sourceServiceClients_clientPolicy_settlement_lawError service.contract
    service.timely timing decoded terminal menu (covered source) sample authentic stateUtility
    deposit
  have readoutLaw : ((service.sourceModel (CommitmentInterface.values
    service.setup.program)).runBehavioral source
      (instructionCount service.setup.program + 1)).map
        (fun final => service.setup.protocolReadout final.state) =
      (service.setup.run decoded).map some :=
    service.setup.runBehavioralFrom_readout (CommitmentInterface.values service.setup.program)
      source (instructionCount service.setup.program + 1)
      (service.setup.executionProtocol
        (CommitmentInterface.values service.setup.program)).initHistory
      (Nat.le_refl _)
  have sourceJoint : (service.setup.run decoded).map (fun state => (some state,
      stateUtility state)) =
      ((service.sourceModel (CommitmentInterface.values service.setup.program)).runBehavioral
        source (instructionCount service.setup.program + 1)).map
        (fun final => (service.setup.protocolReadout final.state,
          fun who => (service.setup.protocolReadout final.state).elim 0
            (fun state => forfeited (service.setup.parameterOutcome parameter state) who))) := by
    have mapped := congrArg (PMF.map fun output :
        Option (State L service.setup.program.terminalCtx) =>
      (output, fun who => output.elim 0
        (fun state => forfeited (service.setup.parameterOutcome parameter state) who)))
      readoutLaw
    simp only [PMF.map_comp] at mapped
    exact mapped.symm
  rw [sourceJoint, sourceLaw] at close
  exact close

end AsyncServiceSpec

end Vegas
