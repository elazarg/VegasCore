/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.IntendedNash
import Vegas.Game.SourceServiceTurnSettlement
import Vegas.Game.AsyncServiceNash

/-! # Approximate Nash equilibria of the intended game under a contract builder

Composing Nash preservation for the intended game
(`Vegas.SourceProgram.Setup.intended_forfeit_isεNash_preserved`) with the forward
transfer to turn-counted clients
(`Vegas.AsyncServiceSpec.isεBestResponse_clientProfile_of_firstTurn_bounds`) and their
honest execution (`Vegas.sourceServiceClients_clientPolicy_settlement_lawError`), at the
forfeited utility: if every native policy against the first-turn clients is
bounded by a source deviation, the turn-counted clients of every source profile
extending an `ε`-Nash equilibrium of the intended game are an
`(ε + 2 * δ * R)`-Nash equilibrium of every admitting response menu, and their
joint law of typed outcome and realized settlement is within `δ` of the
intended joint law of typed cells, public default history and payoff.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Finite Player]
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
of terminal store and payoff. The supplied reader replaces the service readout. -/
theorem intended_clientProfile_isεNash_of_firstTurn_bounds_readout {Parameter : Type}
    (reader : (serviceApplication service.setup service.mode service.duration
      service.leaks).ProtocolState → Option (Config Player L service.setup.program.terminalCtx))
    (wellFormed : service.setup.WellFormed)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (forfeit : ℝ)
    (range : service.setup.TerminalPayoffSpread (CommitmentInterface.values
      service.setup.program) parameter utility forfeit)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (menu : (serviceApplication service.setup service.mode service.duration
      service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (covered : ∀ (source : Profile (service.sourceModel (CommitmentInterface.values
      service.setup.program)).behavioralSignature) who,
      menu.Admissible (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler who
        (serviceClientPolicy service.setup service.mode service.duration service.leaks
          service.bound turns timing
          (normalizeDisclosureProfile service.setup.program (service.setup.decodeBehavioralProfile
            (CommitmentInterface.values service.setup.program) source)) who))
    (low : Player → ℝ) (spread : ℝ)
    (within : service.ReadoutSettlementRange reader parameter
      (forfeitUtility service.setup.program forfeit utility) sample deposit low (fun _ => spread))
    (intended : Profile service.setup.intendedModel.behavioralSignature)
    (source : Profile (service.sourceModel (CommitmentInterface.values
      service.setup.program)).behavioralSignature)
    (agrees : (service.setup.intendedRestriction (CommitmentInterface.values
      service.setup.program)).ExtendsProfile intended source)
    (terminal : FirstTurnReadoutLaw service.setup service.mode service.duration service.leaks reader
      service.horizon service.scheduler service.bound turns
      (normalizeDisclosureProfile service.setup.program (service.setup.decodeBehavioralProfile
        (CommitmentInterface.values service.setup.program) source))) (ε : ℝ)
    (equilibrium : IsεNash (service.setup.intendedModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
      (fun final who => (service.setup.protocolReadout final.state).elim 0
        (fun state => utility (service.setup.parameterOutcome parameter state) who)) ε
      intended) :
    let forfeited := forfeitUtility service.setup.program forfeit utility
    let base := readoutBaseUtility reader
      (fun state => forfeited (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) deposit
    let settle := TerminalAudit.settlement base
      ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) deposit
    let clients := normalizeDisclosureProfile service.setup.program
      (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
        source)
    (∀ who (alternative : (serviceApplication service.setup service.mode service.duration
      service.leaks).Policy),
      ∃ deviation : (service.sourceModel (CommitmentInterface.values
        service.setup.program)).BehavioralPolicy who,
        expect (((serviceApplication service.setup service.mode service.duration
          service.leaks).roundsFrom (serviceInitialLaw service.setup service.mode)
            service.scheduler (deviatedTurnProfile service.bound turns
              (firstTurnTiming service.setup turns service.mode) clients who alternative)
            service.horizon).map (serviceApplication service.setup service.mode service.duration
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
        (ε + 2 * timing.deferralError * spread)
        (service.clientProfile (CommitmentInterface.values service.setup.program) menu timing
          source) ∧
      PMF.WithinTV timing.deferralError
        (((menu.information (serviceInitialLaw service.setup service.mode) service.horizon
          service.scheduler).runBehavioral (service.clientProfile (CommitmentInterface.values
            service.setup.program) menu timing source)
            (2 * service.horizon + 1)).bind (fun final =>
              (settle final.state).map fun payoffs =>
                (
                  (reader
                    final.state).map (fun config => (config.state, config.defaults)), payoffs)))
        ((service.setup.intendedModel.runBehavioral intended
            (instructionCount service.setup.program + 1)).map
          (fun final => ((service.setup.protocolReadout final.state).map
              (fun config => (config.state, config.defaults)),
            fun who => (service.setup.protocolReadout final.state).elim 0
              (fun state => utility (service.setup.parameterOutcome parameter state) who)))) := by
  let : Fintype Player := Fintype.ofFinite Player
  intro forfeited base payoff settle clients firstTurn
  obtain ⟨sourceNash, _, sourceLaw⟩ := service.setup.intended_forfeit_isεNash_preserved
    (CommitmentInterface.values service.setup.program)
    (sourceService_finiteBindingTypes service.setup service.bounds service.values)
    wellFormed parameter utility forfeit range intended source agrees ε equilibrium
  refine ⟨(isεNash_iff_εBestResponse _ _).mpr
    (service.isεBestResponse_clientProfile_of_firstTurn_bounds_readout (CommitmentInterface.values
      service.setup.program) reader parameter forfeited sample authentic deposit menu timing
        covered low
      (fun _ => spread) within ε source terminal firstTurn sourceNash), ?_⟩
  let decoded := service.setup.decodeBehavioralProfile
    (CommitmentInterface.values service.setup.program) source
  let pairUtility := fun result : State L service.setup.program.terminalCtx ×
      DefaultHistory Player =>
    forfeited (parameter (initialState service.setup.program result.1),
      ⟨sourcePublicEnv result.1, result.2⟩)
  have close := sourceServiceClients_clientPolicy_settlement_lawError_readout reader
    service.contract
    timing decoded terminal menu (covered source) sample authentic pairUtility
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
  have sourceJoint : (service.setup.run decoded).map (fun config =>
      (some (config.state, config.defaults), pairUtility (config.state, config.defaults))) =
      ((service.sourceModel (CommitmentInterface.values service.setup.program)).runBehavioral
        source (instructionCount service.setup.program + 1)).map
        (fun final => ((service.setup.protocolReadout final.state).map
          (fun config => (config.state, config.defaults)),
          fun who => (service.setup.protocolReadout final.state).elim 0
            (fun config => forfeited (service.setup.parameterOutcome parameter config) who))) := by
    have mapped := congrArg (PMF.map fun output :
        Option (Config Player L service.setup.program.terminalCtx) =>
      (output.map (fun config => (config.state, config.defaults)), fun who => output.elim 0
        (fun config => forfeited (service.setup.parameterOutcome parameter config) who))) readoutLaw
    simpa only [PMF.map_comp, Function.comp_def, Option.map_some, Option.elim_some,
      pairUtility, Setup.parameterOutcome, publicOutcome] using mapped.symm
  have projectedLaw := congrArg (PMF.map fun outcome =>
    (outcome.1.map (fun config => (config.state, config.defaults)), outcome.2)) sourceLaw
  simp only [PMF.map_comp, Function.comp_def] at projectedLaw
  rw [sourceJoint, projectedLaw] at close
  exact close

/-- The service-reader instance of `intended_clientProfile_isεNash_of_firstTurn_bounds_readout`. -/
theorem intended_clientProfile_isεNash_of_firstTurn_bounds {Parameter : Type}
    (wellFormed : service.setup.WellFormed)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (forfeit : ℝ)
    (range : service.setup.TerminalPayoffSpread (CommitmentInterface.values
      service.setup.program) parameter utility forfeit)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (menu : (serviceApplication service.setup service.mode service.duration
      service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (covered : ∀ (source : Profile (service.sourceModel (CommitmentInterface.values
      service.setup.program)).behavioralSignature) who,
      menu.Admissible (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler who
        (serviceClientPolicy service.setup service.mode service.duration service.leaks
          service.bound turns timing
          (normalizeDisclosureProfile service.setup.program (service.setup.decodeBehavioralProfile
            (CommitmentInterface.values service.setup.program) source)) who))
    (low : Player → ℝ) (spread : ℝ)
    (within : service.SettlementRange parameter
      (forfeitUtility service.setup.program forfeit utility) sample deposit low (fun _ => spread))
    (intended : Profile service.setup.intendedModel.behavioralSignature)
    (source : Profile (service.sourceModel (CommitmentInterface.values
      service.setup.program)).behavioralSignature)
    (agrees : (service.setup.intendedRestriction (CommitmentInterface.values
      service.setup.program)).ExtendsProfile intended source)
    (terminal : FirstTurnSourceLaw service.setup service.mode service.duration service.leaks
      service.horizon service.scheduler service.bound turns
      (normalizeDisclosureProfile service.setup.program (service.setup.decodeBehavioralProfile
        (CommitmentInterface.values service.setup.program) source))) (ε : ℝ)
    (equilibrium : IsεNash (service.setup.intendedModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
      (fun final who => (service.setup.protocolReadout final.state).elim 0
        (fun state => utility (service.setup.parameterOutcome parameter state) who)) ε
      intended) :
    let forfeited := forfeitUtility service.setup.program forfeit utility
    let base := serviceBaseUtility service.setup service.mode service.duration service.leaks
      (fun state => forfeited (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) deposit
    let settle := TerminalAudit.settlement base
      ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) deposit
    let clients := normalizeDisclosureProfile service.setup.program
      (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
        source)
    (∀ who (alternative : (serviceApplication service.setup service.mode service.duration
      service.leaks).Policy),
      ∃ deviation : (service.sourceModel (CommitmentInterface.values
        service.setup.program)).BehavioralPolicy who,
        expect (((serviceApplication service.setup service.mode service.duration
          service.leaks).roundsFrom (serviceInitialLaw service.setup service.mode)
            service.scheduler (deviatedTurnProfile service.bound turns
              (firstTurnTiming service.setup turns service.mode) clients who alternative)
            service.horizon).map (serviceApplication service.setup service.mode service.duration
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
        (ε + 2 * timing.deferralError * spread)
        (service.clientProfile (CommitmentInterface.values service.setup.program) menu timing
          source) ∧
      PMF.WithinTV timing.deferralError
        (((menu.information (serviceInitialLaw service.setup service.mode) service.horizon
          service.scheduler).runBehavioral (service.clientProfile (CommitmentInterface.values
            service.setup.program) menu timing source)
            (2 * service.horizon + 1)).bind (fun final =>
              (settle final.state).map fun payoffs =>
                (
                  (serviceSourceReadout service.setup service.mode service.duration service.leaks
                    final.state).map (fun config => (config.state, config.defaults)), payoffs)))
        ((service.setup.intendedModel.runBehavioral intended
            (instructionCount service.setup.program + 1)).map
          (fun final => ((service.setup.protocolReadout final.state).map
              (fun config => (config.state, config.defaults)),
            fun who => (service.setup.protocolReadout final.state).elim 0
              (fun state => utility (service.setup.parameterOutcome parameter state) who)))) :=
  service.intended_clientProfile_isεNash_of_firstTurn_bounds_readout
    (serviceSourceReadout service.setup service.mode service.duration service.leaks)
    wellFormed parameter utility forfeit range sample authentic deposit menu timing covered low
    spread within intended source agrees terminal ε equilibrium

end AsyncServiceSpec

end Vegas
