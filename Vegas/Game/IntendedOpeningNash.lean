/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncOpeningDeviationBound
import Vegas.Game.IntendedAsyncNash
import Vegas.Game.IntendedOpeningExtension

/-! # Approximate Nash equilibria of the intended game for opening clients

Every service graph is reveal-relaxed (`Vegas.serviceGraph_revealRelaxedOrdered`);
under concurrent reveals a run of disclosures completes concurrently. A
client of the intended game opens each of its disclosures from its own stored
commitment, whatever else is pending: it never waits for, or reads, another
owner's opening. Its source policy discloses at every reveal, and its first-turn
clients open exactly their effective disclosures
(`Vegas.AsyncServiceSpec.openingClients_opensEffectively`).

Their honest runs have the source outcome law
(`Vegas.openingFirstTurn_readout_law`), and every native deviation against them
is bounded by a source deviation, a withheld disclosure being a forfeit
(`Vegas.AsyncServiceSpec.openingFirstTurn_deviation_bound`). With Nash
preservation for the intended game, the turn-counted clients of a disclosing
source profile extending an `ε`-Nash equilibrium of the intended game are an
`(ε + 2 * δ * R)`-Nash equilibrium of every admitting response menu, with the
intended joint law of outcome and settlement within `δ`
(`Vegas.AsyncServiceSpec.intended_openingClientProfile_isεNash`).
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

omit [Fintype Player] in
/-- The clients of a source profile that discloses at every reveal open
exactly their effective disclosures. -/
theorem openingClients_opensEffectively
    (source : Profile (service.sourceModel (CommitmentInterface.values
      service.setup.program)).behavioralSignature)
    (disclosing : ∀ player, Disclosing service.setup.program
      (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
        source player)) (player : Player) :
    (sourceServiceClientProfile service.setup
      (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
        source) player).OpensEffectively service.setup.program []
          (Revelations.initial service.setup.context) := by
  have opening := openingProfile_opensEffectively service.setup.program []
    (Revelations.initial service.setup.context)
    (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
      source) player
  rwa [openingProfile_eq_of_disclosing _ _ _ _ disclosing] at opening

/-- **Intended approximate Nash equilibria for opening clients.** In every
dependency mode of the service graph, concurrent reveals included, for a
well-formed setup, with a forfeit no smaller than the
payoff range, for every authentic audit and every nonnegative deposit, the
turn-counted clients of a source profile that discloses at every reveal and
extends an `ε`-Nash equilibrium of the intended game are an
`(ε + 2 * δ * R)`-Nash equilibrium of every admitting response menu under the
forfeit pass, and their joint law of typed outcome and realized settlement is
within `δ` in total variation of the intended joint law of terminal store and
payoff. -/
theorem intended_openingClientProfile_isεNash {Parameter : Type}
    (wellFormed : service.setup.WellFormed)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (forfeit : ℝ) (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    (menu : (serviceApplication service.setup service.mode service.deadline
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
    (disclosing : ∀ player, Disclosing service.setup.program
      (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
        source player)) (ε : ℝ)
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
              (fun state => utility (service.setup.parameterOutcome parameter state) who)))) :=
  service.intended_clientProfile_isεNash_of_firstTurn_bounds wellFormed parameter utility
    forfeit range sample authentic deposit menu timing covered low spread within intended source
    agrees
    (openingFirstTurn_readout_law service.setup service.leaks
      (serviceGraph_revealRelaxedOrdered service.setup service.mode) service.contract
      service.timely turns _ (service.openingClients_opensEffectively source disclosing)) ε
    equilibrium (fun who alternative => service.openingFirstTurn_deviation_bound
      (serviceGraph_revealRelaxedOrdered service.setup service.mode) wellFormed parameter utility
      forfeit range sample deposit nonnegative intended source agrees
      (service.openingClients_opensEffectively source disclosing) who alternative)

/-- **Intended approximate Nash equilibria for opening clients, existentially.**
Every `ε`-Nash equilibrium of the intended game extends to a source profile
that discloses at every reveal (`Vegas.SourceProgram.Setup.openingExtension`),
and the turn-counted clients of that extension are an `(ε + 2 * δ * R)`-Nash
equilibrium of every admitting response menu, in every dependency mode, with
the intended joint law of outcome and settlement within `δ`. -/
theorem intended_openingExtension_isεNash {Parameter : Type}
    (wellFormed : service.setup.WellFormed)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (forfeit : ℝ) (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    (menu : (serviceApplication service.setup service.mode service.deadline
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
    (ε : ℝ)
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
    ∃ source : Profile (service.sourceModel (CommitmentInterface.values
      service.setup.program)).behavioralSignature,
      (service.setup.intendedRestriction (CommitmentInterface.values
        service.setup.program)).ExtendsProfile intended source ∧
      (∀ player, Disclosing service.setup.program
        (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
          source player)) ∧
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
                (fun state => utility (service.setup.parameterOutcome parameter state) who)))) :=
  ⟨service.setup.openingExtension intended, service.setup.openingExtension_extends intended,
    service.setup.openingExtension_disclosing intended,
    service.intended_openingClientProfile_isεNash wellFormed parameter utility forfeit range
      sample authentic deposit nonnegative menu timing covered low spread within intended
      (service.setup.openingExtension intended) (service.setup.openingExtension_extends intended)
      (service.setup.openingExtension_disclosing intended) ε equilibrium⟩

end AsyncServiceSpec

end Vegas
