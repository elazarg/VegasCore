/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCompilation
import Vegas.Game.IntendedPreservation
import Vegas.Game.IntendedServiceCompilation
import Vegas.Game.SourceServiceNash
import Vegas.Game.AsyncServiceNash
import Vegas.Game.IntendedServiceNash
import Vegas.Game.IntendedAsyncNash

/-! # Checked sequential-equilibrium preservation, Nash correspondence and termination -/

noncomputable section

namespace Vegas.Paper

open GameTheory Vegas Interaction
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

open Vegas.SourceProgram Vegas.EventGraphRuntime
  GameTheory.Protocol GameTheory.Enforcement in
/-- Every original sequential equilibrium of a source program whose
commitment payload types are finite has a sequential equilibrium of the audited
bounded raw runtime with the source joint law of the typed terminal state and
payoff, the payoff realized as settlement. The audit charges no player on any
history the native equilibrium reaches. The authentic partial audit and
positive conditional coverage are explicit service assumptions. -/
theorem source_audited_raw_sequential_equilibrium [Fintype Player] [IExpr.ResultTypes L]
    {Parameter : Type} (service : SourceServiceSpec Player L)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup) →
      PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) (positive : ∀ who, 0 < probability who)
    (coverage : ∀ who actual record, record ∈ actual → record.2.sender = who →
      record.1.permits record.2 = false →
      probability who ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (source : service.sourceModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibrium
      (service.setup.decision_antichain (CommitmentInterface.values service.setup.program))
      service.sourceTerminates
      (fun who final => (service.setup.protocolReadout final.state).elim 0
        (fun state => utility (service.setup.parameterOutcome parameter state) who))) :
    let raw := service.bounds.rawMenu (runtime service.setup) service.leaks
    let base := baseUtility service.setup service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit service.setup service.leaks service.bounds service.rosters
      service.network base (fun owner => min (probability owner) 1)
    let payoff := TerminalAudit.utility base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    let settle := TerminalAudit.settlement base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    ∃ target : (raw.information (initialLaw service.setup) service.planLength
        service.scheduler).BehavioralAssessment,
      target.IsSequentialEquilibrium
        (raw.decisionInformationAntichain (initialLaw service.setup) service.planLength
          service.scheduler) service.rawTerminates
        (fun who history => payoff history.state who) ∧
      (∀ final ∈ ((raw.information (initialLaw service.setup) service.planLength
          service.scheduler).runBehavioralTerminalFrom service.rawTerminates target.strategy
            service.rawInitial).support, ∀ who,
        TerminalAudit.charge ((runtime service.setup).serviceAuditObservation service.leaks)
          (sourceServiceAudit service.setup service.leaks sample) final.state who = 0) ∧
      ((raw.information (initialLaw service.setup) service.planLength
          service.scheduler).runBehavioralTerminalFrom service.rawTerminates target.strategy
            service.rawInitial).bind
          (fun final => (settle final.state).map (fun payoffs =>
            (sourceReadout service.setup service.leaks final.state, payoffs))) =
        (service.sourceModel.runBehavioralTerminalFrom service.sourceTerminates source.strategy
            service.sourceInitial).map
              (fun final => (service.setup.protocolReadout final.state,
                fun who => (service.setup.protocolReadout final.state).elim 0
                  (fun state => utility (service.setup.parameterOutcome parameter state)
                    who))) :=
  service.audited_raw_sequentialEquilibrium_preserved parameter utility sample authentic
    probability positive coverage source equilibrium

/-- info: 'Vegas.Paper.source_audited_raw_sequential_equilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_audited_raw_sequential_equilibrium

open Vegas.SourceProgram in
/-- Every history of the source protocol ends within its instruction bound; this
certifies the terminal play in `source_audited_raw_sequential_equilibrium`. -/
theorem source_protocol_horizon [IExpr.ResultTypes L]
    (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) :
    (setup.executionProtocol admission).BoundedHorizon (instructionCount setup.program + 1) :=
  setup.protocol_bounded admission

/-- info: 'Vegas.Paper.source_protocol_horizon' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_protocol_horizon

open Vegas.EventGraphRuntime in
/-- Every history of the bounded raw runtime ends within its fuel; this certifies
the native terminal play in `source_audited_raw_sequential_equilibrium`. -/
theorem raw_service_horizon [Fintype Player] [IExpr.ResultTypes L]
    (service : SourceServiceSpec Player L) :
    ((service.bounds.rawMenu (runtime service.setup) service.leaks).protocol
      (initialLaw service.setup) service.planLength service.scheduler).BoundedHorizon
        service.fuel :=
  (service.bounds.rawMenu (runtime service.setup) service.leaks).bounded _ _ _

/-- info: 'Vegas.Paper.raw_service_horizon' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.raw_service_horizon

/-- info: 'Vegas.SourceServiceSpec.completeAudit_raw_sequentialEquilibrium_preserved'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceServiceSpec.completeAudit_raw_sequentialEquilibrium_preserved

open Vegas.SourceProgram GameTheory.Protocol in
/-- **Intended-game preservation.** The intended game of a setup offers, at an
owner's commit, only the values its guard is predicted to accept from the
owner's observation, and at an owner's reveal only opening. For a well-formed
setup (every guard satisfiable at every commit the intended game reaches, and
values in every initial commitment cell) with finite commitment payload types
and a finite initial law, every sequential equilibrium of the intended game has
a sequential equilibrium of the source game under the forfeit pass, which
charges the owner of every failed reveal a forfeit no smaller than the payoff
range. Its joint law of typed terminal state and payoff is the intended one,
and no reveal fails on any history it reaches. -/
theorem intended_sequential_equilibrium [Fintype Player] [IExpr.ResultTypes L]
    (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (forfeit : ℝ) (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who))) :
    ∃ target : (setup.informationModel
        (CommitmentInterface.values setup.program)).BehavioralAssessment,
      target.IsSequentialEquilibrium (setup.decision_antichain _)
        (setup.protocol_bounded _).wellFoundedHistories
        (fun who final => (setup.protocolReadout final.state).elim 0
          (fun state => forfeitUtility setup.program forfeit utility
            (setup.parameterOutcome parameter state) who)) ∧
      (∀ final ∈ ((setup.informationModel
          (CommitmentInterface.values setup.program)).runBehavioralTerminalFrom
            (setup.protocol_bounded _).wellFoundedHistories target.strategy
            (setup.executionProtocol
              (CommitmentInterface.values setup.program)).initHistory).support,
        ∀ terminal, setup.protocolReadout final.state = some terminal →
          ∀ who, failedReveals setup.program who (publicOutcome setup.program terminal) = 0) ∧
      ((setup.informationModel
          (CommitmentInterface.values setup.program)).runBehavioralTerminalFrom
            (setup.protocol_bounded _).wellFoundedHistories target.strategy
            (setup.executionProtocol
              (CommitmentInterface.values setup.program)).initHistory).map
          (fun final => (setup.protocolReadout final.state,
            fun who => (setup.protocolReadout final.state).elim 0
              (fun state => forfeitUtility setup.program forfeit utility
                (setup.parameterOutcome parameter state) who))) =
        (setup.intendedModel.runBehavioralTerminalFrom setup.intended_bounded.wellFoundedHistories
            intended.strategy setup.intendedProtocol.initHistory).map
          (fun final => (setup.protocolReadout final.state,
            fun who => (setup.protocolReadout final.state).elim 0
              (fun state => utility (setup.parameterOutcome parameter state) who))) :=
  setup.intended_sequentialEquilibrium_preserved finite wellFormed parameter utility forfeit
    range _ _ intended equilibrium

/-- info: 'Vegas.Paper.intended_sequential_equilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_sequential_equilibrium

/-- info: 'Vegas.SourceServiceSpec.intended_audited_raw_sequentialEquilibrium' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceServiceSpec.intended_audited_raw_sequentialEquilibrium

open Vegas.SourceProgram Vegas.EventGraphRuntime
  GameTheory.Protocol GameTheory.Enforcement in
/-- **Reflection of approximate Nash on the calendar ledger.** If the compiled
raw profile of a source profile is an `ε`-Nash equilibrium of the audited
bounded raw runtime, then the source profile is an `ε`-Nash equilibrium of the
source protocol model, with the same `ε`. The compiled profile plays each
player's source policy on the roster calendar with timing weight one half and
gives it canonical raw response names (`Vegas.SourceServiceSpec.compileProfile`). -/
theorem source_audited_raw_nash_reflection [Fintype Player] [IExpr.ResultTypes L]
    {Parameter : Type} (service : SourceServiceSpec Player L)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup) →
      PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) (ε : ℝ)
    (source : Profile service.sourceModel.behavioralSignature) :
    let raw := service.bounds.rawMenu (runtime service.setup) service.leaks
    let base := baseUtility service.setup service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit service.setup service.leaks service.bounds service.rosters
      service.network base (fun owner => min (probability owner) 1)
    let payoff := TerminalAudit.utility base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    IsεNash ((raw.information (initialLaw service.setup) service.planLength
        service.scheduler).toBehavioralGameForm service.fuel)
        (fun history who => payoff history.state who) ε (service.compileProfile source) →
      IsεNash (service.sourceModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        ε source :=
  service.isεNash_of_compileProfile parameter utility sample authentic probability ε source

/-- info: 'Vegas.Paper.source_audited_raw_nash_reflection' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_audited_raw_nash_reflection

open Vegas.SourceProgram Vegas.EventGraphRuntime
  GameTheory.Protocol GameTheory.Enforcement in
/-- **Approximate Nash correspondence on the calendar ledger.** Under the
service assumptions of `source_audited_raw_sequential_equilibrium` (an authentic
partial audit with positive conditional coverage, and the deposit sized from
the base utility and that coverage), the compiled raw profile of a source
profile is an `ε`-Nash equilibrium of the audited bounded raw runtime if and
only if the source profile is an `ε`-Nash equilibrium of the source protocol
model, for every `ε`. The forward direction rests on the fact that every
deviation in the permitted menu has the typed outcome law of a source deviation
(`Vegas.SourceServiceSpec.exists_source_deviation_law`). -/
theorem source_audited_raw_nash_iff [Fintype Player] [IExpr.ResultTypes L]
    {Parameter : Type} (service : SourceServiceSpec Player L)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup) →
      PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) (positive : ∀ who, 0 < probability who)
    (coverage : ∀ who actual record, record ∈ actual → record.2.sender = who →
      record.1.permits record.2 = false →
      probability who ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (ε : ℝ) (source : Profile service.sourceModel.behavioralSignature) :
    let raw := service.bounds.rawMenu (runtime service.setup) service.leaks
    let base := baseUtility service.setup service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit service.setup service.leaks service.bounds service.rosters
      service.network base (fun owner => min (probability owner) 1)
    let payoff := TerminalAudit.utility base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    IsεNash ((raw.information (initialLaw service.setup) service.planLength
        service.scheduler).toBehavioralGameForm service.fuel)
        (fun history who => payoff history.state who) ε (service.compileProfile source) ↔
      IsεNash (service.sourceModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        ε source :=
  service.isεNash_compileProfile_iff parameter utility sample authentic probability positive
    coverage ε source

/-- info: 'Vegas.Paper.source_audited_raw_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_audited_raw_nash_iff

/-- info: 'Vegas.SourceServiceSpec.exists_source_deviation_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceServiceSpec.exists_source_deviation_law

open Vegas.SourceProgram Vegas.EventGraphRuntime
  GameTheory.Protocol GameTheory.Enforcement in
/-- **Reflection of approximate Nash under an arbitrary contract builder.**
For a full-source service whose public scheduler satisfies the asynchronous
contract, if the turn-counted clients of a source profile are an `ε`-Nash
equilibrium of a response menu that admits every profile's clients, for the
audited payoff with any deposit, then the source profile is an
`(ε + 2 * δ * R)`-Nash equilibrium of the source protocol model. Here `δ` is
the total deferral weight of the turn timing and every realized payoff value,
charged or not, lies in an interval of length `R`. -/
theorem async_client_nash_reflection [Fintype Player] [IExpr.ResultTypes L]
    {Parameter : Type} (service : AsyncServiceSpec Player L)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup) →
      PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (menu : (application service.setup service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns)
    (covered : ∀ (source : Profile service.sourceModel.behavioralSignature) who,
      menu.Admissible (initialLaw service.setup) service.horizon service.scheduler who
        (sourceServiceTurnPolicy service.setup service.leaks service.bound turns timing
          (sourceServiceClientProfile service.setup (service.setup.decodeBehavioralProfile
            (CommitmentInterface.values service.setup.program) source)) who))
    (low : Player → ℝ) (range : ℝ)
    (within : ∀ who (output : Option (State L service.setup.program.terminalCtx))
      (charged : Bool),
      low who ≤ output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter
          state) who) - (if charged then deposit who else 0) ∧
        output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter
          state) who) - (if charged then deposit who else 0) ≤ low who + range)
    (ε : ℝ) (source : Profile service.sourceModel.behavioralSignature) :
    let base := baseUtility service.setup service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    IsεNash ((menu.information (initialLaw service.setup) service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who) ε
        (service.clientProfile menu timing source) →
      IsεNash (service.sourceModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        (ε + 2 * (∑ event, timing.deferral event) * range) source :=
  service.isεNash_of_clientProfile parameter utility sample authentic deposit menu timing covered
    low range within ε source

/-- info: 'Vegas.Paper.async_client_nash_reflection' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.async_client_nash_reflection

open Vegas.SourceProgram GameTheory.Protocol in
/-- **Approximate Nash preservation for the intended game.** For a well-formed
setup with finite commitment payload types and a finite initial law, and a
forfeit no smaller than the payoff range, every profile of the source game that
plays an `ε`-Nash equilibrium of the intended game at the intended information
values is an `ε`-Nash equilibrium of the source game under the forfeit pass,
with the same `ε`. Its joint law of typed terminal state and payoff is the
intended one, and no reveal fails on any history it reaches. -/
theorem intended_nash [Fintype Player] [IExpr.ResultTypes L]
    (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (forfeit : ℝ) (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile
      (setup.informationModel (CommitmentInterface.values setup.program)).behavioralSignature)
    (agrees : setup.intendedRestriction.ExtendsProfile intended target) (ε : ℝ)
    (equilibrium : IsεNash (setup.intendedModel.toBehavioralGameForm
        (instructionCount setup.program + 1))
      (fun final who => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)) ε intended) :
    IsεNash ((setup.informationModel
        (CommitmentInterface.values setup.program)).toBehavioralGameForm
          (instructionCount setup.program + 1))
      (fun final who => (setup.protocolReadout final.state).elim 0
        (fun state => forfeitUtility setup.program forfeit utility
          (setup.parameterOutcome parameter state) who)) ε target ∧
    (∀ final ∈ ((setup.informationModel (CommitmentInterface.values setup.program)).runBehavioral
        target (instructionCount setup.program + 1)).support,
      ∀ terminal, setup.protocolReadout final.state = some terminal →
        ∀ who, failedReveals setup.program who (publicOutcome setup.program terminal) = 0) ∧
    ((setup.informationModel (CommitmentInterface.values setup.program)).runBehavioral
        target (instructionCount setup.program + 1)).map
        (fun final => (setup.protocolReadout final.state,
          fun who => (setup.protocolReadout final.state).elim 0
            (fun state => forfeitUtility setup.program forfeit utility
              (setup.parameterOutcome parameter state) who))) =
      (setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
        (fun final => (setup.protocolReadout final.state,
          fun who => (setup.protocolReadout final.state).elim 0
            (fun state => utility (setup.parameterOutcome parameter state) who))) :=
  setup.intended_isεNash_preserved finite wellFormed parameter utility forfeit range intended
    target agrees ε equilibrium

/-- info: 'Vegas.Paper.intended_nash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_nash

open Vegas.SourceProgram Vegas.EventGraphRuntime
  GameTheory.Protocol GameTheory.Enforcement in
/-- **Intended approximate Nash equilibria on the calendar ledger.** Under the
service assumptions of `source_audited_raw_nash_iff`, for a well-formed setup
and a forfeit no smaller than the payoff range, the compiled raw profile of
every source profile that extends an `ε`-Nash equilibrium of the intended game
is an `ε`-Nash equilibrium of the audited bounded raw runtime under the forfeit
pass, with the same `ε`, and its joint law of typed outcome and audited payoff
vector is the intended joint law of terminal store and payoff. The deposit is
sized from the forfeited utility. -/
theorem intended_audited_raw_nash [Fintype Player] [IExpr.ResultTypes L]
    {Parameter : Type} (service : SourceServiceSpec Player L)
    (wellFormed : service.setup.WellFormed)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (forfeit : ℝ) (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (sample : List (SettledEvidence service.setup) →
      PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) (positive : ∀ who, 0 < probability who)
    (coverage : ∀ who actual record, record ∈ actual → record.2.sender = who →
      record.1.permits record.2 = false →
      probability who ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (intended : Profile service.setup.intendedModel.behavioralSignature)
    (source : Profile service.sourceModel.behavioralSignature)
    (agrees : service.setup.intendedRestriction.ExtendsProfile intended source) (ε : ℝ)
    (equilibrium : IsεNash (service.setup.intendedModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
      (fun final who => (service.setup.protocolReadout final.state).elim 0
        (fun state => utility (service.setup.parameterOutcome parameter state) who)) ε intended) :
    let forfeited := forfeitUtility service.setup.program forfeit utility
    let raw := service.bounds.rawMenu (runtime service.setup) service.leaks
    let base := baseUtility service.setup service.leaks
      (fun state => forfeited (service.setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit service.setup service.leaks service.bounds service.rosters
      service.network base (fun owner => min (probability owner) 1)
    let payoff := TerminalAudit.utility base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    IsεNash ((raw.information (initialLaw service.setup) service.planLength
        service.scheduler).toBehavioralGameForm service.fuel)
        (fun history who => payoff history.state who) ε (service.compileProfile source) ∧
      ((raw.information (initialLaw service.setup) service.planLength
          service.scheduler).runBehavioral (service.compileProfile source) service.fuel).map
          (fun final => (sourceReadout service.setup service.leaks final.state,
            payoff final.state)) =
        (service.setup.intendedModel.runBehavioral intended
            (instructionCount service.setup.program + 1)).map
          (fun final => (service.setup.protocolReadout final.state,
            fun who => (service.setup.protocolReadout final.state).elim 0
              (fun state => utility (service.setup.parameterOutcome parameter state) who))) :=
  service.intended_audited_raw_isεNash wellFormed parameter utility forfeit range sample
    authentic probability positive coverage intended source agrees ε equilibrium

/-- info: 'Vegas.Paper.intended_audited_raw_nash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_audited_raw_nash

/-- info: 'Vegas.sourceServiceTurnPolicy_deviation_roundsFrom_bind_within' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.sourceServiceTurnPolicy_deviation_roundsFrom_bind_within

/-- info: 'Vegas.AsyncServiceSpec.isεNash_clientProfile_of_firstTurn_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.isεNash_clientProfile_of_firstTurn_bounds

/-- info: 'Vegas.AsyncServiceSpec.intended_clientProfile_isεNash_of_firstTurn_bounds' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.intended_clientProfile_isεNash_of_firstTurn_bounds

/-- info: 'GameTheory.Protocol.InformationModel.ActionRestriction.isεNash_extends_of_debt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.ActionRestriction.isεNash_extends_of_debt

end Vegas.Paper

