/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCompilation
import Vegas.Game.IntendedPreservation
import Vegas.Game.IntendedServiceCompilation
import Vegas.Game.SourceServiceNash
import Vegas.Game.AsyncServiceNash
import Vegas.Game.IntendedServiceNash
import Vegas.Game.IntendedAsyncNash
import Vegas.Game.IntendedOpeningNash
import Vegas.Game.AsyncServiceDeviationBound
import Vegas.Game.AsyncServiceRawNash
import Vegas.Game.EventCompilation
import Vegas.EventGraph.RevealRelaxedScheduling
import Vegas.Examples.LateLeak.Preservation

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
charged or not, lies in an interval of length `R`.
The service graph is barrier ordered, as in the sequential and the
concurrent-binding dependency modes (`Vegas.serviceGraph_barrierOrdered`), with
any configured deadlines. -/
theorem async_client_nash_reflection [Fintype Player] [IExpr.ResultTypes L]
    {Parameter : Type} (service : AsyncServiceSpec Player L)
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (menu : (serviceApplication service.setup service.mode service.deadline
      service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (covered : ∀ (source : Profile service.sourceModel.behavioralSignature) who,
      menu.Admissible (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler who
        (serviceClientPolicy service.setup service.mode service.deadline service.leaks
          service.bound turns timing
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
    let base := serviceBaseUtility service.setup service.mode service.deadline service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit
    IsεNash ((menu.information (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who) ε
        (service.clientProfile menu timing source) →
      IsεNash (service.sourceModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        (ε + 2 * (∑ event, timing.deferral event) * range) source :=
  service.isεNash_of_clientProfile ordered parameter utility sample authentic deposit menu
    timing covered
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

open Vegas.SourceProgram Vegas.EventGraphRuntime
  GameTheory.Protocol GameTheory.Enforcement in
/-- **Approximate Nash correspondence on the bounded raw ledger, for every
contract builder.** For a full-source service whose public scheduler satisfies
the asynchronous contract, for every authentic audit and every nonnegative
deposit: if a source profile is an `ε`-Nash equilibrium of the source protocol
model, its turn-counted clients are an `(ε + 2 * δ * R)`-Nash equilibrium of the
audited bounded raw ledger; conversely, if the clients are an `ε`-Nash
equilibrium there, the source profile is an `(ε + 2 * δ * R)`-Nash equilibrium.
Here `δ` is the total deferral weight of the turn timing and every realized
payoff value, charged or not, lies in an interval of length `R`. Each client
completes its turn-counted policy by silence after its own off-policy
responses, which changes no execution law; the bounded raw menu admits these
clients (`Vegas.sourceServiceClientPolicy_raw_admissible`). The forward
direction rests on the fact that every native policy of one player against the
first-turn clients has the typed outcome law of a source deviation whose
bindings may fail (`Vegas.asyncDeviation_readout_law`).
The service graph is barrier ordered, as in the sequential and the
concurrent-binding dependency modes (`Vegas.serviceGraph_barrierOrdered`), with
any configured deadlines. -/
theorem async_client_nash_correspondence [Fintype Player] [IExpr.ResultTypes L]
    {Parameter : Type} (service : AsyncServiceSpec Player L)
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (low : Player → ℝ) (range : ℝ)
    (within : ∀ who (output : Option (State L service.setup.program.terminalCtx))
      (charged : Bool),
      low who ≤ output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter
          state) who) - (if charged then deposit who else 0) ∧
        output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter
          state) who) - (if charged then deposit who else 0) ≤ low who + range)
    (ε : ℝ) (source : Profile service.sourceModel.behavioralSignature) :
    let base := serviceBaseUtility service.setup service.mode service.deadline service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit
    (IsεNash (service.sourceModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        ε source →
      IsεNash ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
        service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who)
        (ε + 2 * (∑ event, timing.deferral event) * range)
        (service.clientProfile service.rawMenu timing source)) ∧
    (IsεNash ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
      service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who) ε
        (service.clientProfile service.rawMenu timing source) →
      IsεNash (service.sourceModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        (ε + 2 * (∑ event, timing.deferral event) * range) source) :=
  service.isεNash_rawClientProfile_approximate ordered parameter utility sample authentic
    deposit
    nonnegative timing low range within ε source

/-- info: 'Vegas.Paper.async_client_nash_correspondence' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.async_client_nash_correspondence

open Vegas.SourceProgram Vegas.EventGraphRuntime
  GameTheory.Protocol GameTheory.Enforcement in
/-- **Intended approximate Nash equilibria on the bounded raw ledger, for
every contract builder.** For a well-formed setup with finite commitment
payload types and a finite initial law, a forfeit no smaller than the payoff
range, every authentic audit and every nonnegative deposit, and every scheduler
satisfying the asynchronous contract, the turn-counted clients of a source
profile extending an `ε`-Nash equilibrium of the intended game are an
`(ε + 2 * δ * R)`-Nash equilibrium of the audited bounded raw ledger under the
forfeit pass, and their joint law of typed outcome and realized settlement is
within `δ` in total variation of the intended joint law of terminal store and
payoff.
The service graph is barrier ordered, as in the sequential and the
concurrent-binding dependency modes (`Vegas.serviceGraph_barrierOrdered`), with
any configured deadlines. -/
theorem intended_async_client_nash [Fintype Player] [IExpr.ResultTypes L]
    {Parameter : Type} (service : AsyncServiceSpec Player L)
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (wellFormed : service.setup.WellFormed)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (forfeit : ℝ) (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
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
    (source : Profile service.sourceModel.behavioralSignature)
    (agrees : service.setup.intendedRestriction.ExtendsProfile intended source) (ε : ℝ)
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
    IsεNash ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
      service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who)
        (ε + 2 * (∑ event, timing.deferral event) * spread)
        (service.clientProfile service.rawMenu timing source) ∧
      PMF.WithinTV (∑ event, timing.deferral event)
        (((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
          service.horizon
          service.scheduler).runBehavioral (service.clientProfile service.rawMenu timing source)
            (2 * service.horizon + 1)).bind (fun final =>
              (settle final.state).map fun payoffs =>
                (serviceSourceReadout service.setup service.mode service.deadline service.leaks
                  final.state, payoffs)))
        ((service.setup.intendedModel.runBehavioral intended
            (instructionCount service.setup.program + 1)).map
          (fun final => (service.setup.protocolReadout final.state,
            fun who => (service.setup.protocolReadout final.state).elim 0
              (fun state => utility (service.setup.parameterOutcome parameter state) who)))) :=
  service.intended_rawClientProfile_isεNash ordered wellFormed parameter utility forfeit range
    sample authentic deposit nonnegative timing low spread within intended source agrees ε
    equilibrium

/-- info: 'Vegas.Paper.intended_async_client_nash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_async_client_nash

open Vegas.SourceProgram Vegas.EventGraphRuntime
  GameTheory.Protocol GameTheory.Enforcement in
/-- **Exact Nash correspondence on the bounded raw ledger, for every contract
builder.** For a full-source service whose public scheduler satisfies the
asynchronous contract, for every authentic audit and every nonnegative deposit,
the first-turn clients of a source profile (each owner makes its source
decision at its first opportunity) are an `ε`-Nash equilibrium of the audited
bounded raw ledger exactly when the source profile is an `ε`-Nash equilibrium
of the source protocol model, for every `ε`. Realized payoffs need only lie in
some bounded interval. This is `async_client_nash_correspondence` at deferral
weight zero.
The service graph is barrier ordered, as in the sequential and the
concurrent-binding dependency modes (`Vegas.serviceGraph_barrierOrdered`), with
any configured deadlines. -/
theorem async_first_turn_nash_iff [Fintype Player] [IExpr.ResultTypes L]
    {Parameter : Type} (service : AsyncServiceSpec Player L)
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    (turns : Nat)
    (low : Player → ℝ) (range : ℝ)
    (within : ∀ who (output : Option (State L service.setup.program.terminalCtx))
      (charged : Bool),
      low who ≤ output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter
          state) who) - (if charged then deposit who else 0) ∧
        output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter
          state) who) - (if charged then deposit who else 0) ≤ low who + range)
    (ε : ℝ) (source : Profile service.sourceModel.behavioralSignature) :
    let base := serviceBaseUtility service.setup service.mode service.deadline service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit
    IsεNash ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
      service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who) ε
        (service.clientProfile service.rawMenu (firstTurnTiming service.setup turns service.mode)
          source) ↔
      IsεNash (service.sourceModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        ε source :=
  service.isεNash_firstTurnClientProfile_iff ordered parameter utility sample authentic
    deposit
    nonnegative turns low range within ε source

/-- info: 'Vegas.Paper.async_first_turn_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.async_first_turn_nash_iff

open Vegas.SourceProgram Vegas.EventGraphRuntime
  GameTheory.Protocol GameTheory.Enforcement in
/-- **Intended Nash equilibria on the bounded raw ledger, for every contract
builder.** For a well-formed setup with finite commitment payload types and a
finite initial law, a forfeit no smaller than the payoff range, every authentic
audit and every nonnegative deposit, and every scheduler satisfying the
asynchronous contract, the first-turn clients of a source profile extending an
`ε`-Nash equilibrium of the intended game are an `ε`-Nash equilibrium of the
audited bounded raw ledger under the forfeit pass, with the same `ε`, and their
joint law of typed outcome and realized settlement is the intended joint law of
terminal store and payoff. This is `intended_async_client_nash` at deferral
weight zero.
The service graph is barrier ordered, as in the sequential and the
concurrent-binding dependency modes (`Vegas.serviceGraph_barrierOrdered`), with
any configured deadlines. -/
theorem intended_async_first_turn_nash [Fintype Player] [IExpr.ResultTypes L]
    {Parameter : Type} (service : AsyncServiceSpec Player L)
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (wellFormed : service.setup.WellFormed)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (forfeit : ℝ) (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    (turns : Nat)
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
    (source : Profile service.sourceModel.behavioralSignature)
    (agrees : service.setup.intendedRestriction.ExtendsProfile intended source) (ε : ℝ)
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
    IsεNash ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
      service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who) ε
        (service.clientProfile service.rawMenu (firstTurnTiming service.setup turns service.mode)
          source) ∧
      ((service.rawMenu.information (serviceInitialLaw service.setup service.mode) service.horizon
          service.scheduler).runBehavioral
            (service.clientProfile service.rawMenu (firstTurnTiming service.setup turns
              service.mode) source)
            (2 * service.horizon + 1)).bind (fun final =>
              (settle final.state).map fun payoffs =>
                (serviceSourceReadout service.setup service.mode service.deadline service.leaks
                  final.state, payoffs)) =
        (service.setup.intendedModel.runBehavioral intended
            (instructionCount service.setup.program + 1)).map
          (fun final => (service.setup.protocolReadout final.state,
            fun who => (service.setup.protocolReadout final.state).elim 0
              (fun state => utility (service.setup.parameterOutcome parameter state) who))) :=
  service.intended_firstTurnClientProfile_isεNash ordered wellFormed parameter utility forfeit
    range sample authentic deposit nonnegative turns low spread within intended source
    agrees ε equilibrium

/-- info: 'Vegas.Paper.intended_async_first_turn_nash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_async_first_turn_nash

open Vegas.SourceProgram Vegas.EventGraphRuntime
  GameTheory.Protocol GameTheory.Enforcement in
/-- **Intended approximate Nash equilibria for opening clients, in every
dependency mode.** For a well-formed setup with finite commitment payload types
and a finite initial law, a forfeit no smaller than the payoff range, every
authentic audit and every nonnegative deposit, and every scheduler satisfying
the asynchronous contract, every `ε`-Nash equilibrium of the intended game
extends to a source profile that discloses at every reveal, whose turn-counted
clients are an `(ε + 2 * δ * R)`-Nash equilibrium of the audited bounded raw ledger
under the forfeit pass, and their joint law of typed outcome and realized
settlement is within `δ` in total variation of the intended joint law of
terminal store and payoff.
Every dependency mode is covered, the concurrent-reveal mode included: there a
run of disclosures completes in any order, each client opening its own
disclosures from its stored commitment without waiting for any other opening,
and a deviator that withholds one of its disclosures after seeing another
owner's opening in the same run forfeits. -/
theorem intended_opening_client_nash [Fintype Player] [IExpr.ResultTypes L]
    {Parameter : Type} (service : AsyncServiceSpec Player L)
    (wellFormed : service.setup.WellFormed)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (forfeit : ℝ) (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
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
    ∃ source : Profile service.sourceModel.behavioralSignature,
      service.setup.intendedRestriction.ExtendsProfile intended source ∧
      (∀ player, Disclosing service.setup.program
        (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
          source player)) ∧
      IsεNash ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
        service.horizon
          service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
          (fun history who => payoff history.state who)
          (ε + 2 * (∑ event, timing.deferral event) * spread)
          (service.clientProfile service.rawMenu timing source) ∧
        PMF.WithinTV (∑ event, timing.deferral event)
          (((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
            service.horizon
            service.scheduler).runBehavioral (service.clientProfile service.rawMenu timing source)
              (2 * service.horizon + 1)).bind (fun final =>
                (settle final.state).map fun payoffs =>
                  (serviceSourceReadout service.setup service.mode service.deadline service.leaks
                    final.state, payoffs)))
          ((service.setup.intendedModel.runBehavioral intended
              (instructionCount service.setup.program + 1)).map
            (fun final => (service.setup.protocolReadout final.state,
              fun who => (service.setup.protocolReadout final.state).elim 0
                (fun state => utility (service.setup.parameterOutcome parameter state) who)))) :=
  service.intended_openingExtension_isεNash wellFormed parameter utility forfeit range
    sample authentic deposit nonnegative service.rawMenu timing (service.rawMenu_admits timing)
    low spread within intended ε equilibrium

/-- info: 'Vegas.Paper.intended_opening_client_nash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_opening_client_nash

/-- info: 'Vegas.AsyncServiceSpec.intended_openingClientProfile_isεNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.intended_openingClientProfile_isεNash

/-- info: 'Vegas.AsyncServiceSpec.intended_openingExtension_isεNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.intended_openingExtension_isεNash

/-- info: 'Vegas.SourceProgram.Setup.openingExtension_disclosing' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.openingExtension_disclosing

/-- info: 'Vegas.AsyncServiceSpec.openingFirstTurn_deviation_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.openingFirstTurn_deviation_bound

/-- info: 'Vegas.asyncDeviation_withheld_readout' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.asyncDeviation_withheld_readout

/-- info: 'Vegas.openingFirstTurn_readout_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.openingFirstTurn_readout_law

open Vegas.SourceProgram in
/-- **Approximate Nash correspondence on the concurrent event graph.** The
compiled event graph keeps only the public-barrier dependencies: every public
event waits for all earlier events and all later events wait for it, while
commitments of different owners between two public events complete in any
order. For a setup with finite commitment payload types and a finite initial
law, every adaptive public scheduler of that graph, every utility of the public
source result and every `ε`, the compiled profile of a source profile is an
`ε`-Nash equilibrium of the scheduled graph execution exactly when the source
profile is an `ε`-Nash equilibrium of the source game. This is the ideal graph
execution, without the message runtime, builder or audit. -/
theorem concurrent_event_nash_iff [IExpr.ResultTypes L]
    (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (scheduler : setup.eventGraph.PublicScheduler)
    (utility : PublicOutcome setup.program → Player → ℝ)
    (ε : ℝ) (profile : BehavioralProfile setup.program) :
    IsεNash (setup.eventGame scheduler)
        (fun outcome who => utility (setup.eventPublicOutcome outcome) who)
        ε (compileEventProfile setup.program profile) ↔
      IsεNash setup.gameForm utility ε profile :=
  setup.eventGame_approximate_nash_iff finite scheduler utility ε profile

/-- info: 'Vegas.Paper.concurrent_event_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.concurrent_event_nash_iff

/-- info: 'Vegas.SourceProgram.Setup.eventGame_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.eventGame_approximate_nash_iff

/-- info: 'Vegas.EventGraph.runPolicies_concurrentReveals_store' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.runPolicies_concurrentReveals_store

/-- info: 'Vegas.AsyncServiceSpec.isεNash_clientProfile_approximate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.isεNash_clientProfile_approximate

/-- info: 'Vegas.AsyncServiceSpec.intended_clientProfile_isεNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.intended_clientProfile_isεNash

/-- info: 'Vegas.sourceServiceClientPolicy_raw_admissible' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.sourceServiceClientPolicy_raw_admissible

/-- info: 'Vegas.asyncDeviation_readout_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.asyncDeviation_readout_law

/-- info: 'Vegas.AsyncServiceSpec.firstTurn_deviation_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.firstTurn_deviation_bound

/-- info: 'Vegas.deviatedTurnProfile_roundsFrom_bind_within' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.deviatedTurnProfile_roundsFrom_bind_within

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


/-- **Late sends with leaked openings break sequential-equilibrium
preservation.** In the late-turn game a sender of type `(v, s)` (`P(v = 1) =
9/20`, label uniform over three values) opens at a protected turn or sends at
one of two late turns, where an opening is included by a content-blind coin of
probability `99/100`; a listener sees an opening still pending between the late
turns, then answers. With reward scale `2`, forfeit `6` and drop charge `3`,
the intended game (only the protected turn) has a sequential equilibrium; all
its sequential equilibria have the intended outcome law, in which every type
opens at the protected turn and the listener answers safely; and no sequential
equilibrium of the late-turn game has that law. -/
theorem late_leak_intended_outcome_not_preserved :
    (∃ A : (lateLeakModel .sample false).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain .sample false)
        (lateLeak_terminates .sample false) (lateLeakPayoff .sample false)) ∧
    (∀ A : (lateLeakModel .sample false).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain .sample false)
          (lateLeak_terminates .sample false) (lateLeakPayoff .sample false) →
        lateLeakOutcomeLaw .sample false A.strategy = lateLeakIntendedOutcome) ∧
    ∀ A : (lateLeakModel .sample true).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain .sample true)
          (lateLeak_terminates .sample true) (lateLeakPayoff .sample true) →
        lateLeakOutcomeLaw .sample true A.strategy ≠ lateLeakIntendedOutcome :=
  lateLeak_intended_outcome_not_preserved _ LateLeakParameters.sample_deferralPays

/-- info: 'Vegas.Paper.late_leak_intended_outcome_not_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.late_leak_intended_outcome_not_preserved

/-- **Late-sending margins that break preservation.** For every reward scale
`R`, forfeit `D`, drop charge `c` and inclusion probability `q` in `(0, 1)` of
the late-turn game with the prior and listener payoffs above, if `R > 0`,
sending at the last late turn strictly beats never sending
(`q (D - R) > (1 - q) c`) and the full guess reward beats the safe answer at
the protected turn (`q R - (1 - q) (D + c) > R/2`), then the intended game has
a sequential equilibrium, all its sequential equilibria have the intended
outcome law, and no sequential equilibrium of the late-turn game has that
law. -/
theorem late_leak_not_preserved_when_deferral_pays (G : LateLeakParameters)
    (pays : G.DeferralPays) :
    (∃ A : (lateLeakModel G false).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain G false) (lateLeak_terminates G false)
        (lateLeakPayoff G false)) ∧
    (∀ A : (lateLeakModel G false).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain G false) (lateLeak_terminates G false)
          (lateLeakPayoff G false) →
        lateLeakOutcomeLaw G false A.strategy = lateLeakIntendedOutcome) ∧
    ∀ A : (lateLeakModel G true).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain G true) (lateLeak_terminates G true)
          (lateLeakPayoff G true) →
        lateLeakOutcomeLaw G true A.strategy ≠ lateLeakIntendedOutcome :=
  lateLeak_intended_outcome_not_preserved G pays

/-- info: 'Vegas.Paper.late_leak_not_preserved_when_deferral_pays' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.late_leak_not_preserved_when_deferral_pays

/-- info: 'Vegas.lateLeak_intended_outcome_not_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_intended_outcome_not_preserved

/-- **No forfeit or drop-charge margin restores preservation.** For every
reward scale `R > 0`, forfeit `D > R` and drop charge `c ≥ 0`, the explicit
inclusion threshold `max (c / (D - R + c)) ((D + c + R/2) / (D + c + R))` is
below one, and for every inclusion probability `q` in `(0, 1)` above it, the
late-turn game with parameters `R`, `D`, `c` and `q` loses the intended
outcome: the intended game has a sequential equilibrium, all its sequential
equilibria have the intended outcome law, and no sequential equilibrium of the
late-turn game has that law. -/
theorem late_leak_not_preserved_for_every_margin (R D c : ℝ) (reward_pos : 0 < R)
    (margin : R < D) (charge : 0 ≤ c) :
    lateLeakInclusionThreshold R D c < 1 ∧
    ∀ q : Set.Ioo (0 : ℝ) 1, lateLeakInclusionThreshold R D c < q →
      (∃ A : (lateLeakModel ⟨R, D, c, q⟩ false).BehavioralAssessment,
        A.IsSequentialEquilibrium (lateLeak_antichain ⟨R, D, c, q⟩ false)
          (lateLeak_terminates ⟨R, D, c, q⟩ false) (lateLeakPayoff ⟨R, D, c, q⟩ false)) ∧
      (∀ A : (lateLeakModel ⟨R, D, c, q⟩ false).BehavioralAssessment,
        A.IsSequentialEquilibrium (lateLeak_antichain ⟨R, D, c, q⟩ false)
            (lateLeak_terminates ⟨R, D, c, q⟩ false) (lateLeakPayoff ⟨R, D, c, q⟩ false) →
          lateLeakOutcomeLaw ⟨R, D, c, q⟩ false A.strategy = lateLeakIntendedOutcome) ∧
      ∀ A : (lateLeakModel ⟨R, D, c, q⟩ true).BehavioralAssessment,
        A.IsSequentialEquilibrium (lateLeak_antichain ⟨R, D, c, q⟩ true)
            (lateLeak_terminates ⟨R, D, c, q⟩ true) (lateLeakPayoff ⟨R, D, c, q⟩ true) →
          lateLeakOutcomeLaw ⟨R, D, c, q⟩ true A.strategy ≠ lateLeakIntendedOutcome :=
  lateLeak_not_preserved_for_every_margin R D c reward_pos margin charge

/-- info: 'Vegas.Paper.late_leak_not_preserved_for_every_margin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.late_leak_not_preserved_for_every_margin

/-- info: 'Vegas.lateLeak_not_preserved_for_every_margin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_not_preserved_for_every_margin

end Vegas.Paper

