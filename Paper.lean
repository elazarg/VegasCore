/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCompilation
import Vegas.Game.IntendedPreservation
import Vegas.Game.IntendedServiceCompilation
import GameTheoryExtensions.Analysis.Protocol.PublicScheduling
import Vegas.Game.SourceSiteNonterminal
import Vegas.Pending.ReactiveLateCollection
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
import Vegas.Examples.LateLeak.OutcomeSeparation
import Vegas.Examples.LateLeak.ObservableOutcomeSeparation
import Vegas.Examples.LateLeak.PenaltyPreservation
import Vegas.Examples.LateLeak.CalibratedPenaltyPreservation
import Vegas.Examples.LateLeak.SettleLatePreservation
import Interaction.ReactiveSurvival
import Vegas.Game.ServiceRosterProtection
import GameTheoryExtensions.Analysis.PositiveCollection
import GameTheoryExtensions.Analysis.DisclosureReliability
import Interaction.ReactiveCompleteObservation
import Vegas.Examples.CommittedResolutionRecovery
import Vegas.Examples.CommittedResolutionReadout
import Vegas.Examples.CommittedResolutionBobService
import Vegas.Examples.LateLeak.CompleteObservationPosterior
import Vegas.Examples.LateLeak.CompleteObservationValue
import Vegas.Examples.LateLeak.CompleteObservationPreservation
import Vegas.Examples.LateLeak.CompleteObservationProtectedPosterior
import Vegas.Examples.LateLeak.CompleteObservationCostPreservation
import Vegas.Examples.LateLeak.ObservationAdvantage
import GameTheoryExtensions.Analysis.Protocol.PublicationFailureObstruction
import Vegas.Game.ProbabilisticServiceObstruction
import Vegas.Examples.CommittedResolutionBobAudit
import Vegas.Examples.CommittedResolutionBobDecision
import Vegas.Examples.CommittedResolutionBobFailure
import Vegas.Examples.CommittedResolutionBobReadout
import Vegas.Examples.CommittedResolutionBobIncentive
import Vegas.Pending.EventResolutionEnvironment
import Vegas.Examples.CommittedResolutionReliability
import Vegas.Examples.CommittedResolutionErasure
import Vegas.Examples.LateOpeningRuntimeSource
import Vegas.Examples.LateOpeningRuntimeSourceBeliefs
import Vegas.Examples.LateOpeningRuntimeSourceOptimality
import Vegas.Examples.LateOpeningRuntimeSourcePreservation
import Vegas.Examples.LateOpeningRuntimeSourceEquilibrium
import Vegas.Examples.LateOpeningRuntimeCoverage
import Vegas.Examples.LateOpeningRuntimeServiceClock
import Vegas.Examples.LateOpeningRuntimeServiceCompletion
import Vegas.Examples.LateOpeningRuntimeServiceOpportunity
import Vegas.Examples.LateOpeningRuntimeServiceContract
import Vegas.Examples.LateOpeningRuntimeServiceErasure
import Vegas.Examples.LateOpeningRuntimeObservation
import Vegas.Examples.LateOpeningRuntimeLatePrefix
import Vegas.Examples.LateOpeningRuntimeLateHistories
import Vegas.Examples.LateOpeningRuntimeReliability
import Vegas.Examples.LateOpeningRuntimeTerminalReceipt
import Vegas.Pending.ReactiveAcceptanceUniqueness
import Vegas.Examples.LateOpeningRuntimeFiberEvidence
import Vegas.Examples.LateOpeningRuntimeUtility
import Vegas.Examples.LateOpeningRuntimeNash
import Vegas.Examples.LateOpeningRuntimeRetryAudit
import Vegas.Examples.LateOpeningRuntimeAliceContinuation
import Vegas.Examples.LateOpeningRuntimeAliceRationality
import Vegas.Examples.LateOpeningRuntimeAliceEmptyDecision
import Vegas.Examples.LateOpeningRuntimeAliceOpeningAudit
import Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality
import Vegas.Examples.LateOpeningRuntimeAliceOpeningAliases
import Vegas.Examples.LateOpeningRuntimeAliceFinalSupport
import Vegas.Examples.LateOpeningRuntimeAliceFirstRationality
import Vegas.Examples.LateOpeningRuntimeAliceFirstWitness
import Vegas.Examples.LateOpeningRuntimeAliceFirstTremble
import Vegas.Examples.LateOpeningRuntimeAliceNormalization
import Vegas.Examples.LateOpeningRuntimeAliceEmptyWitness
import Vegas.Examples.LateOpeningRuntimeAliceWitness
import Vegas.Examples.LateOpeningRuntimeAliceTremble
import Vegas.Examples.LateOpeningRuntimeProtectedReceipt
import Vegas.Examples.LateOpeningRuntimePreservingLaw
import Vegas.Examples.LateOpeningRuntimeEarlyBobAudit
import Vegas.Examples.LateOpeningRuntimeEarlyBobRationality
import Vegas.Examples.LateOpeningRuntimeBobBindingService
import Vegas.Examples.LateOpeningRuntimeBobBindingWitness
import Vegas.Examples.LateOpeningRuntimeBobAnswerPayoff
import Vegas.Examples.LateOpeningRuntimeBobBindingDecision
import Vegas.Examples.LateOpeningRuntimeBobBindingOptimization
import Vegas.Examples.LateOpeningRuntimeBobBindingSettlement
import Vegas.Examples.LateOpeningRuntimeBobKnownBit
import Vegas.Examples.LateOpeningRuntimeBobKnownBitWitness
import Vegas.Examples.LateOpeningRuntimeFirstObservation
import Vegas.Examples.LateOpeningRuntimeBobQuietPrefix
import Vegas.Examples.LateOpeningRuntimeBobSafeContinuation
import Vegas.Examples.LateOpeningRuntimeBobIncentive
import Vegas.Examples.LateOpeningRuntimeBobRationality
import Vegas.Examples.LateOpeningRuntimeBobSuffix
import Vegas.Examples.LateOpeningRuntimeEquilibrium
import Vegas.Examples.LateOpeningRuntimeEquilibriumConstraints
import Vegas.Examples.LateLeak.SettleLateLikelihood
import Vegas.Pending.ReactiveLateLottery

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

open GameTheory.Protocol in
/-- **Sequential equilibrium under bounded public scheduling.** A finite source
game with decision recall is expanded by a public scheduler: before every
source transition a fixed number of tokens is drawn from a kernel that reads
only a public projection of the source history, the transcript so far and the
pending count, and each player observes its own view of every token (a public
part and, for instance, a private leak drawn from the same public data); waits
are chance moves, and a ready state offers the source menus. If every decision
fiber of the source is nonterminal, and every
player can recover from its information at each of its decisions the public
projections of all prefixes and the actors they fix, then every sequential
equilibrium of the source model has a sequential equilibrium of the expansion
by any finitely supported scheduler with the same law of erased terminal
histories, whose strategy plays the source law at every decision of the
expansion. The scheduler's likelihood is constant on every information fiber
and cancels in Bayes' rule, so beliefs are the source beliefs transported
along the transcript. -/
theorem public_scheduling_sequential_equilibrium {ι : Type} [Fintype ι] [DecidableEq ι]
    {E : ExecutionProtocol ι} {Pub Token View : Type} (S : PublicScheduler E Pub Token View)
    (M : InformationModel E) [Finite E.History] {bound : ℕ} (bounded : E.BoundedHorizon bound)
    (sourceRecall : M.DecisionRecall)
    (nonterminal : ∀ i (site : M.InformationSite i), site.AllNonterminal)
    (recoverable : ∀ i (site : M.InformationSite i)
      (h h' : M.InformationHistory i site.1), S.pubTrace h.1.trace = S.pubTrace h'.1.trace)
    (actors : ∀ i (h h' : E.History), S.pub h = S.pub h' →
      (E.active h.state i ↔ E.active h'.state i))
    (finiteKernel : ∀ pub τ p, (S.kernel pub τ p).support.Finite)
    {Outcome : Type*} (observe : E.History → Outcome) (utility : Outcome → ι → ℝ)
    (source : M.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibrium sourceRecall.decisionInformationAntichain
      bounded.wellFoundedHistories (fun i h => utility (observe h) i)) :
    ∃ target : (S.model M).BehavioralAssessment,
      target.IsSequentialEquilibrium
        (S.decisionRecall M sourceRecall recoverable actors).decisionInformationAntichain
        (S.boundedHorizon bounded).wellFoundedHistories
        (fun i x => utility (observe (S.erase x)) i) ∧
      ((S.model M).runBehavioralTerminalFrom (S.boundedHorizon bounded).wellFoundedHistories
          target.strategy S.protocol.initHistory).map (fun x => observe (S.erase x)) =
        (M.runBehavioralTerminalFrom bounded.wellFoundedHistories source.strategy
          E.initHistory).map observe ∧
      ∀ i (site : (S.model M).InformationSite i),
        target.strategy i site.1 = S.liftProfile M source.strategy i site.1 :=
  S.expanded_sequentialEquilibrium M bounded sourceRecall nonterminal recoverable actors
    finiteKernel observe utility source equilibrium

/-- info: 'Vegas.Paper.public_scheduling_sequential_equilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.public_scheduling_sequential_equilibrium

/-- info: 'GameTheory.Protocol.PublicScheduler.expanded_sequentialEquilibrium' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.PublicScheduler.expanded_sequentialEquilibrium

/-- info: 'Vegas.SourceProgram.Setup.decision_allNonterminal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.decision_allNonterminal

/-- info: 'Vegas.EventGraphRuntime.deadPacket_collection_continuation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.deadPacket_collection_continuation

/-- info: 'Vegas.EventGraphRuntime.lateSend_collection_continuation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.lateSend_collection_continuation

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
    (admission : CommitmentInterface service.setup.program)
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (menu : (serviceApplication service.setup service.mode service.deadline
      service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (covered : ∀ (source : Profile (service.sourceModel admission).behavioralSignature) who,
      menu.Admissible (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler who
        (serviceClientPolicy service.setup service.mode service.deadline service.leaks
          service.bound turns timing
          (sourceServiceClientProfile service.setup (service.setup.decodeBehavioralProfile
            admission source)) who))
    (low : Player → ℝ) (range : ℝ)
    (within : ∀ who (output : Option (State L service.setup.program.terminalCtx))
      (charged : Bool),
      low who ≤ output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter
          state) who) - (if charged then deposit who else 0) ∧
        output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter
          state) who) - (if charged then deposit who else 0) ≤ low who + range)
    (ε : ℝ) (source : Profile (service.sourceModel admission).behavioralSignature) :
    let base := serviceBaseUtility service.setup service.mode service.deadline service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit
    IsεNash ((menu.information (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who) ε
        (service.clientProfile admission menu timing source) →
      IsεNash ((service.sourceModel admission).toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        (ε + 2 * (∑ event, timing.deferral event) * range) source :=
  service.isεNash_of_clientProfile admission ordered parameter utility sample authentic deposit menu
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
any configured deadlines. The binding interface is arbitrary: immediate binding
failure may be admitted at every site, at none, or at selected sites. -/
theorem async_client_nash_correspondence [Fintype Player] [IExpr.ResultTypes L]
    {Parameter : Type} (service : AsyncServiceSpec Player L)
    (admission : CommitmentInterface service.setup.program)
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
    (ε : ℝ) (source : Profile (service.sourceModel admission).behavioralSignature) :
    let base := serviceBaseUtility service.setup service.mode service.deadline service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit
    (IsεNash ((service.sourceModel admission).toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        ε source →
      IsεNash ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
        service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who)
        (ε + 2 * (∑ event, timing.deferral event) * range)
        (service.clientProfile admission service.rawMenu timing source)) ∧
    (IsεNash ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
      service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who) ε
        (service.clientProfile admission service.rawMenu timing source) →
      IsεNash ((service.sourceModel admission).toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        (ε + 2 * (∑ event, timing.deferral event) * range) source) :=
  service.isεNash_rawClientProfile_approximate admission ordered parameter utility sample authentic
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
    (source : Profile (service.sourceModel (CommitmentInterface.values
      service.setup.program)).behavioralSignature)
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
        (service.clientProfile (CommitmentInterface.values service.setup.program) service.rawMenu
          timing source) ∧
      PMF.WithinTV (∑ event, timing.deferral event)
        (((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
          service.horizon
          service.scheduler).runBehavioral (service.clientProfile (CommitmentInterface.values
            service.setup.program) service.rawMenu timing source)
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
any configured deadlines. Every binding interface is covered, including
immediate failed bindings and site-dependent admission of that choice. -/
theorem async_first_turn_nash_iff [Fintype Player] [IExpr.ResultTypes L]
    {Parameter : Type} (service : AsyncServiceSpec Player L)
    (admission : CommitmentInterface service.setup.program)
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
    (ε : ℝ) (source : Profile (service.sourceModel admission).behavioralSignature) :
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
        (service.clientProfile admission service.rawMenu (firstTurnTiming service.setup turns
          service.mode)
          source) ↔
      IsεNash ((service.sourceModel admission).toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        ε source :=
  service.isεNash_firstTurnClientProfile_iff admission ordered parameter utility sample authentic
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
    (source : Profile (service.sourceModel (CommitmentInterface.values
      service.setup.program)).behavioralSignature)
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
        (service.clientProfile (CommitmentInterface.values service.setup.program) service.rawMenu
          (firstTurnTiming service.setup turns service.mode)
          source) ∧
      ((service.rawMenu.information (serviceInitialLaw service.setup service.mode) service.horizon
          service.scheduler).runBehavioral
            (service.clientProfile (CommitmentInterface.values service.setup.program)
              service.rawMenu (firstTurnTiming service.setup turns
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
    ∃ source : Profile (service.sourceModel (CommitmentInterface.values
      service.setup.program)).behavioralSignature,
      service.setup.intendedRestriction.ExtendsProfile intended source ∧
      (∀ player, Disclosing service.setup.program
        (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
          source player)) ∧
      IsεNash ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
        service.horizon
          service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
          (fun history who => payoff history.state who)
          (ε + 2 * (∑ event, timing.deferral event) * spread)
          (service.clientProfile (CommitmentInterface.values service.setup.program)
            service.rawMenu timing source) ∧
        PMF.WithinTV (∑ event, timing.deferral event)
          (((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
            service.horizon
            service.scheduler).runBehavioral (service.clientProfile (CommitmentInterface.values
              service.setup.program) service.rawMenu timing source)
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
    sample authentic deposit nonnegative service.rawMenu timing (service.rawMenu_admits
      (CommitmentInterface.values service.setup.program) timing)
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

/-- **The settle-late runtime loses the intended outcome for every margin.** The
late-turn game placed in an asynchronous runtime: a builder that settles all
late packets in one inclusion step after the sender's last late activation,
with one observe-only listener activation between the late turns; a stateless
leak rule that shows each pending opening independently with probability `λ` at
every listener activation, so that a dropped opening stays pending and may be
seen when the listener answers; Luce inclusion laws `q` for one late opening
and `q / (1 + q)` for each of two; a blind retry; raw signals at the protected
turn, after a protected opening and at both late turns under an escrow that
charges `c` at most once; and a listener raw packet of cost c_L that the
sender sees. For every reward scale `R > 0`, forfeit `D > R`, charge `c > R/2`,
leak probability `λ` in `(0, 1)` (for instance `1/2`) and packet cost c_L,
the explicit inclusion threshold is below one, and for every inclusion
probability `q` above it: the intended game (open at the protected turn, emit
nothing more) has a sequential equilibrium, all its sequential equilibria have
the intended outcome law, and no sequential equilibrium of the settle-late game
has that law. -/
theorem settle_late_not_preserved_for_every_margin (R D c : ℝ) (reward_pos : 0 < R)
    (margin : R < D) (charge : R / 2 < c) (leak : Set.Ioo (0 : ℝ) 1) (packetCost : ℝ) :
    settleLateInclusionThreshold R D c leak < 1 ∧
    ∀ q : Set.Ioo (0 : ℝ) 1, settleLateInclusionThreshold R D c leak < q →
      (∃ A : (settleLateModel ⟨⟨R, D, c, q⟩, leak, packetCost⟩ false).BehavioralAssessment,
        A.IsSequentialEquilibrium (settleLate_antichain ⟨⟨R, D, c, q⟩, leak, packetCost⟩ false)
          (settleLate_terminates ⟨⟨R, D, c, q⟩, leak, packetCost⟩ false)
          (settleLatePayoff ⟨⟨R, D, c, q⟩, leak, packetCost⟩ false)) ∧
      (∀ A : (settleLateModel ⟨⟨R, D, c, q⟩, leak, packetCost⟩ false).BehavioralAssessment,
        A.IsSequentialEquilibrium (settleLate_antichain ⟨⟨R, D, c, q⟩, leak, packetCost⟩ false)
            (settleLate_terminates ⟨⟨R, D, c, q⟩, leak, packetCost⟩ false)
            (settleLatePayoff ⟨⟨R, D, c, q⟩, leak, packetCost⟩ false) →
          settleLateOutcomeLaw ⟨⟨R, D, c, q⟩, leak, packetCost⟩ false A.strategy =
            settleLateIntendedOutcome) ∧
      ∀ A : (settleLateModel ⟨⟨R, D, c, q⟩, leak, packetCost⟩ true).BehavioralAssessment,
        A.IsSequentialEquilibrium (settleLate_antichain ⟨⟨R, D, c, q⟩, leak, packetCost⟩ true)
            (settleLate_terminates ⟨⟨R, D, c, q⟩, leak, packetCost⟩ true)
            (settleLatePayoff ⟨⟨R, D, c, q⟩, leak, packetCost⟩ true) →
          settleLateOutcomeLaw ⟨⟨R, D, c, q⟩, leak, packetCost⟩ true A.strategy ≠
            settleLateIntendedOutcome :=
  settleLate_not_preserved_for_every_margin R D c reward_pos margin charge leak packetCost

/-- info: 'Vegas.Paper.settle_late_not_preserved_for_every_margin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.settle_late_not_preserved_for_every_margin

/-- info: 'Vegas.settleLate_not_preserved_for_every_margin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.settleLate_not_preserved_for_every_margin

/-- info: 'Vegas.settleLate_intended_outcome_not_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.settleLate_intended_outcome_not_preserved

/-- Every sequential equilibrium of the sample late-leak game is separated
from the intended full terminal-state law by at least 267/2000 in total
variation. This quantifies the obstruction; it is not a chain-wide claim. -/
theorem late_leak_equilibrium_total_variation_gap
    {A : (lateLeakModel LateLeakParameters.sample true).BehavioralAssessment}
    (equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain LateLeakParameters.sample true)
      (lateLeak_terminates LateLeakParameters.sample true)
      (lateLeakPayoff LateLeakParameters.sample true))
    {error : ℝ}
    (close : PMF.WithinTV error (lateLeakOutcomeLaw LateLeakParameters.sample true A.strategy)
      lateLeakIntendedOutcome) :
    (267 / 2000 : ℝ) ≤ error :=
  lateLeak_sample_totalVariation_lower_bound equilibrium close

/-- info: 'Vegas.Paper.late_leak_equilibrium_total_variation_gap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.late_leak_equilibrium_total_variation_gap

/-- info: 'Vegas.lateLeak_equilibrium_totalVariation_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_equilibrium_totalVariation_lower_bound

/-- info: 'GameTheory.Math.Probability.eventProbability_foldl_ge_prod' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Math.Probability.eventProbability_foldl_ge_prod

/-- info: 'Interaction.ReactiveApplication.runRounds_eventProbability_ge_pow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.runRounds_eventProbability_ge_pow

/-- info: 'Vegas.rosterScheduler_activation_fits' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.rosterScheduler_activation_fits

/-- info: 'Vegas.rosterScheduler_network_independent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.rosterScheduler_network_independent

/-- With fixed late inclusion below one, sufficiently large failure costs
preserve the intended law even with visible dropped openings. A target SE
exists, and every target SE has that law. -/
theorem late_leak_outcome_preserved_by_failure_costs (G : LateLeakParameters)
    (reward : 0 ≤ G.reward) (never : G.reward / 2 < G.forfeit)
    (attempt : G.reward / 2 < (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge)) :
    (∃ A : (lateLeakModel G true).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain G true)
        (lateLeak_terminates G true) (lateLeakPayoff G true)) ∧
    ∀ A : (lateLeakModel G true).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain G true)
        (lateLeak_terminates G true) (lateLeakPayoff G true) →
      lateLeakOutcomeLaw G true A.strategy = lateLeakIntendedOutcome := by
  obtain ⟨assessment, equilibrium, _⟩ :=
    lateLeak_preserving_equilibrium_of_half_reward_costs reward never attempt
  exact ⟨⟨assessment, equilibrium⟩,
    lateLeak_outcome_preserved_of_half_reward_costs reward never attempt⟩

/-- info: 'Vegas.Paper.late_leak_outcome_preserved_by_failure_costs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.late_leak_outcome_preserved_by_failure_costs

/-- info: 'Vegas.lateLeak_exists_preserving_dropCharge' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_exists_preserving_dropCharge

/-- info: 'Vegas.lateLeak_exists_preserving_dropCharge_of_half_reward' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_exists_preserving_dropCharge_of_half_reward

/-- info: 'Vegas.lateLeak_outcome_preserved_of_rational_bayes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_outcome_preserved_of_rational_bayes

/-- info: 'Vegas.lateLeak_sequentialEquilibrium_preserved_of_half_reward_costs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_sequentialEquilibrium_preserved_of_half_reward_costs

/-- info: 'Vegas.lateLeak_exists_preserving_forfeit_without_dropCharge' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_exists_preserving_forfeit_without_dropCharge

/-- The late-leak gap survives erasing every transmission-timing detail.
This law retains initial type, success/failure and the listener's answer. -/
theorem late_leak_equilibrium_result_total_variation_gap
    {A : (lateLeakModel LateLeakParameters.sample true).BehavioralAssessment}
    (equilibrium : A.IsSequentialEquilibrium (lateLeak_antichain LateLeakParameters.sample true)
      (lateLeak_terminates LateLeakParameters.sample true)
      (lateLeakPayoff LateLeakParameters.sample true))
    {error : ℝ}
    (close : PMF.WithinTV error
      (lateLeakResultLaw LateLeakParameters.sample true A.strategy)
      lateLeakIntendedResultLaw) :
    (3 / 2000 : ℝ) ≤ error :=
  lateLeak_sample_result_totalVariation_lower_bound equilibrium close

/-- info: 'Vegas.Paper.late_leak_equilibrium_result_total_variation_gap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.late_leak_equilibrium_result_total_variation_gap

/-- info: 'Vegas.lateLeak_equilibrium_result_not_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_equilibrium_result_not_preserved

/-- info: 'Interaction.ReactiveApplication.runUntil_eventProbability_ge_pow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.runUntil_eventProbability_ge_pow

end Vegas.Paper

/-- info: 'GameTheory.Enforcement.exists_positive_collection_floor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Enforcement.exists_positive_collection_floor

/-- info: 'GameTheory.GameForm.exists_positive_mixed_collection_floor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.GameForm.exists_positive_mixed_collection_floor

/-- info: 'GameTheory.DisclosureReliability.exists_uniform_reliability_forfeit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.DisclosureReliability.exists_uniform_reliability_forfeit

/-- info: 'Interaction.ReactiveApplication.complete_decision_submitted_visible' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.complete_decision_submitted_visible

/-- info: 'Vegas.Examples.CommittedResolutionRecovery.initialized_clean_recovery' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommittedResolutionRecovery.initialized_clean_recovery

/-- info: 'Vegas.lateOpeningPublicCanonical_consistent_public_beliefs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateOpeningPublicCanonical_consistent_public_beliefs

/-- info: 'Vegas.lateOpeningPublic_sender_context_best_response' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateOpeningPublic_sender_context_best_response

/-- info: 'Vegas.Examples.CommittedResolutionReadout.bob_success_true' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommittedResolutionReadout.bob_success_true

/-- info: 'Vegas.lateOpeningPublic_exists_sequential_equilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateOpeningPublic_exists_sequential_equilibrium

/-- info: 'GameTheory.Protocol.PublicationFailure.outageRun_totalVariation_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.PublicationFailure.outageRun_totalVariation_lower_bound

/-- info: 'Vegas.lateOpeningPublic_preserves_intended_sequential_equilibria' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateOpeningPublic_preserves_intended_sequential_equilibria

/-- info: 'Vegas.lateOpeningPublic_twice_reward_preserves_sequential_equilibria' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateOpeningPublic_twice_reward_preserves_sequential_equilibria

/-- info: 'Vegas.lateOpeningPublic_outcome_of_cost_gap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateOpeningPublic_outcome_of_cost_gap

/-- info: 'Vegas.Examples.CommittedResolutionBobService.canonical_bob_round' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommittedResolutionBobService.canonical_bob_round

/-- info: 'Vegas.lateLeak_partial_observation_opposite_preferences' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_partial_observation_opposite_preferences

/-- info: 'Vegas.service_behavioral_outage_not_realized' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.service_behavioral_outage_not_realized

/-- info: 'Vegas.Examples.CommittedResolutionBobAudit.canonical_bob_audit_clear' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommittedResolutionBobAudit.canonical_bob_audit_clear

/-- info: 'Vegas.EventGraphRuntime.environmentStep_resolution_no_success' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.environmentStep_resolution_no_success

/-- info: 'Vegas.Examples.CommittedResolutionBobDecision.bob_continuation_current_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommittedResolutionBobDecision.bob_continuation_current_law

/-- info: 'Vegas.Examples.CommittedResolutionBobFailure.bob_failed_response_at_horizon' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommittedResolutionBobFailure.bob_failed_response_at_horizon

/-- info: 'Vegas.Examples.CommittedResolutionBobReadout.bob_continuation_readout_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommittedResolutionBobReadout.bob_continuation_readout_eq

/-- info: 'Vegas.AsyncServiceSpec.firstTurnClientProfile_settlement_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.firstTurnClientProfile_settlement_law

/-- info: 'Vegas.Examples.CommittedResolutionReliability.exists_contract_below_failure_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommittedResolutionReliability.exists_contract_below_failure_floor

/-- info: 'Vegas.EventGraphRuntime.blindToLatePackets_pendingLottery' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.blindToLatePackets_pendingLottery

/-- info: 'GameTheory.Protocol.InformationModel.AsymptoticHistoryLikelihood.belief_face'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.InformationModel.AsymptoticHistoryLikelihood.belief_face

/-- info: 'Vegas.settleLate_opposite_timing_excludes_label' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.settleLate_opposite_timing_excludes_label

/-- info: 'Vegas.Examples.LateOpeningRuntimeSource.consistent_bobBinding_uniform' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeSource.consistent_bobBinding_uniform

/-- info: 'Vegas.Examples.LateOpeningRuntimeSource.bob_answer_law_value_eq_safe_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeSource.bob_answer_law_value_eq_safe_iff

/-- info: 'Vegas.Examples.LateOpeningRuntimeSource.bob_answer_law_safe_probability_of_near_optimal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeSource.bob_answer_law_safe_probability_of_near_optimal

/-- info: 'Vegas.Examples.LateOpeningRuntimeSource.intended_equilibrium_preserved_under_withholding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeSource.intended_equilibrium_preserved_under_withholding

/-- info: 'Vegas.Examples.LateOpeningRuntimeSource.exists_withholding_sequential_equilibrium'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeSource.exists_withholding_sequential_equilibrium

/-- info: 'Vegas.Examples.CommittedResolutionBobIncentive.canonical_bob_response_regret'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommittedResolutionBobIncentive.canonical_bob_response_regret

/-- info: 'Vegas.Examples.LateOpeningRuntimeSource.intended_equilibrium_terminal_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeSource.intended_equilibrium_terminal_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeSource.exists_withholding_equilibrium_with_safe_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeSource.exists_withholding_equilibrium_with_safe_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeSource.bayes_rational_terminal_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeSource.bayes_rational_terminal_law

/-- info: 'Vegas.Examples.CommittedResolutionErasure.certain_late_inclusion_with_joint_contract'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.CommittedResolutionErasure.certain_late_inclusion_with_joint_contract

/-- info: 'Vegas.Examples.LateOpeningRuntimeService.clock_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeService.clock_history

/-- info: 'Vegas.Examples.LateOpeningRuntimeServiceErasure.scheduler_blind' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeServiceErasure.scheduler_blind

/-- info: 'Vegas.Examples.LateOpeningRuntimeReadout.bob_continuation_success_immutable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeReadout.bob_continuation_success_immutable

/-- info: 'Vegas.Examples.LateOpeningRuntimeUtility.alice_accepted_openings_audit_clean'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeUtility.alice_accepted_openings_audit_clean

/-- info: 'Vegas.Examples.LateOpeningRuntimeService.completes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeService.completes

/-- info: 'Vegas.Examples.LateOpeningRuntimeObservation.leaks_singleton' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeObservation.leaks_singleton

/-- info: 'Vegas.Examples.LateOpeningRuntimeService.binding_values_covered' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeService.binding_values_covered

/-- info: 'Vegas.Examples.LateOpeningRuntimeService.initial_values_covered' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeService.initial_values_covered

/-- info: 'Vegas.Examples.LateOpeningRuntimeService.opportunity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeService.opportunity

/-- info: 'Vegas.Examples.LateOpeningRuntimeLatePrefix.firstBob_recall_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLatePrefix.firstBob_recall_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeService.contract_and_blind' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeService.contract_and_blind

/-- info: 'Vegas.Examples.LateOpeningRuntimeService.protected_submission_receipt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeService.protected_submission_receipt

/-- info: 'Vegas.Examples.LateOpeningRuntimeNash.first_opportunity_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeNash.first_opportunity_nash_iff

/-- info: 'Vegas.Examples.LateOpeningRuntimeNash.first_opportunity_settlement_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeNash.first_opportunity_settlement_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeFiberEvidence.bob_information_no_packets'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeFiberEvidence.bob_information_no_packets

/-- info: 'Interaction.ReactiveApplication.emitted_zero_has_no_prior_outputs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.emitted_zero_has_no_prior_outputs

/-- info: 'Vegas.Examples.LateOpeningRuntimeLateAcceptance.answerDecision_unseen_timing_info'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeLateAcceptance.answerDecision_unseen_timing_info

/-- info: 'Vegas.Examples.LateOpeningRuntimeLateHistories.answerDecision_trace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLateHistories.answerDecision_trace

/-- info: 'Vegas.Examples.LateOpeningRuntimeReliability.exists_joint_service_below_failure_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeReliability.exists_joint_service_below_failure_floor

/-- info: 'Vegas.Examples.LateOpeningRuntimeTerminalReceipt.terminal_receipt_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeTerminalReceipt.terminal_receipt_law

/-- info: 'Vegas.EventGraphRuntime.accepting_identifiers_unique' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.accepting_identifiers_unique

/-- info: 'Vegas.Examples.LateOpeningRuntimeTerminalReceipt.exists_joint_service_with_exact_failure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeTerminalReceipt.exists_joint_service_with_exact_failure

/-- info: 'Vegas.Examples.LateOpeningRuntimeRetryAudit.alice_two_envelopes_utility_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeRetryAudit.alice_two_envelopes_utility_bound

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobIncentive.canonical_dominates' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobIncentive.canonical_dominates

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobIncentive.canonical_regret' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobIncentive.canonical_regret

/-- info: 'Interaction.ReactiveApplication.ResponseMenu.exists_sequentialEquilibrium'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.exists_sequentialEquilibrium

/-- info: 'Vegas.Examples.LateOpeningRuntimeEquilibrium.exists_sequential_equilibrium'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeEquilibrium.exists_sequential_equilibrium

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceContinuation.quiet_expected_payoff_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceContinuation.quiet_expected_payoff_lower

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceContinuation.quiet_strictly_beats_second_packet'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceContinuation.quiet_strictly_beats_second_packet

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceContinuation.exists_service_with_quiet_normalization'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAliceContinuation.exists_service_with_quiet_normalization

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobRationality.equilibrium_final_failure_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobRationality.equilibrium_final_failure_zero

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobRationality.final_failure_le_of_deviation_regret'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobRationality.final_failure_le_of_deviation_regret

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobSuffix.finalDecision_trace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobSuffix.finalDecision_trace

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobSuffix.final_disclosure_class_nonempty'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobSuffix.final_disclosure_class_nonempty

/-- info: 'Interaction.ReactiveApplication.continuation_policy_independent_of_unactivated'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.continuation_policy_independent_of_unactivated


/-- info: 'Interaction.ReactiveApplication.ResponseMenu.run_last_response_of_unactivated'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.ResponseMenu.run_last_response_of_unactivated


/-- info: 'Interaction.ReactiveApplication.receipt_identifiers_distinct_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.receipt_identifiers_distinct_history


/-- info: 'Interaction.ReactiveApplication.rejected_identifier_not_accepted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.rejected_identifier_not_accepted


/-- info: 'Vegas.Examples.LateOpeningRuntimeProtectedOpening.protected_miss_terminal_failure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeProtectedOpening.protected_miss_terminal_failure


/-- info: 'Vegas.Examples.LateOpeningRuntimeProtectedReceipt.native_almost_sure_success_protected_receipt_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeProtectedReceipt.native_almost_sure_success_protected_receipt_law


/-- info: 'Vegas.Examples.LateOpeningRuntimeEarlyBobAudit.early_submission_continuation_utility_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeEarlyBobAudit.early_submission_continuation_utility_bound


/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceDecision.decision_of_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceDecision.decision_of_information


/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceIncentive.quiet_second_packet_regret'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceIncentive.quiet_second_packet_regret


/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceRationality.quiet_regret'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceRationality.quiet_regret


/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceRationality.equilibrium_second_packet_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceRationality.equilibrium_second_packet_zero


/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceRationality.second_packet_le_of_deviation_regret'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceRationality.second_packet_le_of_deviation_regret


/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceWitness.last_alice_class_nonempty'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceWitness.last_alice_class_nonempty


/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceTremble.weighted_retry_ratio_tendsto'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceTremble.weighted_retry_ratio_tendsto

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceTremble.equilibrium_consistency_retry_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceTremble.equilibrium_consistency_retry_bound

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobBindingService.binding_round'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobBindingService.binding_round

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobQuietPrefix.binding_activation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobQuietPrefix.binding_activation

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceEmptyDecision.quiet_pending_empty'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceEmptyDecision.quiet_pending_empty

/-- info: 'GameTheory.Math.Probability.eventProbability_le_of_two_value_comparisons'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Math.Probability.eventProbability_le_of_two_value_comparisons

/-- info: 'Interaction.ReactiveApplication.traffic_envelope_eq_ledger_of_id_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.traffic_envelope_eq_ledger_of_id_eq

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobSafeContinuation.safe_continuation_clean'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobSafeContinuation.safe_continuation_clean

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobSafeContinuation.safe_continuation_nonnegative'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobSafeContinuation.safe_continuation_nonnegative

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceOpeningAudit.permitted_alice_payload'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceOpeningAudit.permitted_alice_payload

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceOpeningAudit.nongenuine_envelope_utility_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceOpeningAudit.nongenuine_envelope_utility_bound

/-- info: 'Vegas.Examples.LateOpeningRuntimeEarlyBobRationality.equilibrium_early_response_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeEarlyBobRationality.equilibrium_early_response_law

/-- info:
'Vegas.Examples.LateOpeningRuntimeEarlyBobRationality.early_packet_le_of_deviation_regrets'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeEarlyBobRationality.early_packet_le_of_deviation_regrets

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality.opening_regret'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality.opening_regret

/-- info:
'Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality.equilibrium_nongenuine_response_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality.equilibrium_nongenuine_response_zero

/-- info:
'Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality.nongenuine_le_of_deviation_regret'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality.nongenuine_le_of_deviation_regret

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobSafeContinuation.answer_continuation_clean'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobSafeContinuation.answer_continuation_clean

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobBindingInformation.decision_of_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobBindingInformation.decision_of_information

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobBindingWitness.failed_binding_representative'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobBindingWitness.failed_binding_representative

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobAnswerPayoff.failed_answer_continuation_payoff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobAnswerPayoff.failed_answer_continuation_payoff

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobBindingDecision.answer_context_value'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobBindingDecision.answer_context_value

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobBindingDecision.exists_bit_guess_value_ge_half'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobBindingDecision.exists_bit_guess_value_ge_half

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobBindingDecision.equilibrium_binding_value_ge_half'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobBindingDecision.equilibrium_binding_value_ge_half

/-- info:
'Vegas.Examples.LateOpeningRuntimeBobBindingWitness.failed_binding_information_representative'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobBindingWitness.failed_binding_information_representative

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceNormalization.equilibrium_last_responses'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceNormalization.equilibrium_last_responses

/-- info:
'Vegas.Examples.LateOpeningRuntimeAliceNormalization.exists_service_with_last_responses_normalized'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAliceNormalization.exists_service_with_last_responses_normalized

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceEmptyWitness.secondLateDecision_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceEmptyWitness.secondLateDecision_trace

/-- info: 'Vegas.Examples.LateOpeningRuntimeEquilibriumConstraints.equilibrium_constraints'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeEquilibriumConstraints.equilibrium_constraints

/-- info:
'Vegas.Examples.LateOpeningRuntimeEquilibriumConstraints.sequentially_rational_constraints'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeEquilibriumConstraints.sequentially_rational_constraints

/-- info:
'Vegas.Examples.LateOpeningRuntimeEquilibriumConstraints.exists_service_with_constraints'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeEquilibriumConstraints.exists_service_with_constraints

/-- info: 'Interaction.ReactiveApplication.eraseRecall_runRounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.eraseRecall_runRounds

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceOpeningAliases.opening_payoff_law_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceOpeningAliases.opening_payoff_law_eq

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceFinalSupport.final_response_value_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceFinalSupport.final_response_value_lower

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceQuietPrefix.final_decision_of_silence'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceQuietPrefix.final_decision_of_silence

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceFirstRationality.equilibrium_nongenuine_packet_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAliceFirstRationality.equilibrium_nongenuine_packet_zero

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceFirstWitness.first_alice_class_nonempty'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceFirstWitness.first_alice_class_nonempty

/-- info: 'Vegas.Examples.LateOpeningRuntimePreservingLaw.successful_readout_protected_receipt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimePreservingLaw.successful_readout_protected_receipt

/-- info: 'Vegas.Examples.LateOpeningRuntimePreservingLaw.intended_law_protected_receipt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimePreservingLaw.intended_law_protected_receipt

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobRawPayoff.continuation_payoff_le_score'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobRawPayoff.continuation_payoff_le_score

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobBindingOptimization.rational_supported_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobBindingOptimization.rational_supported_binding

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobBindingOptimization.rational_value_eq_bestGuessValue'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobBindingOptimization.rational_value_eq_bestGuessValue

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobKnownBit.equilibrium_correct_publication'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobKnownBit.equilibrium_correct_publication

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobKnownBitWitness.failed_publication_known_bit_class'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobKnownBitWitness.failed_publication_known_bit_class

/-- info:
'Vegas.Examples.LateOpeningRuntimeAliceFirstTremble.equilibrium_consistency_nongenuine_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAliceFirstTremble.equilibrium_consistency_nongenuine_bound

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceFirstTremble.weighted_nongenuine_ratio_tendsto'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceFirstTremble.weighted_nongenuine_ratio_tendsto

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobBindingSettlement.rational_supported_clean_settlement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobBindingSettlement.rational_supported_clean_settlement

/-- info: 'Vegas.Examples.LateOpeningRuntimeFirstObservation.first_observation_probability'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeFirstObservation.first_observation_probability
