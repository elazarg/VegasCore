/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions
import Vegas.Source.Safety
import Interaction.ReactiveImplementation
import Interaction.ReactivePolicyMenuInvariant
import Interaction.ReactiveProvenance
import Interaction.ReactiveSchedulerDensity
import Vegas.Pending.CompletionService
import Vegas.Pending.PhaseSingletonTransition
import Vegas.Pending.PhaseClearMetadata
import Vegas.Pending.PhaseCheckpointExclusion
import Vegas.Pending.PhaseStaticCountVerdict
import Vegas.Pending.ReactiveFirstOpportunity
import Interaction.MessageNetworkMapOperations
import Vegas.Compile
import Vegas.Game
import Vegas.Examples.LateLeak
import Vegas.Examples.ProgramPayments
import Vegas.Examples.ProgramPaymentsRuntime
import Vegas.Examples.BoundedPaymentAuction
import Vegas.Examples.SequentialPhaseServiceEquilibrium
import VegasTests.RepeatedActivation

/-! # Paper theorems

Paper-facing statements, each pinned to the three standard axioms. The build
rejects `sorry` and the source policy rejects axiom declarations, so these pins
are the axiom audit.
-/

noncomputable section

namespace Vegas.Paper

open GameTheory Vegas Interaction
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

open Vegas.SourceProgram in
theorem concurrent_source_raw_sequential_equilibrium
    [Fintype Player] [IExpr.ResultTypes L]
    (setup : Setup (Player := Player) (L := L))
    (implementation : ReservedConcurrentImplementation setup)
    (payoffs : ConcurrentPayoffs setup) (countAudit : ConcurrentCountAudit setup)
    (valid : implementation.Valid payoffs countAudit)
    (source : setup.intendedModel.BehavioralAssessment)
    (equilibrium : payoffs.SourceEquilibrium source) :
    ∃ target : implementation.model.BehavioralAssessment,
      implementation.PreservesAssessment payoffs countAudit source target :=
  Vegas.concurrentRawSequentialPreservation setup implementation payoffs countAudit
    valid source equilibrium

/-- info: 'Vegas.Paper.concurrent_source_raw_sequential_equilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.concurrent_source_raw_sequential_equilibrium

open Vegas.SourceProgram in
theorem source_protocol_horizon [IExpr.ResultTypes L]
    (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) :
    (setup.executionProtocol admission).BoundedHorizon (instructionCount setup.program + 1) :=
  setup.protocol_bounded admission

/-- info: 'Vegas.Paper.source_protocol_horizon' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_protocol_horizon

open Vegas.SourceProgram GameTheory.Protocol in
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
  setup.intended_sequentialEquilibrium_preserved
      (CommitmentInterface.values setup.program) finite wellFormed parameter utility forfeit
    range _ _ intended equilibrium

/-- info: 'Vegas.Paper.intended_sequential_equilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_sequential_equilibrium

open Vegas.SourceProgram GameTheory.Protocol in
theorem exclusion_sequential_equilibrium [Fintype Player] [IExpr.ResultTypes L]
    (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who))) :
    ∃ target : setup.exclusionModel.BehavioralAssessment,
      target.IsSequentialEquilibrium setup.exclusion_decisionRecall.decisionInformationAntichain
        setup.exclusion_bounded.wellFoundedHistories
        (fun who final => (setup.protocolReadout final.state).elim 0
          (fun state => exclusionUtility setup.program excludedPayoff utility
            (setup.parameterOutcome parameter state) who)) ∧
      (setup.exclusionRestriction wellFormed).ExtendsProfile intended.strategy
        target.strategy ∧
      (∀ who site, target.belief who ((setup.exclusionRestriction wellFormed).site who site) =
        (intended.belief who site).map
          ((setup.exclusionRestriction wellFormed).informationHistory who site)) ∧
      (setup.exclusionModel.runBehavioralTerminalFrom setup.exclusion_bounded.wellFoundedHistories
          target.strategy setup.exclusionProtocol.initHistory).map
          (fun final => (setup.protocolReadout final.state,
            fun who => (setup.protocolReadout final.state).elim 0
              (fun state => exclusionUtility setup.program excludedPayoff utility
                (setup.parameterOutcome parameter state) who))) =
        (setup.intendedModel.runBehavioralTerminalFrom setup.intended_bounded.wellFoundedHistories
            intended.strategy setup.intendedProtocol.initHistory).map
          (fun final => (setup.protocolReadout final.state,
            fun who => (setup.protocolReadout final.state).elim 0
              (fun state => utility (setup.parameterOutcome parameter state) who))) :=
  setup.intended_sequentialEquilibrium_extends_to_exclusion finite wellFormed parameter utility
    excludedPayoff below _ _ intended equilibrium

/-- info: 'Vegas.Paper.exclusion_sequential_equilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.exclusion_sequential_equilibrium

open GameTheory.Protocol in
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

open Vegas.SourceProgram Vegas.EventGraphRuntime
  GameTheory.Protocol GameTheory.Enforcement in
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
        (ε + 2 * timing.deferralError * range) source := by
  intro base payoff equilibrium
  exact (isεNash_iff_εBestResponse _ _).mpr
    (service.isεBestResponse_of_clientProfile admission ordered parameter utility sample authentic
      deposit menu timing covered low (fun _ => range) within ε source equilibrium)

/-- info: 'Vegas.Paper.async_client_nash_reflection' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.async_client_nash_reflection

open Vegas.SourceProgram GameTheory.Protocol in
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
    (agrees : (setup.intendedRestriction (CommitmentInterface.values
      setup.program)).ExtendsProfile intended target) (ε : ℝ)
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
        (ε + 2 * timing.deferralError * range)
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
        (ε + 2 * timing.deferralError * range) source) :=
  service.isεNash_rawClientProfile_approximate admission ordered parameter utility sample authentic
    deposit
    nonnegative timing low range within ε source

/-- info: 'Vegas.Paper.async_client_nash_correspondence' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.async_client_nash_correspondence

open Vegas.SourceProgram Vegas.EventGraphRuntime
  GameTheory.Protocol GameTheory.Enforcement in
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
    (agrees : (service.setup.intendedRestriction (CommitmentInterface.values
      service.setup.program)).ExtendsProfile intended source) (ε : ℝ)
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
        (ε + 2 * timing.deferralError * spread)
        (service.clientProfile (CommitmentInterface.values service.setup.program) service.rawMenu
          timing source) ∧
      PMF.WithinTV timing.deferralError
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
    (agrees : (service.setup.intendedRestriction (CommitmentInterface.values
      service.setup.program)).ExtendsProfile intended source) (ε : ℝ)
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
      (service.setup.intendedRestriction (CommitmentInterface.values
        service.setup.program)).ExtendsProfile intended source ∧
      (∀ player, Disclosing service.setup.program
        (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
          source player)) ∧
      IsεNash ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
        service.horizon
          service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
          (fun history who => payoff history.state who)
          (ε + 2 * timing.deferralError * spread)
          (service.clientProfile (CommitmentInterface.values service.setup.program)
            service.rawMenu timing source) ∧
        PMF.WithinTV timing.deferralError
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

open Vegas.SourceProgram in
theorem scheduled_terminal_state_law [IExpr.ResultTypes L]
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (scheduler : (toEventGraph program).PublicScheduler)
    (profile : BehavioralProfile program) (state : State L Γ) :
    ((toEventGraph program).terminalOutcomes scheduler
        (compileEventProfile program profile) (encodeInputs state)).map
      (terminalState program) =
    SourceProgram.run program profile state :=
  Vegas.scheduled_terminalState_law program scheduler profile state

/-- info: 'Vegas.Paper.scheduled_terminal_state_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.scheduled_terminal_state_law

open Vegas.SourceProgram in
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

theorem late_leak_intended_outcome_not_preserved :
    (∃ A : (lateLeakModel .sample false).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain .sample false)
        (lateLeak_terminates .sample false) (lateLeakPayoff .sample false)) ∧
    (∀ A : (lateLeakModel .sample false).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain .sample false)
          (lateLeak_terminates .sample false) (lateLeakPayoff .sample false) →
        lateLeakOutcomeLaw .sample false A.strategy = lateLeakIntendedOutcome) ∧
    (∃ A : (lateLeakModel .sample true).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain .sample true)
        (lateLeak_terminates .sample true) (lateLeakPayoff .sample true)) ∧
    ∀ A : (lateLeakModel .sample true).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain .sample true)
          (lateLeak_terminates .sample true) (lateLeakPayoff .sample true) →
        lateLeakOutcomeLaw .sample true A.strategy ≠ lateLeakIntendedOutcome :=
  lateLeak_intended_outcome_not_preserved _ LateLeakParameters.sample_deferralPays

/-- info: 'Vegas.Paper.late_leak_intended_outcome_not_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.late_leak_intended_outcome_not_preserved

theorem late_leak_not_preserved_when_deferral_pays (G : LateLeakParameters)
    (pays : G.DeferralPays) :
    (∃ A : (lateLeakModel G false).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain G false) (lateLeak_terminates G false)
        (lateLeakPayoff G false)) ∧
    (∀ A : (lateLeakModel G false).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain G false) (lateLeak_terminates G false)
          (lateLeakPayoff G false) →
        lateLeakOutcomeLaw G false A.strategy = lateLeakIntendedOutcome) ∧
    (∃ A : (lateLeakModel G true).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain G true) (lateLeak_terminates G true)
        (lateLeakPayoff G true)) ∧
    ∀ A : (lateLeakModel G true).BehavioralAssessment,
      A.IsSequentialEquilibrium (lateLeak_antichain G true) (lateLeak_terminates G true)
          (lateLeakPayoff G true) →
        lateLeakOutcomeLaw G true A.strategy ≠ lateLeakIntendedOutcome :=
  lateLeak_intended_outcome_not_preserved G pays

/-- info: 'Vegas.Paper.late_leak_not_preserved_when_deferral_pays' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.late_leak_not_preserved_when_deferral_pays

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
      (∃ A : (lateLeakModel ⟨R, D, c, q⟩ true).BehavioralAssessment,
        A.IsSequentialEquilibrium (lateLeak_antichain ⟨R, D, c, q⟩ true)
          (lateLeak_terminates ⟨R, D, c, q⟩ true) (lateLeakPayoff ⟨R, D, c, q⟩ true)) ∧
      ∀ A : (lateLeakModel ⟨R, D, c, q⟩ true).BehavioralAssessment,
        A.IsSequentialEquilibrium (lateLeak_antichain ⟨R, D, c, q⟩ true)
            (lateLeak_terminates ⟨R, D, c, q⟩ true) (lateLeakPayoff ⟨R, D, c, q⟩ true) →
          lateLeakOutcomeLaw ⟨R, D, c, q⟩ true A.strategy ≠ lateLeakIntendedOutcome :=
  lateLeak_not_preserved_for_every_margin R D c reward_pos margin charge

/-- info: 'Vegas.Paper.late_leak_not_preserved_for_every_margin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.late_leak_not_preserved_for_every_margin

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
      (∃ A : (settleLateModel ⟨⟨R, D, c, q⟩, leak, packetCost⟩ true).BehavioralAssessment,
        A.IsSequentialEquilibrium (settleLate_antichain ⟨⟨R, D, c, q⟩, leak, packetCost⟩ true)
          (settleLate_terminates ⟨⟨R, D, c, q⟩, leak, packetCost⟩ true)
          (settleLatePayoff ⟨⟨R, D, c, q⟩, leak, packetCost⟩ true)) ∧
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

open Vegas.EventGraphRuntime GameTheory.Protocol GameTheory.Enforcement in
theorem one_packet_raw_sequential_equilibrium [Fintype Player] [IExpr.ResultTypes L]
    {graph : Vegas.EventGraph Player L} (bounds : MessageBounds graph)
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    [(runtime.reactiveApplication leaks).FiniteNature initial scheduler]
    (service : EvidenceReportService (CountEvidence graph))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : CountEvidenceCoverage service observationRate deliveryRate)
    (utility : (runtime.reactiveApplication leaks).ProtocolState → Player → ℝ)
    (normalized : ∀ state,
      utility ((runtime.reactiveNormalization leaks).state state) = utility state)
    (lower upper deposit : Player → ℝ)
    (lower_le : ∀ state who, lower who ≤ utility state who)
    (le_upper : ∀ state who, utility state who ≤ upper who)
    (deposit_nonnegative : ∀ who, 0 ≤ deposit who)
    (sufficient : ∀ who,
      upper who - lower who ≤ observationRate who * deliveryRate who * deposit who)
    (source : ((bounds.onePacketMenu runtime leaks).information initial horizon
      scheduler).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibrium
      ((bounds.onePacketMenu runtime leaks).decisionInformationAntichain initial horizon
        scheduler)
      ((bounds.onePacketMenu runtime leaks).bounded initial horizon
        scheduler).wellFoundedHistories
      (fun who final => utility final.state who)) :
    let payoff := TerminalAudit.utility utility (runtime.reactiveApplication leaks).stateTraffic
      (runtime.countAudit leaks service.sample) deposit
    let settle := TerminalAudit.settlement utility
      (runtime.reactiveApplication leaks).stateTraffic (runtime.countAudit leaks service.sample)
      deposit
    ∃ target : ((bounds.rawMenu runtime leaks).information initial horizon
        scheduler).BehavioralAssessment,
      target.IsSequentialEquilibrium
        ((bounds.rawMenu runtime leaks).decisionInformationAntichain initial horizon scheduler)
        ((bounds.rawMenu runtime leaks).bounded initial horizon scheduler).wellFoundedHistories
        (fun who final => payoff final.state who) ∧
      (∀ final ∈ (((bounds.rawMenu runtime leaks).information initial horizon
          scheduler).runBehavioral target.strategy (2 * horizon + 1)).support,
        ∀ who, TerminalAudit.charge (runtime.reactiveApplication leaks).stateTraffic
          (runtime.countAudit leaks service.sample) final.state who = 0) ∧
      (((bounds.rawMenu runtime leaks).information initial horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).map
          (fun final => (runtime.reactiveNormalization leaks).state final.state) =
        (((bounds.onePacketMenu runtime leaks).information initial horizon
          scheduler).runBehavioral source.strategy (2 * horizon + 1)).map
          GameTheory.Protocol.ExecutionProtocol.History.state ∧
      (((bounds.rawMenu runtime leaks).information initial horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).bind
          (fun final => (settle final.state).map fun payoffs =>
            ((runtime.reactiveNormalization leaks).state final.state, payoffs)) =
        (((bounds.onePacketMenu runtime leaks).information initial horizon
          scheduler).runBehavioral source.strategy (2 * horizon + 1)).map
          (fun final => (final.state, utility final.state)) := by
  intro payoff settle
  obtain ⟨target, truncated, clean⟩ := bounds.onePacket_raw_sequentialEquilibrium runtime leaks
    initial horizon scheduler service observationRate deliveryRate delivery_nonnegative coverage
    utility normalized lower upper deposit lower_le le_upper deposit_nonnegative sufficient source
    equilibrium
  exact ⟨target, (target.isSequentialEquilibrium_iff_truncated_of_bounded _ _ _
    ((bounds.rawMenu runtime leaks).bounded initial horizon scheduler) _).mpr truncated, clean⟩

/-- info: 'Vegas.Paper.one_packet_raw_sequential_equilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.one_packet_raw_sequential_equilibrium

open Classical in
open Vegas.SourceProgram Vegas.EventGraphRuntime GameTheory.Protocol GameTheory.Enforcement in
theorem recovery_intended_raw_sequential_equilibrium [Fintype Player] [IExpr.ResultTypes L]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (horizon : Nat)
    (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)
    [(recoveryApplication (runtime setup) leaks).FiniteNature
      (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup)))
        (initialLaw setup)) scheduler]
    [Finite setup.intendedProtocol.History]
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    {Public : Type*} {signal : State L setup.context → Public}
    (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal) {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks
      (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup)))
        (initialLaw setup)) horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks
      (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup)))
        (initialLaw setup)) horizon scheduler bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks
      (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup)))
        (initialLaw setup)) horizon scheduler)
    (timely : AsyncTimely (runtime setup) delay bound)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)))
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (service : EvidenceReportService (CountEvidence (graph setup)))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : CountEvidenceCoverage service observationRate deliveryRate)
    (deposit : Player → ℝ) (deposit_nonnegative : ∀ who, 0 ≤ deposit who)
    (sufficient : ∀ who,
      max 0 (max (excludedPayoff who) (upperUtility who)) -
          min 0 (min (excludedPayoff who) (lowerUtility who)) ≤
        observationRate who * deliveryRate who * deposit who) :
    let initial := PMF.map
      (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
    let raw := Recovery.rawMenu (runtime setup) leaks bounds
    let observe := (recoveryApplication (runtime setup) leaks).stateTraffic
    let audit := Recovery.countAudit (runtime setup) leaks service.sample
    let base := recoveryExclusionBase parameter utility excludedPayoff
    let payoff := TerminalAudit.utility base observe audit deposit
    let settle := TerminalAudit.settlement base observe audit deposit
    ∃ target : (raw.information initial horizon scheduler).BehavioralAssessment,
      target.IsSequentialEquilibrium
        (raw.decisionInformationAntichain initial horizon scheduler)
        (raw.bounded initial horizon scheduler).wellFoundedHistories
        (fun who final => payoff final.state who) ∧
      (∀ final ∈ ((raw.information initial horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).support,
        ∀ control, final.state = some control → control.execution.application.excluded = ∅) ∧
      (∀ final ∈ ((raw.information initial horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
      ((raw.information initial horizon scheduler).runBehavioral target.strategy
          (2 * horizon + 1)).bind
          (fun final => (settle final.state).map fun payoffs =>
            (sourceReadout setup leaks (RecoveryProjection.protocolState (runtime setup) leaks
              final.state), payoffs)) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  intro initial raw observe audit base payoff settle
  obtain ⟨target, truncated, clean⟩ :=
    Vegas.recovery_intended_raw_sequentialEquilibrium_preserved parameter utility excludedPayoff
      wellFormed independent observable opportunity inclusion completes timely lowerUtility
      upperUtility lower_le le_upper below intended equilibrium covers coversInputs capacity service
      observationRate deliveryRate delivery_nonnegative coverage deposit deposit_nonnegative
      sufficient
  exact ⟨target, (target.isSequentialEquilibrium_iff_truncated_of_bounded _ _ _
    (raw.bounded initial horizon scheduler) _).mpr truncated, clean⟩

/-- info: 'Vegas.Paper.recovery_intended_raw_sequential_equilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.recovery_intended_raw_sequential_equilibrium

open Classical in
open Vegas.SourceProgram Vegas.EventGraphRuntime GameTheory.Protocol GameTheory.Enforcement in
theorem sequential_phase_intended_raw_sequential_equilibrium [Fintype Player] [IExpr.ResultTypes L]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (horizon : Nat)
    (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
    [(phaseApplication (runtime setup) leaks).FiniteNature
      (SequentialPhase.phaseInitialLaw setup) scheduler]
    [Finite setup.intendedProtocol.History]
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    {Public : Type*} {signal : State L setup.context → Public}
    (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal) {delay bound : (graph setup).EventId → Nat}
    (opportunity : PhaseService.Opportunity (runtime setup) leaks
      (SequentialPhase.phaseInitialLaw setup) horizon scheduler delay)
    (inclusion : PhaseService.ProtectedInclusion (runtime setup) leaks
      (SequentialPhase.phaseInitialLaw setup) horizon scheduler bound)
    (completes : PhaseService.CompletesPlay (runtime setup) leaks
      (SequentialPhase.phaseInitialLaw setup) horizon scheduler)
    (timely : AsyncTimely (runtime setup) delay bound)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)))
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (service : EvidenceReportService (PhaseCount.Evidence (graph setup)))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : PhaseCount.EvidenceCoverage service observationRate deliveryRate)
    (deposit : Player → ℝ) (deposit_nonnegative : ∀ who, 0 ≤ deposit who)
    (sufficient : ∀ who,
      max 0 (max (excludedPayoff who) (upperUtility who)) -
          min 0 (min (excludedPayoff who) (lowerUtility who)) ≤
        observationRate who * deliveryRate who * deposit who) :
    let initial := SequentialPhase.phaseInitialLaw setup
    let raw := PhaseCount.rawMenu (runtime setup) leaks bounds
    let observe := (phaseApplication (runtime setup) leaks).stateTraffic
    let audit := PhaseCount.audit (runtime setup) leaks service.sample
    let base := phaseExclusionBase setup .sequential (runtime setup) leaks
      (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
    let payoff := TerminalAudit.utility base observe audit deposit
    let settle := TerminalAudit.settlement base observe audit deposit
    ∃ target : (raw.information initial horizon scheduler).BehavioralAssessment,
      target.IsSequentialEquilibrium
        (raw.decisionInformationAntichain initial horizon scheduler)
        (raw.bounded initial horizon scheduler).wellFoundedHistories
        (fun who final => payoff final.state who) ∧
      (∀ final ∈ ((raw.information initial horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).support,
        ∀ control, final.state = some control →
          control.execution.application.current.excluded = ∅) ∧
      (∀ final ∈ ((raw.information initial horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
      ((raw.information initial horizon scheduler).runBehavioral target.strategy
          (2 * horizon + 1)).bind
          (fun final => (settle final.state).map fun payoffs =>
            (phaseSourceReadout setup .sequential (runtime setup) leaks final.state, payoffs)) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  intro initial raw observe audit base payoff settle
  obtain ⟨target, truncated, clean⟩ :=
    Vegas.SequentialPhase.intended_raw_sequentialEquilibrium_preserved setup leaks bounds horizon
      scheduler parameter utility excludedPayoff
      wellFormed independent observable opportunity inclusion completes timely lowerUtility
      upperUtility lower_le le_upper below intended equilibrium covers coversInputs capacity service
      observationRate deliveryRate delivery_nonnegative coverage deposit deposit_nonnegative
      sufficient
  exact ⟨target, (target.isSequentialEquilibrium_iff_truncated_of_bounded _ _ _
    (raw.bounded initial horizon scheduler) _).mpr truncated, clean⟩

/-- info: 'Vegas.Paper.sequential_phase_intended_raw_sequential_equilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sequential_phase_intended_raw_sequential_equilibrium

end Vegas.Paper

/-! Program-payment laws and full-deviation equilibria use the same standard axioms. -/

/-- info: 'GameTheory.Enforcement.TerminalAudit.jointSettlement_add_valuation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Enforcement.TerminalAudit.jointSettlement_add_valuation

/-- info: 'GameTheory.Enforcement.TerminalAudit.jointSettlement_sub_valuation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Enforcement.TerminalAudit.jointSettlement_sub_valuation

/-- info: 'Vegas.SourceProgram.Setup.scheduled_setup_payment_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.scheduled_setup_payment_law

/-- info: 'Vegas.SourceProgram.Setup.scheduled_setup_payment_utility_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.scheduled_setup_payment_utility_law

/-- info: 'Vegas.SourceProgram.Setup.eventGame_payment_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.eventGame_payment_approximate_nash_iff

/-- info: 'Vegas.SourceProgram.Setup.parameterEventGame_payment_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.parameterEventGame_payment_approximate_nash_iff

/-- info: 'Vegas.Examples.ProgramPayments.bonus_true_isNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ProgramPayments.bonus_true_isNash

/-- info: 'Vegas.Examples.ProgramPayments.zero_false_isNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ProgramPayments.zero_false_isNash

/-- info: 'Vegas.Examples.ProgramPayments.compiled_isNash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ProgramPayments.compiled_isNash_iff

/-- info: 'Vegas.Examples.ProgramPayments.compiled_bonus_true_isNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ProgramPayments.compiled_bonus_true_isNash

/-- info: 'Vegas.Examples.ProgramPayments.compiled_zero_false_isNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ProgramPayments.compiled_zero_false_isNash

/-- info: 'Vegas.AsyncServiceSpec.paymentExpectedUtility_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.paymentExpectedUtility_eq

/-- info: 'Vegas.AsyncServiceSpec.payment_firstTurnClientProfile_isεNash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.payment_firstTurnClientProfile_isεNash_iff

/-- info: 'Vegas.AsyncServiceSpec.payment_firstTurnClientProfile_settlement_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.payment_firstTurnClientProfile_settlement_law

/-! Deferring clients, concrete runtime equilibria and monetary SE readouts. -/

/-- info: 'GameTheory.optional_monetary_payoff_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.optional_monetary_payoff_bounds

/-- info: 'GameTheory.Enforcement.TerminalAudit.jointSettlement_readout_sub_valuation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Enforcement.TerminalAudit.jointSettlement_readout_sub_valuation

/-- info: 'Vegas.AsyncServiceSpec.payment_within_of_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.payment_within_of_bounds

/-- info: 'Vegas.AsyncServiceSpec.payment_rawClientProfile_isεNash_approximate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.payment_rawClientProfile_isεNash_approximate

/-- info: 'Vegas.SourceProgram.Setup.protocol_payoff_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.protocol_payoff_law

/-- info: 'Vegas.SourceProgram.Setup.protocol_isεNash_of_decoded' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.protocol_isεNash_of_decoded

/-- info: 'Vegas.SourceProgram.Setup.protocol_isεNash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.protocol_isεNash_iff

/-- info: 'Vegas.Examples.ProgramPaymentsRuntime.runtime_isNash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ProgramPaymentsRuntime.runtime_isNash_iff

/-- info: 'Vegas.Examples.ProgramPaymentsRuntime.bonus_true_isNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ProgramPaymentsRuntime.bonus_true_isNash

/-- info: 'Vegas.Examples.ProgramPaymentsRuntime.zero_false_isNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ProgramPaymentsRuntime.zero_false_isNash

/-- info: 'Vegas.Examples.ProgramPaymentsRuntime.bonus_false_not_isNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ProgramPaymentsRuntime.bonus_false_not_isNash

/-- info: 'Vegas.Examples.ProgramPaymentsRuntime.zero_true_not_isNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ProgramPaymentsRuntime.zero_true_not_isNash

/-- info: 'Vegas.Examples.ProgramPaymentsRuntime.settlement_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ProgramPaymentsRuntime.settlement_law

/-- info: 'Vegas.SourceProgram.exclusionUtility_parameterPaymentUtility' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.exclusionUtility_parameterPaymentUtility

/-- info: 'Vegas.SourceProgram.parameterPaymentUtility_exit_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.parameterPaymentUtility_exit_iff

/-- info: 'Vegas.phaseExclusionBase_expect_monetaryUtility' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseExclusionBase_expect_monetaryUtility

/-- info: 'Vegas.recoveryExclusionBase_expect_monetaryUtility' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recoveryExclusionBase_expect_monetaryUtility

/-- info: 'Vegas.ConcurrentPayoffs.programPayments_bounded' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ConcurrentPayoffs.programPayments_bounded

/-- info: 'Vegas.ReservedConcurrentImplementation.auditedUtility_programPayments_eq_expect' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ReservedConcurrentImplementation.auditedUtility_programPayments_eq_expect

/-- info: 'Vegas.concurrent_programPayments_sequential_preservation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.concurrent_programPayments_sequential_preservation

/-- info: 'Vegas.recoveryExclusionBase_valuation_factors' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recoveryExclusionBase_valuation_factors

/-- info: 'Vegas.recovery_jointCashLaw_of_utility_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recovery_jointCashLaw_of_utility_law

/-! Model-independent probability and enforcement extensions retain guarded utility. -/

/-- info: 'Vegas.SourceProgram.Setup.parameterProtocol_isεNash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.parameterProtocol_isεNash_iff

/-- info: 'GameTheory.Protocol.InformationModel.bayesBelief_projection_of_proportional_reach' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Protocol.InformationModel.bayesBelief_projection_of_proportional_reach

/-- info: 'GameTheory.Protocol.InformationModel.ActionRestriction.sequential_equilibrium_extends' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Protocol.InformationModel.ActionRestriction.sequential_equilibrium_extends

/-- info: 'GameTheory.Protocol.InformationModel.BehavioralAssessment.exists_consistent_completion_subsequence' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Protocol.InformationModel.BehavioralAssessment.exists_consistent_completion_subsequence

/-- info: 'GameTheory.exists_pooled_bestResponses' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.exists_pooled_bestResponses

/-- info: 'GameTheory.Math.Probability.abs_expect_sub_le_expect_abs_sub' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Math.Probability.abs_expect_sub_le_expect_abs_sub

/-- info: 'GameTheory.Math.Probability.aemeasurable_of_pmf_pushforward' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Math.Probability.aemeasurable_of_pmf_pushforward

/-- info: 'GameTheory.Math.Probability.lintegral_of_pmf_pushforward' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Math.Probability.lintegral_of_pmf_pushforward

/-- info: 'GameTheory.Enforcement.alarm_detection_le_outside_mass' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Enforcement.alarm_detection_le_outside_mass

/-- info: 'GameTheory.Enforcement.outsideAlarm_detection' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Enforcement.outsideAlarm_detection

/-- info: 'GameTheory.Enforcement.exists_sound_sanction_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Enforcement.exists_sound_sanction_iff

/-- info: 'GameTheory.Math.Probability.sum_weights_div_sum_le_of_bounded_counterpart' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Math.Probability.sum_weights_div_sum_le_of_bounded_counterpart

/-- info: 'GameTheory.Math.Probability.expect_retained_gain_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Math.Probability.expect_retained_gain_le

/-- info: 'GameTheory.Math.Probability.GainComparison.sum_abs_errors' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Math.Probability.GainComparison.sum_abs_errors

/-- info: 'Interaction.ReactiveApplication.round_map_congr' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Interaction.ReactiveApplication.round_map_congr

/-- info: 'Vegas.SourceProgram.exists_pureMixture_run' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.exists_pureMixture_run

/-- info: 'Vegas.Examples.BoundedPaymentAuction.publicPayoffs_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.BoundedPaymentAuction.publicPayoffs_eq

/-- info: 'Vegas.Examples.BoundedPaymentAuction.paymentUtility_eq_economic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.BoundedPaymentAuction.paymentUtility_eq_economic

/-- info: 'Vegas.Examples.BoundedPaymentAuction.compiled_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.BoundedPaymentAuction.compiled_nash_iff

/-- info: 'Vegas.Examples.BoundedPaymentAuction.truthful_not_dominant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.BoundedPaymentAuction.truthful_not_dominant

/-- info: 'GameTheory.Math.Probability.expect_le_of_dominated_readout' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Math.Probability.expect_le_of_dominated_readout

/-- info: 'GameTheory.Math.Probability.withinTV_map_of_partial_classes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Math.Probability.withinTV_map_of_partial_classes

/-- info: 'Interaction.ReactiveApplication.Implementation.realizeJoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Interaction.ReactiveApplication.Implementation.realizeJoint

/-- info: 'Interaction.ReactiveApplication.schedulerMixture_trace_density' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Interaction.ReactiveApplication.schedulerMixture_trace_density

/-- info: 'Vegas.EventGraphRuntime.CompletionService.terminal_of_dependencyHeight' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.CompletionService.terminal_of_dependencyHeight

/-- info: 'Vegas.SourceProgram.ProtocolState.deviation_debt_or_admitted_failure' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.ProtocolState.deviation_debt_or_admitted_failure

/-- info: 'Vegas.decodeObservation?_congr_of_visible' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.decodeObservation?_congr_of_visible

/-- info: 'Vegas.ContextRefsBefore.tail_cons' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ContextRefsBefore.tail_cons

/-- info: 'GameTheory.Protocol.InformationModel.ActionRestriction.isεNash_extends_of_debt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Protocol.InformationModel.ActionRestriction.isεNash_extends_of_debt

/-- info: 'GameTheory.Math.Probability.abs_expect_filter_sub_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Math.Probability.abs_expect_filter_sub_le

/-- info: 'GameTheory.Protocol.IsLegalJoint.update' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.IsLegalJoint.update

/-- info: 'GameTheory.Protocol.ExecutionProtocol.TracePrefix.exists_entering_transition' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Protocol.ExecutionProtocol.TracePrefix.exists_entering_transition

/-- info: 'GameTheory.Protocol.ExecutionProtocol.TracePrefix.exists_last_transition' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Protocol.ExecutionProtocol.TracePrefix.exists_last_transition

/-- info: 'Interaction.ReactiveApplication.PolicyInvariant.run_menu' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Interaction.ReactiveApplication.PolicyInvariant.run_menu

/-- info: 'Interaction.ReactiveApplication.Issued.mem_response_keys' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Interaction.ReactiveApplication.Issued.mem_response_keys

/-- info: 'Vegas.EventGraphRuntime.handle_commitment_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.handle_commitment_iff

/-- info: 'Vegas.EventGraphRuntime.handle_opening_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.handle_opening_iff

/-- info: 'Vegas.ContextRefs.Agrees.cast_config' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ContextRefs.Agrees.cast_config

/-- info: 'Vegas.ContextRefs.Agrees.of_cast_config_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ContextRefs.Agrees.of_cast_config_eq

/-- info: 'Vegas.EventGraphRuntime.CompletionStep.accepted_eq_of_config_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.CompletionStep.accepted_eq_of_config_eq

/-- info: 'Vegas.EventGraphRuntime.ExclusionEvidence.environment' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.ExclusionEvidence.environment

/-- info: 'Vegas.EventGraphRuntime.ExclusionEvidence.commitment_owners' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.ExclusionEvidence.commitment_owners

/-- info: 'Vegas.EventGraphRuntime.phase_attempt_stopped_prefix_metadata' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.phase_attempt_stopped_prefix_metadata

/-- info: 'Vegas.EventGraphRuntime.phase_attempt_stopped_receipt_snapshot' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.phase_attempt_stopped_receipt_snapshot

/-- info: 'Vegas.EventGraphRuntime.phase_attempt_stopped_exclusion_origin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.phase_attempt_stopped_exclusion_origin

/-- info: 'Vegas.AsyncServiceSpec.isεBestResponse_of_clientProfile' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.AsyncServiceSpec.isεBestResponse_of_clientProfile

/-- info: 'Vegas.AsyncServiceSpec.isεBestResponse_clientProfile_of_firstTurn_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.AsyncServiceSpec.isεBestResponse_clientProfile_of_firstTurn_bounds

/-- info: 'Vegas.EventGraphRuntime.Recovery.forbidden_choice_not_supported' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.Recovery.forbidden_choice_not_supported

/-- info: 'Vegas.SourceProgram.Setup.initialLaw_splice_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.initialLaw_splice_mul

/-- info: 'Vegas.SourceProgram.Setup.splice_mem_support' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.splice_mem_support

/-- info: 'Vegas.ownerSwap_priorScaled' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ownerSwap_priorScaled

/-- info: 'Vegas.site_hiddenPublicFiberInputs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.site_hiddenPublicFiberInputs

/-- info: 'Vegas.ownerSwap_priorClosed_given_public' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ownerSwap_priorClosed_given_public

/-- info: 'Vegas.ownerSwap_baseLawAgrees' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ownerSwap_baseLawAgrees

/-- info: 'Vegas.ownerSwap_baseLawAgrees_late' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ownerSwap_baseLawAgrees_late

/-- info: 'Interaction.ReactiveApplication.own_verdict_iff_outputs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Interaction.ReactiveApplication.own_verdict_iff_outputs

/-- info: 'Interaction.ReactiveApplication.audit_collection_continuation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Interaction.ReactiveApplication.audit_collection_continuation

/-- info: 'GameTheory.Enforcement.TerminalAudit.utility_abs_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Enforcement.TerminalAudit.utility_abs_le

/-- info: 'Vegas.EventGraphRuntime.Recovery.ownerCountClean_of_past' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.Recovery.ownerCountClean_of_past

/-- info: 'GameTheory.Math.Probability.abs_sum_mul_sub_le_sum_abs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Math.Probability.abs_sum_mul_sub_le_sum_abs

/-- info: 'GameTheory.Math.Probability.abs_sum_mul_sub_le_half_sum_abs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Math.Probability.abs_sum_mul_sub_le_half_sum_abs

/-- info: 'GameTheory.Math.Probability.sum_abs_div_sum_add_sub_div_sum_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Math.Probability.sum_abs_div_sum_add_sub_div_sum_le

/-- info: 'GameTheory.Math.Probability.abs_normalized_sub_base_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Math.Probability.abs_normalized_sub_base_le

/-- info: 'GameTheory.Math.Probability.abs_normalized_sub_le_of_base_agree' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Math.Probability.abs_normalized_sub_le_of_base_agree

/-- info: 'GameTheory.Math.Probability.NearProductWeights.sum_abs_nativeLaw_sub_sourceLaw_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Math.Probability.NearProductWeights.sum_abs_nativeLaw_sub_sourceLaw_le

/-- info: 'GameTheory.Math.Probability.fiberPosterior_map_readout' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Math.Probability.fiberPosterior_map_readout

/-- info: 'GameTheory.Math.Probability.observation_fiber_mass' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Math.Probability.observation_fiber_mass

/-- info: 'GameTheory.Protocol.InformationModel.tendsto_projectionErrorBound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Protocol.InformationModel.tendsto_projectionErrorBound

/-- info: 'GameTheory.Protocol.InformationModel.sum_abs_projectedBelief_sub_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Protocol.InformationModel.sum_abs_projectedBelief_sub_le

/-- info: 'GameTheory.Protocol.InformationModel.tendsto_sum_abs_projectedBelief_sub' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Protocol.InformationModel.tendsto_sum_abs_projectedBelief_sub

/-- info: 'PMF.split_converges' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  PMF.split_converges

/-- info: 'GameTheory.Protocol.InformationModel.BehavioralAssessment.perturb_strategy_converges' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Protocol.InformationModel.BehavioralAssessment.perturb_strategy_converges

/-- info: 'GameTheory.Protocol.InformationModel.consistent_update_of_reach_invariant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Protocol.InformationModel.consistent_update_of_reach_invariant

/-- info: 'GameTheory.Math.Probability.bind_branch_lower' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Math.Probability.bind_branch_lower

/-- info: 'GameTheory.Math.Probability.bind_same_initial_domination' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Math.Probability.bind_same_initial_domination

/-- info: 'PMF.WithinTV.of_bind_point' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  PMF.WithinTV.of_bind_point

/-- info: 'Vegas.EventGraphRuntime.handle_opening_config_step' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.handle_opening_config_step

/-- info: 'Vegas.EventGraphRuntime.handle_config_mem_step' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.handle_config_mem_step

/-- info: 'Vegas.EventGraphRuntime.handle_commitment_vacant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.handle_commitment_vacant

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.empty_processing_prefix_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.ReservedEpoch.empty_processing_prefix_law

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.empty_processing_segment' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.ReservedEpoch.empty_processing_segment

/-- info: 'Vegas.CompiledSuffix.commitPrefix_bind_interval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.CompiledSuffix.commitPrefix_bind_interval

/-- info: 'Vegas.recordsEntry_transition' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.recordsEntry_transition

/-- info: 'Vegas.splice_public_initial_inputs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.splice_public_initial_inputs

/-- info: 'Vegas.public_signal_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.public_signal_preserved

/-- info: 'Vegas.initial_public_cells_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.initial_public_cells_eq

/-- info: 'Vegas.initial_public_inputs_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.initial_public_inputs_eq

/-- info: 'Vegas.drawn_splicePoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.drawn_splicePoint

/-- info: 'Vegas.forcedAgent_of_splice' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.forcedAgent_of_splice

/-- info: 'Vegas.keyedRecord_near' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.keyedRecord_near

/-- info: 'Vegas.recovery_intended_raw_sequentialEquilibrium_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.recovery_intended_raw_sequentialEquilibrium_preserved

/-- info: 'Vegas.firstTurnTiming_deferralError' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.firstTurnTiming_deferralError

/-- info: 'Vegas.TurnTiming.deferralError_mem_Icc' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.TurnTiming.deferralError_mem_Icc

/-- info: 'Vegas.TurnTiming.deferralError_le_sum' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.TurnTiming.deferralError_le_sum

/-- info: 'Vegas.overriddenTurnProfile_fix_roundsFrom_bind_lower' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.overriddenTurnProfile_fix_roundsFrom_bind_lower

/-- info: 'Vegas.overriddenTurnProfile_roundsFrom_bind_lower' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.overriddenTurnProfile_roundsFrom_bind_lower

/-- info: 'Vegas.overriddenTurnProfile_roundsFrom_bind_within' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.overriddenTurnProfile_roundsFrom_bind_within

/-- info: 'Vegas.serviceTurnPolicy_roundsFrom_bind_within' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.serviceTurnPolicy_roundsFrom_bind_within

/-- info: 'Vegas.deviatedTurnProfile_roundsFrom_bind_within' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.deviatedTurnProfile_roundsFrom_bind_within

/-- info: 'Vegas.sourceServiceTurnPolicy_execution_settlement_lawError' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.sourceServiceTurnPolicy_execution_settlement_lawError

/-- info: 'Vegas.EventGraph.readyIndependent_of_ownerless' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraph.readyIndependent_of_ownerless

/-- info: 'Vegas.EventGraph.ReadyIndependent.policyStepThen_map_semanticKey_comm' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraph.ReadyIndependent.policyStepThen_map_semanticKey_comm

/-- info: 'Vegas.EventGraph.ReadyIndependent.runPlan_normalized_semantic_eq_canonical' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraph.ReadyIndependent.runPlan_normalized_semantic_eq_canonical

/-- info: 'Vegas.EventGraph.ReadyIndependent.runPolicies_store_eq_canonical' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraph.ReadyIndependent.runPolicies_store_eq_canonical

/-- info: 'Vegas.EventGraph.BarrierOrdered.readyIndependent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraph.BarrierOrdered.readyIndependent

/-- info: 'Vegas.EventGraph.RevealRelaxedOrdered.readyIndependent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraph.RevealRelaxedOrdered.readyIndependent

/-- info: 'Vegas.sequentialRuntimePhasePlan_singleton' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.sequentialRuntimePhasePlan_singleton

/-- info: 'Vegas.sequentialRuntimePhaseAt_events' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.sequentialRuntimePhaseAt_events

/-- info: 'Vegas.EventGraphRuntime.RuntimePhase.ready_mem_sequential' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.RuntimePhase.ready_mem_sequential

/-- info: 'Vegas.EventGraphRuntime.PhaseRuntimeState.settle_global_quiescent_sequential' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseRuntimeState.settle_global_quiescent_sequential

/-- info: 'Vegas.EventGraphRuntime.phaseApplication_initial_quiescent_sequential' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.phaseApplication_initial_quiescent_sequential

/-- info: 'Vegas.EventGraphRuntime.RuntimePhase.no_survivors_of_miss' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.RuntimePhase.no_survivors_of_miss

/-- info: 'Vegas.EventGraphRuntime.RuntimePhase.drain_eq_completeAutomatic_of_singleton' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.RuntimePhase.drain_eq_completeAutomatic_of_singleton

/-- info: 'Vegas.EventGraphRuntime.PhaseRuntimeState.settle_generation_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseRuntimeState.settle_generation_eq

/-- info: 'Vegas.EventGraphRuntime.RuntimePhase.restore_completeAutomatic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.RuntimePhase.restore_completeAutomatic

/-- info: 'Vegas.RecoveryOnePacket.intended_sequentialEquilibrium_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.RecoveryOnePacket.intended_sequentialEquilibrium_preserved

/-- info: 'Vegas.EventGraphRuntime.PhaseRuntimeState.environment_expire_singleton' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseRuntimeState.environment_expire_singleton

/-- info: 'Vegas.EventGraphRuntime.phaseClearMetadata_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.phaseClearMetadata_history

/-- info: 'Vegas.EventGraphRuntime.phaseRetired_excluded_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.phaseRetired_excluded_history

/-- info: 'Vegas.EventGraphRuntime.PhaseRuntimeState.settle_current_eq_drain' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseRuntimeState.settle_current_eq_drain

/-- info: 'Vegas.EventGraphRuntime.PhaseRecoveryProjection.observe_state' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseRecoveryProjection.observe_state

/-- info: 'Vegas.EventGraphRuntime.PhaseRecoveryProjection.knownPackets' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseRecoveryProjection.knownPackets

/-- info: 'Vegas.EventGraphRuntime.PhaseRecoveryProjection.normalization_projected' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseRecoveryProjection.normalization_projected

/-- info: 'Vegas.EventGraphRuntime.PhaseRecoveryProjection.rawMenu_projected' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseRecoveryProjection.rawMenu_projected

/-- info: 'Vegas.EventGraphRuntime.PhaseRecoveryProjection.normalizedMenu_projected' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseRecoveryProjection.normalizedMenu_projected

/-- info: 'Vegas.RecoveryOnePacket.initialized_limit_no_exclusion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.RecoveryOnePacket.initialized_limit_no_exclusion

/-- info: 'Vegas.EventGraphRuntime.phaseAcceptedCheckpointFrame_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.phaseAcceptedCheckpointFrame_history

/-- info: 'Vegas.EventGraphRuntime.phaseCheckpointAlignment_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.phaseCheckpointAlignment_history

/-- info: 'Vegas.EventGraphRuntime.phaseCheckpointExcluded_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.phaseCheckpointExcluded_history

/-- info: 'Vegas.EventGraphRuntime.SequentialPhaseObservation.publicView_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.SequentialPhaseObservation.publicView_history

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.clear_network_packets_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseCount.clear_network_packets_history

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.permits_eq_countPermits_of_static' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseCount.permits_eq_countPermits_of_static

/-- info: 'Vegas.recovery_intended_raw_sequentialEquilibrium_of_onePacket' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.recovery_intended_raw_sequentialEquilibrium_of_onePacket

/-- info: 'Interaction.ReactiveApplication.SubmissionNormalization.recall_submissionCount' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication.SubmissionNormalization in
#print axioms recall_submissionCount

/-- info: 'Vegas.EventGraphRuntime.PhaseService.ProtectedInclusion.clear_native_onePacket' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.EventGraphRuntime.PhaseService.ProtectedInclusion in
#print axioms clear_native_onePacket

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.onePacketMenu_closed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.EventGraphRuntime.PhaseCount in
#print axioms onePacketMenu_closed

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.onePacket_alias_sequentialEquilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.EventGraphRuntime.PhaseCount in
#print axioms onePacket_alias_sequentialEquilibrium

/-- info: 'Vegas.EventGraphRuntime.SequentialPhasePlayerInformation.information_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.EventGraphRuntime.SequentialPhasePlayerInformation in
#print axioms information_history

/-- info: 'Vegas.EventGraphRuntime.phase_environment_current_sequential_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.EventGraphRuntime in
#print axioms phase_environment_current_sequential_history

/-- info: 'Vegas.EventGraphRuntime.phase_handle_current_sequential_clear_onePacket_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.EventGraphRuntime in
#print axioms phase_handle_current_sequential_clear_onePacket_history

/-- info: 'Vegas.EventGraphRuntime.PhaseRecoveryProjection.recovery_onePacket_mem_of_normal_phase_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.EventGraphRuntime.PhaseRecoveryProjection in
#print axioms recovery_onePacket_mem_of_normal_phase_history

/-- info: 'Vegas.countPermits_localEnvelope_ready_of_clear_trace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms countPermits_localEnvelope_ready_of_clear_trace

/-- info: 'Vegas.EventGraphRuntime.inclusionFitsDeadline_of_unrecalled_turn' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.EventGraphRuntime in
#print axioms inclusionFitsDeadline_of_unrecalled_turn

/-- info: 'Interaction.MessageNetwork.mapPayload_includePending' depends on axioms:
[propext] -/
#guard_msgs (whitespace := lax) in
open Interaction.MessageNetwork in
#print axioms mapPayload_includePending

/-- info: 'Interaction.ReactiveApplication.ResponseMenu.recorded_environment_prefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication.ResponseMenu in
#print axioms recorded_environment_prefix

/-- info: 'Vegas.EventGraphRuntime.SequentialPhaseSchedulerInformation.scheduler_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.EventGraphRuntime.SequentialPhaseSchedulerInformation in
#print axioms scheduler_history

/-- info: 'Vegas.phase_onePacket_mem_of_recovery_paired_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms phase_onePacket_mem_of_recovery_paired_history

/-- info: 'GameTheory.Protocol.InformationModel.bayesBelief_eq_stopped_fiber_map' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms bayesBelief_eq_stopped_fiber_map

/-- info: 'GameTheory.Protocol.InformationModel.runBehavioralUntil_map_eq_of_step_maps' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms runBehavioralUntil_map_eq_of_step_maps

/-- info: 'Interaction.ReactiveApplication.ResponseMenu.decision_predecessor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication.ResponseMenu in
#print axioms decision_predecessor

/-- info: 'Vegas.EventGraphRuntime.PhaseRecoveryProjection.transition_projected_clear_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.EventGraphRuntime.PhaseRecoveryProjection in
#print axioms transition_projected_clear_history

/-- info: 'Vegas.exists_canonical_phase_of_clear_recovery_trace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms exists_canonical_phase_of_clear_recovery_trace

/-- info: 'Vegas.phaseExclusionBase_eq_recoveryExclusionBase' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms phaseExclusionBase_eq_recoveryExclusionBase

/-- info: 'Vegas.phase_owesFailure_expected_payoff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms phase_owesFailure_expected_payoff

/-- info: 'Vegas.SequentialPhase.exists_consistent_completion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms exists_consistent_completion

/-- info: 'Vegas.SequentialPhase.recoveryComparisonStrategy_at_clear' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms recoveryComparisonStrategy_at_clear

/-- info: 'Vegas.EventGraphRuntime.SequentialPhaseRecoveryPolicy.exists_recovery_site_bayes_state_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.EventGraphRuntime.SequentialPhaseRecoveryPolicy in
#print axioms exists_recovery_site_bayes_state_eq

/-- info: 'Vegas.phase_firstActivation_inclusionFits' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms phase_firstActivation_inclusionFits

/-- info: 'Vegas.phase_prescribed_packet_settles' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms phase_prescribed_packet_settles

/-- info: 'Vegas.SequentialPhase.comparisonPolicy_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms comparisonPolicy_history

/-- info: 'Vegas.SequentialPhase.component_comparison_run_until_exclusion_or_guard_map_state' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms component_comparison_run_until_exclusion_or_guard_map_state

/-- info: 'Vegas.SequentialPhase.component_comparison_bayes_state_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms component_comparison_bayes_state_eq

/-- info: 'Vegas.OnePacketComparison.assembled_foreign_exit_mass_le_rank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.OnePacketComparison in
#print axioms assembled_foreign_exit_mass_le_rank

/-- info: 'Vegas.SequentialPhase.nativeComparison_foreign_exit_mass_le_rank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms nativeComparison_foreign_exit_mass_le_rank

/-- info: 'Vegas.SequentialPhase.native_pendingBinding_sourceKernel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms native_pendingBinding_sourceKernel

/-- info: 'Vegas.phase_expect_sub_debt_stopped_le_foreign_exit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms phase_expect_sub_debt_stopped_le_foreign_exit

/-- info: 'Vegas.phase_belief_expect_abs_sub_debt_stopped_le_foreign_exit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms phase_belief_expect_abs_sub_debt_stopped_le_foreign_exit

/-- info: 'Vegas.SequentialPhase.component_local_comparison_run_until_exclusion_or_guard_map_state' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms component_local_comparison_run_until_exclusion_or_guard_map_state

/-- info: 'Vegas.completionValue_expect_affine_of_completed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms completionValue_expect_affine_of_completed

/-- info: 'Vegas.pendingBinding_sourceKernel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms pendingBinding_sourceKernel

/-- info: 'Vegas.phase_boundary_firstActivation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms phase_boundary_firstActivation

/-- info: 'Vegas.EventGraphRuntime.due_owner_recalled_turn_of_opportunity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.EventGraphRuntime in
#print axioms due_owner_recalled_turn_of_opportunity

/-- info: 'Vegas.recovery_debt_stopped_expect_eq_native' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms recovery_debt_stopped_expect_eq_native

/-- info: 'GameTheory.Protocol.InformationModel.sequentialEquilibrium_of_copied_comparisons_limit_of_lawError' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms sequentialEquilibrium_of_copied_comparisons_limit_of_lawError

/-- info: 'GameTheory.Protocol.InformationModel.exists_sequentialEquilibrium_limit_of_pooled_comparisons_of_lawError' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms exists_sequentialEquilibrium_limit_of_pooled_comparisons_of_lawError

/-- info: 'GameTheory.Protocol.InformationModel.runBehavioralTerminalFrom_map_eq_until_of_stable_readout' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms runBehavioralTerminalFrom_map_eq_until_of_stable_readout

/-- info: 'Vegas.SequentialPhase.component_initialized_readout_withinTV' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms component_initialized_readout_withinTV

/-- info: 'Vegas.SequentialPhase.initialized_limit_no_exclusion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms initialized_limit_no_exclusion

/-- info: 'Vegas.SequentialPhase.component_initialized_masked_state_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms component_initialized_masked_state_law

/-- info: 'Vegas.SequentialPhase.localValue_native_comparison_error_vanishes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms localValue_native_comparison_error_vanishes

/-- info: 'Vegas.SequentialPhase.keyed_component_value_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms keyed_component_value_bounds

/-- info: 'Vegas.SequentialPhase.component_owing_localGain_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms component_owing_localGain_eq_zero

/-- info: 'Vegas.SequentialPhase.canonical_raw_sequentialEquilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms canonical_raw_sequentialEquilibrium

/-- info: 'Vegas.SequentialPhase.nativeComparison_pending_value_affine' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms nativeComparison_pending_value_affine

/-- info: 'Vegas.SequentialPhase.nativeComparison_local_completion_value_sub_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms nativeComparison_local_completion_value_sub_le

/-- info: 'Vegas.SequentialPhase.recovery_bayes_debt_stopped_eq_native' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms recovery_bayes_debt_stopped_eq_native

/-- info: 'GameTheory.Protocol.PublicScheduler.expanded_sequentialEquilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.PublicScheduler in
#print axioms expanded_sequentialEquilibrium

/-- info: 'Vegas.SequentialPhase.nativeComparison_nonlate_pending_comparisons' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms nativeComparison_nonlate_pending_comparisons

/-- info: 'Vegas.SequentialPhase.phase_strategy_native_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms phase_strategy_native_law

/-- info: 'Vegas.SequentialPhase.localGain_native_comparison_error_vanishes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms localGain_native_comparison_error_vanishes

/-- info: 'Vegas.SequentialPhase.keyed_component_mixture_gain_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms keyed_component_mixture_gain_bounds

/-- info: 'Vegas.SequentialPhase.keyed_main_value_sub_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms keyed_main_value_sub_le

/-- info: 'Vegas.SequentialPhase.keyed_component_gain_le_of_mixtures' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms keyed_component_gain_le_of_mixtures

/-- info: 'Vegas.SequentialPhase.localGain_eq_zero_of_unpending_notOwing' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms localGain_eq_zero_of_unpending_notOwing

/-- info: 'Vegas.SequentialPhase.keyed_local_comparisons' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms keyed_local_comparisons

/-- info: 'Vegas.SequentialPhase.nonlate_local_comparisons' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms nonlate_local_comparisons

/-- info: 'Vegas.SequentialPhase.local_comparisons' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms local_comparisons

/-- info: 'Vegas.SequentialPhase.intended_sequentialEquilibrium_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms intended_sequentialEquilibrium_preserved

/-- info: 'Vegas.SequentialPhase.intended_raw_sequentialEquilibrium_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SequentialPhase in
#print axioms intended_raw_sequentialEquilibrium_preserved

/-- info: 'Vegas.RecoveryOnePacket.unintendedCommitment_stopped_value' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.RecoveryOnePacket in
#print axioms unintendedCommitment_stopped_value

/-- info: 'Vegas.RecoveryOnePacket.unintendedCommitment_value_sub_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.RecoveryOnePacket in
#print axioms unintendedCommitment_value_sub_le

/-- info: 'GameTheory.Math.abs_le_sum_interval_width' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math in
#print axioms abs_le_sum_interval_width

/-- info: 'Interaction.EvidenceReportService.complete_deliveredEvidence' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.EvidenceReportService in
#print axioms complete_deliveredEvidence

/-- info: 'Interaction.EvidenceReportService.complete_sample' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.EvidenceReportService in
#print axioms complete_sample

/-- info: 'Interaction.EvidenceReportService.complete_observation_mass' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.EvidenceReportService in
#print axioms complete_observation_mass

/-- info: 'Interaction.EvidenceReportService.complete_delivery_mass' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.EvidenceReportService in
#print axioms complete_delivery_mass

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.completeEvidence_coverage' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.EventGraphRuntime.PhaseCount in
#print axioms completeEvidence_coverage

/-- info: 'Vegas.Examples.SequentialPhaseService.opportunity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SequentialPhaseService in
#print axioms opportunity

/-- info: 'Vegas.Examples.SequentialPhaseService.protectedInclusion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SequentialPhaseService in
#print axioms protectedInclusion

/-- info: 'Vegas.Examples.SequentialPhaseService.completesPlay' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SequentialPhaseService in
#print axioms completesPlay

/-- info: 'Vegas.Examples.SequentialPhaseService.timely' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SequentialPhaseService in
#print axioms timely

/-- info: 'Vegas.Examples.SequentialPhaseService.physical_contract' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SequentialPhaseService in
#print axioms physical_contract

/-- info: 'Vegas.Examples.SequentialPhaseService.outputValues' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SequentialPhaseService in
#print axioms outputValues

/-- info: 'Vegas.Examples.SequentialPhaseService.inputValues' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SequentialPhaseService in
#print axioms inputValues

/-- info: 'Vegas.Examples.SequentialPhaseService.candidateCapacity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SequentialPhaseService in
#print axioms candidateCapacity

/-- info: 'Vegas.Examples.SequentialPhaseService.nonconstant_payment' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SequentialPhaseService in
#print axioms nonconstant_payment

/-- info: 'Vegas.Examples.SequentialPhaseService.terminal_execution_exists' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SequentialPhaseService in
#print axioms terminal_execution_exists

/-- info: 'Vegas.Examples.SequentialPhaseService.independent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SequentialPhaseService in
#print axioms independent

/-- info: 'Vegas.Examples.SequentialPhaseService.observable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SequentialPhaseService in
#print axioms observable

/-- info: 'Vegas.Examples.SequentialPhaseService.wellFormed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SequentialPhaseService in
#print axioms wellFormed

/-- info: 'Vegas.Examples.SequentialPhaseService.initialState_supported' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SequentialPhaseService in
#print axioms initialState_supported

/-- info: 'Vegas.Examples.SequentialPhaseService.owner_decision_exists' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SequentialPhaseService in
#print axioms owner_decision_exists

/-- info: 'Vegas.RecoveryOnePacket.recovery_unintendedCommitment_stopped_value' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.RecoveryOnePacket in
#print axioms recovery_unintendedCommitment_stopped_value

/-- info: 'Vegas.RecoveryOnePacket.recovery_unintendedCommitment_value_sub_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.RecoveryOnePacket in
#print axioms recovery_unintendedCommitment_value_sub_le

/-- info: 'Vegas.Examples.SequentialPhaseService.sourceUtility_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SequentialPhaseService in
#print axioms sourceUtility_bounds

/-- info: 'Vegas.Examples.SequentialPhaseService.sourceUtility_eq_programTransfer' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SequentialPhaseService in
#print axioms sourceUtility_eq_programTransfer

/-- info: 'Vegas.Examples.SequentialPhaseService.intendedFallbackAction_mem' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SequentialPhaseService in
#print axioms intendedFallbackAction_mem

/-- info: 'Vegas.Examples.SequentialPhaseService.intended_equilibrium_exists' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SequentialPhaseService in
#print axioms intended_equilibrium_exists

/-- info: 'Vegas.Examples.SequentialPhaseService.funded_raw_equilibrium_exists' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SequentialPhaseService in
#print axioms funded_raw_equilibrium_exists

/-- info: 'GameTheory.Protocol.InformationModel.abs_expect_runBehavioralUntil_sub_le_of_potential' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms abs_expect_runBehavioralUntil_sub_le_of_potential

/-- info: 'GameTheory.Protocol.InformationModel.abs_expect_runBehavioralUntil_sub_le_of_stepTV_potential' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms abs_expect_runBehavioralUntil_sub_le_of_stepTV_potential

/-- info: 'GameTheory.Protocol.InformationModel.abs_expect_runBehavioralUntil_sub_le_of_stepTV' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms abs_expect_runBehavioralUntil_sub_le_of_stepTV

/-- info: 'GameTheory.Math.Probability.kernelPosterior_toReal_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math.Probability in
#print axioms kernelPosterior_toReal_apply

/-- info: 'GameTheory.Math.Probability.kernelPosterior_weight_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math.Probability in
#print axioms kernelPosterior_weight_le

/-- info: 'GameTheory.Math.Probability.payoffIntegrable_kernelPosterior' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math.Probability in
#print axioms payoffIntegrable_kernelPosterior

/-- info: 'GameTheory.Math.Probability.payoffIntegrable_kernelLikelihood_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math.Probability in
#print axioms payoffIntegrable_kernelLikelihood_mul

/-- info: 'GameTheory.Math.Probability.payoffIntegrable_bind_kernelPosterior' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math.Probability in
#print axioms payoffIntegrable_bind_kernelPosterior

/-- info: 'GameTheory.Math.Probability.expect_kernelPosterior' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math.Probability in
#print axioms expect_kernelPosterior

/-- info: 'GameTheory.Math.Probability.expect_kernelPosterior_sub_expect' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math.Probability in
#print axioms expect_kernelPosterior_sub_expect

/-- info: 'GameTheory.Math.Probability.expect_kernelPosterior_nonpos' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math.Probability in
#print axioms expect_kernelPosterior_nonpos

/-- info: 'GameTheory.Math.Probability.abs_expect_kernelPosterior_sub_expect_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math.Probability in
#print axioms abs_expect_kernelPosterior_sub_expect_le

/-- info: 'GameTheory.Math.Probability.abs_expect_kernelPosterior_changed_gain_sub_expect_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math.Probability in
#print axioms abs_expect_kernelPosterior_changed_gain_sub_expect_le

/-- info: 'GameTheory.Math.Probability.kernelPosterior_eq_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math.Probability in
#print axioms kernelPosterior_eq_iff

/-- info: 'GameTheory.Math.Probability.kernelPosterior_eq_of_constant_likelihood' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math.Probability in
#print axioms kernelPosterior_eq_of_constant_likelihood

/-- info: 'GameTheory.Math.Probability.expect_eq_of_observable_span' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math.Probability in
#print axioms expect_eq_of_observable_span

/-- info: 'GameTheory.Math.Probability.abs_expect_sub_le_of_observable_span' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math.Probability in
#print axioms abs_expect_sub_le_of_observable_span

/-- info: 'GameTheory.Math.Probability.expect_bind_eq_of_closed_observables' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math.Probability in
#print axioms expect_bind_eq_of_closed_observables

/-- info: 'GameTheory.Math.Probability.expect_iterate_eq_of_closed_observables' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math.Probability in
#print axioms expect_iterate_eq_of_closed_observables

/-- info: 'GameTheory.Protocol.Context.ofBelief_gain_eq_expect' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.Context in
#print axioms ofBelief_gain_eq_expect

/-- info: 'GameTheory.Protocol.Context.ofBelief_gain_after_observation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.Context in
#print axioms ofBelief_gain_after_observation

/-- info: 'GameTheory.Protocol.Context.isLocallyOptimal_after_observation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.Context in
#print axioms isLocallyOptimal_after_observation

/-- info: 'GameTheory.Protocol.InformationModel.BehavioralAssessment.IsSequentiallyConsistent.belief_prod_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms BehavioralAssessment.IsSequentiallyConsistent.belief_prod_eq

/-- info: 'GameTheory.GameForm.play_ignorePublicSignal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.GameForm in
#print axioms play_ignorePublicSignal

/-- info: 'GameTheory.GameForm.play_update_ignorePublicSignal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.GameForm in
#print axioms play_update_ignorePublicSignal

/-- info: 'GameTheory.GameForm.isNash_ignorePublicSignal_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.GameForm in
#print axioms isNash_ignorePublicSignal_iff

/-- info: 'GameTheory.Protocol.ExecutionProtocol.trace_length_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.ExecutionProtocol in
#print axioms trace_length_le

/-- info: 'GameTheory.Protocol.ExecutionProtocol.cumulative_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.ExecutionProtocol in
#print axioms cumulative_bounds

/-- info: 'GameTheory.Protocol.ExecutionProtocol.cumulative_mono' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.ExecutionProtocol in
#print axioms cumulative_mono

/-- info: 'GameTheory.Protocol.ExecutionProtocol.cumulative_integrable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.ExecutionProtocol in
#print axioms cumulative_integrable

/-- info: 'GameTheory.Protocol.InformationModel.expectedCharge_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms expectedCharge_bounds

/-- info: 'GameTheory.Protocol.InformationModel.expectedCharge_integrable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms expectedCharge_integrable

/-- info: 'GameTheory.Protocol.InformationModel.expectedCharge_drift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms expectedCharge_drift

/-- info: 'Interaction.ReactiveApplication.responseCharge_le_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication in
#print axioms responseCharge_le_one

/-- info: 'Interaction.ReactiveApplication.remainingResponses_le_rank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication in
#print axioms remainingResponses_le_rank

/-- info: 'Interaction.ReactiveApplication.remainingResponses_step' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication in
#print axioms remainingResponses_step

/-- info: 'Interaction.ReactiveApplication.ResponseMenu.active_card' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication.ResponseMenu in
#print axioms active_card

/-- info: 'Interaction.ReactiveApplication.ResponseMenu.remainingResponses_le_horizon_add_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication.ResponseMenu in
#print axioms remainingResponses_le_horizon_add_one

/-- info: 'Interaction.ReactiveApplication.ResponseMenu.run_one_eq_of_no_actor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication.ResponseMenu in
#print axioms run_one_eq_of_no_actor

/-- info: 'Interaction.ReactiveApplication.responseCount_step' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication in
#print axioms responseCount_step

/-- info: 'Interaction.ReactiveApplication.responseCount_add_remainingResponses_step' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication in
#print axioms responseCount_add_remainingResponses_step

/-- info: 'Interaction.ReactiveApplication.responseCount_add_remainingResponses_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication in
#print axioms responseCount_add_remainingResponses_le

/-- info: 'Interaction.ReactiveApplication.ResponseMenu.cumulativeCharge_eq_responseCount' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication.ResponseMenu in
#print axioms cumulativeCharge_eq_responseCount

/-- info: 'Interaction.ReactiveApplication.ResponseMenu.responseCount_le_horizon' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication.ResponseMenu in
#print axioms responseCount_le_horizon

/-- info: 'Interaction.ReactiveApplication.ResponseMenu.responseCount_integrable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication.ResponseMenu in
#print axioms responseCount_integrable

/-- info: 'Interaction.ReactiveApplication.ResponseMenu.expectedCharge_eq_expectedResponses' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication.ResponseMenu in
#print axioms expectedCharge_eq_expectedResponses

/-- info: 'Interaction.ReactiveApplication.ResponseMenu.stopped_responseCount_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication.ResponseMenu in
#print axioms stopped_responseCount_bounds

/-- info: 'Interaction.ReactiveApplication.ResponseMenu.expectedResponses_bounds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication.ResponseMenu in
#print axioms expectedResponses_bounds

/-- info: 'Interaction.ReactiveApplication.ResponseMenu.expectedResponses_integrable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication.ResponseMenu in
#print axioms expectedResponses_integrable

/-- info: 'Interaction.ReactiveApplication.ResponseMenu.expectedResponses_drift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication.ResponseMenu in
#print axioms expectedResponses_drift

/-- info: 'Vegas.onePacket_step_withinTV_honest' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms onePacket_step_withinTV_honest

/-- info: 'Vegas.onePacket_stopped_expect_sub_le_of_potential' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms onePacket_stopped_expect_sub_le_of_potential

/-- info: 'Vegas.onePacket_stopped_expect_sub_le_remainingResponses' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms onePacket_stopped_expect_sub_le_remainingResponses

/-- info: 'Vegas.onePacket_stopped_expect_sub_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms onePacket_stopped_expect_sub_le

/-- info: 'Vegas.onePacket_stopped_withinTV_honest' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms onePacket_stopped_withinTV_honest

/-- info: 'Vegas.onePacket_stopped_expect_sub_le_expectedResponses' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms onePacket_stopped_expect_sub_le_expectedResponses

/-- info: 'Vegas.onePacket_terminal_withinTV_honest' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms onePacket_terminal_withinTV_honest

/-- info: 'Vegas.onePacket_bounded_withinTV_honest' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms onePacket_bounded_withinTV_honest

/-- info: 'Vegas.onePacket_bounded_readout_exclusion_withinTV' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms onePacket_bounded_readout_exclusion_withinTV

/-- info: 'Vegas.onePacket_stopped_withinTV_of_history_retention' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms onePacket_stopped_withinTV_of_history_retention

/-- info: 'Vegas.onePacket_mixture_stopped_withinTV_honest' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms onePacket_mixture_stopped_withinTV_honest

/-- info: 'GameTheory.Protocol.InformationModel.abs_expect_runBehavioralUntil_sub_le_of_stepTV_interval_potential' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms abs_expect_runBehavioralUntil_sub_le_of_stepTV_interval_potential

/-- info: 'GameTheory.Protocol.InformationModel.runBehavioralTerminalFrom_eq_until_false' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms runBehavioralTerminalFrom_eq_until_false

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_local_phase_value_sub_le_of_boundary_values' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.RecoveryOnePacket in
#print axioms nativeComparison_local_phase_value_sub_le_of_boundary_values

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_local_completion_value_sub_le_of_boundary_values' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.RecoveryOnePacket in
#print axioms nativeComparison_local_completion_value_sub_le_of_boundary_values

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_pending_value_affine_of_boundary_values' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.RecoveryOnePacket in
#print axioms nativeComparison_pending_value_affine_of_boundary_values

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_keyed_value_sub_le_of_pending' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.RecoveryOnePacket in
#print axioms nativeComparison_keyed_value_sub_le_of_pending

/-- info: 'Vegas.RecoveryOnePacket.nativeComparison_keyed_value_bounds_of_pending' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.RecoveryOnePacket in
#print axioms nativeComparison_keyed_value_bounds_of_pending

/-- info: 'VegasTests.RepeatedActivation.repeatedActivation_round' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open VegasTests.RepeatedActivation in
#print axioms repeatedActivation_round

/-- info: 'VegasTests.RepeatedActivation.repeatedActivation_run_two' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open VegasTests.RepeatedActivation in
#print axioms repeatedActivation_run_two

/-- info: 'VegasTests.RepeatedActivation.responses_exceed_source_events' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open VegasTests.RepeatedActivation in
#print axioms responses_exceed_source_events

/-- info: 'GameTheory.Math.exists_affine_ray' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math in
#print axioms exists_affine_ray

/-- info: 'GameTheory.Math.InvariantObservables.orbitSpan_le' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math.InvariantObservables in
#print axioms orbitSpan_le

/-- info: 'GameTheory.Math.InvariantObservables.comparison_word_eq_zero' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math.InvariantObservables in
#print axioms comparison_word_eq_zero

/-- info: 'GameTheory.Math.InvariantObservables.exists_finite_closed_basis' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math.InvariantObservables in
#print axioms exists_finite_closed_basis

/-- info: 'GameTheory.Protocol.PrivateStrategy.runBehavioral_value_mem' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.PrivateStrategy in
#print axioms runBehavioral_value_mem

/-- info: 'GameTheory.Protocol.PrivateStrategy.expect_runBehavioral_eq_of_closed_observables' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.PrivateStrategy in
#print axioms expect_runBehavioral_eq_of_closed_observables

/-- info: 'GameTheory.Protocol.PrivateStrategy.runBehavioral_joint_readout_eq_of_closed_observables' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.PrivateStrategy in
#print axioms runBehavioral_joint_readout_eq_of_closed_observables

/-- info: 'GameTheory.Protocol.InformationModel.powerProfile_historyReachWeight' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms powerProfile_historyReachWeight

/-- info: 'GameTheory.Protocol.InformationModel.powerProfile_history_scaled_tendsto' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms powerProfile_history_scaled_tendsto

/-- info: 'GameTheory.Protocol.InformationModel.powerAssessment_consistent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms powerAssessment_consistent

/-- info: 'GameTheory.Protocol.InformationModel.powerCertificate_consistent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms powerCertificate_consistent

/-- info: 'GameTheory.Protocol.InformationModel.expectedCharge_drift_of_abs_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms expectedCharge_drift_of_abs_le

/-- info: 'GameTheory.Protocol.InformationModel.expect_runBehavioralUntil_sub_eq_expectedCharge' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms expect_runBehavioralUntil_sub_eq_expectedCharge

/-- info: 'GameTheory.Math.Probability.expect_eq_on_observable_span' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Math.Probability in
#print axioms expect_eq_on_observable_span

/-- info: 'GameTheory.Protocol.PrivateStrategy.runBehavioral_joint_readout_eq_of_certificate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.PrivateStrategy in
#print axioms runBehavioral_joint_readout_eq_of_certificate

/-! Mathematical results cited in the maintained manuscript, including prose invariants. -/

/-- info: 'Vegas.SourceProgram.Setup.terminal_guards_hold' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SourceProgram.Setup in
#print axioms terminal_guards_hold

/-- info: 'Vegas.sourceObserve_privateInput' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms sourceObserve_privateInput

/-- info: 'Vegas.SourceProgram.Setup.revealed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SourceProgram.Setup in
#print axioms revealed

/-- info: 'Vegas.canonical_setup_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms canonical_setup_law

/-- info: 'Vegas.scheduled_setup_deviation_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms scheduled_setup_deviation_law

/-- info: 'Vegas.rosterScheduler_asyncContract' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms rosterScheduler_asyncContract

/-- info: 'Vegas.Examples.CommitRevealAuction.truthful_not_dominant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.CommitRevealAuction in
#print axioms truthful_not_dominant

/-- info: 'Vegas.Examples.CommitRevealAuction.translated_truthful_not_dominant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.CommitRevealAuction in
#print axioms translated_truthful_not_dominant

/-- info: 'Vegas.AsyncServiceSpec.clientSettlementLaw_withinTV' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.AsyncServiceSpec in
#print axioms clientSettlementLaw_withinTV

/-- info: 'Vegas.AsyncServiceSpec.clientSettlementLaw_event_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.AsyncServiceSpec in
#print axioms clientSettlementLaw_event_lower_bound

/-- info: 'Vegas.AsyncServiceSpec.clientSettlementLaw_expect_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.AsyncServiceSpec in
#print axioms clientSettlementLaw_expect_lower_bound
