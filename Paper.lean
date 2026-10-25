/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions
import Interaction.ReactiveImplementation
import Interaction.ReactivePolicyMenuInvariant
import Interaction.ReactiveProvenance
import Interaction.ReactiveSchedulerDensity
import Vegas.Pending.CompletionService
import Vegas.Compile
import Vegas.Game
import Vegas.Examples.LateLeak
import Vegas.Examples.ProgramPayments
import Vegas.Examples.ProgramPaymentsRuntime
import Vegas.Examples.BoundedPaymentAuction

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
