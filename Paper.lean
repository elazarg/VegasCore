/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions
import Vegas.Game
import Vegas.Examples.LateLeak

/-! # Paper theorems

Paper-facing statements and their checked axiom dependencies.
Detailed dependency regressions live in `VegasTests.AxiomAudit`.
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
        (ε + 2 * (∑ event, timing.deferral event) * range) source :=
  service.isεNash_of_clientProfile admission ordered parameter utility sample authentic deposit menu
    timing covered
    low range within ε source

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
      target.IsSequentialEquilibriumFor
        ((bounds.rawMenu runtime leaks).decisionInformationAntichain initial horizon scheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun history => payoff history.state who) (2 * horizon + 1)) ∧
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
          (fun final => (final.state, utility final.state)) :=
  bounds.onePacket_raw_sequentialEquilibrium runtime leaks initial horizon scheduler service
    observationRate deliveryRate delivery_nonnegative coverage utility normalized lower upper
    deposit lower_le le_upper deposit_nonnegative sufficient source equilibrium

/-- info: 'Vegas.Paper.one_packet_raw_sequential_equilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.one_packet_raw_sequential_equilibrium

end Vegas.Paper
