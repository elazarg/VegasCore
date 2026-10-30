/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.Safety
import Vegas.Compile.EventGraphScheduling
import Vegas.Compile.EventGraphDeviation
import Vegas.Game.EventCompilation
import Vegas.Game.CompilerCorrectness
import Vegas.Pending.GraphRefinement
import Vegas.Game.IntendedPreservation
import Vegas.Game.IntendedNash
import Vegas.Game.AsyncServiceRawNash
import Vegas.Game.AsyncClientObservables
import Vegas.Game.ProgramPaymentAsyncNash
import Vegas.Game.OnePacketExtension
import Vegas.Game.RecoverySequentialCompilation
import Vegas.Game.RecoveryClientObservables
import Vegas.Game.RecoveryPaymentPreservation
import Vegas.Game.ServiceRosterAsync
import Vegas.Examples.LateLeak
import Vegas.Examples.CommitRevealAuction
import Vegas.Examples.BoundedPaymentAuction
import Vegas.Examples.OddsEvensRecoveryRawEquilibrium
import Vegas.Examples.OddsEvensFullSource

/-! # Paper theorems

Paper-facing statements and the other mathematical results the maintained
manuscript states, each pinned to the three standard axioms. The build rejects
`sorry`, and the source policy rejects axiom declarations and trust escape
hatches throughout the tree, so results the manuscript does not state need no
pin here.

-/

noncomputable section

namespace Vegas.Paper

open GameTheory Vegas Interaction
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

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
    (keepsReveals : service.mode ≠ .concurrentReveals)
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
        (ε + 2 * timing.deferralError * range) source) := by
  have ordered : (serviceGraph service.setup service.mode).BarrierOrdered :=
    service.setup.eventGraph.withMode_barrierOrdered
      (toEventGraph_barrierOrdered service.setup.program) service.mode keepsReveals
  exact service.isεNash_rawClientProfile_approximate admission ordered parameter utility sample
    authentic deposit
    nonnegative timing low range within ε source

/-- info: 'Vegas.Paper.async_client_nash_correspondence' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.async_client_nash_correspondence

open Vegas.SourceProgram Vegas.EventGraphRuntime
  GameTheory.Protocol GameTheory.Enforcement in
theorem intended_async_client_nash [Fintype Player] [IExpr.ResultTypes L]
    {Parameter : Type} (service : AsyncServiceSpec Player L)
    (keepsReveals : service.mode ≠ .concurrentReveals)
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
              (fun state => utility (service.setup.parameterOutcome parameter state) who)))) := by
  have ordered : (serviceGraph service.setup service.mode).BarrierOrdered :=
    service.setup.eventGraph.withMode_barrierOrdered
      (toEventGraph_barrierOrdered service.setup.program) service.mode keepsReveals
  exact service.intended_rawClientProfile_isεNash ordered wellFormed parameter utility forfeit range
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
    (keepsReveals : service.mode ≠ .concurrentReveals)
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
        ε source := by
  have ordered : (serviceGraph service.setup service.mode).BarrierOrdered :=
    service.setup.eventGraph.withMode_barrierOrdered
      (toEventGraph_barrierOrdered service.setup.program) service.mode keepsReveals
  exact service.isεNash_firstTurnClientProfile_iff admission ordered parameter utility sample
    authentic deposit
    nonnegative turns low range within ε source

/-- info: 'Vegas.Paper.async_first_turn_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.async_first_turn_nash_iff

open Vegas.SourceProgram Vegas.EventGraphRuntime
  GameTheory.Protocol GameTheory.Enforcement in
theorem intended_async_first_turn_nash [Fintype Player] [IExpr.ResultTypes L]
    {Parameter : Type} (service : AsyncServiceSpec Player L)
    (keepsReveals : service.mode ≠ .concurrentReveals)
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
              (fun state => utility (service.setup.parameterOutcome parameter state) who))) := by
  have ordered : (serviceGraph service.setup service.mode).BarrierOrdered :=
    service.setup.eventGraph.withMode_barrierOrdered
      (toEventGraph_barrierOrdered service.setup.program) service.mode keepsReveals
  exact service.intended_firstTurnClientProfile_isεNash ordered wellFormed parameter utility forfeit
    range sample authentic deposit nonnegative turns low spread within intended source
    agrees ε equilibrium

/-- info: 'Vegas.Paper.intended_async_first_turn_nash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_async_first_turn_nash

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
    utility normalized lower upper deposit (fun history who => lower_le history.state who)
    (fun history who => le_upper history.state who) deposit_nonnegative sufficient source equilibrium
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
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (horizon : Nat)
    (scheduler : (recoveryApplication runtime leaks).Scheduler)
    [(recoveryApplication runtime leaks).FiniteNature
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
    (opportunity : Recovery.Opportunity runtime leaks
      (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup)))
        (initialLaw setup)) horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion runtime leaks
      (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup)))
        (initialLaw setup)) horizon scheduler bound)
    (completes : Recovery.CompletesPlay runtime leaks
      (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup)))
        (initialLaw setup)) horizon scheduler)
    (timely : AsyncTimely runtime delay bound)
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
    let raw := Recovery.rawMenu runtime leaks bounds
    let observe := (recoveryApplication runtime leaks).stateTraffic
    let audit := Recovery.countAudit runtime leaks service.sample
    let base := recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff
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
            (sourceReadout setup runtime leaks (RecoveryProjection.protocolState runtime leaks
              final.state), payoffs)) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  intro initial raw observe audit base payoff settle
  obtain ⟨target, truncated, clean⟩ :=
    Vegas.recovery_intended_raw_sequentialEquilibrium_preserved (runtime := runtime) parameter
      utility excludedPayoff
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

/-- info: 'Vegas.RecoveryClientSpec.compile_correct' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryClientSpec.compile_correct

/-- info: 'Vegas.RecoveryClientCompilation.clients_sequentiallyRational' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryClientCompilation.clients_sequentiallyRational

/-- info: 'Vegas.RecoveryClientSpec.compile_ledger_correct' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryClientSpec.compile_ledger_correct

/-- info: 'Vegas.RecoveryClientCompilation.ledgerClients_sequentiallyRational' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryClientCompilation.ledgerClients_sequentiallyRational

/-- info: 'Vegas.RecoveryClientSpec.intended_outcomeLaws_subset' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryClientSpec.intended_outcomeLaws_subset

/-- info: 'Vegas.RecoveryClientCompilation.clients_postprocessLaw' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoveryClientCompilation.clients_postprocessLaw

end Vegas.Paper

/-! Mathematical results cited in the maintained manuscript, including prose invariants. -/

/-- info: 'Vegas.SourceProgram.Setup.intendedState_trace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.intendedState_trace

/-- info: 'Vegas.SourceProgram.Setup.failedReveals_eq_zero_of_intendedState' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.failedReveals_eq_zero_of_intendedState

/-- info: 'Vegas.asyncDeviation_readout_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.asyncDeviation_readout_law

/-- info: 'Vegas.AsyncServiceSpec.payment_firstTurnClientProfile_settlement_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.payment_firstTurnClientProfile_settlement_law

/-- info: 'Vegas.Examples.BoundedPaymentAuction.truthful_not_dominant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.BoundedPaymentAuction.truthful_not_dominant

/-- info: 'Vegas.Recovery.intended_raw_programPayments_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Recovery.intended_raw_programPayments_preserved

/-- info: 'Vegas.Examples.OddsEvensRecoveryRaw.intended_equilibrium_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.OddsEvensRecoveryRaw.intended_equilibrium_preserved

/-- info: 'Vegas.Examples.OddsEvensRecoveryRaw.fair_equilibrium_exists' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.OddsEvensRecoveryRaw.fair_equilibrium_exists

/-- info: 'Vegas.Examples.OddsEvens.fair_full_source_equilibrium_exists' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.OddsEvens.fair_full_source_equilibrium_exists

/-- info: 'Vegas.Examples.OddsEvensRecoveryRaw.collection_probability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.OddsEvensRecoveryRaw.collection_probability

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

/-- info: 'Vegas.EventGraphRuntime.reactive_protocol_graph_refinement' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.reactive_protocol_graph_refinement

/-- info: 'Vegas.AsyncServiceSpec.firstTurnClientProfile_graph_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.firstTurnClientProfile_graph_law

/-- info: 'Vegas.AsyncServiceSpec.firstTurnClientProfile_outcome_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.firstTurnClientProfile_outcome_law

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

/-- info: 'Vegas.rosterScheduler_asyncTimely' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.rosterScheduler_asyncTimely

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
