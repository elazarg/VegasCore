module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.PublicationPolicy
public import Vegas.Source.Safety
public import Vegas.Game.IntendedNash
public import Vegas.Game.PrefixClientNash
public import Vegas.Game.SourcePrefixForfeit
public import Vegas.Game.IntendedSourceProfile
public import Vegas.Game.SourceProtocolNash
public import Vegas.Compile.EventGraphScheduling
public import Vegas.EventGraph.ExecutionOrder
public import Vegas.Game.EventCompilation
public import Interaction.DelayedEvidence
public import Vegas.Pending.CountReportObservation
public import Vegas.Pending.CountReportSelection
public import Vegas.Pending.GraphRefinement
public import Vegas.Game.SourceServiceFirstTurnCompletion
public import Vegas.Game.AsyncServiceRawNash
public import Vegas.Game.AsyncClientObservables
public import Vegas.Game.ProgramPaymentAsyncNash
public import Vegas.Game.ClientCompiler
public import Vegas.Game.ClientAssessmentFidelity
public import Vegas.Game.PaymentPreservation
public import Vegas.Examples.OddsEvensRawEquilibrium
public import Vegas.Examples.OddsEvensConcurrentNative
public import Vegas.Examples.BoundedAuctionService
public import Vegas.Examples.OddsEvensFullSource
public import Vegas.Examples.CommitRevealAuction
public import Vegas.Examples.ConcurrentRevealOrderLaw
public import Vegas.Examples.LateLeak

@[expose] public section

/-! # Claims of the maintained paper

The definitions below name the observations, payoffs and execution laws used
in the claims. Each theorem has its complete statement and an adjacent guarded
check of its exact standard-axiom dependencies.
-/

noncomputable section

section SourceAndGraph

/-! # Source games, graph execution and the ordinary compiler

A source configuration retains typed cells, the public default history and the
players' own choices. The observation `sourceObserve who state` copies public data
and publication results unchanged. For a commitment or private-input cell it is
`some (state.get cell)` when `cell.owner = who`, and `none` otherwise. A decision
view also carries the public default history and that player's own-choice recall.

An obligation retains a guard and references to its subject and inputs.
`Vegas.SourceProgram.Obligation.accepts` applies the guard decision
`Vegas.SourceGuard.accepts` to their published results:
a failed subject or code-read input discharges the obligation; otherwise the
Boolean guard code must hold. This is publication safety, independently of
whether the binding was admitted or an owner chose to disclose.
-/


universe u

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
open Interaction Vegas.EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A complete terminal source configuration, including its default record. -/
abbrev Vegas.Paper.TerminalConfig (setup : Setup (Player := Player) (L := L)) :=
  Config Player L setup.program.terminalCtx

open Vegas.Paper

/-- Every reveal owned by every player succeeded in the public result. -/
def Vegas.Paper.NoFailedReveals (setup : Setup (Player := Player) (L := L))
    (terminal : TerminalConfig setup) : Prop :=
  ∀ who, setup.program.failedReveals who (setup.program.publicOutcome terminal) = 0

/-- The terminal revelation references determined by the source syntax. -/
abbrev Vegas.Paper.terminalRevelations (setup : Setup (Player := Player) (L := L)) :
    Revelations setup.program.terminalCtx :=
  setup.program.finalRevelations (Revelations.initial setup.context)

/-- A retained guard accepts the terminal published subject and inputs. -/
def Vegas.Paper.PublishedGuardAccepts (setup : Setup (Player := Player) (L := L))
    (terminal : TerminalConfig setup) (obligation : Obligation setup.program.terminalCtx) : Prop :=
  obligation.accepts (terminalRevelations setup) terminal.state = true

/-- A terminal payoff lifted through the protocol's optional readout. -/
def Vegas.Paper.readoutPayoff (setup : Setup (Player := Player) (L := L))
    (payoff : TerminalConfig setup → Player → ℝ) (state : setup.ProtocolState) (who : Player) : ℝ :=
  (setup.protocolReadout state).elim 0 (fun terminal => payoff terminal who)

/-- The joint observation of the terminal configuration and each player's payoff. -/
def Vegas.Paper.readoutAndPayoff (setup : Setup (Player := Player) (L := L))
    (payoff : TerminalConfig setup → Player → ℝ) (state : setup.ProtocolState) :=
  (setup.protocolReadout state, readoutPayoff setup payoff state)

section Source

variable (setup : Setup (Player := Player) (L := L))

/-- A source instruction completes once; the extra step draws the initial state. -/
theorem Vegas.Paper.protocol_bounded (admission : CommitmentInterface setup.program) :
    (setup.executionProtocol admission).BoundedHorizon (setup.program.instructionCount + 1) :=
  setup.protocol_bounded admission

/-- info: 'Vegas.Paper.protocol_bounded' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.protocol_bounded

/-- Play over source histories has the written-order law, for every legal
protocol profile and every admitted source profile. -/
theorem Vegas.Paper.protocol_readout_law [Finite Player]
    (admission : CommitmentInterface setup.program) :
    (∀ profile : Profile (setup.informationModel admission).behavioralSignature,
      ((setup.informationModel admission).runBehavioral profile
          (setup.program.instructionCount + 1)).map
          (fun final => setup.protocolReadout final.state) =
        (setup.run (setup.decodeBehavioralProfile admission profile)).map some) ∧
    (∀ (profile : BehavioralProfile setup.program)
      (permitted : ∀ who, (profile who).Admitted setup.program admission),
      ((setup.informationModel admission).runBehavioral
          (setup.encodeBehavioralProfile admission profile permitted)
          (setup.program.instructionCount + 1)).map
          (fun final => setup.protocolReadout final.state) =
        (setup.run profile).map some) :=
  setup.protocol_readout_law admission

/-- info: 'Vegas.Paper.protocol_readout_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.protocol_readout_law

theorem Vegas.Paper.intended_no_failed_reveals (wellFormed : setup.WellFormed)
    (history : setup.intendedProtocol.History) {terminal : TerminalConfig setup}
    (read : setup.protocolReadout history.state = some terminal) :
    NoFailedReveals setup terminal :=
  setup.intended_no_failed_reveals wellFormed history read

/-- info: 'Vegas.Paper.intended_no_failed_reveals' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_no_failed_reveals

theorem Vegas.Paper.revealed {owner : Player} {payload : L.Ty} {name : VarId}
    (binding : HasVar setup.program.terminalCtx name (.commitment owner payload)) :
    (terminalRevelations setup binding).isRevealed = true :=
  setup.revealed binding

/-- info: 'Vegas.Paper.revealed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.revealed

theorem Vegas.Paper.terminal_guards_hold (profile : BehavioralProfile setup.program)
    (terminal : TerminalConfig setup) (supported : terminal ∈ (setup.run profile).support)
    (obligation : Obligation setup.program.terminalCtx)
    (retained : obligation ∈ setup.program.finalRegistry []) :
    PublishedGuardAccepts setup terminal obligation :=
  setup.terminal_guards_hold profile terminal supported obligation retained

/-- info: 'Vegas.Paper.terminal_guards_hold' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.terminal_guards_hold

section Forfeits

variable [Finite Player] {Parameter : Type}
  (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)

/-- The original utility evaluated on the initial parameter and public source result. -/
def Vegas.Paper.sourcePayoff (terminal : TerminalConfig setup) : Player → ℝ :=
  utility (setup.parameterOutcome parameter terminal)

/-- The original utility minus the specified penalty for each failed reveal. -/
def Vegas.Paper.forfeitPayoff (forfeit : ℝ) (terminal : TerminalConfig setup) : Player → ℝ :=
  setup.program.forfeitUtility forfeit utility (setup.parameterOutcome parameter terminal)

variable (finite : setup.program.FiniteBindingTypes) [initialFinite : setup.FiniteInitialLaw]
  (wellFormed : setup.WellFormed) (forfeit : ℝ)

local notation "horizon" => setup.program.instructionCount + 1
local notation "base" => sourcePayoff setup parameter utility
local notation "penalized" => forfeitPayoff setup parameter utility forfeit

include finite wellFormed initialFinite in
theorem Vegas.Paper.intended_forfeit_isεNash_preserved
    (admission : CommitmentInterface setup.program)
    (range : setup.TerminalPayoffSpread admission parameter utility forfeit)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel admission).behavioralSignature)
    (agrees : (setup.intendedRestriction admission).ExtendsProfile intended target) (ε : ℝ)
    (equilibrium : IsεNash (setup.intendedModel.toBehavioralGameForm horizon)
      (fun final => readoutPayoff setup base final.state) ε intended) :
    IsεNash ((setup.informationModel admission).toBehavioralGameForm horizon)
        (fun final => readoutPayoff setup penalized final.state) ε target ∧
      (∀ final ∈ ((setup.informationModel admission).runBehavioral target horizon).support,
        ∀ terminal,
        setup.protocolReadout final.state = some terminal → NoFailedReveals setup terminal) ∧
      ((setup.informationModel admission).runBehavioral target horizon).map
          (fun final => readoutAndPayoff setup penalized final.state) =
        (setup.intendedModel.runBehavioral intended horizon).map
          (fun final => readoutAndPayoff setup base final.state) := by
  exact setup.intended_forfeit_isεNash_preserved admission finite wellFormed parameter utility
    forfeit range intended target agrees ε equilibrium

/-- info: 'Vegas.Paper.intended_forfeit_isεNash_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_forfeit_isεNash_preserved

include finite wellFormed initialFinite in
theorem Vegas.Paper.intended_forfeit_sequentialEquilibrium_preserved
    (admission : CommitmentInterface setup.program)
    (range : setup.TerminalPayoffSpread admission parameter utility forfeit)
    (intendedTerminates : setup.intendedProtocol.WellFoundedHistories)
    (sourceTerminates : (setup.executionProtocol admission).WellFoundedHistories)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      intendedTerminates (fun who final => readoutPayoff setup base final.state who)) :
    ∃ target : (setup.informationModel admission).BehavioralAssessment,
      target.IsSequentialEquilibrium (setup.decision_antichain admission) sourceTerminates
        (fun who final => readoutPayoff setup penalized final.state who) ∧
      (setup.intendedRestriction admission).ExtendsProfile intended.strategy target.strategy ∧
      (∀ who site, target.belief who ((setup.intendedRestriction admission).site who site) =
        (intended.belief who site).map
          ((setup.intendedRestriction admission).informationHistory who site)) ∧
      (∀ final ∈ ((setup.informationModel admission).runBehavioralTerminalFrom sourceTerminates
          target.strategy (setup.executionProtocol admission).initHistory).support,
        ∀ terminal, setup.protocolReadout final.state = some terminal →
          NoFailedReveals setup terminal) ∧
      ((setup.informationModel admission).runBehavioralTerminalFrom sourceTerminates
          target.strategy (setup.executionProtocol admission).initHistory).map
          (fun final => readoutAndPayoff setup penalized final.state) =
        (setup.intendedModel.runBehavioralTerminalFrom intendedTerminates intended.strategy
          setup.intendedProtocol.initHistory).map
          (fun final => readoutAndPayoff setup base final.state) := by
  exact setup.intended_forfeit_sequentialEquilibrium_preserved admission finite wellFormed
    parameter utility forfeit range intendedTerminates sourceTerminates intended equilibrium

/-- info: 'Vegas.Paper.intended_forfeit_sequentialEquilibrium_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_forfeit_sequentialEquilibrium_preserved

local notation "forfeiture" => CommitmentInterface.forfeiture setup.program

include finite wellFormed initialFinite in
/-- Prescribed clients of every disclosing intended extension preserve its Nash error,
complete configuration/payoff law and clean play for all dependency choices retaining
reveal-relaxed barriers, including concurrent private bindings and reveals. -/
theorem Vegas.Paper.intended_concurrent_forfeit
    (deps : setup.dataflowGraph.Dependencies)
    (relaxed : (setup.dataflowGraph.withDependencies deps).RevealRelaxedOrdered)
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel forfeiture).behavioralSignature)
    (agrees : (setup.intendedRestriction forfeiture).ExtendsProfile intended target) (ε : ℝ)
    (equilibrium : IsεNash (setup.intendedModel.toBehavioralGameForm horizon)
      (fun final => readoutPayoff setup base final.state) ε intended)
    (disclosing : ∀ who, Disclosing setup.program
      (setup.decodeBehavioralProfile forfeiture target who))
    (scheduler : (setup.dataflowGraph.withDependencies deps).PublicScheduler) :
    IsεNash ((setup.dataflowGraph.withDependencies deps).gameForm (setup.graphInputs deps)
        scheduler) (setup.graphForfeitPayoff deps parameter utility forfeit) ε
        (compilePrescribedProfile setup.program deps
          (setup.decodeBehavioralProfile forfeiture target)) ∧
      (∀ outcome ∈ (((setup.dataflowGraph.withDependencies deps).gameForm (setup.graphInputs deps)
          scheduler).play (compilePrescribedProfile setup.program deps
            (setup.decodeBehavioralProfile forfeiture target))).support,
        (setup.graphReadout deps outcome).defaulted = ∅ ∧
          NoFailedReveals setup (setup.graphReadout deps outcome)) ∧
      (((setup.dataflowGraph.withDependencies deps).gameForm (setup.graphInputs deps)
          scheduler).play (compilePrescribedProfile setup.program deps
            (setup.decodeBehavioralProfile forfeiture target))).map
          (fun outcome => (some (setup.graphReadout deps outcome),
            setup.graphForfeitPayoff deps parameter utility forfeit outcome)) =
        (setup.intendedModel.runBehavioral intended horizon).map
          (fun final => (setup.protocolReadout final.state,
            readoutPayoff setup base final.state)) ∧
      (setup.dataflowGraph.withDependencies deps).SubmitsBindings
        (compilePrescribedProfile setup.program deps
          (setup.decodeBehavioralProfile forfeiture target)) ∧
      (∀ who event (actor : (setup.dataflowGraph.withDependencies deps).actor? event = some who),
        (publication : ((setup.dataflowGraph.withDependencies deps).outputLayout
          event).IsPublication) →
          ∀ (observation : (setup.dataflowGraph.withDependencies deps).PlayerObservation who)
            (active : who ∉ observation.defaulted),
            compilePrescribedProfile setup.program deps
              (setup.decodeBehavioralProfile forfeiture target) who event actor observation active =
                PMF.pure (EventGraph.EventField.openAction _ publication)) := by
  obtain ⟨nash, clean, law⟩ := setup.compileIntendedExtension_forfeit deps relaxed finite wellFormed
    parameter utility forfeit range intended target agrees disclosing ε equilibrium scheduler
  exact ⟨nash, clean, law,
    compilePrescribedProfile_submits setup.program deps _,
    fun who event actor publication observation active =>
      compilePrescribedProfile_publication setup.program deps _ disclosing who event actor
        publication observation active⟩

/-- info: 'Vegas.Paper.intended_concurrent_forfeit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_concurrent_forfeit

local notation "bindingRevealDeps" =>
  setup.dataflowGraph.bindingDependencies setup.revealDependencies

local notation "bindingRevealGraph" =>
  setup.dataflowGraph.withDependencies bindingRevealDeps

include finite wellFormed initialFinite in
/-- The combined binding/reveal relaxation is a concrete instance of intended
forfeiture preservation, with the complete payoff law and prescribed-client discipline. -/
theorem Vegas.Paper.intended_bindingReveal_forfeit
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel forfeiture).behavioralSignature)
    (agrees : (setup.intendedRestriction forfeiture).ExtendsProfile intended target) (ε : ℝ)
    (equilibrium : IsεNash (setup.intendedModel.toBehavioralGameForm horizon)
      (fun final => readoutPayoff setup base final.state) ε intended)
    (disclosing : ∀ who, Disclosing setup.program
      (setup.decodeBehavioralProfile forfeiture target who))
    (scheduler : (bindingRevealGraph).PublicScheduler) :
    IsεNash ((bindingRevealGraph).gameForm (setup.graphInputs bindingRevealDeps) scheduler)
        (setup.graphForfeitPayoff bindingRevealDeps parameter utility forfeit) ε
        (compilePrescribedProfile setup.program bindingRevealDeps
          (setup.decodeBehavioralProfile forfeiture target)) ∧
      (∀ outcome ∈ (((bindingRevealGraph).gameForm (setup.graphInputs bindingRevealDeps)
          scheduler).play (compilePrescribedProfile setup.program bindingRevealDeps
            (setup.decodeBehavioralProfile forfeiture target))).support,
        (setup.graphReadout bindingRevealDeps outcome).defaulted = ∅ ∧
          NoFailedReveals setup (setup.graphReadout bindingRevealDeps outcome)) ∧
      (((bindingRevealGraph).gameForm (setup.graphInputs bindingRevealDeps) scheduler).play
          (compilePrescribedProfile setup.program bindingRevealDeps
            (setup.decodeBehavioralProfile forfeiture target))).map
          (fun outcome => (some (setup.graphReadout bindingRevealDeps outcome),
            setup.graphForfeitPayoff bindingRevealDeps parameter utility forfeit outcome)) =
        (setup.intendedModel.runBehavioral intended horizon).map
          (fun final => (setup.protocolReadout final.state,
            readoutPayoff setup base final.state)) ∧
      (bindingRevealGraph).SubmitsBindings
        (compilePrescribedProfile setup.program bindingRevealDeps
          (setup.decodeBehavioralProfile forfeiture target)) ∧
      (∀ who event (actor : (bindingRevealGraph).actor? event = some who),
        (publication : ((bindingRevealGraph).outputLayout event).IsPublication) →
          ∀ (observation : (bindingRevealGraph).PlayerObservation who)
            (active : who ∉ observation.defaulted),
            compilePrescribedProfile setup.program bindingRevealDeps
              (setup.decodeBehavioralProfile forfeiture target) who event actor observation active =
                PMF.pure (EventGraph.EventField.openAction _ publication)) := by
  have relaxed : (bindingRevealGraph).RevealRelaxedOrdered :=
    setup.informationGraph.relaxReveals.relaxBindings_revealRelaxedOrdered
      (setup.informationGraph.relaxReveals_revealRelaxedOrdered
        (toInformationGraph_barrierOrdered setup.program).revealRelaxedOrdered)
  exact Vegas.Paper.intended_concurrent_forfeit (setup := setup) (parameter := parameter)
    (utility := utility) (finite := finite) (wellFormed := wellFormed) (forfeit := forfeit)
    bindingRevealDeps relaxed range intended target agrees ε equilibrium disclosing scheduler

/-- info: 'Vegas.Paper.intended_bindingReveal_forfeit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_bindingReveal_forfeit

include finite wellFormed initialFinite in
/-- Effective-opening source-prefix clients preserve the intended Nash error,
actual full readout/payoff law and clean play under concurrent bindings and reveals. -/
theorem Vegas.Paper.intended_concurrent_ledger
    (deps : setup.dataflowGraph.Dependencies)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel forfeiture).behavioralSignature)
    (agrees : (setup.intendedRestriction forfeiture).ExtendsProfile intended target) (ε : ℝ)
    (equilibrium : IsεNash (setup.intendedModel.toBehavioralGameForm horizon)
      (fun final => readoutPayoff setup base final.state) ε intended)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player
      (WitnessedPacket (serviceGraph setup deps)))
    {ledgerHorizon turns : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) ledgerHorizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound) :
    let app := serviceApplication setup deps duration leaks
    let clients := serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps)
      (effectiveOpening (compilePrescribedProfile setup.program deps
        (setup.decodeBehavioralProfile forfeiture target)))
    let native := app.roundsFrom (serviceInitialLaw setup deps) scheduler clients ledgerHorizon
    IsεNash (serviceGame setup deps duration leaks scheduler ledgerHorizon)
        (setup.graphForfeitConfigPayoff deps parameter utility forfeit) ε clients ∧
      (∀ final ∈ native.support,
        final.application.config.cut.Terminal ∧ final.application.config.defaulted = ∅ ∧
          ∃ terminal, serviceRankedReadout setup deps duration leaks (app.finished final) =
            some terminal ∧ NoFailedReveals setup terminal) ∧
      native.map (fun final =>
        (serviceRankedReadout setup deps duration leaks (app.finished final),
          setup.graphForfeitConfigPayoff deps parameter utility forfeit
            final.application.config)) =
        (setup.intendedModel.runBehavioral intended horizon).map
          (fun final => (setup.protocolReadout final.state,
            readoutPayoff setup base final.state)) := by
  exact native_compileIntendedExtension_preserved setup deps relaxed finite wellFormed parameter
    utility forfeit range intended target agrees ε equilibrium duration leaks (turns := turns)
    scheduler bound contract timely

/-- info: 'Vegas.Paper.intended_concurrent_ledger' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_concurrent_ledger

include finite wellFormed initialFinite in
/-- Effective-opening source-prefix clients preserve the intended Nash error,
actual full readout/payoff law and clean play under concurrent bindings and reveals. -/
theorem Vegas.Paper.intended_bindingReveal_ledger
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel forfeiture).behavioralSignature)
    (agrees : (setup.intendedRestriction forfeiture).ExtendsProfile intended target) (ε : ℝ)
    (equilibrium : IsεNash (setup.intendedModel.toBehavioralGameForm horizon)
      (fun final => readoutPayoff setup base final.state) ε intended)
    (duration : (serviceGraph setup bindingRevealDeps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player
      (WitnessedPacket (serviceGraph setup bindingRevealDeps)))
    {ledgerHorizon turns : Nat}
    {scheduler : (serviceApplication setup bindingRevealDeps duration leaks).Scheduler}
    {delay bound : (serviceGraph setup bindingRevealDeps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup bindingRevealDeps duration) leaks
      (serviceInitialLaw setup bindingRevealDeps) ledgerHorizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup bindingRevealDeps duration) delay bound) :
    let app := serviceApplication setup bindingRevealDeps duration leaks
    let clients := serviceReferenceTurnPolicy setup bindingRevealDeps duration leaks bound turns
      (firstTurnTiming setup turns bindingRevealDeps)
      (effectiveOpening (compilePrescribedProfile setup.program bindingRevealDeps
        (setup.decodeBehavioralProfile forfeiture target)))
    let native := app.roundsFrom (serviceInitialLaw setup bindingRevealDeps) scheduler clients
      ledgerHorizon
    IsεNash (serviceGame setup bindingRevealDeps duration leaks scheduler ledgerHorizon)
        (setup.graphForfeitConfigPayoff bindingRevealDeps parameter utility forfeit) ε clients ∧
      (∀ final ∈ native.support,
        final.application.config.cut.Terminal ∧ final.application.config.defaulted = ∅ ∧
          ∃ terminal, serviceRankedReadout setup bindingRevealDeps duration leaks
              (app.finished final) =
            some terminal ∧ NoFailedReveals setup terminal) ∧
      native.map (fun final =>
        (serviceRankedReadout setup bindingRevealDeps duration leaks (app.finished final),
          setup.graphForfeitConfigPayoff bindingRevealDeps parameter utility forfeit
            final.application.config)) =
        (setup.intendedModel.runBehavioral intended horizon).map
          (fun final => (setup.protocolReadout final.state,
            readoutPayoff setup base final.state)) := by
  have relaxed : (serviceGraph setup bindingRevealDeps).RevealRelaxedOrdered :=
    setup.informationGraph.relaxReveals.relaxBindings_revealRelaxedOrdered
      (setup.informationGraph.relaxReveals_revealRelaxedOrdered
        (toInformationGraph_barrierOrdered setup.program).revealRelaxedOrdered)
  exact Vegas.Paper.intended_concurrent_ledger (setup := setup) (parameter := parameter)
    (utility := utility) (finite := finite) (wellFormed := wellFormed) (forfeit := forfeit)
    (turns := turns) bindingRevealDeps relaxed range intended target agrees ε equilibrium
    duration leaks contract timely

/-- info: 'Vegas.Paper.intended_bindingReveal_ledger' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_bindingReveal_ledger

omit [Finite Player] initialFinite in
/-- Every intended profile has an extension that opens at every reveal. -/
theorem Vegas.Paper.exists_disclosing_extension
    (admission : CommitmentInterface setup.program)
    (intended : Profile setup.intendedModel.behavioralSignature) :
    ∃ target : Profile (setup.informationModel admission).behavioralSignature,
      (setup.intendedRestriction admission).ExtendsProfile intended target ∧
        ∀ who, Disclosing setup.program (setup.decodeBehavioralProfile admission target who) :=
  setup.exists_disclosing_extension admission intended

/-- info: 'Vegas.Paper.exists_disclosing_extension' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.exists_disclosing_extension

end Forfeits
end Source

/-! Complete graph event orders depend only on dependencies. The source-information
compiler additionally imposes the total source order, while prescribed profiles
support the stated dependency relaxations. -/

section Graph

/-- Complete run orders, even at fixed strategies and inputs, are exactly the
topological orderings of the graph's dependencies. -/
theorem Vegas.Paper.event_orders_iff_topological (graph : EventGraph Player L)
    (events : List graph.EventId) (profile : graph.BehavioralProfile) (inputs : graph.Inputs) :
    (∃ (scheduler : graph.PublicScheduler) (final : graph.Config),
      final ∈ (graph.runPolicies scheduler profile inputs).support ∧
        final.history.map EventCompletion.event = events) ↔ graph.order.Topological events :=
  (EventGraph.topological_iff_supported_run events profile inputs).symm

/-- info: 'Vegas.Paper.event_orders_iff_topological' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.event_orders_iff_topological

/-- The same deterministic public scheduler forces a given topological order
for every behavioral profile and initial input. -/
theorem Vegas.Paper.topological_order_forced (graph : EventGraph Player L)
    (events : List graph.EventId) (topological : graph.order.Topological events) :
    ∀ (profile : graph.BehavioralProfile) (inputs : graph.Inputs),
      (graph.runPolicies (EventGraph.orderedScheduler events) profile inputs).map
          (fun config => config.history.map EventCompletion.event) = PMF.pure events :=
  EventGraph.runPolicies_orderedScheduler events topological

/-- info: 'Vegas.Paper.topological_order_forced' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.topological_order_forced

/-- The topological orders are precisely the lists obtained from numeric rank
by adjacent swaps with no direct dependency edge in either direction. -/
theorem Vegas.Paper.topological_iff_adjacent_swaps (order : EventOrder)
    (events : List (Fin order.eventCount)) :
    order.Topological events ↔
      Relation.ReflTransGen order.AdjacentSwap (List.finRange order.eventCount) events :=
  order.topological_iff_swaps events

/-- info: 'Vegas.Paper.topological_iff_adjacent_swaps' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.topological_iff_adjacent_swaps

variable {Γ : SourceCtx Player L} {openNames : Finset VarId}

/-! Every public scheduler of the information graph selects the same event plan.
Compiled profiles retain the complete source configuration law. Approximate Nash
equilibrium is preserved and reflected with the same error for every utility of
the public source outcome. -/

theorem Vegas.Paper.toInformationGraph_policyPlan_eq
    (program : SourceProgram Player L Γ openNames) :
    let infoGraph := toInformationGraph program
    ∀ graphProfile : infoGraph.BehavioralProfile,
      let planUnder := infoGraph.policyPlan graphProfile
      ∀ first second : infoGraph.PublicScheduler, planUnder first = planUnder second :=
  fun graphProfile first second =>
    Vegas.toInformationGraph_policyPlan_eq program graphProfile first second

/-- info: 'Vegas.Paper.toInformationGraph_policyPlan_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.toInformationGraph_policyPlan_eq

theorem Vegas.Paper.scheduled_terminalConfig_law (program : SourceProgram Player L Γ openNames) :
    let infoGraph := toInformationGraph program
    ∀ (scheduler : infoGraph.PublicScheduler) (profile : BehavioralProfile program)
      (state : State L Γ),
      let graphRun := infoGraph.terminalOutcomes scheduler (compileEventProfile program profile)
        (encodeInputs state)
      graphRun.map (terminalConfig program) = program.run profile state :=
  fun scheduler profile state => Vegas.scheduled_terminalConfig_law program scheduler profile state

/-- info: 'Vegas.Paper.scheduled_terminalConfig_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.scheduled_terminalConfig_law

theorem Vegas.Paper.eventGame_approximate_nash_iff (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (scheduler : setup.informationGraph.PublicScheduler)
    (utility : PublicOutcome setup.program → Player → ℝ)
    (ε : ℝ) (profile : BehavioralProfile setup.program) :
    IsεNash (setup.eventGame scheduler)
        (fun outcome who => utility (setup.eventPublicOutcome outcome) who)
        ε (compileEventProfile setup.program profile) ↔
      IsεNash setup.gameForm utility ε profile :=
  setup.eventGame_approximate_nash_iff finite scheduler utility ε profile

/-- info: 'Vegas.Paper.eventGame_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.eventGame_approximate_nash_iff

/-- On every dependency choice retaining the reveal-relaxed barriers, prescribed
source-prefix clients of a submitting, disclosing source profile preserve the complete
source-configuration and fixed-exit payoff law under every public scheduler. No
equilibrium, finiteness or independence premise is required. -/
theorem Vegas.Paper.compilePrescribedProfile_law (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excluded : Player → ℝ) (source : BehavioralProfile setup.program) :
    let graph := setup.dataflowGraph.withDependencies deps
    let payoff := fun terminal =>
      exclusionUtility setup.program excluded utility (setup.parameterOutcome parameter terminal)
    let withPayoff := fun terminal => (some terminal, payoff terminal)
    graph.RevealRelaxedOrdered →
    (∀ who, SourceProgram.SubmitsBindings setup.program (source who)) →
    (∀ who, Disclosing setup.program (source who)) →
    ∀ scheduler : graph.PublicScheduler,
      let graphRun := (graph.gameForm (setup.graphInputs deps) scheduler).play
        (compilePrescribedProfile setup.program deps source)
      (graphRun.map (setup.graphReadout deps)).map withPayoff =
        (setup.run source).map withPayoff := by
  intro graph payoff withPayoff relaxed submits disclosing scheduler graphRun
  rw [PMF.map_comp]
  refine Eq.trans ?_ (setup.compilePrescribedProfile_law deps relaxed parameter utility excluded
    source submits disclosing scheduler)
  congr 1
  funext outcome
  simp only [Function.comp_apply, withPayoff, payoff, SourceProgram.Setup.graphPayoff,
    dite_eq_left outcome.2]
  rfl

/-- info: 'Vegas.Paper.compilePrescribedProfile_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compilePrescribedProfile_law

end Graph

/-! Relaxing independent reveals does not preserve unrestricted source profiles: in the
commit–reveal auction, a profile whose second reveal depends on the first published bid
has different terminal store laws under two public schedulers of the reveal-relaxed graph. -/

section RevealOrder

open Vegas.Examples.ConcurrentRevealOrderLaw in
theorem Vegas.Paper.reveal_order_changes_store_law :
    let storeLaw := fun scheduler : graph.PublicScheduler =>
      (graph.runPolicies scheduler compiled initial.inputs).map Vegas.EventGraph.Config.store
    storeLaw bobFirstScheduler ≠ storeLaw graph.canonicalScheduler :=
  Vegas.Examples.ConcurrentRevealOrderLaw.terminal_store_laws_differ

/-- info: 'Vegas.Paper.reveal_order_changes_store_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.reveal_order_changes_store_law

end RevealOrder

/-! A native protocol control exposes a graph configuration. Each raw transition
follows a finite graph path, and initialized histories retain graph reachability.
A service completion guarantee additionally makes every terminal field available. -/

section Runtime

theorem Vegas.Paper.reactive_protocol_graph_refinement {graph : EventGraph Player L}
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : ℕ)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler) :
    let ledger := (reactiveApplication timeouts) leaks
    let initial := inputs.map EventGraphRuntime.State.initial
    let protocol := ledger.protocol initial horizon scheduler
    let configAt := fun control : ledger.Control => control.execution.application.config
    (∀ before after joint,
      some after ∈ (ledger.transition initial horizon scheduler (some before) joint).support →
        Relation.ReflTransGen EventGraph.Config.Step (configAt before) (configAt after)) ∧
    ∀ control, protocol.Trace (some control) →
      (∃ input ∈ inputs.support, (configAt control).Reachable input) ∧
      (CompletesPlay timeouts leaks initial horizon scheduler →
        protocol.terminal (some control) →
        (configAt control).cut.Terminal ∧ ∀ field, ((configAt control).store field).isSome) :=
  Vegas.EventGraphRuntime.reactive_protocol_graph_refinement timeouts leaks inputs horizon scheduler

/-- info: 'Vegas.Paper.reactive_protocol_graph_refinement' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.reactive_protocol_graph_refinement

/-- Reporting only the first observed violation per sender preserves the full
charge-vector law under batch capture and delivery and satisfies role coverage. -/
theorem Vegas.Paper.firstCountReports_audit {graph : EventGraph Player L}
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (capture delivery : Set.Icc (0 : ℝ) 1) :
    let service := thinnedFirstCountReports (graph := graph) capture delivery
    CountEvidenceCoverage service (fun _ => capture.val) (fun _ => delivery.val) ∧
    (∀ (seen : List (CountEvidence graph)) (who : Player),
      (firstCountReports seen).find? (fun item => item.2.sender == who) =
        seen.find? (fun item => item.2.sender == who && !countPermits item.1 item.2)) ∧
    (∀ (seen : List (CountEvidence graph)) (reports : List (EvidenceReport (CountEvidence graph))),
      reports ∈ (service.reports seen).support →
        (reports.map (fun report => report.evidence.2.sender)).Nodup) ∧
    ∀ traffic : List ((reactiveApplication timeouts) leaks).TrafficRecord,
      countAudit timeouts leaks service.sample traffic = countAudit timeouts leaks
        (EvidenceReportService.thinned capture delivery).sample traffic := by
  exact ⟨thinnedFirstCountReports_coverage capture delivery, find_firstCountReports,
    thinnedFirstCountReports_senders_nodup capture delivery,
    thinnedFirstCountReports_audit timeouts leaks capture delivery⟩

/-- info: 'Vegas.Paper.firstCountReports_audit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.firstCountReports_audit

/-- An authentic archive can certify forbidden packets by checking earlier sender serials. -/
theorem Vegas.Paper.observed_count_reports {graph : EventGraph Player L}
    (network : MessageNetwork Player (WitnessedPacket graph))
    (unique : network.UniqueIds) (seen : List (Message Player (WitnessedPacket graph)))
    (authentic : seen ⊆ network.inputs) (message : Message Player (WitnessedPacket graph)) :
    message ∈ observedCountReports seen ↔
      message ∈ seen ∧
      (∀ n < message.id.2, (message.sender, n) ∈ seen.map Message.id) ∧
      countPermits network.inputs message = false :=
  mem_observedCountReports network unique seen authentic message

/-- info: 'Vegas.Paper.observed_count_reports' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.observed_count_reports

/-- A complete sender stream suffices on every legal prefix. -/
theorem Vegas.Paper.sender_archive_report {graph : EventGraph Player L}
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (EventGraphRuntime.State graph)) (horizon : ℕ)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (control : ((reactiveApplication timeouts) leaks).Control)
    (trace : (((reactiveApplication timeouts) leaks).protocol initial horizon scheduler).Trace
      (some control))
    (sender : Player) (seen : List (Message Player (WitnessedPacket graph)))
    (authentic : seen ⊆ control.execution.network.inputs)
    (complete : ∀ m ∈ control.execution.network.inputs, m.sender = sender → m ∈ seen) :
    ((observedCountReports seen).find? (fun m => m.sender == sender)).isSome ↔
      ∃ m ∈ control.execution.network.inputs, m.sender = sender ∧
        countPermits control.execution.network.inputs m = false :=
  observedCountReports_sender_history timeouts leaks initial horizon scheduler control trace
    sender seen authentic complete

/-- info: 'Vegas.Paper.sender_archive_report' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sender_archive_report

/-- The same observed binding packet has opposite count verdicts across two histories. -/
theorem Vegas.Paper.ambiguous_binding_report {graph : EventGraph Player L}
    (sender : Player) (event : graph.EventId)
    (owned : bindingOwnedBy graph sender event = true) (raw : Raw L) :
    ∃ (message first prior : Message Player (WitnessedPacket graph)),
      message.id = (sender, 1) ∧ first.id = (sender, 0) ∧ prior.id = first.id ∧
      message.payload = ⟨.commitment event (sender, .prepared 0), none, some ⟨event⟩⟩ ∧
      first.payload.call = .malformed raw ∧ prior.payload = message.payload ∧
      countPermits [first, message] message = true ∧
      countPermits [prior, message] message = false :=
  binding_countVerdicts_differ sender event owned raw

/-- info: 'Vegas.Paper.ambiguous_binding_report' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.ambiguous_binding_report

/-- An authentic subarchive preserves a permitted event-bound opening precisely
when it contains an earlier matching commitment. -/
theorem Vegas.Paper.opening_report_predecessor {graph : EventGraph Player L}
    (actual seen : List (Message Player (WitnessedPacket graph))) (authentic : seen ⊆ actual)
    (message : Message Player (WitnessedPacket graph)) (event binding : graph.EventId)
    (handle : Handle graph) (raw : Raw L) (call : message.payload.call = .opening event handle raw)
    (resolves : match nodeView graph event with
      | .resolve _ _ ref .. => ref.field = .inr binding
      | _ => False)
    (lawful : countPermits actual message = true) :
    countPermits seen message = true ↔ ∃ prior, EarlierOwnPacket seen message prior ∧
      prior.payload.call = .commitment binding handle :=
  opening_permitted_iff_commitment_observed actual seen authentic message event binding handle raw
    call resolves lawful

/-- info: 'Vegas.Paper.opening_report_predecessor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.opening_report_predecessor

/-- A forbidden submission can leave the entire passive observation unchanged. -/
theorem Vegas.Paper.unobserved_submission {graph : EventGraph Player L}
    (sender observer : Player) (call : Payload graph) :
    let net : MessageNetwork Player (WitnessedPacket graph) := .empty
    let (message, after) := net.submit sender ⟨call, none, none⟩
    message ∈ after.inputs ∧ countPermits after.inputs message = false ∧
      after.observe observer = net.observe observer :=
  forbiddenSubmission_sameView sender observer call

/-- info: 'Vegas.Paper.unobserved_submission' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.unobserved_submission

/-- With unrestricted inclusion delay, the sharp uniform collection bound is zero. -/
theorem Vegas.Paper.uniform_count_collection_bound {graph : EventGraph Player L}
    (window : ChallengeWindow) (actual : List (CountEvidence graph)) (sender : Player)
    (bound : ℝ) :
    (∀ service : EvidenceReportService (CountEvidence graph), service.window = window →
      service.observations actual = PMF.pure actual →
      (∀ reports ∈ (service.reports actual).support,
        reports.map EvidenceReport.evidence = actual ∧ ∀ r ∈ reports, r.submittedAt = 0) →
      bound ≤ ((service.sample actual).toOuterMeasure (countViolation sender)).toReal) ↔
      bound ≤ 0 :=
  EvidenceReportService.uniform_collection_bound_iff window actual (countViolation sender)
    (by simp [countViolation]) bound

/-- info: 'Vegas.Paper.uniform_count_collection_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.uniform_count_collection_bound

end Runtime

/-! The ordinary physical compiler uses actual first-turn clients, including
silent omission and withholding followed by expiry. Its readout law records
the complete typed source state and public default history. The following law
quantifies over every observation of that joint result and every source profile.
`AsyncContract` requires bounded owner opportunities, protected inclusion of an
owner's sole submitted identifier, and completion on initialized legal terminal
histories. `AsyncTimely` requires `delay event + bound event < duration event`
for each owned event; both conditions concern the supplied scheduler and runtime. -/

section OrdinaryCompiler

theorem Vegas.Paper.sourceServiceClientPolicy_law
    {setup : Setup (Player := Player) (L := L)} [Finite Player]
    (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    {horizon turns : ℕ} (scheduler : (application setup timeouts leaks).Scheduler)
    (delay bound : setup.informationGraph.EventId → ℕ)
    (contract : AsyncContract timeouts leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (original : BehavioralProfile setup.program) {Outcome : Type u}
    (read : State L setup.program.terminalCtx × DefaultHistory Player → Outcome) :
    let ledger := application setup timeouts leaks
    let clients := serviceClientPolicy setup setup.informationDependencies timeouts.duration
      leaks bound turns (firstTurnTiming setup turns)
      (setup.program.normalizeDisclosureProfile original)
    let ledgerRun := ledger.roundsFrom (initialLaw setup) scheduler clients horizon
    let readout := fun execution => sourceReadout setup timeouts leaks (ledger.finished execution)
    let observe := fun terminal : TerminalConfig setup => read (terminal.state, terminal.defaults)
    let clientLaw := (ledgerRun.map readout).map (Option.map observe)
    let sourceLaw := (setup.run original).map (fun terminal => some (observe terminal))
    let graphRun := (setup.informationGraph.canonicalGame
      (setup.initialLaw.map setup.eventInputs)).play (compileEventProfile setup.program original)
    let graphLaw :=
      graphRun.map (fun terminal => some (observe (terminalConfig setup.program terminal)))
    clientLaw = sourceLaw ∧ clientLaw = graphLaw := by
  intro ledger clients ledgerRun readout observe clientLaw sourceLaw graphRun graphLaw
  refine ⟨?_, ?_⟩
  · simpa only [clientLaw, sourceLaw, ledgerRun, readout, observe, PMF.map_comp,
      Function.comp_def] using
      Vegas.sourceServiceClientPolicy_outcome_law timeouts leaks scheduler delay bound original
        contract timely read
  · simpa only [clientLaw, graphLaw, ledgerRun, readout, observe, graphRun, PMF.map_comp,
      Function.comp_def] using
      Vegas.sourceServiceClientPolicy_graph_law timeouts leaks scheduler delay bound original
        contract timely read

/-- info: 'Vegas.Paper.sourceServiceClientPolicy_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sourceServiceClientPolicy_law

end OrdinaryCompiler

end SourceAndGraph

section NativeNash

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol
open GameTheory.Math.Probability GameTheory.Enforcement Interaction Vegas.EventGraphRuntime

section Asynchronous
variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)
  (admission : CommitmentInterface service.setup.program)
  {Parameter : Type} (parameter : State L service.setup.context → Parameter)
  (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
  (sample : List (SettledEvidence service.setup service.setup.informationDependencies) →
    PMF (List (SettledEvidence service.setup service.setup.informationDependencies))) (deposit :
      Player → ℝ)

/-- The bounded raw ledger game, with every response admitted by the message bounds. -/
abbrev Vegas.Paper.ledgerModel :=
  service.rawMenu.information (serviceInitialLaw service.setup
    service.setup.informationDependencies)
      service.horizon service.scheduler

open Vegas.Paper

/-- Source approximate Nash equilibrium for the declared terminal utility. -/
def Vegas.Paper.sourceNash (ε : ℝ)
    (source : Profile (service.sourceModel admission).behavioralSignature) : Prop :=
  IsεNash ((service.sourceModel admission).toBehavioralGameForm
      (service.setup.program.instructionCount + 1))
      (fun final => readoutPayoff service.setup
        (sourcePayoff service.setup parameter utility) final.state) ε source

/-- Intended approximate Nash equilibrium, before publication failures are admitted. -/
def Vegas.Paper.intendedNash (ε : ℝ)
    (intended : Profile service.setup.intendedModel.behavioralSignature) : Prop :=
  IsεNash (service.setup.intendedModel.toBehavioralGameForm
      (service.setup.program.instructionCount + 1))
      (fun final => readoutPayoff service.setup
        (sourcePayoff service.setup parameter utility) final.state) ε
    intended

/-- The actual evidence audit is applied to the terminal source utility. -/
def Vegas.Paper.ledgerSettlement :=
  TerminalAudit.settlement
      (serviceBaseUtility service.setup service.setup.informationDependencies service.duration
        service.leaks
        (fun terminal => utility (service.setup.parameterOutcome parameter terminal)))
      ((serviceAuditObservation (serviceTimeouts service.setup
        service.setup.informationDependencies service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.setup.informationDependencies service.duration
        service.leaks sample) deposit

/-- Audited utility on the native state, using the declared terminal payoff. -/
def Vegas.Paper.ledgerUtility :=
  TerminalAudit.utility
      (serviceBaseUtility service.setup service.setup.informationDependencies service.duration
        service.leaks
        (fun terminal => utility (service.setup.parameterOutcome parameter terminal)))
      ((serviceAuditObservation (serviceTimeouts service.setup
        service.setup.informationDependencies service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.setup.informationDependencies service.duration
        service.leaks sample) deposit

/-- Expected utility under the same audit and bounded raw ledger game. -/
def Vegas.Paper.ledgerNash (ε : ℝ)
    (profile : Profile (ledgerModel service).behavioralSignature) : Prop :=
  IsεNash (service.gameForm service.rawMenu)
      (fun final who => ledgerUtility service parameter utility sample deposit final.state who)
      ε profile

/-- Joint law of terminal cells, public defaults and realized audited payoffs. -/
def Vegas.Paper.ledgerJointLaw
    (profile : Profile (ledgerModel service).behavioralSignature) :=
  (service.run service.rawMenu profile).bind fun final =>
      (ledgerSettlement service parameter utility sample deposit final.state).map fun payoffs =>
        ((serviceSourceReadout service.setup service.setup.informationDependencies service.duration
          service.leaks
          final.state).map (fun terminal => (terminal.state, terminal.defaults)), payoffs)

/-- The corresponding joint law of the intended game. -/
def Vegas.Paper.intendedJointLaw
    (intended : Profile service.setup.intendedModel.behavioralSignature) :=
  (service.setup.intendedModel.runBehavioral intended
      (service.setup.program.instructionCount + 1)).map fun final =>
        ((service.setup.protocolReadout final.state).map
            (fun terminal => (terminal.state, terminal.defaults)),
          readoutPayoff service.setup (sourcePayoff service.setup parameter utility) final.state)

variable (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
  (nonnegative : ∀ who, 0 ≤ deposit who)

include authentic nonnegative

/-- Deferral changes the Nash error by at most twice the law error times the payoff range. -/
theorem Vegas.Paper.isεNash_rawClientProfile_approximate
    {turns : Nat} (timing : TurnTiming service.setup turns service.setup.informationDependencies)
    (low : Player → ℝ) (range : ℝ)
    (within : service.SettlementRange parameter utility sample deposit low (fun _ => range))
    (ε : ℝ) (source : Profile (service.sourceModel admission).behavioralSignature) :
    let clients := service.clientProfile admission service.rawMenu timing source
    (sourceNash service admission parameter utility ε source →
      ledgerNash service parameter utility sample deposit
        (ε + 2 * timing.deferralError * range) clients) ∧
    (ledgerNash service parameter utility sample deposit ε clients →
      sourceNash service admission parameter utility
        (ε + 2 * timing.deferralError * range) source) := by
  exact service.isεNash_rawClientProfile_approximate admission parameter utility
    sample authentic deposit nonnegative timing low range within ε source

/-- info: 'Vegas.Paper.isεNash_rawClientProfile_approximate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.isεNash_rawClientProfile_approximate

/-- Acting at the first opportunity preserves and reflects the same Nash error. -/
theorem Vegas.Paper.isεNash_firstTurnClientProfile_iff
    (turns : Nat) (low : Player → ℝ) (range : ℝ)
    (within : service.SettlementRange parameter utility sample deposit low (fun _ => range))
    (ε : ℝ) (source : Profile (service.sourceModel admission).behavioralSignature) :
    ledgerNash service parameter utility sample deposit ε
      (service.clientProfile admission service.rawMenu
        (firstTurnTiming service.setup turns service.setup.informationDependencies) source) ↔
      sourceNash service admission parameter utility ε source := by
  exact service.isεNash_firstTurnClientProfile_iff admission parameter utility
    sample authentic deposit nonnegative turns low range within ε source

/-- info: 'Vegas.Paper.isεNash_firstTurnClientProfile_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.isεNash_firstTurnClientProfile_iff

omit nonnegative

/-- Every profile retains its joint terminal observation law within the deferral error. -/
theorem Vegas.Paper.clientSettlementLaw_withinTV
    {turns : Nat} (timing : TurnTiming service.setup turns service.setup.informationDependencies)
    (source : Profile (service.sourceModel admission).behavioralSignature)
    (terminalUtility : State L service.setup.program.terminalCtx × DefaultHistory Player →
      Player → ℝ) :
    PMF.WithinTV timing.deferralError
      (service.clientSettlementLaw admission timing source sample terminalUtility deposit)
      (service.sourceSettlementLaw admission source terminalUtility) := by
  exact service.clientSettlementLaw_withinTV admission timing source sample authentic
    terminalUtility deposit

/-- info: 'Vegas.Paper.clientSettlementLaw_withinTV' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.clientSettlementLaw_withinTV

/-- Monetary clients preserve actual receipts jointly with typed cells and public defaults. -/
theorem Vegas.Paper.payment_firstTurnClientProfile_settlement_law
    (turns : Nat) (source : Profile (service.sourceModel admission).behavioralSignature) :
    ((service.run service.rawMenu
      (service.clientProfile admission service.rawMenu
        (firstTurnTiming service.setup turns service.setup.informationDependencies) source)).bind
          fun final =>
        (service.paymentSettlement sample deposit final.state).map fun receipts =>
          ((serviceSourceReadout service.setup service.setup.informationDependencies
            service.duration service.leaks
            final.state).map (fun terminal => (terminal.state, terminal.defaults)), receipts)) =
      (service.setup.run (service.setup.decodeBehavioralProfile admission source)).map
        (fun terminal => (some (terminal.state, terminal.defaults),
          service.setup.transfers (service.setup.program.publicOutcome terminal))) := by
  exact service.payment_firstTurnClientProfile_settlement_law admission sample authentic
    deposit turns source

/-- info: 'Vegas.Paper.payment_firstTurnClientProfile_settlement_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.payment_firstTurnClientProfile_settlement_law

include nonnegative

section Intended
variable (wellFormed : service.setup.WellFormed) (forfeit : ℝ)
  (range : service.setup.TerminalPayoffSpread
    (CommitmentInterface.values service.setup.program) parameter utility forfeit)
  (low : Player → ℝ) (spread : ℝ)
  (within : service.SettlementRange parameter
    (forfeitUtility service.setup.program forfeit utility) sample deposit low (fun _ => spread))
  (intended : Profile service.setup.intendedModel.behavioralSignature)
  (source : Profile (service.sourceModel
    (CommitmentInterface.values service.setup.program)).behavioralSignature)
  (agrees : (service.setup.intendedRestriction
    (CommitmentInterface.values service.setup.program)).ExtendsProfile intended source)
  (ε : ℝ) (equilibrium : intendedNash service parameter utility ε intended)

include authentic nonnegative wellFormed range within agrees equilibrium

/-- Intended Nash equilibria compile with explicit deferral error and joint-law error. -/
theorem Vegas.Paper.intended_rawClientProfile_isεNash
    {turns : Nat} (timing : TurnTiming service.setup turns service.setup.informationDependencies) :
    let clients := service.clientProfile (CommitmentInterface.values service.setup.program)
      service.rawMenu timing source
    let forfeited := forfeitUtility service.setup.program forfeit utility
    ledgerNash service parameter forfeited sample deposit
      (ε + 2 * timing.deferralError * spread) clients ∧
      PMF.WithinTV timing.deferralError
        (ledgerJointLaw service parameter forfeited sample deposit clients)
        (intendedJointLaw service parameter utility intended) := by
  exact service.intended_rawClientProfile_isεNash wellFormed parameter utility forfeit
    range sample authentic deposit nonnegative timing low spread within intended source agrees
    ε equilibrium

/-- info: 'Vegas.Paper.intended_rawClientProfile_isεNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_rawClientProfile_isεNash

/-- First-opportunity clients retain the intended Nash error and exact joint payoff law. -/
theorem Vegas.Paper.intended_firstTurnClientProfile_isεNash (turns : Nat) :
    let clients := service.clientProfile (CommitmentInterface.values service.setup.program)
      service.rawMenu (firstTurnTiming service.setup turns service.setup.informationDependencies)
        source
    let forfeited := forfeitUtility service.setup.program forfeit utility
    ledgerNash service parameter forfeited sample deposit ε clients ∧
      ledgerJointLaw service parameter forfeited sample deposit clients =
        intendedJointLaw service parameter utility intended := by
  exact service.intended_firstTurnClientProfile_isεNash wellFormed parameter utility
    forfeit range sample authentic deposit nonnegative turns low spread within intended source
    agrees ε equilibrium

/-- info: 'Vegas.Paper.intended_firstTurnClientProfile_isεNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_firstTurnClientProfile_isεNash

end Intended
end Asynchronous

end NativeNash

section PhysicalClients

/-! # Sequential compilation to bounded physical clients

`ClientSpec` packages the source, service, finite message alphabet, payoff bounds
and authentic evidence collection conditions. `ClientCompilation` retains the
selected raw assessment, its sequential equilibrium, absence of public defaults
and charges, and the joint complete source-configuration/settled-payoff law.
Its refinement certificate retains the intended strategy and actual replay
posterior at genuine source decisions. Every source history has an exact replay
preimage at every corresponding native site. The same retained native assessment
is sequentially rational, and matching continuations preserve complete normalized
histories jointly with actual settled payoffs through the audit and raw aliases.
-/


open Vegas Vegas.SourceProgram Vegas.EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability GameTheory.Enforcement

section ClientRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts setup.informationGraph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
  {bounds : MessageBounds setup.informationGraph} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}
  {Parameter : Type} {parameter : Vegas.State L setup.context → Parameter}

local notation "app" => application setup timeouts leaks
local notation "Initial" => initialLaw setup
local notation "raw" => bounds.rawMenu timeouts leaks
local notation "model" => ReactiveApplication.ResponseMenu.information
  (bounds.rawMenu timeouts leaks) Initial horizon scheduler
local notation "sourceFuel" => instructionCount setup.program + 1
local notation "sourceConfigAt" => sourceReadout setup timeouts leaks

section Equilibrium

variable {utility : Parameter × PublicOutcome setup.program → Player → ℝ}
  {excludedPayoff : Player → ℝ}

theorem Vegas.Paper.intended_raw_sequentialEquilibrium_preserved
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended) :
    Nonempty (ClientCompilation spec intended) := by
  exact Vegas.intended_raw_sequentialEquilibrium_preserved spec intended equilibrium

/-- info: 'Vegas.Paper.intended_raw_sequentialEquilibrium_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_raw_sequentialEquilibrium_preserved

theorem Vegas.Paper.compile_correct
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended) :
    let compiled := spec.compile intended equilibrium
    Nonempty (ClientAssessmentRefinement setup timeouts leaks bounds horizon scheduler
      intended compiled.assessment) ∧
    compiled.assessment.IsSequentialEquilibrium
      ((raw).decisionInformationAntichain Initial horizon scheduler)
      ((raw).bounded Initial horizon scheduler).wellFoundedHistories
      (fun who final => spec.payoff who final.state) ∧
    (∀ who, (raw).restrictPolicy Initial horizon scheduler who (compiled.clients who) =
      compiled.assessment.strategy who) ∧
    ((app).finish Initial horizon scheduler compiled.clients none).bind spec.observation =
      (setup.intendedModel.runBehavioral intended.strategy sourceFuel).map
        (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  exact spec.compile_correct intended equilibrium

/-- info: 'Vegas.Paper.compile_correct' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compile_correct

/-- At matching raw sites, replay of the actual ledger belief has the supplied
source posterior, even at a later activation or a zero-probability site. -/
theorem Vegas.Paper.raw_belief_replay
    {spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff}
    {intended : setup.intendedModel.BehavioralAssessment}
    (compiled : ClientCompilation spec intended) {who : Player}
    (source : setup.intendedModel.InformationSite who)
    (site : (onePacketModel setup timeouts leaks bounds Initial horizon
      scheduler).InformationSite who)
    (rawSite : (model).InformationSite who)
    (same : ((reactiveNormalization timeouts) leaks).site (raw)
      (bounds.rawMenu_recall timeouts leaks) Initial horizon scheduler who rawSite =
      (bounds.onePacketRestriction timeouts leaks Initial horizon scheduler).site who site)
    (projected : source.1 = projectView setup timeouts leaks who site.1)
    (forced : forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks)
      Initial horizon scheduler who site.1)
    {past : List (app).PlayerEntry} {view : (app).PlayerView}
    (shown : site.1 = some (past, view)) {event : setup.informationGraph.EventId}
    (ownTurn : view.application.publicView.ownTurn? who = some event) :
    (compiled.assessment.belief who rawSite).map (fun history =>
      rawIntendedHistory? setup timeouts leaks bounds horizon scheduler history.1) =
    (intended.belief who source).map (fun history => some history.1) :=
  compiled.raw_belief_replay source site rawSite same projected forced shown ownTurn

/-- info: 'Vegas.Paper.raw_belief_replay' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.raw_belief_replay

theorem Vegas.Paper.compile_ledger_correct
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended)
    (unobserved : leaks.DeliversNothing) :
    let compiled := spec.compile intended equilibrium
    Nonempty (ClientAssessmentRefinement setup timeouts leaks bounds horizon scheduler
      intended compiled.assessment) ∧
    compiled.assessment.IsSequentialEquilibrium
      ((raw).decisionInformationAntichain Initial horizon scheduler)
      ((raw).bounded Initial horizon scheduler).wellFoundedHistories
      (fun who final => spec.payoff who final.state) ∧
    (∀ who, ReactiveApplication.Policy.IgnoresLeakedFields app (compiled.ledgerClients who)) ∧
    (∀ (history : ((raw).protocol Initial horizon scheduler).History) who,
      (raw).restrictPolicy Initial horizon scheduler who (compiled.ledgerClients who)
        ((model).infoOf who history.trace) =
      compiled.assessment.strategy who ((model).infoOf who history.trace)) ∧
    ((app).finish Initial horizon scheduler compiled.ledgerClients none).bind spec.observation =
      (setup.intendedModel.runBehavioral intended.strategy sourceFuel).map
        (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  exact spec.compile_ledger_correct intended equilibrium unobserved

/-- info: 'Vegas.Paper.compile_ledger_correct' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compile_ledger_correct

/-- Physical continuations at represented clean source boundaries preserve
ordinary source utility jointly with the full source configuration, without
defaults, failed reveals or audit charges, including off-path boundaries. -/
theorem Vegas.Paper.clients_continuation
    {spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff}
    {intended : setup.intendedModel.BehavioralAssessment}
    (compiled : ClientCompilation spec intended)
    (rank : Nat)
    (nativeStart : ((bounds.onePacketMenu timeouts leaks).protocol Initial horizon
      scheduler).History)
    (rawStart : ((raw).protocol Initial horizon scheduler).History)
    (same : ((reactiveNormalization timeouts) leaks).history (raw)
      (bounds.rawMenu_recall timeouts leaks) Initial horizon scheduler rawStart =
      (bounds.onePacketRestriction timeouts leaks Initial horizon scheduler).history nativeStart)
    (anchor : (app).Execution)
    (state : nativeStart.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary setup timeouts leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (valid : ProtocolState.Intended setup.program point) :
    ((app).finish Initial horizon scheduler compiled.clients rawStart.state).bind spec.observation =
      (setup.continuationLaw (setup.intendedOpeningProfile intended.strategy) (some point)).map
        (fun terminal => (some terminal, utility (setup.parameterOutcome parameter terminal))) ∧
    ∀ outcome ∈ ((app).finish Initial horizon scheduler compiled.clients rawStart.state).support,
      ∃ (control : (app).Control) (terminal : Config Player L setup.program.terminalCtx),
        outcome = some control ∧
        sourceReadout setup timeouts leaks outcome = some terminal ∧
        control.execution.application.config.defaulted = ∅ ∧
        (∀ who, failedReveals setup.program who (publicOutcome setup.program terminal) = 0) ∧
        ∀ who, TerminalAudit.charge (app).stateTraffic
          ((countAudit timeouts) leaks spec.evidenceService.sample) outcome who = 0 :=
  compiled.clients_continuation_at_sourceBoundary rank nativeStart rawStart same anchor state
    boundary point decoded valid

/-- info: 'Vegas.Paper.clients_continuation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.clients_continuation

theorem Vegas.Paper.clients_sequentiallyRational
    {spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff}
    {intended : setup.intendedModel.BehavioralAssessment}
    (compiled : ClientCompilation spec intended)
    (who : Player) (site : (model).InformationSite who)
    (alternative : (app).Policy)
    (covered : (raw).Admissible Initial horizon scheduler who alternative) :
    expect ((compiled.assessment.belief who site).bind fun history =>
      (app).finish Initial horizon scheduler (Function.update compiled.clients who alternative)
        history.1.state) (spec.payoff who) ≤
    expect ((compiled.assessment.belief who site).bind fun history =>
      (app).finish Initial horizon scheduler compiled.clients history.1.state)
        (spec.payoff who) := by
  exact compiled.clients_sequentiallyRational who site alternative covered

/-- info: 'Vegas.Paper.clients_sequentiallyRational' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.clients_sequentiallyRational

theorem Vegas.Paper.ledgerClients_sequentiallyRational
    {spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff}
    {intended : setup.intendedModel.BehavioralAssessment}
    (compiled : ClientCompilation spec intended)
    (unobserved : leaks.DeliversNothing)
    (who : Player) (site : (model).InformationSite who)
    (alternative : (app).Policy)
    (covered : (raw).Admissible Initial horizon scheduler who alternative) :
    expect ((compiled.assessment.belief who site).bind fun history =>
      (app).finish Initial horizon scheduler
        (Function.update compiled.ledgerClients who alternative) history.1.state)
        (spec.payoff who) ≤
    expect ((compiled.assessment.belief who site).bind fun history =>
      (app).finish Initial horizon scheduler compiled.ledgerClients history.1.state)
        (spec.payoff who) := by
  exact compiled.ledgerClients_sequentiallyRational unobserved who site alternative covered

/-- info: 'Vegas.Paper.ledgerClients_sequentiallyRational' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.ledgerClients_sequentiallyRational

end Equilibrium

/-- The joint law of original inputs, full typed outcome and actual audited cash
under a bounded raw policy profile. Observation, authentic evidence collection
and deposits are those of the client specification; public default uses the
setup's declared exit transfer. -/
def Vegas.Paper.rawProgramPaymentLaw
    {utility : Parameter × PublicOutcome setup.program → Player → ℝ}
    {excludedPayoff : Player → ℝ}
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff)
    (profile : Profile (model).behavioralSignature) : PMF (TerminalObservation setup) :=
  ((raw).run Initial horizon scheduler profile).bind fun final =>
      spec.programPaymentObservation final.state

/-- The actual physical-client execution with the same audited cash observation. -/
def Vegas.Paper.physicalProgramPaymentLaw
    {utility : Parameter × PublicOutcome setup.program → Player → ℝ}
    {excludedPayoff : Player → ℝ}
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff)
    (clients : Player → (app).Policy) : PMF (TerminalObservation setup) :=
  ((app).finish Initial horizon scheduler clients none).bind spec.programPaymentObservation

section Payments

variable (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (exitPayoff : Player → ℝ)

theorem Vegas.Paper.intended_raw_programPayments_preserved
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility exitPayoff)
    (intended : setup.intendedModel.BehavioralAssessment)
    (compiled : ClientCompilation spec intended) :
    Vegas.Paper.rawProgramPaymentLaw spec compiled.assessment.strategy =
        setup.intendedPaymentLaw intended ∧
      Vegas.Paper.physicalProgramPaymentLaw spec compiled.clients =
        setup.intendedPaymentLaw intended := by
  exact ⟨Vegas.intended_raw_programPayments_preserved setup timeouts leaks bounds horizon scheduler
      parameter utility exitPayoff spec intended compiled,
    compiled.clients_programPayments_preserved setup timeouts leaks bounds horizon scheduler
      parameter utility exitPayoff spec intended⟩

/-- info: 'Vegas.Paper.intended_raw_programPayments_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_raw_programPayments_preserved

end Payments
end ClientRuntime

end PhysicalClients

section ConcreteInstances

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol
open GameTheory.Math.Probability GameTheory.Enforcement Interaction Vegas.EventGraphRuntime

section ConcreteService
open Vegas.Examples

/-- The concrete periodic builder supplies its declared opportunity, inclusion
and completion guarantees on every initialized legal history. -/
theorem Vegas.Paper.oddsEvens_asyncContract :
    AsyncContract OddsEvensService.timeouts OddsEvensService.leaks OddsEvensService.initial
      OddsEvensService.horizon OddsEvensService.scheduler (fun _ => 3) (fun _ => 2) :=
  Vegas.Examples.OddsEvensService.contract

/-- info: 'Vegas.Paper.oddsEvens_asyncContract' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.oddsEvens_asyncContract

/-- Reaction three and inclusion two fit within every six-tick deadline. -/
theorem Vegas.Paper.oddsEvens_asyncTimely :
    AsyncTimely OddsEvensService.timeouts (fun _ => 3) (fun _ => 2) :=
  PeriodicService.timely (graph := OddsEvens.compiled)

/-- info: 'Vegas.Paper.oddsEvens_asyncTimely' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.oddsEvens_asyncTimely

end ConcreteService

section ConcurrentOddsEvens

open Vegas Vegas.SourceProgram Vegas.EventGraph Vegas.EventGraphRuntime Interaction
  GameTheory GameTheory.Protocol GameTheory.Math.Probability
open Vegas.Examples.OddsEvens Vegas.Examples.OddsEvensConcurrent

/-- The concrete graph permits both bindings and, after them, both revelations. -/
theorem Vegas.Paper.oddsEvens_concurrent_geometry :
    {0, 1} ⊆ initial.cut.enabled ∧
    ∀ evenBit oddBit : Bool,
      Config.Reachable initial.inputs (bothBound evenBit oddBit) ∧
        {2, 3} ⊆ (bothBound evenBit oddBit).cut.enabled := by
  exact ⟨bindings_enabled_initial, fun evenBit oddBit =>
    ⟨bothBound_reachable evenBit oddBit, reveals_enabled_after_bindings evenBit oddBit⟩⟩

/-- info: 'Vegas.Paper.oddsEvens_concurrent_geometry' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.oddsEvens_concurrent_geometry

/-- Every public scheduler preserves the fair graph equilibrium and its full joint law. -/
theorem Vegas.Paper.oddsEvens_concurrent_graph (scheduler : graph.PublicScheduler) :
    IsεNash (graph.gameForm (setup.graphInputs dependencies) scheduler)
      (setup.graphForfeitPayoff dependencies (fun _ => ()) sourceUtility 200) 0 graphClients ∧
    (∀ outcome ∈ ((graph.gameForm (setup.graphInputs dependencies) scheduler).play
        graphClients).support,
      (setup.graphReadout dependencies outcome).defaulted = ∅ ∧
        ∀ who, failedReveals program who
          (publicOutcome program (setup.graphReadout dependencies outcome)) = 0) ∧
    (((graph.gameForm (setup.graphInputs dependencies) scheduler).play graphClients).map
      (fun outcome => (some (setup.graphReadout dependencies outcome),
        setup.graphForfeitPayoff dependencies (fun _ => ()) sourceUtility 200 outcome))) =
      uniformJointLaw ∧
    ∀ who, expect ((graph.gameForm (setup.graphInputs dependencies) scheduler).play graphClients)
      (fun outcome => setup.graphForfeitPayoff dependencies (fun _ => ()) sourceUtility 200
        outcome who) = 100 :=
  graph_equilibrium scheduler

/-- info: 'Vegas.Paper.oddsEvens_concurrent_graph' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.oddsEvens_concurrent_graph

/-- The concrete periodic ledger preserves fair play against arbitrary raw deviations. -/
theorem Vegas.Paper.oddsEvens_concurrent_ledger :
    let app := serviceApplication setup dependencies serviceDuration leaks
    let native := app.roundsFrom (serviceInitialLaw setup dependencies) serviceScheduler
      clients serviceHorizon
    IsεNash (serviceGame setup dependencies serviceDuration leaks serviceScheduler serviceHorizon)
      (setup.graphForfeitConfigPayoff dependencies (fun _ => ()) sourceUtility 200) 0 clients ∧
    (∀ final ∈ native.support,
      final.application.config.cut.Terminal ∧ final.application.config.defaulted = ∅ ∧
        ∃ terminal,
          serviceRankedReadout setup dependencies serviceDuration leaks (app.finished final) =
            some terminal ∧ ∀ who,
              failedReveals program who (publicOutcome program terminal) = 0) ∧
    native.map (fun final =>
      (serviceRankedReadout setup dependencies serviceDuration leaks (app.finished final),
        setup.graphForfeitConfigPayoff dependencies (fun _ => ()) sourceUtility 200
          final.application.config)) = uniformJointLaw ∧
    ∀ who, expect native (fun final => setup.graphForfeitConfigPayoff dependencies (fun _ => ())
      sourceUtility 200 final.application.config who) = 100 :=
  native_equilibrium

/-- info: 'Vegas.Paper.oddsEvens_concurrent_ledger' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.oddsEvens_concurrent_ledger

end ConcurrentOddsEvens

section FairLedger
open Vegas.Examples
local notation "fairMenu" => OddsEvens.bounds.rawMenu OddsEvensService.timeouts
    OddsEvensService.leaks
local notation "fairModel" => ReactiveApplication.ResponseMenu.information
  (OddsEvens.bounds.rawMenu OddsEvensService.timeouts OddsEvensService.leaks)
  OddsEvensService.initial
  OddsEvensService.horizon OddsEvensService.scheduler
local notation "fairSpec" => OddsEvensRaw.specification

/-- Actual bounded-ledger execution of the concrete fair-game client profile. -/
def Vegas.Paper.fairLedgerRun (profile : Profile (fairModel).behavioralSignature) :=
  (fairMenu).run OddsEvensService.initial OddsEvensService.horizon
    OddsEvensService.scheduler profile

/-- The concrete fair game's joint source-configuration and audited payoff law. -/
def Vegas.Paper.fairLedgerJointLaw (profile : Profile (fairModel).behavioralSignature) :=
  (Vegas.Paper.fairLedgerRun profile).bind fun final =>
      ((fairSpec).settlement final.state).map fun payoffs =>
        (sourceReadout OddsEvens.setup OddsEvensService.timeouts
          OddsEvensService.leaks final.state, payoffs)

/-- A fair ledger equilibrium has no defaults or charges and retains the source payoff law. -/
theorem Vegas.Paper.fair_equilibrium_exists :
    ∃ target : (fairModel).BehavioralAssessment,
      target.IsSequentialEquilibrium
        ((fairMenu).decisionInformationAntichain OddsEvensService.initial
          OddsEvensService.horizon OddsEvensService.scheduler)
        ((fairMenu).bounded OddsEvensService.initial OddsEvensService.horizon
          OddsEvensService.scheduler).wellFoundedHistories
        (fun who final => (fairSpec).payoff who final.state) ∧
      (∀ final ∈ (Vegas.Paper.fairLedgerRun target.strategy).support,
        ∀ control, final.state = some control →
          control.execution.application.config.defaulted = ∅) ∧
      (∀ final ∈ (Vegas.Paper.fairLedgerRun target.strategy).support, ∀ who,
        TerminalAudit.charge OddsEvensService.app.stateTraffic
          ((countAudit OddsEvensService.timeouts) OddsEvensService.leaks
            OddsEvensRaw.evidenceService.sample) final.state who = 0) ∧
      Vegas.Paper.fairLedgerJointLaw target.strategy = OddsEvens.uniformJointLaw ∧
      ∀ who, expect (Vegas.Paper.fairLedgerJointLaw target.strategy)
        (fun realized => realized.2 who) = 100 := by
  exact OddsEvensRaw.fair_equilibrium_exists

/-- info: 'Vegas.Paper.fair_equilibrium_exists' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.fair_equilibrium_exists

/-- Independent half-rate collection and enforcement collect each actual item
with probability one quarter. -/
theorem Vegas.Paper.collection_probability
    (actual : List (CountEvidence OddsEvens.compiled))
    (evidence : CountEvidence OddsEvens.compiled) (member : evidence ∈ actual) :
    ((OddsEvensRaw.evidenceService.sample actual).toOuterMeasure
      {collected | evidence ∈ collected}).toReal = 1 / 4 := by
  exact OddsEvensRaw.collection_probability actual evidence member

/-- info: 'Vegas.Paper.collection_probability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.collection_probability
end FairLedger

section FairSource
open Vegas.Examples.OddsEvens

/-- The fair intended assessment extends to the full source game with its exact joint law. -/
theorem Vegas.Paper.fair_full_source_equilibrium_exists :
    ∃ target : fullModel.BehavioralAssessment,
      target.IsSequentialEquilibrium (setup.decision_antichain fullAdmission)
        fullBounded.wellFoundedHistories fullPayoff ∧
      (setup.intendedRestriction fullAdmission).ExtendsProfile uniformProfile target.strategy ∧
      (fullModel.runBehavioralTerminalFrom fullBounded.wellFoundedHistories target.strategy
        fullProtocol.initHistory).map
        (fun final => (setup.protocolReadout final.state, fun who => fullPayoff who final)) =
          uniformJointLaw := by
  exact Vegas.Examples.OddsEvens.fair_full_source_equilibrium_exists

/-- info: 'Vegas.Paper.fair_full_source_equilibrium_exists' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.fair_full_source_equilibrium_exists

/-- Independent fair source play is a sequential equilibrium. -/
theorem Vegas.Paper.uniformAssessment_equilibrium :
    uniformAssessment.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories terminalUtility := by
  exact Vegas.Examples.OddsEvens.uniformAssessment_equilibrium

/-- info: 'Vegas.Paper.uniformAssessment_equilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.uniformAssessment_equilibrium

/-- Each player receives expected payoff one hundred under the fair source law. -/
theorem Vegas.Paper.uniformJointLaw_expected (who : Vegas.Examples.OddsEvens.Player) :
    expect uniformJointLaw (fun realized => realized.2 who) = 100 := by
  exact Vegas.Examples.OddsEvens.uniformJointLaw_expected who

/-- info: 'Vegas.Paper.uniformJointLaw_expected' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.uniformJointLaw_expected
end FairSource

section PrivateValueAuction

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
open Vegas.Examples.BoundedPrivateValueAuction

local notation "auctionPlayer" => Vegas.Examples.CommitRevealAuction.Player

/-- Truthful bidding gives the same intended equilibrium and full law for every prior. -/
theorem Vegas.Paper.privateValueAuction_intended_equilibrium
    (prior : PMF (auctionPlayer → Bid)) :
    (setup prior).IntendedSequentialEquilibrium values utility (truthfulAssessment prior) ∧
      (truthfulAssessment prior).strategy = truthfulProfile prior ∧
      ((setup prior).intendedModel.runBehavioral (truthfulAssessment prior).strategy
        (instructionCount program + 1)).map (fun final =>
          ((setup prior).protocolReadout final.state, fun who => terminalUtility prior who final)) =
        prior.map (fun types =>
          (some (finalConfig types (types .alice) (types .bob)),
            surplus types (types .alice) (types .bob))) :=
  ⟨truthfulAssessment_equilibrium prior, truthfulAssessment_strategy prior,
    truthfulAssessment_joint_law prior⟩

/-- info: 'Vegas.Paper.privateValueAuction_intended_equilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.privateValueAuction_intended_equilibrium

end PrivateValueAuction

section PrivateValueAuctionNative

open Vegas Vegas.SourceProgram Vegas.EventGraphRuntime Interaction
  GameTheory GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement
open Vegas.Examples.BoundedPrivateValueAuction
open Vegas.Examples.BoundedAuctionService

local notation "auctionTimeouts" => Vegas.Examples.BoundedAuctionService.timeouts
local notation "auctionInitial" => Vegas.Examples.BoundedAuctionService.initialLaw

local notation "auctionPlayer" => Vegas.Examples.CommitRevealAuction.Player

/-- The fixed auction runtime retains one truthful assessment, clean play,
complete utility and executable-cash laws, and expected utility eight sevenths. -/
theorem Vegas.Paper.privateValueAuction_native_equilibrium :
  (
    Nonempty (ClientAssessmentRefinement game auctionTimeouts leaks bounds horizon scheduler
      (truthfulAssessment uniformPrior) compilation.assessment) ∧
    compilation.assessment.IsSequentialEquilibrium
      (raw.decisionInformationAntichain auctionInitial horizon scheduler)
      (raw.bounded auctionInitial horizon scheduler).wellFoundedHistories
      (fun who final => specification.payoff who final.state) ∧
    (∀ who, raw.restrictPolicy auctionInitial horizon scheduler who (compilation.clients who) =
      compilation.assessment.strategy who) ∧
    (∀ final ∈ (raw.run auctionInitial horizon scheduler compilation.assessment.strategy).support,
      ∃ (control : app.Control) (terminal : Config auctionPlayer simpleExpr program.terminalCtx),
        final.state = some control ∧ control.execution.application.config.cut.Terminal ∧
        sourceReadout game auctionTimeouts leaks final.state = some terminal ∧
        control.execution.application.config.defaulted = ∅ ∧
        (∀ who, failedReveals program who (publicOutcome program terminal) = 0) ∧
        ∀ who, TerminalAudit.charge app.stateTraffic
          ((countAudit auctionTimeouts) leaks evidenceService.sample) final.state who = 0) ∧
    (∀ state ∈ (app.finish auctionInitial horizon scheduler compilation.clients none).support,
      ∃ (control : app.Control) (terminal : Config auctionPlayer simpleExpr program.terminalCtx),
        state = some control ∧ control.execution.application.config.cut.Terminal ∧
        sourceReadout game auctionTimeouts leaks state = some terminal ∧
        control.execution.application.config.defaulted = ∅ ∧
        (∀ who, failedReveals program who (publicOutcome program terminal) = 0) ∧
        ∀ who, TerminalAudit.charge app.stateTraffic
          ((countAudit auctionTimeouts) leaks evidenceService.sample) state who = 0) ∧
    rawJointLaw = jointLaw ∧
    ((app.finish auctionInitial horizon scheduler compilation.clients none).bind
      specification.observation) = jointLaw ∧
    ∀ who, expect rawJointLaw (fun realized => realized.2 who) = 8 / 7 ∧
      expect ((app.finish auctionInitial horizon scheduler compilation.clients none).bind
        specification.observation) (fun realized => realized.2 who) = 8 / 7
  ) ∧
  (
    ((raw.run auctionInitial horizon scheduler compilation.assessment.strategy).bind
      (fun final => specification.programPaymentObservation final.state)) =
        game.intendedPaymentLaw (truthfulAssessment uniformPrior) ∧
    ((app.finish auctionInitial horizon scheduler compilation.clients none).bind
      specification.programPaymentObservation) =
        game.intendedPaymentLaw (truthfulAssessment uniformPrior)
  ) :=
  ⟨Vegas.Examples.BoundedAuctionService.native_equilibrium,
    Vegas.Examples.BoundedAuctionService.program_payments_preserved⟩

/-- info: 'Vegas.Paper.privateValueAuction_native_equilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.privateValueAuction_native_equilibrium

end PrivateValueAuctionNative

section AuctionObstruction
open Vegas.Examples.CommitRevealAuction

/-- Selective publication prevents truthful bidding from being dominant. -/
theorem Vegas.Paper.commitRevealAuction_truthful_not_dominant
    (values : Vegas.Examples.CommitRevealAuction.Player → ℝ) (forfeiture : ℝ)
    (valuation : values .alice = 5) :
    ¬ IsDominant setup.valueBindingGame (euPreference (utility values forfeiture))
      Vegas.Examples.CommitRevealAuction.Player.alice (aliceStrategy 5) := by
  exact Vegas.Examples.CommitRevealAuction.truthful_not_dominant values forfeiture valuation

/-- info: 'Vegas.Paper.commitRevealAuction_truthful_not_dominant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.commitRevealAuction_truthful_not_dominant

/-- A utility-preserving translation retains the same dominance obstruction. -/
theorem Vegas.Paper.translated_truthful_not_dominant
    (values : Vegas.Examples.CommitRevealAuction.Player → ℝ) (forfeiture : ℝ)
    (valuation : values .alice = 5)
    (target : GameForm Vegas.Examples.CommitRevealAuction.Player)
    (compile : (who : Vegas.Examples.CommitRevealAuction.Player) →
      setup.valueBindingGame.sig.Strategy who → target.sig.Strategy who)
    (targetUtility : target.sig.Outcome → Vegas.Examples.CommitRevealAuction.Player → ℝ)
    (preserves : ∀ players : Profile setup.valueBindingGame.sig,
      expectedUtility targetUtility .alice (target.play (Profile.map compile players)) =
        expectedUtility (utility values forfeiture) .alice (setup.valueBindingGame.play players))
    (targetIntegrable : ∀ players : Profile setup.valueBindingGame.sig,
      UtilityIntegrable targetUtility .alice (target.play (Profile.map compile players))) :
    ¬ IsDominant target (euPreference targetUtility) .alice (compile .alice (aliceStrategy 5)) := by
  exact Vegas.Examples.CommitRevealAuction.translated_truthful_not_dominant
    values forfeiture valuation target compile targetUtility preserves targetIntegrable

/-- info: 'Vegas.Paper.translated_truthful_not_dominant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.translated_truthful_not_dominant
end AuctionObstruction

section DeferralObstruction

/-- Sequential equilibrium in the diagnostic game, with or without late pending-message access. -/
def Vegas.Paper.lateLeakSequential (game : LateLeakParameters) (leaky : Bool)
    (assessment : (lateLeakModel game leaky).BehavioralAssessment) : Prop :=
  assessment.IsSequentialEquilibrium (lateLeak_antichain game leaky)
      (lateLeak_terminates game leaky) (lateLeakPayoff game leaky)

/-- Profitable late deferral separates every target equilibrium from the intended outcome. -/
theorem Vegas.Paper.lateLeak_intended_outcome_not_preserved
    (game : LateLeakParameters) (pays : game.DeferralPays) :
    (∃ assessment, Vegas.Paper.lateLeakSequential game false assessment) ∧
    (∀ assessment, Vegas.Paper.lateLeakSequential game false assessment →
      lateLeakOutcomeLaw game false assessment.strategy = lateLeakIntendedOutcome) ∧
    (∃ assessment, Vegas.Paper.lateLeakSequential game true assessment) ∧
    (∀ assessment, Vegas.Paper.lateLeakSequential game true assessment →
      lateLeakOutcomeLaw game true assessment.strategy ≠ lateLeakIntendedOutcome) := by
  exact Vegas.lateLeak_intended_outcome_not_preserved game pays

/-- info: 'Vegas.Paper.lateLeak_intended_outcome_not_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.lateLeak_intended_outcome_not_preserved

/-- For each fixed reward, forfeit and drop charge with a positive forfeit margin,
sufficiently reliable late inclusion separates every late-turn equilibrium from the intended law. -/
theorem Vegas.Paper.lateLeak_not_preserved_for_every_margin
    (R D c : ℝ) (reward : 0 < R) (margin : R < D) (charge : 0 ≤ c) :
    lateLeakInclusionThreshold R D c < 1 ∧
      ∀ q : Set.Ioo (0 : ℝ) 1, lateLeakInclusionThreshold R D c < q →
        let game : LateLeakParameters := ⟨R, D, c, q⟩
        (∃ assessment, Vegas.Paper.lateLeakSequential game false assessment) ∧
        (∀ assessment, Vegas.Paper.lateLeakSequential game false assessment →
          lateLeakOutcomeLaw game false assessment.strategy = lateLeakIntendedOutcome) ∧
        (∃ assessment, Vegas.Paper.lateLeakSequential game true assessment) ∧
        (∀ assessment, Vegas.Paper.lateLeakSequential game true assessment →
          lateLeakOutcomeLaw game true assessment.strategy ≠ lateLeakIntendedOutcome) := by
  exact Vegas.lateLeak_not_preserved_for_every_margin R D c reward margin charge

/-- info: 'Vegas.Paper.lateLeak_not_preserved_for_every_margin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.lateLeak_not_preserved_for_every_margin

/-- At each fixed inclusion probability below one, a finite forfeit restores the intended
outcome at a late-turn sequential equilibrium with no drop charge. -/
theorem Vegas.Paper.lateLeak_exists_preserving_forfeit_without_dropCharge
    (R : ℝ) (reward : 0 ≤ R) (q : Set.Ioo (0 : ℝ) 1) :
    ∃ D : ℝ, 0 ≤ D ∧
      let game : LateLeakParameters := ⟨R, D, 0, q⟩
      ∃ assessment, Vegas.Paper.lateLeakSequential game true assessment ∧
        lateLeakOutcomeLaw game true assessment.strategy = lateLeakIntendedOutcome := by
  exact Vegas.lateLeak_exists_preserving_forfeit_without_dropCharge ⟨R, 0, 0, q⟩ reward

/-- info: 'Vegas.Paper.lateLeak_exists_preserving_forfeit_without_dropCharge' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.lateLeak_exists_preserving_forfeit_without_dropCharge

/-- At the sample parameters, both games have sequential equilibria, and every target
equilibrium departs from the one intended outcome law. -/
theorem Vegas.Paper.lateLeak_sample_intended_outcome_not_preserved :
    (∃ assessment, Vegas.Paper.lateLeakSequential LateLeakParameters.sample false assessment) ∧
    (∀ assessment, Vegas.Paper.lateLeakSequential LateLeakParameters.sample false assessment →
      lateLeakOutcomeLaw LateLeakParameters.sample false assessment.strategy =
        lateLeakIntendedOutcome) ∧
    (∃ assessment, Vegas.Paper.lateLeakSequential LateLeakParameters.sample true assessment) ∧
    (∀ assessment, Vegas.Paper.lateLeakSequential LateLeakParameters.sample true assessment →
      lateLeakOutcomeLaw LateLeakParameters.sample true assessment.strategy ≠
        lateLeakIntendedOutcome) := by
  exact Vegas.Paper.lateLeak_intended_outcome_not_preserved LateLeakParameters.sample
    LateLeakParameters.sample_deferralPays

/-- info: 'Vegas.Paper.lateLeak_sample_intended_outcome_not_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.lateLeak_sample_intended_outcome_not_preserved

/-- Every target equilibrium is at least 267/2000 from the intended full outcome law. -/
theorem Vegas.Paper.lateLeak_sample_totalVariation_lower_bound
    {assessment : (lateLeakModel LateLeakParameters.sample true).BehavioralAssessment}
    (equilibrium : Vegas.Paper.lateLeakSequential LateLeakParameters.sample true assessment)
    {error : ℝ}
    (close : PMF.WithinTV error
      (lateLeakOutcomeLaw LateLeakParameters.sample true assessment.strategy)
      lateLeakIntendedOutcome) : 267 / 2000 ≤ error := by
  exact Vegas.lateLeak_sample_totalVariation_lower_bound equilibrium close

/-- info: 'Vegas.Paper.lateLeak_sample_totalVariation_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.lateLeak_sample_totalVariation_lower_bound

/-- The separation persists for public results alone, by at least 3/2000. -/
theorem Vegas.Paper.lateLeak_sample_result_totalVariation_lower_bound
    {assessment : (lateLeakModel LateLeakParameters.sample true).BehavioralAssessment}
    (equilibrium : Vegas.Paper.lateLeakSequential LateLeakParameters.sample true assessment)
    {error : ℝ}
    (close : PMF.WithinTV error
      (lateLeakResultLaw LateLeakParameters.sample true assessment.strategy)
      lateLeakIntendedResultLaw) : 3 / 2000 ≤ error := by
  exact Vegas.lateLeak_sample_result_totalVariation_lower_bound equilibrium close

/-- info: 'Vegas.Paper.lateLeak_sample_result_totalVariation_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.lateLeak_sample_result_totalVariation_lower_bound
end DeferralObstruction

end ConcreteInstances
