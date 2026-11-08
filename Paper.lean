/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.Safety
import Vegas.Game.IntendedNash
import Vegas.Game.ConcurrentRevealPreservation
import Vegas.Game.IntendedOpeningExtension
import Vegas.Game.SourceProtocolNash
import Vegas.Compile.EventGraphScheduling
import Vegas.Game.EventCompilation
import Vegas.Pending.GraphRefinement
import Vegas.Game.SourceServiceFirstTurnCompletion
import Vegas.Game.AsyncServiceRawNash
import Vegas.Game.AsyncClientObservables
import Vegas.Game.ProgramPaymentAsyncNash
import Vegas.Game.ClientCompiler
import Vegas.Game.PaymentPreservation
import Vegas.Examples.OddsEvensRawEquilibrium
import Vegas.Examples.OddsEvensFullSource
import Vegas.Examples.CommitRevealAuction
import Vegas.Examples.LateLeak

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
/-- With independent reveals concurrent, the order-blind compiled clients of a
disclosing extension of an intended `ε`-Nash equilibrium are an `ε`-Nash
equilibrium of the forfeited utility under every public scheduler, with
outcomes read in instruction order, and they have the intended joint law of
terminal configuration and payoff. -/
theorem Vegas.Paper.concurrentReveal_intended_forfeit
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel forfeiture).behavioralSignature)
    (agrees : (setup.intendedRestriction forfeiture).ExtendsProfile intended target) (ε : ℝ)
    (equilibrium : IsεNash (setup.intendedModel.toBehavioralGameForm horizon)
      (fun final => readoutPayoff setup base final.state) ε intended)
    (disclosing : ∀ who, Disclosing setup.program
      (setup.decodeBehavioralProfile forfeiture target who))
    (scheduler : setup.concurrentRevealGraph.PublicScheduler) :
    IsεNash (setup.concurrentRevealGraph.gameForm setup.concurrentInputs scheduler)
        (setup.concurrentForfeitPayoff parameter utility forfeit) ε
        (setup.concurrentRevealGraph.normalizeProfile (compileEventProfile setup.program
          (setup.decodeBehavioralProfile forfeiture target))) ∧
      (∀ outcome ∈ ((setup.concurrentRevealGraph.gameForm setup.concurrentInputs scheduler).play
          (setup.concurrentRevealGraph.normalizeProfile (compileEventProfile setup.program
            (setup.decodeBehavioralProfile forfeiture target)))).support,
        (setup.concurrentReadout outcome).defaulted = ∅ ∧
          NoFailedReveals setup (setup.concurrentReadout outcome)) ∧
      ((setup.concurrentRevealGraph.gameForm setup.concurrentInputs scheduler).play
          (setup.concurrentRevealGraph.normalizeProfile (compileEventProfile setup.program
            (setup.decodeBehavioralProfile forfeiture target)))).map
          (fun outcome => (some (setup.concurrentReadout outcome),
            setup.concurrentForfeitPayoff parameter utility forfeit outcome)) =
        (setup.intendedModel.runBehavioral intended horizon).map
          (fun final => (setup.protocolReadout final.state,
            readoutPayoff setup base final.state)) ∧
      (∀ who event (actor : setup.concurrentRevealGraph.actor? event = some who),
        (publication : (setup.concurrentRevealGraph.outputLayout event).IsPublication) →
          ∀ (observation : setup.concurrentRevealGraph.PlayerObservation who)
            (active : who ∉ observation.defaulted),
            compileEventPolicy setup.program who (setup.decodeBehavioralProfile forfeiture target
              who) event actor observation active =
              PMF.pure (EventGraph.EventField.openAction _ publication)) := by
  obtain ⟨nash, clean, law⟩ := setup.concurrentReveal_intended_forfeit finite wellFormed parameter
    utility forfeit range intended target agrees ε equilibrium disclosing scheduler
  exact ⟨nash, clean, law, fun who event actor publication observation active =>
    compileEventPolicy_publication setup.program who
      (setup.decodeBehavioralProfile forfeiture target who) (disclosing who) event actor
      publication observation active⟩

/-- info: 'Vegas.Paper.concurrentReveal_intended_forfeit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.concurrentReveal_intended_forfeit

include finite wellFormed initialFinite in
/-- The effective-opening clients preserve intended approximate Nash equilibrium,
complete source readout and the payoff vector on the concurrent-reveal ledger.
No public default or failed reveal occurs on supported play. -/
theorem Vegas.Paper.concurrentReveal_intended_ledger
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel forfeiture).behavioralSignature)
    (agrees : (setup.intendedRestriction forfeiture).ExtendsProfile intended target) (ε : ℝ)
    (equilibrium : IsεNash (setup.intendedModel.toBehavioralGameForm horizon)
      (fun final => readoutPayoff setup base final.state) ε intended)
    (disclosing : ∀ who, Disclosing setup.program
      (setup.decodeBehavioralProfile forfeiture target who))
    (duration : (serviceGraph setup .concurrentReveals).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player
      (WitnessedPacket (serviceGraph setup .concurrentReveals)))
    {ledgerHorizon turns : Nat}
    {scheduler : (serviceApplication setup .concurrentReveals duration leaks).Scheduler}
    {delay bound : (serviceGraph setup .concurrentReveals).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup .concurrentReveals duration) leaks
      (serviceInitialLaw setup .concurrentReveals) ledgerHorizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup .concurrentReveals duration) delay bound) :
    IsεNash (concurrentLedgerGame setup duration leaks scheduler ledgerHorizon)
        (concurrentConfigPayoff setup parameter utility forfeit) ε
        (concurrentLedgerClients setup duration leaks bound turns
          (setup.decodeBehavioralProfile forfeiture target)) ∧
      (∀ config ∈ ((concurrentLedgerGame setup duration leaks scheduler ledgerHorizon).play
          (concurrentLedgerClients setup duration leaks bound turns
            (setup.decodeBehavioralProfile forfeiture target))).support,
        config.cut.Terminal ∧ config.defaulted = ∅ ∧ ∃ terminal,
          concurrentRankedRead setup config = some terminal ∧ NoFailedReveals setup terminal) ∧
      (((concurrentLedgerGame setup duration leaks scheduler ledgerHorizon).play
          (concurrentLedgerClients setup duration leaks bound turns
            (setup.decodeBehavioralProfile forfeiture target))).map fun config =>
            (concurrentRankedRead setup config,
              concurrentConfigPayoff setup parameter utility forfeit config)) =
        (setup.intendedModel.runBehavioral intended horizon).map
          (fun final => (setup.protocolReadout final.state,
            readoutPayoff setup base final.state)) :=
  Vegas.concurrentReveal_intended_ledger setup finite wellFormed parameter utility forfeit range
    intended target agrees ε equilibrium disclosing duration leaks contract timely

/-- info: 'Vegas.Paper.concurrentReveal_intended_ledger' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.concurrentReveal_intended_ledger

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

/-! The compiler imposes the total source order. Every public scheduler therefore
selects the same event plan; the scheduler quantifier below supplies no alternate
execution order. Compiled profiles retain the complete source configuration law.
Approximate Nash equilibrium is preserved and reflected with the same error
for every utility of the public source outcome. -/

section Graph

variable {Γ : SourceCtx Player L} {openNames : Finset VarId}

theorem Vegas.Paper.scheduled_terminalConfig_law (program : SourceProgram Player L Γ openNames)
    (scheduler : (toEventGraph program).PublicScheduler)
    (profile : BehavioralProfile program) (state : State L Γ) :
    (∀ (graphProfile : (toEventGraph program).BehavioralProfile)
      (first second : (toEventGraph program).PublicScheduler),
      (toEventGraph program).policyPlan graphProfile first =
        (toEventGraph program).policyPlan graphProfile second) ∧
      ((toEventGraph program).terminalOutcomes scheduler
        (compileEventProfile program profile) (encodeInputs state)).map (terminalConfig program) =
      program.run profile state :=
  ⟨fun graphProfile first second => toEventGraph_policyPlan_eq program graphProfile first second,
    Vegas.scheduled_terminalConfig_law program scheduler profile state⟩

/-- info: 'Vegas.Paper.scheduled_terminalConfig_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.scheduled_terminalConfig_law

theorem Vegas.Paper.eventGame_approximate_nash_iff (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (scheduler : setup.eventGraph.PublicScheduler)
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

end Graph

/-! A native protocol control exposes a graph configuration. Each raw transition
follows a finite graph path, and initialized histories retain graph reachability.
A service completion guarantee additionally makes every terminal field available. -/

section Runtime

variable {graph : EventGraph Player L} (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- The graph configuration retained by a native protocol control. -/
def Vegas.Paper.controlConfig
    (control : ((reactiveApplication timeouts) leaks).Control) : graph.Config :=
  control.execution.application.config

/-- Every typed graph field has an available stored value. -/
def Vegas.Paper.FieldsAvailable (config : graph.Config) : Prop :=
  ∀ field, (config.store field).isSome = true

variable (inputs : PMF graph.Inputs) (horizon : ℕ)
  (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)

local notation "app" => (reactiveApplication timeouts) leaks
local notation "initial" => inputs.map EventGraphRuntime.State.initial
local notation "protocol" => ReactiveApplication.protocol
  ((reactiveApplication timeouts) leaks) (inputs.map EventGraphRuntime.State.initial) horizon
    scheduler
local notation "configAt" => controlConfig timeouts leaks

theorem Vegas.Paper.reactive_protocol_graph_refinement :
    (∀ before after joint,
      some after ∈ ((app).transition initial horizon scheduler (some before) joint).support →
        Relation.ReflTransGen EventGraph.Config.Step (configAt before) (configAt after)) ∧
    ∀ control, (protocol).Trace (some control) →
      (∃ input ∈ inputs.support, (configAt control).Reachable input) ∧
      ((CompletesPlay timeouts) leaks initial horizon scheduler → (protocol).terminal (some
        control) →
        (configAt control).cut.Terminal ∧ FieldsAvailable (configAt control)) :=
  Vegas.EventGraphRuntime.reactive_protocol_graph_refinement timeouts leaks inputs horizon scheduler

/-- info: 'Vegas.Paper.reactive_protocol_graph_refinement' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.reactive_protocol_graph_refinement

end Runtime

/-! The ordinary physical compiler uses actual first-turn clients, including
silent omission and withholding followed by expiry. Its readout law records
the complete typed source state and public default history. The following two
laws quantify over every observation of that joint result and every source profile.
`AsyncContract` requires bounded owner opportunities, protected inclusion of an
owner's sole submitted identifier, and completion on initialized legal terminal
histories. `AsyncTimely` requires `delay event + bound event < duration event`
for each owned event; both conditions concern the supplied scheduler and runtime. -/

section OrdinaryCompiler

variable {setup : Setup (Player := Player) (L := L)} [Finite Player]
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  {horizon turns : ℕ} (scheduler : (application setup timeouts leaks).Scheduler)
  (delay bound : (graph setup).EventId → ℕ) (original : BehavioralProfile setup.program)

/-- The initialized actual-client law, read as an optional complete source configuration. -/
def Vegas.Paper.clientReadoutLaw : PMF (Option (TerminalConfig setup)) :=
  ((application setup timeouts leaks).roundsFrom (initialLaw setup) scheduler
      (serviceClientPolicy setup .sequential timeouts.duration leaks bound turns
        (firstTurnTiming setup turns) (setup.program.normalizeDisclosureProfile original))
      horizon).map
      (fun execution => sourceReadout setup timeouts leaks
        ((application setup timeouts leaks).finished execution))

/-- An observation of the terminal typed state together with public default history. -/
def Vegas.Paper.terminalObservation {Outcome : Type u}
    (read : State L setup.program.terminalCtx × DefaultHistory Player → Outcome)
    (terminal : TerminalConfig setup) : Outcome :=
  read (terminal.state, terminal.defaults)

variable (contract : (AsyncContract timeouts) leaks (initialLaw setup) horizon scheduler delay
  bound)
  (timely : (AsyncTimely timeouts) delay bound) {Outcome : Type u}
  (read : State L setup.program.terminalCtx × DefaultHistory Player → Outcome)

local notation "clientLaw" => clientReadoutLaw (horizon := horizon) (turns := turns)
  timeouts leaks scheduler bound original
local notation "observe" => terminalObservation (setup := setup) read

include contract timely in
theorem Vegas.Paper.sourceServiceClientPolicy_outcome_law :
    (clientLaw).map
        (Option.map (fun terminal => observe terminal)) =
      (setup.run original).map (fun terminal => some (observe terminal)) := by
  dsimp only [clientReadoutLaw, terminalObservation]
  simpa only [PMF.map_comp, Function.comp_def] using
    Vegas.sourceServiceClientPolicy_outcome_law timeouts leaks scheduler delay bound original
      contract timely read

/-- info: 'Vegas.Paper.sourceServiceClientPolicy_outcome_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sourceServiceClientPolicy_outcome_law

include contract timely in
theorem Vegas.Paper.sourceServiceClientPolicy_graph_law :
    (clientLaw).map
        (Option.map (fun terminal => observe terminal)) =
      ((setup.eventGraph.canonicalGame (setup.initialLaw.map setup.eventInputs)).play
        (compileEventProfile setup.program original)).map
        (fun terminal =>
          some (observe (terminalConfig setup.program terminal))) := by
  dsimp only [clientReadoutLaw, terminalObservation]
  simpa only [PMF.map_comp, Function.comp_def] using
    Vegas.sourceServiceClientPolicy_graph_law timeouts leaks scheduler delay bound original
      contract timely read

/-- info: 'Vegas.Paper.sourceServiceClientPolicy_graph_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sourceServiceClientPolicy_graph_law

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
  (sample : List (SettledEvidence service.setup service.mode) →
    PMF (List (SettledEvidence service.setup service.mode))) (deposit : Player → ℝ)

/-- The bounded raw ledger game, with every response admitted by the message bounds. -/
abbrev Vegas.Paper.ledgerModel :=
  service.rawMenu.information (serviceInitialLaw service.setup service.mode)
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
      (serviceBaseUtility service.setup service.mode service.duration service.leaks
        (fun terminal => utility (service.setup.parameterOutcome parameter terminal)))
      ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) deposit

/-- Audited utility on the native state, using the declared terminal payoff. -/
def Vegas.Paper.ledgerUtility :=
  TerminalAudit.utility
      (serviceBaseUtility service.setup service.mode service.duration service.leaks
        (fun terminal => utility (service.setup.parameterOutcome parameter terminal)))
      ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) deposit

/-- Expected utility under the same audit and bounded raw ledger game. -/
def Vegas.Paper.ledgerNash (ε : ℝ)
    (profile : Profile (ledgerModel service).behavioralSignature) : Prop :=
  IsεNash ((ledgerModel service).toBehavioralGameForm (2 * service.horizon + 1))
      (fun final who => ledgerUtility service parameter utility sample deposit final.state who)
      ε profile

/-- Joint law of terminal cells, public defaults and realized audited payoffs. -/
def Vegas.Paper.ledgerJointLaw
    (profile : Profile (ledgerModel service).behavioralSignature) :=
  ((ledgerModel service).runBehavioral profile (2 * service.horizon + 1)).bind fun final =>
      (ledgerSettlement service parameter utility sample deposit final.state).map fun payoffs =>
        ((serviceSourceReadout service.setup service.mode service.duration service.leaks
          final.state).map (fun terminal => (terminal.state, terminal.defaults)), payoffs)

/-- The corresponding joint law of the intended game. -/
def Vegas.Paper.intendedJointLaw
    (intended : Profile service.setup.intendedModel.behavioralSignature) :=
  (service.setup.intendedModel.runBehavioral intended
      (service.setup.program.instructionCount + 1)).map fun final =>
        ((service.setup.protocolReadout final.state).map
            (fun terminal => (terminal.state, terminal.defaults)),
          readoutPayoff service.setup (sourcePayoff service.setup parameter utility) final.state)

variable (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
  (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
  (nonnegative : ∀ who, 0 ≤ deposit who)

include ordered authentic nonnegative

/-- Deferral changes the Nash error by at most twice the law error times the payoff range. -/
theorem Vegas.Paper.isεNash_rawClientProfile_approximate
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
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
  exact service.isεNash_rawClientProfile_approximate admission ordered parameter utility
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
        (firstTurnTiming service.setup turns service.mode) source) ↔
      sourceNash service admission parameter utility ε source := by
  exact service.isεNash_firstTurnClientProfile_iff admission ordered parameter utility
    sample authentic deposit nonnegative turns low range within ε source

/-- info: 'Vegas.Paper.isεNash_firstTurnClientProfile_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.isεNash_firstTurnClientProfile_iff

omit nonnegative

/-- Every profile retains its joint terminal observation law within the deferral error. -/
theorem Vegas.Paper.clientSettlementLaw_withinTV
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (source : Profile (service.sourceModel admission).behavioralSignature)
    (terminalUtility : State L service.setup.program.terminalCtx × DefaultHistory Player →
      Player → ℝ) :
    PMF.WithinTV timing.deferralError
      (service.clientSettlementLaw admission timing source sample terminalUtility deposit)
      (service.sourceSettlementLaw admission source terminalUtility) := by
  exact service.clientSettlementLaw_withinTV admission ordered timing source sample authentic
    terminalUtility deposit

/-- info: 'Vegas.Paper.clientSettlementLaw_withinTV' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.clientSettlementLaw_withinTV

/-- Monetary clients preserve actual receipts jointly with typed cells and public defaults. -/
theorem Vegas.Paper.payment_firstTurnClientProfile_settlement_law
    (turns : Nat) (source : Profile (service.sourceModel admission).behavioralSignature) :
    (((ledgerModel service).runBehavioral
      (service.clientProfile admission service.rawMenu
        (firstTurnTiming service.setup turns service.mode) source)
      (2 * service.horizon + 1)).bind fun final =>
        (service.paymentSettlement sample deposit final.state).map fun receipts =>
          ((serviceSourceReadout service.setup service.mode service.duration service.leaks
            final.state).map (fun terminal => (terminal.state, terminal.defaults)), receipts)) =
      (service.setup.run (service.setup.decodeBehavioralProfile admission source)).map
        (fun terminal => (some (terminal.state, terminal.defaults),
          service.setup.transfers (service.setup.program.publicOutcome terminal))) := by
  exact service.payment_firstTurnClientProfile_settlement_law admission ordered sample authentic
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

include ordered authentic nonnegative wellFormed range within agrees equilibrium

/-- Intended Nash equilibria compile with explicit deferral error and joint-law error. -/
theorem Vegas.Paper.intended_rawClientProfile_isεNash
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode) :
    let clients := service.clientProfile (CommitmentInterface.values service.setup.program)
      service.rawMenu timing source
    let forfeited := forfeitUtility service.setup.program forfeit utility
    ledgerNash service parameter forfeited sample deposit
      (ε + 2 * timing.deferralError * spread) clients ∧
      PMF.WithinTV timing.deferralError
        (ledgerJointLaw service parameter forfeited sample deposit clients)
        (intendedJointLaw service parameter utility intended) := by
  exact service.intended_rawClientProfile_isεNash ordered wellFormed parameter utility forfeit
    range sample authentic deposit nonnegative timing low spread within intended source agrees
    ε equilibrium

/-- info: 'Vegas.Paper.intended_rawClientProfile_isεNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.intended_rawClientProfile_isεNash

/-- First-opportunity clients retain the intended Nash error and exact joint payoff law. -/
theorem Vegas.Paper.intended_firstTurnClientProfile_isεNash (turns : Nat) :
    let clients := service.clientProfile (CommitmentInterface.values service.setup.program)
      service.rawMenu (firstTurnTiming service.setup turns service.mode) source
    let forfeited := forfeitUtility service.setup.program forfeit utility
    ledgerNash service parameter forfeited sample deposit ε clients ∧
      ledgerJointLaw service parameter forfeited sample deposit clients =
        intendedJointLaw service parameter utility intended := by
  exact service.intended_firstTurnClientProfile_isεNash ordered wellFormed parameter utility
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
-/


open Vegas Vegas.SourceProgram Vegas.EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability GameTheory.Enforcement

section ClientRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}
  {Parameter : Type} {parameter : Vegas.State L setup.context → Parameter}

local notation "app" => application setup timeouts leaks
local notation "Initial" => initialLaw setup
local notation "raw" => bounds.rawMenu timeouts leaks
local notation "model" => ReactiveApplication.ResponseMenu.information
  (bounds.rawMenu timeouts leaks) Initial horizon scheduler
local notation "clientFuel" => 2 * horizon + 1
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
    compiled.assessment.IsSequentialEquilibriumFor
      ((raw).decisionInformationAntichain Initial horizon scheduler)
      (fun who site => compiled.assessment.truncatedContinuationContext site
        (fun final => spec.payoff who final.state) clientFuel) ∧
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

theorem Vegas.Paper.compile_ledger_correct
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended)
    (unobserved : leaks.DeliversNothing) :
    let compiled := spec.compile intended equilibrium
    compiled.assessment.IsSequentialEquilibriumFor
      ((raw).decisionInformationAntichain Initial horizon scheduler)
      (fun who site => compiled.assessment.truncatedContinuationContext site
        (fun final => spec.payoff who final.state) clientFuel) ∧
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
  ((model).runBehavioral profile clientFuel).bind fun final =>
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

variable (valuation : Parameter × PublicOutcome setup.program → Player → ℝ)
  (exitValuation : Player → ℝ)

local notation "paidUtility" => setup.parameterPaymentUtility valuation
local notation "exitTransfer" => (fun who => (setup.exitTransfers who : ℝ))
local notation "exitUtility" => (fun who => exitValuation who + exitTransfer who)

theorem Vegas.Paper.intended_raw_programPayments_preserved
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter paidUtility exitUtility)
    (intended : setup.intendedModel.BehavioralAssessment)
    (compiled : ClientCompilation spec intended) :
    Vegas.Paper.rawProgramPaymentLaw spec compiled.assessment.strategy =
        setup.intendedPaymentLaw intended ∧
      Vegas.Paper.physicalProgramPaymentLaw spec compiled.clients =
        setup.intendedPaymentLaw intended := by
  exact ⟨Vegas.intended_raw_programPayments_preserved setup timeouts leaks bounds horizon scheduler
      parameter valuation exitValuation spec intended compiled,
    compiled.clients_programPayments_preserved setup timeouts leaks bounds horizon scheduler
      parameter valuation exitValuation spec intended⟩

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
  ⟨Vegas.Examples.OddsEvensService.opportunity,
      Vegas.Examples.OddsEvensService.protectedInclusion,
      Vegas.Examples.OddsEvensService.completesPlay⟩

/-- info: 'Vegas.Paper.oddsEvens_asyncContract' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.oddsEvens_asyncContract

/-- Reaction three and inclusion two fit within every six-tick deadline. -/
theorem Vegas.Paper.oddsEvens_asyncTimely :
    AsyncTimely OddsEvensService.timeouts (fun _ => 3) (fun _ => 2) :=
  Vegas.Examples.OddsEvensService.timely

/-- info: 'Vegas.Paper.oddsEvens_asyncTimely' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.oddsEvens_asyncTimely

end ConcreteService

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
  (fairModel).runBehavioral profile (2 * OddsEvensService.horizon + 1)

/-- The concrete fair game's joint source-configuration and audited payoff law. -/
def Vegas.Paper.fairLedgerJointLaw (profile : Profile (fairModel).behavioralSignature) :=
  (Vegas.Paper.fairLedgerRun profile).bind fun final =>
      ((fairSpec).settlement final.state).map fun payoffs =>
        (sourceReadout OddsEvensService.fixture OddsEvensService.timeouts
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
    (actual : List (CountEvidence OddsEvensService.compiled))
    (evidence : CountEvidence OddsEvensService.compiled) (member : evidence ∈ actual) :
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
