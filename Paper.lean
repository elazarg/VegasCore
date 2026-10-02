/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.EventScheduling
import Vegas.Game.EventCompilation
import Vegas.Game.EventMessages
import Vegas.Game.EventMessageStrategic
import Vegas.Game.RevealServiceCompilation
import Vegas.Game.RevealServiceRosterCompilation
import Vegas.Game.SourceServiceRawExtension
import Vegas.Game.SourceServiceCompilation
import Vegas.Game.BindingRepairBlock
import Vegas.Pending.ReactiveOpeningSettlement
import Interaction.ScheduledOpeningPosterior
import Vegas.Game.PendingCompositions
import Vegas.Game.ParameterOutcomes
import Vegas.Examples.CommitRevealAuction
import Vegas.Examples.PrivateValueAuction
import Vegas.Source.PrivateInputs
import Vegas.Pending.PrivateInputs
import Vegas.Pending.EventCommitmentBinding
import Vegas.Source.Honest
import Vegas.Source.Safety
import Vegas.Compile.EventGraphPolicy
import Vegas.Compile.EventGraphReadout
import Vegas.Compile.EventGraphCanonical
import Vegas.Compile.EventGraphScheduling
import Vegas.Pending.EventServiceCompletion
import Vegas.Pending.EventSequential
import GameTheoryExtensions.Analysis.ObservationAbstraction
import GameTheoryExtensions.Analysis.Protocol.DecisionExperiment
import GameTheoryExtensions.Analysis.Protocol.DisclosureEnforcementEquilibrium
import GameTheoryExtensions.Analysis.Protocol.DecisionPayoff
import GameTheoryExtensions.Analysis.Protocol.ObservationRequirement
import Vegas.Pending.ReactiveEvidenceOrigin
import Vegas.Examples.SelectiveAssociation.PayoffSeparation
import Vegas.Examples.SelectiveAssociation.Restricted
import Vegas.Examples.SelectiveAssociation.RestrictedRealization
import Vegas.Examples.SelectiveAssociation.RestrictedBinding
import Vegas.Examples.SelectiveAssociation.RestrictedOpeningOptimality
import Vegas.Examples.SelectiveAssociation.RestrictedSymmetry
import Vegas.Examples.ReactiveReadinessRestrictions
import Vegas.Examples.SelectiveAssociation.RestrictedEquilibrium
import Vegas.Examples.SelectiveAssociation.RestrictedSeparation
import Vegas.Examples.MonitoredGuessing.Compilation
import Vegas.Game.ZeroSum
import GameTheory.Math.Probability.ConditionalComparison
import GameTheoryExtensions.Analysis.ZeroSumRegularization
import GameTheoryExtensions.Analysis.CorrelationPayoff
import GameTheoryExtensions.Analysis.Enforcement
import GameTheoryExtensions.Analysis.EnforcementLimits
import GameTheory.Analysis.Protocol.AgentCompletion
import GameTheory.Analysis.Protocol.SequentialExistence
import GameTheoryExtensions.Analysis.Protocol.RestrictionExtension
import GameTheoryExtensions.Analysis.EnforcementSynthesis
import Vegas.Examples.MonitoredGuessing.PayoffInference
import Vegas.Examples.MonitoredGuessing.PayoffLaw
import Vegas.Examples.MonitoredGuessing.WatcherRaw
import Vegas.Examples.MonitoredGuessing.RestrictedFinalComparison
import Vegas.Examples.MonitoredGuessing.DeclaredCompilation
import GameTheoryExtensions.Analysis.ObservableEnforcement
import Interaction.MessageMonitoringProbability
import Interaction.ChallengeWindow
import Vegas.Pending.ReactiveConformance
import GameTheory.Analysis.Protocol.Incentives
import GameTheoryExtensions.Analysis.Protocol.Bayes
import GameTheoryExtensions.Analysis.Protocol.BehavioralContinuity
import GameTheoryExtensions.Analysis.Protocol.BehavioralOneShot
import GameTheoryExtensions.Analysis.Protocol.LocalDeviation
import GameTheoryExtensions.Analysis.Protocol.OneShotLimit
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Support
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Paper theorem audit

Principal source-safety and compilation results for the full failure-aware
language. Each statement delegates directly to its owning theorem; the axiom
pins below check the complete proof dependencies.

The pending-message strategic results use ideal commitments and concrete
bounded service with adaptive delivery. The event-addressed target admits
adaptive public epoch ordering, arbitrary unilateral deviations, and every
source constructor. None of these statements asserts cryptographic,
transaction-ledger, or EVM refinement.
-/

namespace Vegas.Paper

open GameTheory Vegas Interaction
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Every commitment of a checked source program is resolved by the end of its
syntax. This is a static property: no execution, profile, or successful play is
involved. -/
theorem source_commitments_revealed [IExpr.ResultTypes L]
    (source : SourceProgram.Initial (Player := Player) (L := L))
    {owner : Player} {payload : L.Ty} {name : VarId}
    (resource : HasVar source.program.terminalCtx name (.commitment owner payload)) :
    (SourceProgram.finalRevelations source.program
      (Revelations.initial source.context) resource).isRevealed = true :=
  source.revealed resource

/-- info: 'Vegas.Paper.source_commitments_revealed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_commitments_revealed

/-- Private inputs persist under every source policy without requiring publication. -/
theorem source_private_input_preserved [IExpr.ResultTypes L]
    (source : SourceProgram.Initial (Player := Player) (L := L))
    (profile : SourceProgram.BehavioralProfile source.program)
    (outcome : State L source.program.terminalCtx)
    (supported : outcome ∈ (source.run profile).support)
    {owner : Player} {payload : L.Ty} {name : VarId}
    (input : HasVar source.context name (.privateInput owner payload)) :
    outcome.get (SourceProgram.terminalRef source.program input) = source.state.get input :=
  SourceProgram.privateInput_preserved source.program profile
    ⟨source.state, [], Revelations.initial source.context, fun _ => []⟩ outcome supported input

/-- info: 'Vegas.Paper.source_private_input_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_private_input_preserved

omit [DecidableEq Player] in
/-- Native commitment provenance excludes handles for persistent private inputs. -/
theorem native_private_input_no_handle [IExpr.ResultTypes L]
    {graph : Vegas.EventGraph Player L} (state : EventGraphRuntime.State graph)
    (invariant : state.BindingInvariant) (field : graph.Field) (owner : Player) (payload : L.Ty)
    (kind : graph.layout field = .privateInput owner payload) : state.accepted field = none :=
  invariant.privateInput_no_handle field owner payload kind

/-- info: 'Vegas.Paper.native_private_input_no_handle' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.native_private_input_no_handle

/-- An authenticated commitment is binding from submission onward, including
through arbitrary preparation and network actions before inclusion. -/
theorem native_commitment_binding [IExpr.ResultTypes L]
    {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (who : Player)
    (event : graph.EventId) (slot : EventGraphRuntime.CandidateSlot graph)
    (actions : List runtime.application.Action) (after : runtime.application.State)
    (supported : after ∈ (runtime.application.run actions
      (runtime.application.afterSubmit execution who
        (.commitment event (who, slot))).native).support) :
    after.application.candidates.lookup (who, slot) =
      (execution.native.application.candidates.freeze (who, slot)).lookup (who, slot) :=
  EventGraphRuntime.submitted_commitment_binding runtime execution who event slot
    actions after supported

/-- info: 'Vegas.Paper.native_commitment_binding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.native_commitment_binding

/-- Every complete failure-aware source execution decides each retained guard
by its code: either the publication of its subject or of an input read by its
code failed, or all of them succeeded and the code holds on the published
values. Publications are read through the final revelations, which reveal every
commitment (`source_commitments_revealed`). This includes executions with
invalid bindings or withheld disclosures. -/
theorem source_guards_hold [IExpr.ResultTypes L]
    (source : SourceProgram.Initial (Player := Player) (L := L))
    (profile : SourceProgram.BehavioralProfile source.program)
    (outcome : State L source.program.terminalCtx)
    (supported : outcome ∈ (source.run profile).support)
    (obligation : SourceProgram.Obligation source.program.terminalCtx)
    (member : obligation ∈ SourceProgram.finalRegistry source.program []) :
    let revelations : Revelations source.program.terminalCtx :=
      SourceProgram.finalRevelations source.program
      (Revelations.initial source.context)
    ((revelations obligation.source).result outcome = .failure ∨
      ∃ (x : VarId) (τ : L.Ty) (h : HasVar obligation.guard.schema x τ),
        x ∈ L.exprDeps obligation.guard.code ∧
          (obligation.guard.reads h).result revelations outcome = .failure) ∨
    ∃ (subjectValue : L.Val obligation.payload)
      (get : (x : VarId) → (σ : L.Ty) →
        HasVar ((obligation.subject, obligation.payload) :: obligation.guard.schema) x σ →
          x ∈ L.exprDeps obligation.guard.code → L.Val σ),
      (revelations obligation.source).result outcome = .success subjectValue ∧
      (∀ hx, get obligation.subject obligation.payload .here hx = subjectValue) ∧
      (∀ {x τ} (h : HasVar obligation.guard.schema x τ)
        (hx : x ∈ L.exprDeps obligation.guard.code),
          (obligation.guard.reads h).result revelations outcome =
            .success (get x τ (.there h) hx)) ∧
      L.toBool (L.evalDeps obligation.guard.code get) = true :=
  source.terminal_guards_hold profile outcome supported obligation member

/-- info: 'Vegas.Paper.source_guards_hold' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_guards_hold

/-! ## Dependency-driven graph capstones -/

/-- Running the dependency-driven graph in source order preserves the full
source terminal-state law, including a private initial setup distribution.
The scheduler is an instance of the ordinary ready-event executor. -/
theorem source_event_graph_canonical_law [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (profile : SourceProgram.BehavioralProfile setup.program) :
    ((setup.eventGraph.canonicalGame
        (setup.initialLaw.map fun initial => setup.eventInputs initial)).play
      (Vegas.compileEventProfile setup.program
        profile)).map
          (Vegas.terminalState setup.program) =
      setup.run profile :=
  Vegas.canonical_setup_law setup profile

/-- info: 'Vegas.Paper.source_event_graph_canonical_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_event_graph_canonical_law

/-- A source-order graph deviation has one source-policy preimage, chosen
uniformly across private initial setup and against unchanged opponents. -/
theorem source_event_graph_canonical_deviation_law [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (profile : SourceProgram.BehavioralProfile setup.program) (who : Player)
    (replacement : setup.eventGraph.BehavioralPolicy who) :
    ((setup.eventGraph.canonicalGame
        (setup.initialLaw.map fun initial => setup.eventInputs initial)).play
      (Profile.update (sig := setup.eventGraph.gameSignature)
        (Vegas.compileEventProfile setup.program profile)
        who replacement)).map
          (Vegas.terminalState setup.program) =
      setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program) profile who
        (Vegas.backtranslateEventPolicy setup.program
          who replacement)) :=
  Vegas.canonical_setup_deviation_law setup profile who replacement

/-- info: 'Vegas.Paper.source_event_graph_canonical_deviation_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_event_graph_canonical_deviation_law

/-- Evaluating the compiled graph's retained payout code agrees with source
payout evaluation on its decoded terminal state. Utilities remain a separate
interpretation of outcomes. -/
theorem source_event_graph_payout_readout [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (result : {config : setup.eventGraph.Config // config.cut.Terminal}) :
    Vegas.terminalPayouts setup.program result =
      setup.program.evaluatePayoffs
        (Vegas.terminalState setup.program result) :=
  Vegas.terminalPayouts_eq_source setup.program result

/-- info: 'Vegas.Paper.source_event_graph_payout_readout' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_event_graph_payout_readout

/-! ## Asynchronous graph capstones

These are exact targets over the actual graph executor and policy compiler.
The scheduler observes the ideal graph's public store and completion order;
this is not yet the public-message protocol. The source deviation mixture is
chosen before private setup is sampled.
-/

/-- Public asynchronous scheduling preserves and reflects same-error Nash
at normalized canonical profiles for every utility of the terminal typed
store. The compiler supplies the public-barrier certificate. Every event has
finitely many actions and the input law is finitely supported. -/
theorem event_graph_scheduling_approximate_nash_iff [IExpr.ResultTypes L]
    (graph : Vegas.EventGraph Player L) (ordered : graph.BarrierOrdered)
    (finite : graph.FiniteActions)
    (inputs : PMF graph.Inputs) (finiteInputs : inputs.support.Finite)
    (scheduler : graph.PublicScheduler)
    (utility : EventGraph.Store graph.layout → Player → ℝ)
    (ε : ℝ) (profile : graph.BehavioralProfile) :
    IsεNash (graph.gameForm inputs scheduler)
        (fun outcome who => utility (graph.terminalStore outcome) who) ε
        (graph.normalizeProfile profile) ↔
      IsεNash (graph.canonicalGame inputs)
        (fun outcome who => utility (graph.terminalStore outcome) who) ε profile :=
  graph.eventScheduling_approximate_nash_iff ordered finite inputs finiteInputs scheduler utility ε
    profile

/-- info: 'Vegas.Paper.event_graph_scheduling_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.event_graph_scheduling_approximate_nash_iff

/-- Every public schedule of compiled source policies has the source
terminal-state law. -/
theorem source_event_graph_honest_law [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (scheduler : setup.eventGraph.PublicScheduler)
    (profile : SourceProgram.BehavioralProfile setup.program) :
    (setup.initialLaw.bind fun initial =>
      (setup.eventGraph.terminalOutcomes scheduler
        (Vegas.compileEventProfile setup.program profile)
        (setup.eventInputs initial)).map
          (Vegas.terminalState setup.program)) =
      setup.run profile :=
  Vegas.scheduled_setup_law setup scheduler profile

/-- info: 'Vegas.Paper.source_event_graph_honest_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_event_graph_honest_law

/-- An arbitrary unilateral asynchronous graph deviation has a finite
mixture of source deviations against unchanged opponents. Commitment payload
types are finite and the private setup law is finitely supported. -/
theorem source_event_graph_deviation_law [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (scheduler : setup.eventGraph.PublicScheduler)
    (profile : SourceProgram.BehavioralProfile setup.program) (who : Player)
    (replacement : setup.eventGraph.BehavioralPolicy who) :
    ∃ mixture : PMF (SourceProgram.BehavioralPolicy who setup.program), mixture.support.Finite ∧
      (setup.initialLaw.bind fun initial =>
        (setup.eventGraph.terminalOutcomes scheduler
          (Profile.update (sig := setup.eventGraph.gameSignature)
            (Vegas.compileEventProfile setup.program profile)
            who replacement)
          (setup.eventInputs initial)).map
            (Vegas.terminalState setup.program)) =
        mixture.bind fun alternative =>
          setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program)
            profile who alternative) :=
  Vegas.scheduled_setup_deviation_law setup finite scheduler profile who
    replacement

/-- info: 'Vegas.Paper.source_event_graph_deviation_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_event_graph_deviation_law

/-- Full-source compilation preserves and reflects same-error Nash at the
actual asynchronously scheduled graph profile, for every utility of the public
source result. Commitment payload types are finite and the private setup law is
finitely supported. -/
theorem source_event_graph_approximate_nash_iff [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (scheduler : setup.eventGraph.PublicScheduler)
    (utility : SourceProgram.PublicOutcome setup.program → Player → ℝ)
    (ε : ℝ) (profile : SourceProgram.BehavioralProfile setup.program) :
    IsεNash (setup.eventGame scheduler)
        (fun outcome who => utility (SourceProgram.publicOutcome setup.program
          (Vegas.terminalState setup.program outcome)) who)
        ε (Vegas.compileEventProfile setup.program
          profile) ↔
      IsεNash setup.gameForm utility ε profile :=
  setup.eventGame_approximate_nash_iff finite scheduler utility ε profile

/-- info: 'Vegas.Paper.source_event_graph_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_event_graph_approximate_nash_iff

/-- The event-addressed pending game produces a complete graph outcome under
arbitrary player policies, adaptive wire delivery, and public service ordering.
This completion guarantee does not require prescribed player behavior. -/
theorem event_pending_completion [IExpr.ResultTypes L]
    {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
    (inputs : PMF graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (players : Player → runtime.application.PlayerPolicy)
    (next : runtime.application.PolicyExecution)
    (supported : next ∈
      ((runtime.servicedEventGame inputs roster reactionRounds wire order).play players).support) :
    next.native.application.config.outcome?.isSome = true :=
  runtime.servicedEventGame_outcome_total inputs roster reactionRounds wire order players next
    supported

/-- info: 'Vegas.Paper.event_pending_completion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.event_pending_completion

/-- Adding source-order barriers enforces source-ranked completion in the
same native runtime, including under arbitrary player and service policies. -/
theorem sequential_pending_completion_order [IExpr.ResultTypes L]
    {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph.sequentialize)
    (inputs : PMF graph.sequentialize.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (players : Player → runtime.application.PlayerPolicy)
    (next : runtime.application.PolicyExecution)
    (supported : next ∈
      ((runtime.servicedEventGame inputs roster reactionRounds wire order).play players).support) :
    next.native.application.config.history.map EventGraph.Completion.event =
      List.finRange graph.order.eventCount :=
  runtime.servicedSequentialGame_history inputs roster reactionRounds wire order players next
    supported

/-- info: 'Vegas.Paper.sequential_pending_completion_order' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sequential_pending_completion_order

/-! ## Pending-message capstones

Both sequential and concurrent dependency modes use these statements and the
same native executor. These statements use the concrete compiler and service, not a hypothesized
simulation certificate. `ServiceFeasible` requires at least two clock ticks
per event deadline so an event enabled mid-epoch receives its reserved service
opportunities. The compiler's public barriers support exact deviation laws
without a failure-dominance premise. The deviation mixture is chosen before
the private initial state is sampled.
-/

/-- The compiled full-source profile has the source terminal-state law in
either dependency mode of the pending-message runtime. -/
theorem source_event_pending_honest_law [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (profile : SourceProgram.BehavioralProfile setup.program) :
    ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
      (fun who => setup.compileEventPendingStrategy mode runtime who (profile who))).map
        (setup.eventPendingOutcome mode runtime) = (setup.run profile).map some :=
  setup.eventPendingGame_honest_law mode runtime feasible roster reactionRounds wire order profile

/-- info: 'Vegas.Paper.source_event_pending_honest_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_event_pending_honest_law

/-- Every finitely branching native unilateral deviation has the terminal
source-state law of a finite mixture of source deviations against unchanged
opponents. One mixture is chosen across the entire private setup law. -/
theorem source_event_pending_deviation_law [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (mode : EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (wireFinite : wire.FiniteSupport)
    (order : runtime.ServiceOrderPolicy) (orderFinite : order.FiniteSupport)
    (profile : SourceProgram.BehavioralProfile setup.program) (who : Player)
    (replacement : runtime.application.PlayerPolicy)
    (replacementFinite : replacement.FiniteSupport) :
    ∃ mixture : PMF (SourceProgram.BehavioralPolicy who setup.program), mixture.support.Finite ∧
      ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
        (Profile.update (sig := (setup.eventPendingGame mode runtime
          roster reactionRounds wire order).sig)
          (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))
          who replacement)).map (setup.eventPendingOutcome mode runtime) =
      mixture.bind fun alternative =>
        (setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program)
          profile who alternative)).map some :=
  setup.eventPendingGame_deviation_law finite mode runtime feasible roster reactionRounds wire
    wireFinite order orderFinite profile who replacement replacementFinite

/-- info: 'Vegas.Paper.source_event_pending_deviation_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_event_pending_deviation_law

/-- Same-error Nash preservation and reflection at compiled source
profiles in either pending-message dependency mode, for every utility of the
public source result. The utility assigned to a missing outcome is arbitrary;
the concrete service has a separate proved completion theorem. Native
deviations range over finitely branching player policies.

The utility domain here is the outcome, which is the public result. The
deviation law above is the stronger statement, over complete terminal source
states; it is not what this theorem quantifies over. -/
theorem source_event_pending_approximate_nash_iff [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (mode : EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (wireFinite : wire.FiniteSupport)
    (order : runtime.ServiceOrderPolicy) (orderFinite : order.FiniteSupport)
    (utility : SourceProgram.PublicOutcome setup.program → Player → ℝ)
    (missing : Player → ℝ) (ε : ℝ)
    (profile : SourceProgram.BehavioralProfile setup.program) :
    (∀ who (replacement : runtime.application.PlayerPolicy), replacement.FiniteSupport →
      euPreferenceWithin ε
        (fun outcome who => (setup.eventPendingPublicOutcome mode runtime outcome).elim
          (missing who) (fun result => utility result who)) who
        ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
          (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor)))
        ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
          (Profile.update (sig := (setup.eventPendingGame mode runtime
            roster reactionRounds wire order).sig)
            (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))
            who replacement))) ↔
      IsεNash setup.gameForm utility ε profile :=
  setup.eventPendingGame_approximate_nash_iff finite mode runtime feasible roster reactionRounds
    wire wireFinite order orderFinite utility missing ε profile

/-- info: 'Vegas.Paper.source_event_pending_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_event_pending_approximate_nash_iff

/-- Public-result lower bounds survive finitely branching unilateral native
deviations in either dependency mode, independently of adversary preferences. -/
theorem source_event_pending_deviation_guarantee [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (mode : EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (wireFinite : wire.FiniteSupport)
    (order : runtime.ServiceOrderPolicy) (orderFinite : order.FiniteSupport)
    (profile : SourceProgram.BehavioralProfile setup.program) (who : Player)
    (value : SourceProgram.PublicOutcome setup.program → ℝ) (missing bound : ℝ)
    (sourceBound : ∀ alternative : SourceProgram.BehavioralPolicy who setup.program,
      bound ≤ expect (setup.publicRun
        (Profile.update (sig := SourceProgram.gameSignature setup.program)
          profile who alternative)) value)
    (replacement : runtime.application.PlayerPolicy)
    (replacementFinite : replacement.FiniteSupport) :
    bound ≤ expect ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
      (Profile.update (sig := (setup.eventPendingGame mode runtime
        roster reactionRounds wire order).sig)
        (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))
        who replacement))
          (fun outcome =>
            (setup.eventPendingPublicOutcome mode runtime outcome).elim missing value) :=
  setup.eventPendingGame_deviation_guarantee finite mode runtime feasible roster reactionRounds
    wire wireFinite order orderFinite profile who value missing bound sourceBound replacement
    replacementFinite

/-- info: 'Vegas.Paper.source_event_pending_deviation_guarantee' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_event_pending_deviation_guarantee

/-! ## Source-side restrictions

Two moves the source language offers buy a *deviator* nothing: binding a
candidate that will never open, and randomizing. Each restriction is a game of
its own, each simulates the full source game with every deviation considered,
and each therefore composes onto the same message host.

Both readings are about a profile already in the restricted class, and about the
deviations it is checked against. Neither says the restricted game has an
equilibrium: restricting which profiles are considered is a different question
from restricting which deviations they face, and matching pennies is the
standing reminder that a pure game need not have one. -/

/-- Same-error Nash preservation and reflection between the game whose policies
always bind a value and the pending-message service, against finitely branching
native deviations. Commit-time failure is not among the source moves here. -/
theorem value_binding_event_pending_approximate_nash_iff [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (mode : EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (wireFinite : wire.FiniteSupport)
    (order : runtime.ServiceOrderPolicy) (orderFinite : order.FiniteSupport)
    (utility : SourceProgram.PublicOutcome setup.program → Player → ℝ)
    (missing : Player → ℝ) (ε : ℝ)
    (profile : Profile setup.valueBindingGame.sig) :
    (∀ who (replacement : runtime.application.PlayerPolicy), replacement.FiniteSupport →
      euPreferenceWithin ε
        (fun outcome who => (setup.eventPendingPublicOutcome mode runtime outcome).elim
          (missing who) (fun result => utility result who)) who
        ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
          (fun who => setup.compileValueBindingPendingProfile mode runtime who (profile who)))
        ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
          (Profile.update (sig := (setup.eventPendingGame mode runtime
            roster reactionRounds wire order).sig)
            (fun who => setup.compileValueBindingPendingProfile mode runtime who (profile who))
            who replacement))) ↔
      IsεNash setup.valueBindingGame utility ε profile :=
  setup.valueBindingPendingGame_approximate_nash_iff finite mode runtime feasible roster
    reactionRounds wire wireFinite order orderFinite utility missing ε profile

/-- info: 'Vegas.Paper.value_binding_event_pending_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.value_binding_event_pending_approximate_nash_iff

/-- The same for the game whose policies never randomize: checking a pure source
profile against the real host needs only pure source deviations. -/
theorem pure_event_pending_approximate_nash_iff [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (mode : EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (wireFinite : wire.FiniteSupport)
    (order : runtime.ServiceOrderPolicy) (orderFinite : order.FiniteSupport)
    (utility : SourceProgram.PublicOutcome setup.program → Player → ℝ)
    (missing : Player → ℝ) (ε : ℝ)
    (profile : Profile setup.pureGame.sig) :
    (∀ who (replacement : runtime.application.PlayerPolicy), replacement.FiniteSupport →
      euPreferenceWithin ε
        (fun outcome who => (setup.eventPendingPublicOutcome mode runtime outcome).elim
          (missing who) (fun result => utility result who)) who
        ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
          (fun who => setup.compilePurePendingProfile mode runtime who (profile who)))
        ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
          (Profile.update (sig := (setup.eventPendingGame mode runtime
            roster reactionRounds wire order).sig)
            (fun who => setup.compilePurePendingProfile mode runtime who (profile who))
            who replacement))) ↔
      IsεNash setup.pureGame utility ε profile :=
  setup.purePendingGame_approximate_nash_iff finite mode runtime feasible roster reactionRounds
    wire wireFinite order orderFinite utility missing ε profile

/-- info: 'Vegas.Paper.pure_event_pending_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pure_event_pending_approximate_nash_iff

/-! ## Private initial types and truthful plans -/

/-- Compiled prescribed play preserves the joint initial-parameter/public-result law. -/
theorem private_type_event_pending_honest_law [IExpr.ResultTypes L] {Parameter : Type}
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (parameter : State L setup.context → Parameter)
    (mode : EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (wireFinite : wire.FiniteSupport)
    (order : runtime.ServiceOrderPolicy) (orderFinite : order.FiniteSupport)
    (profile : Profile (setup.valueBindingParameterGame parameter).sig) :
    ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
      (fun who => setup.compileValueBindingPendingProfile mode runtime who (profile who))).map
        (setup.eventPendingParameterOutcome parameter mode runtime) =
      ((setup.valueBindingParameterGame parameter).play profile).map some :=
  (setup.valueBindingParameterPendingSimulation finite parameter mode runtime feasible roster
    reactionRounds wire wireFinite order orderFinite).honest_law profile

/-- info: 'Vegas.Paper.private_type_event_pending_honest_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.private_type_event_pending_honest_law

/-- The value-only source abstraction preserves the joint law of initial
parameters and public results, with one deviation mixture across the prior. -/
theorem private_type_event_pending_deviation_law [IExpr.ResultTypes L] {Parameter : Type}
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (parameter : State L setup.context → Parameter)
    (mode : EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (wireFinite : wire.FiniteSupport)
    (order : runtime.ServiceOrderPolicy) (orderFinite : order.FiniteSupport)
    (profile : Profile (setup.valueBindingParameterGame parameter).sig) (who : Player)
    (replacement : runtime.application.PlayerPolicy)
    (replacementFinite : replacement.FiniteSupport) :
    ∃ mixture : PMF (SourceProgram.ValueBindingPolicy who setup.program),
      ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
        (Profile.update (sig := (setup.eventPendingGame mode runtime
          roster reactionRounds wire order).sig)
          (fun actor => setup.compileValueBindingPendingProfile mode runtime actor (profile actor))
          who replacement)).map (setup.eventPendingParameterOutcome parameter mode runtime) =
      mixture.bind fun alternative =>
        ((setup.valueBindingParameterGame parameter).play
          (Profile.update profile who alternative)).map some :=
  (setup.valueBindingParameterPendingSimulation finite parameter mode runtime feasible roster
    reactionRounds wire wireFinite order orderFinite).deviation_mixture profile who replacement
      replacementFinite

/-- info: 'Vegas.Paper.private_type_event_pending_deviation_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.private_type_event_pending_deviation_law

/-- Bayesian incentives for a designated source plan, including a truthful
plan, are preserved and reflected without exposing commit-time failure.
Approximation is measured ex ante under the fixed finite prior. -/
theorem private_type_event_pending_approximate_nash_iff [IExpr.ResultTypes L] {Parameter : Type}
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (parameter : State L setup.context → Parameter)
    (mode : EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (wireFinite : wire.FiniteSupport)
    (order : runtime.ServiceOrderPolicy) (orderFinite : order.FiniteSupport)
    (utility : Parameter × SourceProgram.PublicOutcome setup.program → Player → ℝ)
    (missing : Player → ℝ) (ε : ℝ)
    (profile : Profile (setup.valueBindingParameterGame parameter).sig) :
    (∀ who (replacement : runtime.application.PlayerPolicy), replacement.FiniteSupport →
      euPreferenceWithin ε
        (fun outcome who => (setup.eventPendingParameterOutcome parameter mode runtime outcome).elim
          (missing who) (fun result => utility result who)) who
        ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
          (fun who => setup.compileValueBindingPendingProfile mode runtime who (profile who)))
        ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
          (Profile.update (sig := (setup.eventPendingGame mode runtime
            roster reactionRounds wire order).sig)
            (fun who => setup.compileValueBindingPendingProfile mode runtime who (profile who))
            who replacement))) ↔
      IsεNash (setup.valueBindingParameterGame parameter) utility ε profile :=
  setup.valueBindingParameterPendingGame_approximate_nash_iff finite parameter mode runtime
    feasible roster reactionRounds wire wireFinite order orderFinite utility missing ε profile

/-- info: 'Vegas.Paper.private_type_event_pending_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.private_type_event_pending_approximate_nash_iff

/-- The concrete second-price source program is not dominant-strategy truthful:
an opponent can condition withholding on the earlier public report. -/
theorem auction_truthful_not_dominant
    (values : Examples.CommitRevealAuction.Player → ℝ) (forfeiture : ℝ)
    (valuation : values .alice = 5) :
    ¬ IsDominant Examples.CommitRevealAuction.setup.valueBindingGame
      (euPreference (Examples.CommitRevealAuction.utility values forfeiture))
      Examples.CommitRevealAuction.Player.alice (Examples.CommitRevealAuction.aliceStrategy 5) :=
  Examples.CommitRevealAuction.truthful_not_dominant values forfeiture valuation

/-- info: 'Vegas.Paper.auction_truthful_not_dominant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.auction_truthful_not_dominant

universe uTargetStrategy uTargetOutcome

/-- No utility-preserving translation of this source game can make the
translated truthful policy dominant. The quantified target is unrestricted;
changing the source game is outside this impossibility claim. -/
theorem auction_translated_truthful_not_dominant
    (values : Examples.CommitRevealAuction.Player → ℝ) (forfeiture : ℝ)
    (valuation : values .alice = 5)
    (target : GameForm.{0, uTargetStrategy, uTargetOutcome} Examples.CommitRevealAuction.Player)
    (compile : (who : Examples.CommitRevealAuction.Player) →
      Examples.CommitRevealAuction.setup.valueBindingGame.sig.Strategy who →
      target.sig.Strategy who)
    (targetUtility : target.sig.Outcome → Examples.CommitRevealAuction.Player → ℝ)
    (preserves : ∀ players : Profile Examples.CommitRevealAuction.setup.valueBindingGame.sig,
      expectedUtility targetUtility Examples.CommitRevealAuction.Player.alice
          (target.play (Profile.map compile players)) =
        expectedUtility (Examples.CommitRevealAuction.utility values forfeiture)
          Examples.CommitRevealAuction.Player.alice
          (Examples.CommitRevealAuction.setup.valueBindingGame.play players))
    (targetIntegrable : ∀ players : Profile Examples.CommitRevealAuction.setup.valueBindingGame.sig,
      UtilityIntegrable targetUtility Examples.CommitRevealAuction.Player.alice
        (target.play (Profile.map compile players))) :
    ¬ IsDominant target (euPreference targetUtility) Examples.CommitRevealAuction.Player.alice
      (compile Examples.CommitRevealAuction.Player.alice
        (Examples.CommitRevealAuction.aliceStrategy 5)) :=
  Examples.CommitRevealAuction.translated_truthful_not_dominant values forfeiture valuation
    target compile targetUtility preserves targetIntegrable

/-- info: 'Vegas.Paper.auction_translated_truthful_not_dominant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.auction_translated_truthful_not_dominant

/-! ## Honest play -/

/-- An honest profile -- one that binds a value at every commitment and opens at
every reveal -- completes with no failure recorded anywhere, provided the guards
it retains accept what it actually binds. The premise follows the run: a guard
that rejects a value this profile never binds is no obstacle. -/
theorem source_honest_run_successful [IExpr.ResultTypes L]
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (p : SourceProgram Player L Γ O) (profile : SourceProgram.BehavioralProfile p)
    (honest : ∀ who, SourceProgram.Honest p (profile who))
    (state : State L Γ) (hstate : SourceProgram.Successful state)
    (guards : SourceProgram.GuardsAcceptFrom p profile
      ⟨state, [], Revelations.initial Γ, fun _ => []⟩) :
    ∀ terminal ∈ (SourceProgram.run p profile state).support,
      SourceProgram.Successful terminal :=
  SourceProgram.run_successful p profile honest state hstate guards

/-- info: 'Vegas.Paper.source_honest_run_successful' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_honest_run_successful

/-! ## Abstraction of terminal decisions -/

/-- For a fully informed terminal decision, a deterministic observation
preserves every optimal retained outcome for every fact/report utility exactly
when it determines the retained fact on the prior support. The target policy
may depend on the utility; the necessity claim is stronger than failure of a
particular compiler. This is a decision-experiment theorem. -/
theorem terminal_observation_classification {State Signal Fact : Type*}
    [Finite Fact] [Nonempty Fact]
    (prior : PMF State) (priorFinite : prior.support.Finite) (observe : State → Signal)
    (fact : State → Fact) :
    (∀ utility : Fact → Fact → ℝ, ∀ source : Signal → PMF Fact,
      DecisionExperiment.IsBayesOptimal prior observe (fun state => utility (fact state)) source →
        ∃ target : State → PMF Fact,
          DecisionExperiment.IsBayesOptimal prior id (fun state => utility (fact state)) target ∧
            DecisionExperiment.resultLaw prior id fact target =
              DecisionExperiment.resultLaw prior observe fact source) ↔
      DecisionExperiment.Determines prior observe fact :=
  DecisionExperiment.preserves_all_optima_iff_determines prior priorFinite observe fact

/-- info: 'Vegas.Paper.terminal_observation_classification' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.terminal_observation_classification

/-- Retaining the payoff-relevant fact preserves the entire set of optimal
fact/action outcome laws, for arbitrary public actions and utilities. -/
theorem terminal_observation_optimal_laws {State Signal Fact Action : Type*}
    (prior : PMF State) (priorFinite : prior.support.Finite) (observe : State → Signal)
    (fact : State → Fact)
    (determines : DecisionExperiment.Determines prior observe fact)
    (utility : Fact → Action → ℝ) (law : PMF (Fact × Action)) :
    (∃ policy : Signal → PMF Action,
      DecisionExperiment.IsBayesOptimal prior observe (fun state => utility (fact state)) policy ∧
        DecisionExperiment.resultLaw prior observe fact policy = law) ↔
    (∃ policy : State → PMF Action,
      DecisionExperiment.IsBayesOptimal prior id (fun state => utility (fact state)) policy ∧
        DecisionExperiment.resultLaw prior id fact policy = law) :=
  DecisionExperiment.optimal_result_law_iff prior priorFinite observe fact determines utility
    law

/-- info: 'Vegas.Paper.terminal_observation_optimal_laws' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.terminal_observation_optimal_laws

open DecisionExperiment.Protocol in
/-- The observation criterion also characterizes preservation of every
standard sequential-equilibrium outcome of the terminal decision protocol.
The conclusion allows target strategies and beliefs to depend on the utility. -/
theorem terminal_sequential_observation_classification {State Signal Fact : Type}
    [Finite State] [Finite Fact] [Nonempty Fact]
    (prior : PMF State) (observe : State → Signal) (fact : State → Fact) :
    (∀ utility : Fact → Fact → ℝ,
      ∀ source : (model (Action := Fact) prior observe).BehavioralAssessment,
        source.IsSequentialEquilibrium (antichain prior observe)
          (certificate prior) (fun _ history => payoff (fun state => utility (fact state))
              history.state) →
        ∃ target : (model (Action := Fact) prior id).BehavioralAssessment,
          target.IsSequentialEquilibrium (antichain prior id)
            (certificate prior) (fun _ history => payoff (fun state => utility (fact state))
                history.state) ∧
          observedLaw prior id fact target = observedLaw prior observe fact source) ↔
      DecisionExperiment.Determines prior observe fact :=
  preserves_all_sequentialEquilibria_iff_determines prior observe fact

/-- info: 'Vegas.Paper.terminal_sequential_observation_classification' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.terminal_sequential_observation_classification

open DecisionExperiment.Protocol in
/-- With one declared payoff, a terminal observation may erase a fact precisely
when each supported observation fiber has a common maximizing action. The result
preserves every abstract SE's retained law and permits payoff-dependent target
assessments. It is a one-player terminal classification, not a native compiler
preservation theorem. -/
theorem terminal_fixed_payoff_sequential_classification {State Signal Fact Action : Type}
    [Finite State] [Finite Action] [Nonempty Action]
    (prior : PMF State) (observe : State → Signal) (fact : State → Fact)
    (utility : Fact → Action → ℝ) :
    (∀ source : (model (Action := Action) prior observe).BehavioralAssessment,
      source.IsSequentialEquilibrium (antichain prior observe)
        (certificate prior) (fun _ history => payoff (fun state => utility (fact state))
            history.state) →
      ∃ target : (model (Action := Action) prior id).BehavioralAssessment,
        target.IsSequentialEquilibrium (antichain prior id)
          (certificate prior) (fun _ history => payoff (fun state => utility (fact state))
              history.state) ∧
        observedLaw prior id fact target = observedLaw prior observe fact source) ↔
      DecisionExperiment.HasCommonMaximizer prior observe (fun state => utility (fact state)) :=
  preserves_fixed_payoff_sequentialEquilibria_iff_commonMaximizer prior observe fact utility

/-- info: 'Vegas.Paper.terminal_fixed_payoff_sequential_classification' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.terminal_fixed_payoff_sequential_classification

open Vegas.Examples.SelectiveAssociation in
/-- The actual six-event program has an SE whose returned-payoff law cannot
occur at any sequentially rational assessment of its compiled native game.
Alice's expected source payout is zero; every rational native assessment gives
expected payout at least one half.
The declared payoff and native service are fixed; arbitrary utility-aware
strategy and belief translations into this target are excluded. -/
theorem declared_payoff_sequential_separation (Claim : Type) [Fintype Claim]
    (defaultClaim : Claim) :
    ∃ source : (NamedSource.model Claim).BehavioralAssessment,
      source.IsSequentialEquilibrium
        ((NamedSource.menu Claim).decisionInformationAntichain (PMF.pure NamedSource.initial)
          NamedSource.horizon (NamedSource.scheduler Claim))
        (NamedSource.terminates Claim) NamedSource.payoff ∧
      expect (sourcePayoutLaw source.strategy) id = 0 ∧
      ∀ target : nativeModel.BehavioralAssessment,
        target.IsSequentiallyRational nativeTerminates
            (fun who history => nativeUtility who history.state) →
        sourcePayoutLaw source.strategy ≠ nativePayoutLaw target.strategy :=
  exists_source_equilibrium_no_native_payout_match Claim defaultClaim

/-- info: 'Vegas.Paper.declared_payoff_sequential_separation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.declared_payoff_sequential_separation

/-! ## Full-language sequential equilibrium

The native service, the audit backend and the deposit are fixed before a
source equilibrium is chosen. The statement retains bounded interaction and a
finite response interface, so every commitment payload type is finite; it
asserts no cryptographic or EVM refinement.
-/

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

/-! ## Runtime feature investigation

These results isolate the information effect of passive observation in the
existing native runtime and constrain observation-respecting abstractions.
The restricted native equilibrium is a separate, open proof obligation.
-/

/-- info: 'Interaction.ReactiveApplication.PacketEvidence.foreign_known_published' depends on
axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.PacketEvidence.foreign_known_published

/-- info: 'Vegas.EventGraphRuntime.foreign_certificate_published' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.foreign_certificate_published

/-- info:
'GameTheory.Protocol.InformationModel.ContinuationDecision.observation_fiber_has_common_maximizer'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Protocol.InformationModel.ContinuationDecision.observation_fiber_has_common_maximizer

/-- info: 'Vegas.Examples.SelectiveAssociation.Restricted.four_rounds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.SelectiveAssociation.Restricted.four_rounds

/-- info: 'Vegas.Examples.SelectiveAssociation.Restricted.association_input_hidden' depends on
axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.SelectiveAssociation.Restricted.association_input_hidden

/-- info: 'Vegas.Examples.SelectiveAssociation.Restricted.first_response_guess_bound' depends on
axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.SelectiveAssociation.Restricted.first_response_guess_bound

/-- info: 'Vegas.Examples.SelectiveAssociation.Restricted.binding_success' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.SelectiveAssociation.Restricted.binding_success

/-- info: 'Vegas.Examples.SelectiveAssociation.Restricted.profile_opening_rational' depends on
axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.SelectiveAssociation.Restricted.profile_opening_rational

/-- info: 'Vegas.Examples.SelectiveAssociation.Restricted.CandidateFlip.uniform_prob_of_known_ids'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.SelectiveAssociation.Restricted.CandidateFlip.uniform_prob_of_known_ids

/-- info: 'Vegas.Examples.ReactiveReadinessRestrictions.disclosure_with_ready_commitment_calls'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ReactiveReadinessRestrictions.disclosure_with_ready_commitment_calls

/-- info: 'Vegas.Examples.ReactiveReadinessRestrictions.empty_pool_cleanup_preserves_asymmetry'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ReactiveReadinessRestrictions.empty_pool_cleanup_preserves_asymmetry

/-- info:
'GameTheory.Protocol.InformationModel.ContinuationDecision.rationalAt_of_omitted_dominated' depends
on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  GameTheory.Protocol.InformationModel.ContinuationDecision.rationalAt_of_omitted_dominated

/-- info: 'GameTheory.Math.Probability.filter_observation_toOuterMeasure_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Math.Probability.filter_observation_toOuterMeasure_le

/-- info: 'GameTheory.Math.Probability.PMFConvergesPointwise.toOuterMeasure_toReal_le' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Math.Probability.PMFConvergesPointwise.toOuterMeasure_toReal_le

/-- info:
'GameTheory.Protocol.InformationModel.BehavioralAssessment.continuationContextWith_value_eq_expect_commit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms BehavioralAssessment.continuationContextWith_value_eq_expect_commit

/-- info: 'Vegas.Examples.SelectiveAssociation.Restricted.profile_guesser_rational' depends on
axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.SelectiveAssociation.Restricted.profile_guesser_rational

/-- info: 'Vegas.Examples.SelectiveAssociation.Restricted.bob_prelude_rational' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.SelectiveAssociation.Restricted.bob_prelude_rational

/-- info: 'Vegas.Examples.SelectiveAssociation.Restricted.initialized_payoff_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.SelectiveAssociation.Restricted.initialized_payoff_law

/-- info:
'Vegas.Examples.SelectiveAssociation.Restricted.exists_consistent_guess_assessment_of_tremble'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.SelectiveAssociation.Restricted.exists_consistent_guess_assessment_of_tremble

/-- info: 'Vegas.Examples.SelectiveAssociation.Restricted.alice_early_rational' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.SelectiveAssociation.Restricted.alice_early_rational

/-- info: 'Vegas.Examples.SelectiveAssociation.Restricted.prescribed_sequentiallyRational' depends
on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.SelectiveAssociation.Restricted.prescribed_sequentiallyRational

/-- info: 'Vegas.Examples.SelectiveAssociation.Restricted.exists_sequentialEquilibrium' depends on
axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SelectiveAssociation.Restricted in
#print axioms exists_sequentialEquilibrium

/-- info:
'Vegas.Examples.SelectiveAssociation.Restricted.exists_equilibrium_no_native_payout_match' depends
on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.SelectiveAssociation.Restricted in
#print axioms exists_equilibrium_no_native_payout_match

/-- info: 'GameTheory.IsCoarseCorrelatedEq.extendedExpectedUtility_eq_of_zeroSum' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.IsCoarseCorrelatedEq.extendedExpectedUtility_eq_of_zeroSum

/-- info: 'Vegas.SourceProgram.Setup.valueBindingParameterPendingGame_coarseCorrelated_value'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.SourceProgram.Setup in
#print axioms valueBindingParameterPendingGame_coarseCorrelated_value

/-- info: 'GameTheory.ZeroSumRegularization.exists_saddle' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.ZeroSumRegularization.exists_saddle

/-- info: 'GameTheory.IncentiveComparison.mem_coneWithin_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.IncentiveComparison.mem_coneWithin_iff

/-- info: 'GameTheory.IncentiveComparison.regret_le_norm_comparison_residual' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.IncentiveComparison.regret_le_norm_comparison_residual

/-- info: 'GameTheory.Protocol.InformationModel.sequentialEquilibrium_preservation_iff_coneWithin'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms sequentialEquilibrium_preservation_iff_coneWithin

/-- info: 'GameTheory.CorrelationPayoff.preserves_marginals_iff_additive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.CorrelationPayoff.preserves_marginals_iff_additive

/-- info: 'GameTheory.Enforcement.regret_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Enforcement.regret_le

/-- info: 'GameTheory.Enforcement.exists_optimal_sound_alarm' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Enforcement.exists_optimal_sound_alarm

/-- info: 'GameTheory.Enforcement.exists_sound_deterrent_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Enforcement.exists_sound_deterrent_iff

/-- info: 'GameTheory.Enforcement.exists_sound_alarm_for_penalty_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Enforcement.exists_sound_alarm_for_penalty_iff

/-- info: 'Interaction.MessageNetwork.sampling_delivery_lower' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageNetwork.sampling_delivery_lower

/-- info: 'Vegas.EventGraphRuntime.reactive_decision_submission_permitted' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.reactive_decision_submission_permitted

/-- info: 'GameTheory.Protocol.DisclosureEnforcement.source_equilibrium_implemented' depends on
axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.DisclosureEnforcement.source_equilibrium_implemented

/-- info: 'GameTheory.Protocol.DisclosureEnforcement.every_source_equilibrium_enforceable' depends
on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.DisclosureEnforcement.every_source_equilibrium_enforceable

/-- info: 'GameTheory.Protocol.DisclosureEnforcement.source_equilibrium_preserved_of_range' depends
on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.DisclosureEnforcement.source_equilibrium_preserved_of_range

/-- info: 'GameTheory.Protocol.DisclosureEnforcement.source_equilibrium_preserved_constant_sum'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Protocol.DisclosureEnforcement.source_equilibrium_preserved_constant_sum

/-- info:
'GameTheory.Protocol.InformationModel.BehavioralAssessment.isSequentiallyRationalAt_of_sanction'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel.BehavioralAssessment in
#print axioms isSequentiallyRationalAt_of_sanction

/-- info: 'Vegas.Examples.MonitoredGuessing.source_equilibrium_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.MonitoredGuessing in
#print axioms source_equilibrium_preserved

/-- info: 'Vegas.Examples.MonitoredGuessing.exists_native_sequential_equilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.MonitoredGuessing in
#print axioms exists_native_sequential_equilibrium

/-- info: 'Vegas.Examples.MonitoredGuessing.compiled_source_equilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.MonitoredGuessing in
#print axioms compiled_source_equilibrium

/-- info: 'GameTheory.Enforcement.exists_uniform_sanction_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Enforcement in
#print axioms exists_uniform_sanction_iff

/-- info: 'GameTheory.Protocol.InformationModel.exists_consistent_free_agent_completion' depends on
axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms exists_consistent_free_agent_completion

/-- info: 'GameTheory.Protocol.InformationModel.exists_sequentialEquilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel in
#print axioms exists_sequentialEquilibrium

/-- info: 'GameTheory.Protocol.InformationModel.ActionRestriction.sequential_equilibrium_extends'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel.ActionRestriction in
#print axioms sequential_equilibrium_extends

/-- info:
'GameTheory.Protocol.InformationModel.ActionRestriction.sequentialEquilibrium_extends_of_comparator'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel.ActionRestriction in
#print axioms sequentialEquilibrium_extends_of_comparator

/-- info:
'GameTheory.Protocol.InformationModel.ActionRestriction.sequentialEquilibrium_extends_of_continuation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Protocol.InformationModel.ActionRestriction in
#print axioms sequentialEquilibrium_extends_of_continuation

/-- info: 'GameTheory.Enforcement.inferred_deposit_minimal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open GameTheory.Enforcement in
#print axioms inferred_deposit_minimal

/-- info: 'Vegas.Examples.MonitoredGuessing.inferredCharge_deters' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.MonitoredGuessing in
#print axioms inferredCharge_deters

/-- info: 'Vegas.Examples.MonitoredGuessing.native_initialized_table_payoffs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.MonitoredGuessing in
#print axioms native_initialized_table_payoffs

/-- info: 'Vegas.Examples.MonitoredGuessing.Restricted.watcher_raw_equilibrium_extends' depends on
axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.MonitoredGuessing.Restricted in
#print axioms watcher_raw_equilibrium_extends

/-- info: 'Vegas.Examples.MonitoredGuessing.Restricted.final_comparator_declared_payoff_le' depends
on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.MonitoredGuessing.Restricted in
#print axioms final_comparator_declared_payoff_le

/-- info: 'Vegas.Examples.MonitoredGuessing.Restricted.source_equilibrium_compiles' depends on
axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.MonitoredGuessing.Restricted in
#print axioms source_equilibrium_compiles

/-- info: 'Vegas.Examples.MonitoredGuessing.Restricted.restricted_raw_equilibrium_extends' depends
on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.MonitoredGuessing.Restricted in
#print axioms restricted_raw_equilibrium_extends

/-- info: 'Vegas.Examples.MonitoredGuessing.declared_sequential_equilibrium_preserved' depends on
axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.Examples.MonitoredGuessing in
#print axioms declared_sequential_equilibrium_preserved

/-- info: 'Vegas.source_raw_sequential_equilibrium_preserved'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms source_raw_sequential_equilibrium_preserved

/-- info: 'Vegas.roster_audited_source_sequential_equilibrium_preserved'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms roster_audited_source_sequential_equilibrium_preserved

/-- info: 'Vegas.sourceService_audited_raw_equilibrium_extends'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms sourceService_audited_raw_equilibrium_extends

/-- info: 'Vegas.SourceServiceSpec.completeAudit_raw_sequentialEquilibrium_preserved'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms SourceServiceSpec.completeAudit_raw_sequentialEquilibrium_preserved

/-- info: 'Vegas.EventGraphRuntime.MessageBounds.audited_raw_sequential_equilibrium'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.EventGraphRuntime.MessageBounds in
#print axioms audited_raw_sequential_equilibrium

/-- info: 'Vegas.settled_audited_raw_sequential_equilibrium'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms settled_audited_raw_sequential_equilibrium

/-- info: 'Vegas.EventGraphRuntime.openingWindow_settlement' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas.EventGraphRuntime in
#print axioms openingWindow_settlement

/-- info: 'Interaction.ReactiveApplication.scheduledMixture_waiting_limit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Interaction.ReactiveApplication in
#print axioms scheduledMixture_waiting_limit

/-- info: 'Vegas.reactive_commit_repair' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
open Vegas in
#print axioms reactive_commit_repair

/-- info: 'Interaction.EvidenceReportService.sample_coverage' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.EvidenceReportService.sample_coverage

end Vegas.Paper
