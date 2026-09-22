/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.EventScheduling
import Vegas.Game.EventCompilation
import Vegas.Game.EventMessages
import Vegas.Game.EventMessageStrategic
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
      (SourceProgram.EventLowering.compileEventProfile setup.program
        profile)).map
          (SourceProgram.EventLowering.terminalState setup.program) =
      setup.run profile :=
  SourceProgram.EventLowering.canonical_setup_law setup profile

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
        (SourceProgram.EventLowering.compileEventProfile setup.program profile)
        who replacement)).map
          (SourceProgram.EventLowering.terminalState setup.program) =
      setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program) profile who
        (SourceProgram.EventLowering.backtranslateEventPolicy setup.program
          who replacement)) :=
  SourceProgram.EventLowering.canonical_setup_deviation_law setup profile who replacement

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
    SourceProgram.EventLowering.terminalPayouts setup.program result =
      setup.program.evaluatePayoffs
        (SourceProgram.EventLowering.terminalState setup.program result) :=
  SourceProgram.EventLowering.terminalPayouts_eq_source setup.program result

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
store. The compiler supplies the public-barrier certificate. -/
theorem event_graph_scheduling_approximate_nash_iff [IExpr.ResultTypes L]
    (graph : Vegas.EventGraph Player L) (ordered : graph.BarrierOrdered)
    (inputs : FinDist graph.Inputs) (scheduler : graph.PublicScheduler)
    (utility : EventGraph.Store graph.layout → Player → ℝ)
    (ε : ℝ) (profile : graph.BehavioralProfile) :
    IsεNash (graph.gameForm inputs scheduler)
        (fun outcome who => utility (graph.terminalStore outcome) who) ε
        (graph.normalizeProfile profile) ↔
      IsεNash (graph.canonicalGame inputs)
        (fun outcome who => utility (graph.terminalStore outcome) who) ε profile :=
  graph.eventScheduling_approximate_nash_iff ordered inputs scheduler utility ε profile

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
        (SourceProgram.EventLowering.compileEventProfile setup.program profile)
        (setup.eventInputs initial)).map
          (SourceProgram.EventLowering.terminalState setup.program)) =
      setup.run profile :=
  SourceProgram.EventLowering.scheduled_setup_law setup scheduler profile

/-- info: 'Vegas.Paper.source_event_graph_honest_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_event_graph_honest_law

/-- An arbitrary unilateral asynchronous graph deviation has a finite
mixture of source deviations against unchanged opponents. -/
theorem source_event_graph_deviation_law [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (scheduler : setup.eventGraph.PublicScheduler)
    (profile : SourceProgram.BehavioralProfile setup.program) (who : Player)
    (replacement : setup.eventGraph.BehavioralPolicy who) :
    ∃ mixture : FinDist (SourceProgram.BehavioralPolicy who setup.program),
      (setup.initialLaw.bind fun initial =>
        (setup.eventGraph.terminalOutcomes scheduler
          (Profile.update (sig := setup.eventGraph.gameSignature)
            (SourceProgram.EventLowering.compileEventProfile setup.program profile)
            who replacement)
          (setup.eventInputs initial)).map
            (SourceProgram.EventLowering.terminalState setup.program)) =
        mixture.bind fun alternative =>
          setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program)
            profile who alternative) :=
  SourceProgram.EventLowering.scheduled_setup_deviation_law setup scheduler profile who
    replacement

/-- info: 'Vegas.Paper.source_event_graph_deviation_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_event_graph_deviation_law

/-- Full-source compilation preserves and reflects same-error Nash at the
actual asynchronously scheduled graph profile, for every utility of the public
source result. -/
theorem source_event_graph_approximate_nash_iff [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (scheduler : setup.eventGraph.PublicScheduler)
    (utility : SourceProgram.PublicOutcome setup.program → Player → ℝ)
    (ε : ℝ) (profile : SourceProgram.BehavioralProfile setup.program) :
    IsεNash (setup.eventGame scheduler)
        (fun outcome who => utility (SourceProgram.publicOutcome setup.program
          (SourceProgram.EventLowering.terminalState setup.program outcome)) who)
        ε (SourceProgram.EventLowering.compileEventProfile setup.program
          profile) ↔
      IsεNash setup.gameForm utility ε profile :=
  setup.eventGame_approximate_nash_iff scheduler utility ε profile

/-- info: 'Vegas.Paper.source_event_graph_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_event_graph_approximate_nash_iff

/-- The event-addressed pending game produces a complete graph outcome under
arbitrary player policies, adaptive wire delivery, and public service ordering.
This completion guarantee does not require prescribed player behavior. -/
theorem event_pending_completion [IExpr.ResultTypes L]
    {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
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
    (inputs : FinDist graph.sequentialize.Inputs) (roster : List Player) (reactionRounds : Nat)
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

/-- Every arbitrary native unilateral deviation has the terminal
source-state law of a finite mixture of source deviations against unchanged
opponents. One mixture is chosen across the entire private setup law. -/
theorem source_event_pending_deviation_law [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (profile : SourceProgram.BehavioralProfile setup.program) (who : Player)
    (replacement : runtime.application.PlayerPolicy) :
    ∃ mixture : FinDist (SourceProgram.BehavioralPolicy who setup.program),
      ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
        (Profile.update (sig := (setup.eventPendingGame mode runtime
          roster reactionRounds wire order).sig)
          (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))
          who replacement)).map (setup.eventPendingOutcome mode runtime) =
      mixture.bind fun alternative =>
        (setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program)
          profile who alternative)).map some :=
  setup.eventPendingGame_deviation_law mode runtime feasible roster reactionRounds wire order
    profile who replacement

/-- info: 'Vegas.Paper.source_event_pending_deviation_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_event_pending_deviation_law

/-- Same-error Nash preservation and reflection at compiled source
profiles in either pending-message dependency mode, for every utility of the
public source result. The utility assigned to a missing outcome is arbitrary;
the concrete service has a separate proved completion theorem.

The utility domain here is the outcome, which is the public result. The
deviation law above is the stronger statement, over complete terminal source
states; it is not what this theorem quantifies over. -/
theorem source_event_pending_approximate_nash_iff [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (utility : SourceProgram.PublicOutcome setup.program → Player → ℝ)
    (missing : Player → ℝ) (ε : ℝ)
    (profile : SourceProgram.BehavioralProfile setup.program) :
    IsεNash (setup.eventPendingGame mode runtime roster reactionRounds wire order)
        (fun outcome who => (setup.eventPendingPublicOutcome mode runtime outcome).elim
          (missing who) (fun result => utility result who))
        ε (fun who => setup.compileEventPendingStrategy mode runtime who (profile who)) ↔
      IsεNash setup.gameForm utility ε profile :=
  setup.eventPendingGame_approximate_nash_iff mode runtime feasible roster reactionRounds wire order
    utility missing ε profile

/-- info: 'Vegas.Paper.source_event_pending_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_event_pending_approximate_nash_iff

/-- Public-result lower bounds survive arbitrary unilateral native deviations
in either dependency mode, independently of adversary preferences. -/
theorem source_event_pending_deviation_guarantee [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (profile : SourceProgram.BehavioralProfile setup.program) (who : Player)
    (value : SourceProgram.PublicOutcome setup.program → ℝ) (missing bound : ℝ)
    (sourceBound : ∀ alternative : SourceProgram.BehavioralPolicy who setup.program,
      bound ≤ (setup.publicRun (Profile.update (sig := SourceProgram.gameSignature setup.program)
        profile who alternative)).expect value)
    (replacement : runtime.application.PlayerPolicy) :
    bound ≤ ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
      (Profile.update (sig := (setup.eventPendingGame mode runtime
        roster reactionRounds wire order).sig)
        (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))
        who replacement)).expect
          (fun outcome =>
            (setup.eventPendingPublicOutcome mode runtime outcome).elim missing value) :=
  setup.eventPendingGame_deviation_guarantee mode runtime feasible roster reactionRounds wire order
    profile who value missing bound sourceBound replacement

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
always bind a value and the pending-message service, against arbitrary native
deviations. Commit-time failure is not among the source moves here. -/
theorem value_binding_event_pending_approximate_nash_iff [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (utility : SourceProgram.PublicOutcome setup.program → Player → ℝ)
    (missing : Player → ℝ) (ε : ℝ)
    (profile : Profile setup.valueBindingGame.sig) :
    IsεNash (setup.eventPendingGame mode runtime roster reactionRounds wire order)
        (fun outcome who => (setup.eventPendingPublicOutcome mode runtime outcome).elim
          (missing who) (fun result => utility result who))
        ε (fun who => setup.compileValueBindingPendingProfile mode runtime who (profile who)) ↔
      IsεNash setup.valueBindingGame utility ε profile :=
  setup.valueBindingPendingGame_approximate_nash_iff mode runtime feasible roster reactionRounds
    wire order utility missing ε profile

/-- info: 'Vegas.Paper.value_binding_event_pending_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.value_binding_event_pending_approximate_nash_iff

/-- The same for the game whose policies never randomize: checking a pure source
profile against the real host needs only pure source deviations. -/
theorem pure_event_pending_approximate_nash_iff [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (utility : SourceProgram.PublicOutcome setup.program → Player → ℝ)
    (missing : Player → ℝ) (ε : ℝ)
    (profile : Profile setup.pureGame.sig) :
    IsεNash (setup.eventPendingGame mode runtime roster reactionRounds wire order)
        (fun outcome who => (setup.eventPendingPublicOutcome mode runtime outcome).elim
          (missing who) (fun result => utility result who))
        ε (fun who => setup.compilePurePendingProfile mode runtime who (profile who)) ↔
      IsεNash setup.pureGame utility ε profile :=
  setup.purePendingGame_approximate_nash_iff mode runtime feasible roster reactionRounds
    wire order utility missing ε profile

/-- info: 'Vegas.Paper.pure_event_pending_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pure_event_pending_approximate_nash_iff

/-! ## Private initial types and truthful plans -/

/-- Compiled prescribed play preserves the joint initial-parameter/public-result law. -/
theorem private_type_event_pending_honest_law [IExpr.ResultTypes L] {Parameter : Type}
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (mode : EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (profile : Profile (setup.valueBindingParameterGame parameter).sig) :
    ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
      (fun who => setup.compileValueBindingPendingProfile mode runtime who (profile who))).map
        (setup.eventPendingParameterOutcome parameter mode runtime) =
      ((setup.valueBindingParameterGame parameter).play profile).map some :=
  (setup.valueBindingParameterPendingSimulation parameter mode runtime feasible roster
    reactionRounds wire order).honest_law profile

/-- info: 'Vegas.Paper.private_type_event_pending_honest_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.private_type_event_pending_honest_law

/-- The value-only source abstraction preserves the joint law of initial
parameters and public results, with one deviation mixture across the prior. -/
theorem private_type_event_pending_deviation_law [IExpr.ResultTypes L] {Parameter : Type}
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (mode : EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (profile : Profile (setup.valueBindingParameterGame parameter).sig) (who : Player)
    (replacement : runtime.application.PlayerPolicy) :
    ∃ mixture : FinDist (SourceProgram.ValueBindingPolicy who setup.program),
      ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
        (Profile.update (sig := (setup.eventPendingGame mode runtime
          roster reactionRounds wire order).sig)
          (fun actor => setup.compileValueBindingPendingProfile mode runtime actor (profile actor))
          who replacement)).map (setup.eventPendingParameterOutcome parameter mode runtime) =
      mixture.bind fun alternative =>
        ((setup.valueBindingParameterGame parameter).play
          (Profile.update profile who alternative)).map some :=
  (setup.valueBindingParameterPendingSimulation parameter mode runtime feasible roster
    reactionRounds wire order).deviation_mixture profile who replacement trivial

/-- info: 'Vegas.Paper.private_type_event_pending_deviation_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.private_type_event_pending_deviation_law

/-- Bayesian incentives for a designated source plan, including a truthful
plan, are preserved and reflected without exposing commit-time failure.
Approximation is measured ex ante under the fixed finite prior. -/
theorem private_type_event_pending_approximate_nash_iff [IExpr.ResultTypes L] {Parameter : Type}
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (mode : EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (utility : Parameter × SourceProgram.PublicOutcome setup.program → Player → ℝ)
    (missing : Player → ℝ) (ε : ℝ)
    (profile : Profile (setup.valueBindingParameterGame parameter).sig) :
    IsεNash (setup.eventPendingGame mode runtime roster reactionRounds wire order)
        (fun outcome who =>
          (setup.eventPendingParameterOutcome parameter mode runtime outcome).elim
            (missing who) (fun result => utility result who))
        ε (fun who => setup.compileValueBindingPendingProfile mode runtime who (profile who)) ↔
      IsεNash (setup.valueBindingParameterGame parameter) utility ε profile :=
  setup.valueBindingParameterPendingGame_approximate_nash_iff parameter mode runtime feasible
    roster reactionRounds wire order utility missing ε profile

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
          (Examples.CommitRevealAuction.setup.valueBindingGame.play players)) :
    ¬ IsDominant target (euPreference targetUtility) Examples.CommitRevealAuction.Player.alice
      (compile Examples.CommitRevealAuction.Player.alice
        (Examples.CommitRevealAuction.aliceStrategy 5)) :=
  Examples.CommitRevealAuction.translated_truthful_not_dominant values forfeiture valuation
    target compile targetUtility preserves

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

end Vegas.Paper
