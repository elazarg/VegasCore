/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.GraphCompilation
import Vegas.Game.GraphSetup
import Vegas.Game.GraphMessages
import Vegas.Source.Safety

/-! # Paper theorem audit

Principal source-safety and compilation results for the full failure-aware
language. Every statement delegates directly to its owning theorem; the axiom
pins below check the complete proof dependencies.

The pending-message target uses ideal commitments and a concrete bounded
ordered service with adaptive delivery. These results do not assert
cryptographic, transaction-ledger, or EVM refinement.
-/

namespace Vegas.Paper

open GameTheory Vegas Interaction
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Every complete execution of a failure-aware source program resolves all
publication obligations, without assuming successful or guard-valid play. -/
theorem source_publications_resolved [IExpr.ResultTypes L]
    (source : SourceProgram.Initial (Player := Player) (L := L))
    (profile : SourceProgram.BehavioralProfile source.program)
    (outcome : State L source.program.terminalCtx)
    (supported : outcome ∈ (source.run profile).support)
    {owner : Player} {payload : L.Ty} {name : VarId}
    (resource : HasVar source.program.terminalCtx name (.privateData owner payload)) :
    (outcome.get resource).2 ≠ Publication.pending :=
  source.terminal_resolved profile outcome supported resource

/-- info: 'Vegas.Paper.source_publications_resolved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_publications_resolved

/-- Every complete failure-aware source execution satisfies all retained
guards, including executions with invalid bindings or withheld disclosures. -/
theorem source_guards_satisfied [IExpr.ResultTypes L]
    (source : SourceProgram.Initial (Player := Player) (L := L))
    (profile : SourceProgram.BehavioralProfile source.program)
    (outcome : State L source.program.terminalCtx)
    (supported : outcome ∈ (source.run profile).support) :
    (SourceProgram.finalRegistry source.program []).Satisfied outcome :=
  source.terminal_registry_satisfied profile outcome supported

/-- info: 'Vegas.Paper.source_guards_satisfied' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_guards_satisfied

/-- Complete source-to-graph equality of decoded terminal-state laws. -/
theorem source_graph_honest_law [IExpr.ResultTypes L]
    (source : SourceProgram.Initial (Player := Player) (L := L))
    (profile : SourceProgram.BehavioralProfile source.program) :
    (Vegas.Graph.run source.graph (source.compileGraphProfile profile) source.graphInputs).map
      source.decodeGraph = source.run profile :=
  source.graph_honest_law profile

/-- info: 'Vegas.Paper.source_graph_honest_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_graph_honest_law

/-- Every unilateral graph deviation has an exact source-policy preimage. -/
theorem source_graph_deviation_law [IExpr.ResultTypes L]
    (source : SourceProgram.Initial (Player := Player) (L := L))
    (profile : SourceProgram.BehavioralProfile source.program) (who : Player)
    (replacement : Vegas.Graph.BehavioralPolicy who source.graph) :
    (Vegas.Graph.run source.graph
      (Profile.update (sig := Vegas.Graph.gameSignature source.graph)
        (source.compileGraphProfile profile) who replacement) source.graphInputs).map
      source.decodeGraph =
    source.run (Profile.update (sig := SourceProgram.gameSignature source.program)
      profile who (SourceProgram.backtranslateGraphPolicy source.program source.namesNodup
        SourceProgram.initialMap [] who replacement)) :=
  source.graph_deviation_law profile who replacement

/-- info: 'Vegas.Paper.source_graph_deviation_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_graph_deviation_law

/-- Same-error Nash correspondence for arbitrary utilities of source outcomes. -/
theorem source_graph_approximate_nash_iff [IExpr.ResultTypes L]
    (source : SourceProgram.Initial (Player := Player) (L := L))
    (utility : State L source.program.terminalCtx → Player → ℝ)
    (ε : ℝ) (profile : SourceProgram.BehavioralProfile source.program) :
    IsεNash (Vegas.Graph.gameForm source.graph source.graphInputs)
      (fun outcome who => utility (source.decodeGraph outcome) who) ε
      (source.compileGraphProfile profile) ↔
    IsεNash (SourceProgram.gameForm source.program source.state) utility ε profile :=
  source.graph_approximate_nash_iff utility ε profile

/-- info: 'Vegas.Paper.source_graph_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_graph_approximate_nash_iff

/-- Source-to-graph Nash correspondence also preserves uncertainty about the
sampled private setup: one policy is used across the entire initial law. -/
theorem source_setup_graph_approximate_nash_iff [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (ε : ℝ) (profile : SourceProgram.BehavioralProfile setup.program) :
    IsεNash setup.graphGameForm
      (fun outcome who => utility (setup.decodeGraph outcome) who) ε
      (setup.compileGraphProfile profile) ↔
    IsεNash setup.gameForm utility ε profile :=
  setup.graph_approximate_nash_iff utility ε profile

/-- info: 'Vegas.Paper.source_setup_graph_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_setup_graph_approximate_nash_iff

/-! ## Full-language pending-message capstones

These statements name the actual composed strategy compiler and the actual
serviced message game. The reserved service provides preparation/submission,
inclusion, and clock execution opportunities. Between them an arbitrary wire
policy can expose pending messages and players can react. This is the concrete
bounded service target, not all fair schedulers or a deployed blockchain.

The initial private state is sampled inside the game. In the deviation law,
the mixture is chosen outside that sample. No source constructor is excluded,
and no failure-incentive premise is assumed at this ordered ideal edge.
-/

/-- Every supported target play completes under the concrete bounded service,
including arbitrary native policies and the specified private initial law. -/
theorem source_pending_complete [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (runtime : GraphRuntime Player L (SourceProgram.graphCtx setup.program.terminalCtx))
    (roster : List Player) (reactionRounds : Nat) (wire : runtime.application.WirePolicy)
    (players : Player → runtime.application.PlayerPolicy)
    (outcome : runtime.application.PolicyExecution)
    (supported : outcome ∈
      ((setup.pendingGame runtime roster reactionRounds wire).play players).support) :
    (setup.pendingOutcome runtime outcome).isSome = true :=
  setup.pendingGame_complete runtime roster reactionRounds wire players outcome supported

/-- info: 'Vegas.Paper.source_pending_complete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_pending_complete

/-- Complete source-to-pending honest outcome-law preservation, including
private initial setup, adaptive wire delivery, and arbitrary reaction rosters. -/
theorem source_pending_honest_law [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (runtime : GraphRuntime Player L (SourceProgram.graphCtx setup.program.terminalCtx))
    (roster : List Player) (reactionRounds : Nat) (wire : runtime.application.WirePolicy)
    (profile : SourceProgram.BehavioralProfile setup.program) :
    ((setup.pendingGame runtime roster reactionRounds wire).play
      (fun who => setup.compilePendingStrategy runtime who (profile who))).map
        (setup.pendingOutcome runtime) = (setup.run profile).map some :=
  setup.pendingGame_honest_law runtime roster reactionRounds wire profile

/-- info: 'Vegas.Paper.source_pending_honest_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_pending_honest_law

/-- Every arbitrary unilateral native deviation has the exact outcome law of
a finite mixture of source deviations against unchanged opponents. The mixture
is chosen before the private initial state is sampled. -/
theorem source_pending_deviation_law [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (runtime : GraphRuntime Player L (SourceProgram.graphCtx setup.program.terminalCtx))
    (roster : List Player) (reactionRounds : Nat) (wire : runtime.application.WirePolicy)
    (profile : SourceProgram.BehavioralProfile setup.program) (who : Player)
    (replacement : runtime.application.PlayerPolicy) :
    ∃ mixture : FinDist (SourceProgram.BehavioralPolicy who setup.program),
      ((setup.pendingGame runtime roster reactionRounds wire).play
        (Profile.update (sig := (setup.pendingGame runtime roster reactionRounds wire).sig)
          (fun actor => setup.compilePendingStrategy runtime actor (profile actor))
          who replacement)).map (setup.pendingOutcome runtime) =
      mixture.bind (fun alternative =>
        (setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program)
          profile who alternative)).map some) :=
  setup.pendingGame_deviation_law runtime roster reactionRounds wire profile who replacement

/-- info: 'Vegas.Paper.source_pending_deviation_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_pending_deviation_law

/-- Same-error Nash preservation and reflection at compiled profiles for
arbitrary utilities of source outcomes, against arbitrary native deviations. -/
theorem source_pending_approximate_nash_iff [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (runtime : GraphRuntime Player L (SourceProgram.graphCtx setup.program.terminalCtx))
    (roster : List Player) (reactionRounds : Nat) (wire : runtime.application.WirePolicy)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (missing : Player → ℝ)
    (ε : ℝ) (profile : SourceProgram.BehavioralProfile setup.program) :
    IsεNash (setup.pendingGame runtime roster reactionRounds wire)
      (fun outcome who => (setup.pendingOutcome runtime outcome).elim
        (missing who) (fun state => utility state who)) ε
      (fun who => setup.compilePendingStrategy runtime who (profile who)) ↔
    IsεNash setup.gameForm utility ε profile :=
  setup.pendingGame_approximate_nash_iff runtime roster reactionRounds wire utility missing
    ε profile

/-- info: 'Vegas.Paper.source_pending_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_pending_approximate_nash_iff

/-- Any source-outcome lower bound against unilateral deviations survives
compilation, independently of the native adversary's preferences. -/
theorem source_pending_deviation_guarantee [IExpr.ResultTypes L]
    (setup : SourceProgram.Setup (Player := Player) (L := L))
    (runtime : GraphRuntime Player L (SourceProgram.graphCtx setup.program.terminalCtx))
    (roster : List Player) (reactionRounds : Nat) (wire : runtime.application.WirePolicy)
    (profile : SourceProgram.BehavioralProfile setup.program) (who : Player)
    (value : State L setup.program.terminalCtx → ℝ) (missing bound : ℝ)
    (hbound : ∀ alternative : SourceProgram.BehavioralPolicy who setup.program,
      bound ≤ (setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program)
        profile who alternative)).expect value)
    (replacement : runtime.application.PlayerPolicy) :
    bound ≤ ((setup.pendingGame runtime roster reactionRounds wire).play
      (Profile.update (sig := (setup.pendingGame runtime roster reactionRounds wire).sig)
        (fun actor => setup.compilePendingStrategy runtime actor (profile actor))
        who replacement)).expect
          (fun outcome => (setup.pendingOutcome runtime outcome).elim missing value) :=
  setup.pendingGame_deviation_guarantee runtime roster reactionRounds wire profile who value
    missing bound hbound replacement

/-- info: 'Vegas.Paper.source_pending_deviation_guarantee' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_pending_deviation_guarantee

end Vegas.Paper
