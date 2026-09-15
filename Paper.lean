/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Confluence
import Vegas.EventGraph.Fence
import Vegas.Game.GraphCompilation
import Vegas.Game.GraphSetup
import Vegas.Game.GraphMessages
import Vegas.Game.SourcePublicCandidate
import Vegas.Source.Safety

/-! # Paper theorem audit

This file contains only principal proved claims and expressible compiler
objectives. Proved results delegate directly to implementation theorems;
the explicitly unproved pending-message capstones contain the only admissions.
Their expected diagnostics and axiom pins record that status rather than hiding it.
Supporting probability, replay, provenance, and
coupling lemmas remain checked in their owning modules; they are not repeated
as paper capstones.

The source safety and typed-graph compiler results concern the complete
failure-aware `SourceProgram` semantics. The candidate-message results concern
`WFProgram`; they do not establish pending-message compilation of `SourceProgram`.

The candidate-message results are the strongest currently proved end-to-end
strategic boundary. Their common value type, universally accepting guards,
commitment-produced reveals, absence of compiled sampling, timely-service, and
source quitting hypotheses remain explicit and must not be read as the final
language or blockchain theorem.
-/

namespace Vegas.Paper

open GameTheory Vegas EventGraph Interaction
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

/-- Every complete failure-aware source execution satisfies all retained
guards, including executions with invalid bindings or withheld disclosures. -/
theorem source_guards_satisfied [IExpr.ResultTypes L]
    (source : SourceProgram.Initial (Player := Player) (L := L))
    (profile : SourceProgram.BehavioralProfile source.program)
    (outcome : State L source.program.terminalCtx)
    (supported : outcome ∈ (source.run profile).support) :
    (SourceProgram.finalRegistry source.program []).Satisfied outcome :=
  source.terminal_registry_satisfied profile outcome supported

/-- Complete source-to-graph equality of decoded terminal-state laws. -/
theorem source_graph_honest_law [IExpr.ResultTypes L]
    (source : SourceProgram.Initial (Player := Player) (L := L))
    (profile : SourceProgram.BehavioralProfile source.program) :
    (Vegas.Graph.run source.graph (source.compileGraphProfile profile) source.graphInputs).map
      source.decodeGraph = source.run profile :=
  source.graph_honest_law profile

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

/-- error: declaration uses `sorry` -/
#guard_msgs (whitespace := lax) in
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
          profile who alternative)).map some) := by
  sorry

/-- error: declaration uses `sorry` -/
#guard_msgs (whitespace := lax) in
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
    IsεNash setup.gameForm utility ε profile := by
  sorry

/-- Independent available graph events form a diamond. -/
theorem execution_diamond
    {G : EventGraph.Graph Player L} (hwf : G.WF) {cfg leftNext rightNext : Config G}
    (left right : AvailableEvent G cfg) (hne : left.node ≠ right.node)
    (hleft : leftNext ∈ (stepAvailableEvent G cfg left).support)
    (hright : rightNext ∈ (stepAvailableEvent G cfg right).support) :
    ∃ rightAfterLeft : AvailableEvent G leftNext,
      ∃ leftAfterRight : AvailableEvent G rightNext,
        ∃ finalLeft finalRight : Config G,
          finalLeft ∈ (stepAvailableEvent G leftNext rightAfterLeft).support ∧
          finalRight ∈ (stepAvailableEvent G rightNext leftAfterRight).support ∧
          finalLeft = finalRight :=
  supported_available_events_diamond hwf left right hne hleft hright

/-- Permuting a duplicate-free complete schedule does not change its result. -/
theorem schedule_confluence {G : EventGraph.Graph Player L} (cfg : Config G)
    (value : Fin G.nodeCount → TypedValue L) {left right : List (Fin G.nodeCount)}
    (hperm : List.Perm left right) (hnodup : left.Nodup) :
    cfg.scheduleComplete value left = cfg.scheduleComplete value right :=
  Config.scheduleComplete_perm cfg value hperm hnodup

/-- A reveal depends on every earlier commitment. -/
theorem commit_reveal_barrier (G : EventGraph.Graph Player L)
    {node prior : Fin G.nodeCount} {event priorEvent : EventNode Player L} {source : Nat}
    {who : Player} {guard : EventGuard L}
    (hnode : G.nodes[node]? = some event) (hprior : G.nodes[prior]? = some priorEvent)
    (hlt : (prior : Nat) < (node : Nat)) (hreveal : event.sem = .reveal source)
    (hcommit : priorEvent.sem = .commit who guard) : prior ∈ G.prereqs node :=
  G.prior_commit_mem_prereqs_of_reveal hnode hprior hlt hreveal hcommit

/-- A ready reveal has completed every earlier commitment. -/
theorem ready_reveal_fence (G : EventGraph.Graph Player L) (cfg : Config G)
    {node prior : Fin G.nodeCount} {event priorEvent : EventNode Player L} {source : Nat}
    {who : Player} {guard : EventGuard L}
    (hnode : G.nodes[node]? = some event) (hprior : G.nodes[prior]? = some priorEvent)
    (hlt : (prior : Nat) < (node : Nat)) (hreveal : event.sem = .reveal source)
    (hcommit : priorEvent.sem = .commit who guard) (hready : Ready G cfg node) :
    prior ∈ cfg.done :=
  Ready.prior_commit_done_of_reveal G cfg hnode hprior hlt hreveal hcommit hready

/-- Every candidate-game result has a legal public source realization. -/
theorem pending_candidate_public_source_support
    [Finite Player] {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window)
    (players : Profile model.game.sig) (next : model.game.sig.Outcome)
    (hnext : next ∈ (model.game.play players).support) :
    ∃ final : VEnv L (sourceTerminalCtx source.core.prog),
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := sourceTerminalCtx source.core.prog, env := final,
          cont := .ret (sourceTerminalPayoffs source.core.prog) } ∧
      compilation.publicSourceOutcome? next.native.application.visible.events =
        some final.erasePubEnv :=
  compilation.candidate_public_source_support nullValue window model players next hnext

/-- Honest candidate play has the public written-source outcome law. -/
theorem pending_candidate_public_source_law
    [Finite Player] {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (profile : SourceBehavioralProfile source.core.prog) :
    (model.game.play
      (fun player => compilation.compileCandidatePolicy nullValue window player (profile player))
        ).map (fun next =>
          compilation.publicSourceOutcome? next.native.application.visible.events) =
      ((sourceGameForm source.core.prog source.core.env).play profile).map
        (fun final => some final.erasePubEnv) :=
  compilation.candidate_public_source_law nullValue window model timely profile

/-- Every observation-local native deviation is bounded by a legal source deviation. -/
theorem pending_candidate_public_deviation_bound
    [Finite Player] {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (interpretation :
      Env L.Val (erasePubVCtx (sourceTerminalCtx source.core.prog)) → Player → ℝ)
    (missing : Player → ℝ) (profile : SourceBehavioralProfile source.core.prog)
    (hdominance : source.core.prog.QuitPrefixDominanceAgainst source.core.env nullValue
      (fun final who => interpretation final.erasePubEnv who) profile)
    (who : Player) (replacement : model.game.sig.Strategy who) :
    ∃ alternative : SourceBehavioralPolicy source.core.prog who,
      (model.game.play (Profile.update
        (fun player => compilation.compileCandidatePolicy nullValue window player (profile player))
        who replacement)).expect (fun next =>
          (compilation.publicSourceOutcome? next.native.application.visible.events).elim
            (missing who) (fun outcome => interpretation outcome who)) ≤
      ((sourceGameForm source.core.prog source.core.env).play
        (Profile.update profile who alternative)).expect
          (fun final => interpretation final.erasePubEnv who) :=
  compilation.candidate_public_deviation_bound nullValue window model timely
    interpretation missing profile hdominance who replacement

/-- The source-only quitting condition gives same-error Nash correspondence. -/
theorem pending_candidate_public_nash_iff
    [Finite Player] {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (interpretation :
      Env L.Val (erasePubVCtx (sourceTerminalCtx source.core.prog)) → Player → ℝ)
    (missing : Player → ℝ) (profile : SourceBehavioralProfile source.core.prog)
    (hdominance : source.core.prog.QuitPrefixDominanceAgainst source.core.env nullValue
      (fun final who => interpretation final.erasePubEnv who) profile) (ε : ℝ) :
    IsεNash model.game (fun next who =>
      (compilation.publicSourceOutcome? next.native.application.visible.events).elim
        (missing who) (fun outcome => interpretation outcome who)) ε
      (fun who => compilation.compileCandidatePolicy nullValue window who (profile who)) ↔
    IsεNash (sourceGameForm source.core.prog source.core.env)
      (fun final who => interpretation final.erasePubEnv who) ε profile :=
  compilation.candidate_public_approximate_nash_iff nullValue window model timely
    interpretation missing profile hdominance ε

end Vegas.Paper

/-- info: 'Vegas.Paper.source_publications_resolved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_publications_resolved

/-- info: 'Vegas.Paper.source_guards_satisfied' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_guards_satisfied

/-- info: 'Vegas.Paper.source_graph_honest_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_graph_honest_law
/-- info: 'Vegas.Paper.source_graph_deviation_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_graph_deviation_law
/-- info: 'Vegas.Paper.source_graph_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_graph_approximate_nash_iff
/-- info: 'Vegas.Paper.source_setup_graph_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_setup_graph_approximate_nash_iff
/-- info: 'Vegas.Paper.source_pending_complete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_pending_complete
/-- info: 'Vegas.Paper.source_pending_honest_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_pending_honest_law
/-- info: 'Vegas.Paper.source_pending_deviation_law' depends on axioms:
[propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_pending_deviation_law
/-- info: 'Vegas.Paper.source_pending_approximate_nash_iff' depends on axioms:
[propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_pending_approximate_nash_iff
/-- info: 'Vegas.Paper.execution_diamond' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.execution_diamond
/-- info: 'Vegas.Paper.schedule_confluence' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.schedule_confluence
/-- info: 'Vegas.Paper.commit_reveal_barrier' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.commit_reveal_barrier
/-- info: 'Vegas.Paper.ready_reveal_fence' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.ready_reveal_fence
/-- info: 'Vegas.Paper.pending_candidate_public_source_support' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_candidate_public_source_support
/-- info: 'Vegas.Paper.pending_candidate_public_source_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_candidate_public_source_law
/-- info: 'Vegas.Paper.pending_candidate_public_deviation_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_candidate_public_deviation_bound
/-- info: 'Vegas.Paper.pending_candidate_public_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_candidate_public_nash_iff
