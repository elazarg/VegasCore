/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Confluence
import Vegas.EventGraph.Fence
import Vegas.Game.SourceGraph
import Vegas.Game.SourcePublicCandidate

/-! # Paper theorem audit

This file contains only the principal claims used by the paper.  Every result
is a direct delegation to the active implementation theorem, with its exact
hypotheses visible here.  Supporting probability, replay, provenance, and
coupling lemmas remain checked in their owning modules; they are not repeated
as paper capstones.

The candidate-message results are the strongest currently proved end-to-end
boundary.  Their common value type, universally accepting guards,
commitment-produced reveals, absence of compiled sampling, timely-service, and
source quitting hypotheses remain explicit and must not be read as the final
language or blockchain theorem.
-/

namespace Vegas.Paper

open GameTheory Vegas EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Whole-program equality for the actual graph policy runner. -/
theorem source_graph_honest_law [Fintype Player] (source : WFProgram Player L)
    (profile : SourceBehavioralProfile source.core.prog) :
    ((EventGraph.policyGame (ToEventGraph.compile source.core).graph
      (ToEventGraph.compile source.core).graphWF
      (ToEventGraph.compile_guardLive source.core source.legal)).play
      (source.sourceGraphSimulation.compileProfile profile)).map
        (ToEventGraph.observeSourceOutcome source.core) =
      (denoteSource source.core.prog profile source.core.env).map some :=
  source.sourceGraphSimulation.honest_law profile

/-- Exact source backtranslation of every unilateral declared-read kernel. -/
theorem source_graph_deviation_law [Fintype Player] (source : WFProgram Player L)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : CommitPolicy (ToEventGraph.compile source.core).graph who) :
    ((EventGraph.policyGame (ToEventGraph.compile source.core).graph
      (ToEventGraph.compile source.core).graphWF
      (ToEventGraph.compile_guardLive source.core source.legal)).play
      (Profile.update (source.sourceGraphSimulation.compileProfile profile)
        who replacement)).map (ToEventGraph.observeSourceOutcome source.core) =
      (denoteSource source.core.prog
        (Profile.update (sig := sourceGameSignature source.core.prog) profile who
          (ToEventGraph.backtranslateCommitPolicy source.core who replacement))
        source.core.env).map some :=
  ToEventGraph.runPolicyNodes_source_deviation source.core source.legal profile who replacement

/-- Source and declared-read graph games have the same approximate equilibria. -/
theorem source_graph_approximate_nash_iff [Fintype Player] (source : WFProgram Player L)
    (value : Option (VEnv L (sourceTerminalCtx source.core.prog)) → Player → ℝ)
    (ε : ℝ) (profile : SourceBehavioralProfile source.core.prog) :
    IsεNash (EventGraph.policyGame (ToEventGraph.compile source.core).graph
      (ToEventGraph.compile source.core).graphWF
      (ToEventGraph.compile_guardLive source.core source.legal))
      (fun outcome who => value (ToEventGraph.observeSourceOutcome source.core outcome) who) ε
      (source.sourceGraphSimulation.compileProfile profile) ↔
    IsεNash (sourceGameForm source.core.prog source.core.env)
      (fun outcome who => value (some outcome) who) ε profile :=
  source.source_graph_approximate_nash_iff value ε profile

/-- Independent available graph events form a diamond. -/
theorem execution_diamond
    {G : Graph Player L} (hwf : G.WF) {cfg leftNext rightNext : Config G}
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
theorem schedule_confluence {G : Graph Player L} (cfg : Config G)
    (value : Fin G.nodeCount → TypedValue L) {left right : List (Fin G.nodeCount)}
    (hperm : List.Perm left right) (hnodup : left.Nodup) :
    cfg.scheduleComplete value left = cfg.scheduleComplete value right :=
  Config.scheduleComplete_perm cfg value hperm hnodup

/-- A reveal depends on every earlier commitment. -/
theorem commit_reveal_barrier (G : Graph Player L)
    {node prior : Fin G.nodeCount} {event priorEvent : EventNode Player L} {source : Nat}
    {who : Player} {guard : EventGuard L}
    (hnode : G.nodes[node]? = some event) (hprior : G.nodes[prior]? = some priorEvent)
    (hlt : (prior : Nat) < (node : Nat)) (hreveal : event.sem = .reveal source)
    (hcommit : priorEvent.sem = .commit who guard) : prior ∈ G.prereqs node :=
  G.prior_commit_mem_prereqs_of_reveal hnode hprior hlt hreveal hcommit

/-- A ready reveal has completed every earlier commitment. -/
theorem ready_reveal_fence (G : Graph Player L) (cfg : Config G)
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
