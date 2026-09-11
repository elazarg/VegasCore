/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceLaw
import Vegas.Compile.SourceView
import Vegas.EventGraph
import Vegas.Core.AccountingIntegrity
import Vegas.Compile.ApplicationPlanOutcome
import Vegas.Compile.ApplicationForwardLaw
import Vegas.Compile.ApplicationTimeoutForwardLaw
import Vegas.Compile.WindowedSourceSafety
import Vegas.Compile.WindowedForwardLaw
import Vegas.Game.Windowed
import Vegas.Compile.PublicChoiceResolution
import Vegas.Compile.BindingTimeoutCompilation
import Vegas.Compile.ApplicationWithholding
import Vegas.Compile.ConditionalExpirationSourceCoupling
import Vegas.Compile.ConditionalPhaseExecution
import Vegas.Compile.WindowedService

/-! # Paper theorem audit

Proved entries delegate directly to repository theorems. Open targets use
explicit `sorry` proofs and are pinned to `sorryAx`; they are not checked
results. Expected admission warnings are guarded, so unrelated warnings still
fail the build. The strict paper checker rejects every open target.

The public-result laws below observe completion and executable public terminal
bindings. Pending delivery laws concern the concrete fixed delivery service;
adaptive scheduling and full source-outcome laws remain further obligations.
-/

namespace Vegas.Paper

open GameTheory GameTheory.Math.Probability EventGraph

theorem source_strategy_support
    {Player : Type} [DecidableEq Player] {L : IExpr} {Γ : VCtx Player L}
    (prog : VegasCore Player L Γ) (profile : SourceBehavioralProfile prog)
    (env : VEnv L Γ) (result : VEnv L (sourceTerminalCtx prog))
    (hsupport : result ∈ (denoteSource prog profile env).support) :
    SmallStep.Star { ctx := Γ, env := env, cont := prog }
      { ctx := sourceTerminalCtx prog, env := result,
        cont := .ret (sourceTerminalPayoffs prog) } :=
  denoteSource_support_star prog profile env result hsupport

theorem source_decision_information
    {Player : Type} [DecidableEq Player] {L : IExpr} {Γ : VCtx Player L}
    (state : ToEventGraph.BuildState Player L Γ) (who : Player)
    (hinjective : ToEventGraph.FieldOfNameInjective state.fieldOf) :
    Function.Bijective (ToEventGraph.viewEnvOfReadEnv state who) :=
  ToEventGraph.viewEnvOfReadEnv_bijective state who hinjective

theorem source_publication_barrier
    {Player : Type} [DecidableEq Player] {L : IExpr}
    {G : Graph Player L} {cfg : Config G} {who : Player}
    {commit publication : Fin G.nodeCount} {row : EventNode Player L}
    (hreachable : Reachable G cfg) (hcommit : ReadyCommitNode G cfg who commit)
    (hrow : G.nodes[publication]? = some row)
    (hlt : (commit : Nat) < (publication : Nat))
    (hinternal : NodeSem.isInternal row.sem = true) : publication ∉ cfg.done :=
  hcommit.later_internal_not_done hreachable hrow hlt hinternal

theorem source_decision_roundtrip
    {Player : Type} [DecidableEq Player] {L : IExpr} {Γ : VCtx Player L}
    {name : VarId} {ty : L.Ty}
    (state : ToEventGraph.BuildState Player L Γ) (who : Player)
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (hinjective : ToEventGraph.FieldOfNameInjective state.fieldOf)
    (policy : (visible : Env L.Val (eraseVCtx (viewVCtx who Γ))) →
      FinDist {value : L.Val ty // evalGuard guard value visible = true})
    (visible : Env L.Val (eraseVCtx (viewVCtx who Γ))) :
    ToEventGraph.backtranslateSourceDecision state who guard hinjective
      (ToEventGraph.compileSourceDecision state who guard policy) visible = policy visible :=
  ToEventGraph.backtranslate_compileSourceDecision state who guard hinjective policy visible

theorem graph_decision_roundtrip
    {Player : Type} [DecidableEq Player] {L : IExpr} {Γ : VCtx Player L}
    {name : VarId} {ty : L.Ty}
    (state : ToEventGraph.BuildState Player L Γ) (who : Player)
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (hinjective : ToEventGraph.FieldOfNameInjective state.fieldOf)
    (policy : (reads : ReadEnv L (ToEventGraph.eventGuardOf state who guard).choiceReads) →
      FinDist {value : L.Val ty //
        (ToEventGraph.eventGuardOf state who guard).eval value reads = true})
    (reads : ReadEnv L (ToEventGraph.eventGuardOf state who guard).choiceReads) :
    ToEventGraph.compileSourceDecision state who guard
      (ToEventGraph.backtranslateSourceDecision state who guard hinjective policy) reads =
        policy reads :=
  ToEventGraph.compile_backtranslateSourceDecision state who guard hinjective policy reads

theorem schedule_confluence
    {Player : Type} [DecidableEq Player] {L : IExpr}
    {G : Graph Player L} (cfg : Config G)
    (value : Fin G.nodeCount → TypedValue L)
    {left right : List (Fin G.nodeCount)}
    (hperm : List.Perm left right) (hnodup : left.Nodup) :
    cfg.scheduleComplete value left = cfg.scheduleComplete value right :=
  Config.scheduleComplete_perm cfg value hperm hnodup

theorem schedule_observation_confluence
    {Player : Type} [DecidableEq Player] {L : IExpr}
    {G : Graph Player L} (cfg : Config G) (who : Player)
    (value : Fin G.nodeCount → TypedValue L)
    {left right : List (Fin G.nodeCount)}
    (hperm : List.Perm left right) (hnodup : left.Nodup) :
    (publicObserve G (cfg.scheduleComplete value left),
        observe G (cfg.scheduleComplete value left) who) =
      (publicObserve G (cfg.scheduleComplete value right),
        observe G (cfg.scheduleComplete value right) who) :=
  Config.scheduleComplete_observe_perm cfg who value hperm hnodup

theorem execution_diamond
    {Player : Type} [DecidableEq Player] {L : IExpr}
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

theorem commit_reveal_barrier
    {Player : Type} [DecidableEq Player] {L : IExpr}
    (G : Graph Player L)
    {node prior : Fin G.nodeCount}
    {event priorEvent : EventNode Player L} {source : Nat}
    {who : Player} {guard : EventGuard L}
    (hnode : G.nodes[node]? = some event)
    (hprior : G.nodes[prior]? = some priorEvent)
    (hlt : (prior : Nat) < (node : Nat))
    (hreveal : event.sem = .reveal source)
    (hcommit : priorEvent.sem = .commit who guard) :
    prior ∈ G.prereqs node :=
  G.prior_commit_mem_prereqs_of_reveal hnode hprior hlt hreveal hcommit

theorem ready_reveal_fence
    {Player : Type} [DecidableEq Player] {L : IExpr}
    (G : Graph Player L) (cfg : Config G) {node prior : Fin G.nodeCount}
    {event priorEvent : EventNode Player L} {source : Nat}
    {who : Player} {guard : EventGuard L}
    (hnode : G.nodes[node]? = some event) (hprior : G.nodes[prior]? = some priorEvent)
    (hlt : (prior : Nat) < (node : Nat)) (hreveal : event.sem = .reveal source)
    (hcommit : priorEvent.sem = .commit who guard) (hready : Ready G cfg node) :
    prior ∈ cfg.done :=
  Ready.prior_commit_done_of_reveal G cfg hnode hprior hlt hreveal hcommit hready


/-- info: 'Vegas.Paper.source_strategy_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_strategy_support

/-- info: 'Vegas.Paper.source_decision_information' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_decision_information

/-- info: 'Vegas.Paper.source_publication_barrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_publication_barrier

/-- info: 'Vegas.Paper.source_decision_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_decision_roundtrip

/-- info: 'Vegas.Paper.graph_decision_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.graph_decision_roundtrip

/-- info: 'Vegas.Paper.schedule_confluence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.schedule_confluence

/-- info: 'Vegas.Paper.schedule_observation_confluence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.schedule_observation_confluence

/-- info: 'Vegas.Paper.execution_diamond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.execution_diamond

/-- info: 'Vegas.Paper.commit_reveal_barrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.commit_reveal_barrier

/-- info: 'Vegas.Paper.ready_reveal_fence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.ready_reveal_fence

end Vegas.Paper

noncomputable section
namespace Vegas.Paper.Source
open GameTheory GameTheory.Math.Probability GameTheory.Protocol
open Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

theorem committed_binding_accounted (source : WFProgram Player L) (name : VarId)
    (hname : name ∈ CommittedVars source.core.prog) :
    name ∈ RevealedSources source.core.prog ∨
      name ∈ source.accounted.dispositions :=
  source.committed_source_resolved name hname

theorem initial_binding_accounted (source : WFProgram Player L) (name : VarId)
    (hname : name ∈ SealedVars source.core.Γ) :
    name ∈ RevealedSources source.core.prog ∨
      name ∈ source.accounted.dispositions :=
  source.initial_sealed_source_resolved name hname

theorem binding_resolutions_nodup (source : WFProgram Player L) :
    source.accounted.resolvedSources.Nodup :=
  source.resolutions_nodup

/-- Public-message compilation preserves possible completed public outcomes;
the source run and runtime initialization are both explicit. -/
theorem public_application_outcome (source : WFProgram Player L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (ToEventGraph.BuildState.fromInitial
        (ToEventGraph.initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat)
    (select : (code : PublicChoiceCode Player L) →
      Option (PublicFallbackCode L code.guard.ty))
    (actions : List ((plan.image deadlineOf).withChoiceTimeouts select).application.Action)
    (next : ((plan.image deadlineOf).withChoiceTimeouts select).application.State)
    (hnext : next ∈ (((plan.image deadlineOf).withChoiceTimeouts select).application.run actions
      (Interaction.MessageApplication.State.initial
        ((plan.image deadlineOf).withChoiceTimeouts select).application
        (ApplicationImage.State.initial
          (ApplicationImage.Memory.initial (ToEventGraph.compile source.core).graph)))).support)
    (hfinished : next.application.memory.finished
      (ToEventGraph.compile source.core).graph.nodeCount = true) :
    ∃ terminalEnv : VEnv L (ToEventGraph.compile source.core).terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := (ToEventGraph.compile source.core).terminalCtx, env := terminalEnv,
          cont := .ret (ToEventGraph.compile source.core).sourcePayoffs } ∧
      (ToEventGraph.compile source.core).readPublicTerminal? next.application.memory =
        some terminalEnv.erasePubEnv :=
  ApplicationPlan.run_source_public_outcome source plan deadlineOf select actions next hnext
    hfinished

/-- The same public-outcome safety statement quantifies over arbitrary
randomized policies, without asserting a source-policy correspondence. -/
theorem public_application_policy_outcome (source : WFProgram Player L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (ToEventGraph.BuildState.fromInitial
        (ToEventGraph.initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat)
    (select : (code : PublicChoiceCode Player L) →
      Option (PublicFallbackCode L code.guard.ty))
    (players : Player →
      ((plan.image deadlineOf).withChoiceTimeouts select).application.PlayerPolicy)
    (environment :
      ((plan.image deadlineOf).withChoiceTimeouts select).application.EnvironmentPolicy)
    (schedule : List (@Interaction.MessageApplication.Invocation Player))
    (next : ((plan.image deadlineOf).withChoiceTimeouts select).application.PolicyExecution)
    (hnext : next ∈
      (((plan.image deadlineOf).withChoiceTimeouts select).application.runPolicies
      players environment schedule
      (Interaction.MessageApplication.PolicyExecution.initial
        ((plan.image deadlineOf).withChoiceTimeouts select).application
        (Interaction.MessageApplication.State.initial
          ((plan.image deadlineOf).withChoiceTimeouts select).application
          (ApplicationImage.State.initial
            (ApplicationImage.Memory.initial (ToEventGraph.compile source.core).graph))))).support)
    (hfinished : next.native.application.memory.finished
      (ToEventGraph.compile source.core).graph.nodeCount = true) :
    ∃ terminalEnv : VEnv L (ToEventGraph.compile source.core).terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := (ToEventGraph.compile source.core).terminalCtx, env := terminalEnv,
          cont := .ret (ToEventGraph.compile source.core).sourcePayoffs } ∧
      (ToEventGraph.compile source.core).readPublicTerminal? next.native.application.memory =
        some terminalEnv.erasePubEnv :=
  ApplicationPlan.runPolicies_source_public_outcome source plan deadlineOf select players
    environment schedule next hnext hfinished

/-- Activation-relative deadlines retain source-outcome safety for arbitrary
public-message policies, including both optional fallback families. -/
theorem public_application_windowed_outcome (source : WFProgram Player L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (ToEventGraph.BuildState.fromInitial
        (ToEventGraph.initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode Player L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode Player L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat)
    (players : Player → (plan.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (environment : (plan.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy)
    (schedule : List (@Interaction.MessageApplication.Invocation Player))
    (next : (plan.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hnext : next ∈ ((plan.windowed deadlineOf binding choice windowOf).application.runPolicies
      players environment schedule
      (Interaction.MessageApplication.PolicyExecution.initial _
        (Interaction.MessageApplication.State.initial _
          ((plan.windowed deadlineOf binding choice windowOf).initial
            (ApplicationImage.State.initial
              (ApplicationImage.Memory.initial
                (ToEventGraph.compile source.core).graph)))))).support)
    (hfinished : next.native.application.base.memory.finished
      (ToEventGraph.compile source.core).graph.nodeCount = true) :
    ∃ terminalEnv : VEnv L (ToEventGraph.compile source.core).terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := (ToEventGraph.compile source.core).terminalCtx, env := terminalEnv,
          cont := .ret (ToEventGraph.compile source.core).sourcePayoffs } ∧
      (ToEventGraph.compile source.core).readPublicTerminal? next.native.application.base.memory =
        some terminalEnv.erasePubEnv :=
  plan.windowed_runPolicies_source_public_outcome source deadlineOf binding choice windowOf
    players environment schedule next hnext hfinished

/-- For an eligible application plan, lifting one source profile and running
the emitted serial reference service gives the source law of joint completion
and public terminal output, including with optional binding and public-choice
fallbacks. -/
theorem public_application_reference_law (source : WFProgram Player L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (ToEventGraph.BuildState.fromInitial
        (ToEventGraph.initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode Player L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode Player L) → Option (PublicFallbackCode L code.guard.ty))
    (profile : SourceBehavioralProfile source.core.prog)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins) :
    (((((plan.image deadlineOf).withBindingTimeouts binding).withChoiceTimeouts
      choice).application.runPolicies
      (plan.liftProfile deadlineOf profile) (plan.image deadlineOf).serialService
      (plan.image deadlineOf).serviceInvocations (plan.initialExecution deadlineOf)).map
        (fun out =>
          (out.native.application.memory.finished
              (ToEventGraph.compile source.core).graph.nodeCount,
            (ToEventGraph.compile source.core).readPublicTerminal?
              out.native.application.memory))) =
      (denoteSource source.core.prog profile source.core.env).map fun terminal =>
        (true, some (cast (congrArg (VEnv L)
          (ToEventGraph.compileCore_terminalCtx_eq_sourceTerminalCtx source.core.prog
            source.core.fresh
            (ToEventGraph.BuildState.fromInitial
              (ToEventGraph.initialState source.core.Γ source.core.env
                source.core.wctx))).symm) terminal).erasePubEnv) :=
  plan.timeout_service_source_public_law source deadlineOf binding choice profile hinitial horigins

/-- Source-ordered admission with optional binding and public-choice fallbacks
retains the generated reference service's exact joint completion and public-output
law. It asserts neither progress under other services nor deviation simulation. -/
theorem public_application_ordered_reference_law (source : WFProgram Player L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (ToEventGraph.BuildState.fromInitial
        (ToEventGraph.initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode Player L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode Player L) → Option (PublicFallbackCode L code.guard.ty))
    (profile : SourceBehavioralProfile source.core.prog)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins) :
    (((((plan.image deadlineOf).withBindingTimeouts binding).withChoiceTimeouts
      choice).orderedApplication.runPolicies
      (plan.liftProfile deadlineOf profile) (plan.image deadlineOf).serialService
      (plan.image deadlineOf).serviceInvocations (plan.initialExecution deadlineOf)).map
        (fun out =>
          (out.native.application.memory.finished
              (ToEventGraph.compile source.core).graph.nodeCount,
            (ToEventGraph.compile source.core).readPublicTerminal?
              out.native.application.memory))) =
      (denoteSource source.core.prog profile source.core.env).map fun terminal =>
        (true, some (cast (congrArg (VEnv L)
          (ToEventGraph.compileCore_terminalCtx_eq_sourceTerminalCtx source.core.prog
            source.core.fresh
            (ToEventGraph.BuildState.fromInitial
              (ToEventGraph.initialState source.core.Γ source.core.env
                source.core.wctx))).symm) terminal).erasePubEnv) :=
  plan.ordered_timeout_service_source_public_law source deadlineOf binding choice
    profile hinitial horigins

/-- Public activation clocks retain the source reference law through an
explicit erasure of current and remembered observations. -/
theorem public_application_windowed_reference_law (source : WFProgram Player L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (ToEventGraph.BuildState.fromInitial
        (ToEventGraph.initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode Player L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode Player L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (profile : SourceBehavioralProfile source.core.prog)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins) :
    let runtime := plan.windowed deadlineOf binding choice windowOf
    let execution := Interaction.MessageApplication.PolicyExecution.initial runtime.application
      (Interaction.MessageApplication.State.initial runtime.application
        (runtime.initial (ApplicationImage.State.initial
          (ApplicationImage.Memory.initial (ToEventGraph.compile source.core).graph))))
    (runtime.application.runPolicies
      (fun who => runtime.liftPlayerPolicy (plan.liftProfile deadlineOf profile who))
      (runtime.liftEnvironmentPolicy (plan.image deadlineOf).serialService)
      (plan.image deadlineOf).serviceInvocations execution).map (fun out =>
        (out.native.application.base.memory.finished
            (ToEventGraph.compile source.core).graph.nodeCount,
          (ToEventGraph.compile source.core).readPublicTerminal?
            out.native.application.base.memory)) =
      (denoteSource source.core.prog profile source.core.env).map fun terminal =>
        (true, some (cast (congrArg (VEnv L)
          (ToEventGraph.compileCore_terminalCtx_eq_sourceTerminalCtx source.core.prog
            source.core.fresh (ToEventGraph.BuildState.fromInitial
              (ToEventGraph.initialState source.core.Γ source.core.env source.core.wctx))).symm)
            terminal).erasePubEnv) :=
  plan.windowed_service_source_public_law source deadlineOf binding choice windowOf
    profile hinitial horigins

section WindowedDeviation

open Vegas.ToEventGraph

/-- The initialized fixed block service simulates every randomized unilateral
raw policy by a finite mixture of legal source policies, observing completion
and the executable public output. -/
theorem public_application_windowed_deviation_mixture
    {P : Type} [DecidableEq P] {L : IExpr}
    (source : WFProgram P L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (profile : SourceBehavioralProfile source.core.prog) (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (roster : List P) (focal : P)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins)
    (hfallbacks : plan.BlockFallbacks binding choice)
    (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ plan.instructions deadlineOf,
      ∀ actor, instruction.submitter = some actor → actor ∈ roster)
    (replacement : (plan.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (relay : P) (hrelay : relay ∈ roster) (hrelayOther : relay ≠ focal) :
    ∃ sourceMixture : FinDist (SourceBehavioralPolicy source.core.prog focal),
    (((plan.windowed deadlineOf binding choice windowOf).application.runPolicies
      (plan.windowedPlayers profile deadlineOf binding choice windowOf focal replacement)
      ((plan.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (List.replicate (plan.instructions deadlineOf).length
        (WindowedApplication.blockInvocations roster)).flatten
      (plan.windowedInitialExecution deadlineOf binding choice windowOf)).map fun out =>
        (out.native.application.base.memory.finished (compile source.core).graph.nodeCount,
          (compile source.core).readPublicTerminal? out.native.application.base.memory)) =
      sourceMixture.bind fun sourceReplacement =>
        (denoteSource source.core.prog
          (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
            sourceReplacement) source.core.env).map fun terminal =>
          (true, some (cast (congrArg (VEnv L)
            (compileCore_terminalCtx_eq_sourceTerminalCtx source.core.prog source.core.fresh
              (BuildState.fromInitial
                (initialState source.core.Γ source.core.env source.core.wctx))).symm)
              terminal).erasePubEnv) :=
  ApplicationPlan.windowed_deviation_source_public_mixture source plan profile deadlineOf
    binding choice windowOf roster focal hinitial horigins hfallbacks hroster howners replacement
    relay hrelay hrelayOther

/-- The coordinatewise compiled source profile has its exact public-result law
in the actual fixed block-service game. The focal player only indexes the proof. -/
theorem public_application_windowed_game_honest_law
    {P : Type} [DecidableEq P] {L : IExpr}
    (source : WFProgram P L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (profile : SourceBehavioralProfile source.core.prog) (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (roster : List P) (focal : P)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins)
    (hfallbacks : plan.BlockFallbacks binding choice) (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ plan.instructions deadlineOf,
      ∀ actor, instruction.submitter = some actor → actor ∈ roster) :
    ((source.windowedGame plan deadlineOf binding choice windowOf roster).play
      (fun who => source.windowedCompilePolicy plan deadlineOf binding choice windowOf
        who (profile who))).map
        (source.windowedPublicResult plan deadlineOf binding choice windowOf) =
      ((sourceGameForm source.core.prog source.core.env).play profile).map
        source.publicResult :=
  source.windowed_honest_public_law plan deadlineOf binding choice windowOf profile roster
    focal hinitial horigins hfallbacks hroster howners

/-- The native windowed game transfers every source lower bound on the public
result to arbitrary randomized raw-command deviations. -/
theorem public_application_windowed_game_guarantee
    {P : Type} [DecidableEq P] {L : IExpr}
    (source : WFProgram P L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (profile : SourceBehavioralProfile source.core.prog) (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (roster : List P) (focal : P)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins)
    (hfallbacks : plan.BlockFallbacks binding choice) (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ plan.instructions deadlineOf,
      ∀ actor, instruction.submitter = some actor → actor ∈ roster)
    (value : (Bool × Option (Env L.Val
      (erasePubVCtx (compile source.core).terminalCtx))) → ℝ)
    (bound : ℝ)
    (hbound : ∀ alternative : SourceBehavioralPolicy source.core.prog focal,
      bound ≤ ((sourceGameForm source.core.prog source.core.env).play
        (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
          alternative)).expect (fun terminal => value (source.publicResult terminal)))
    (replacement : (source.windowedGame plan deadlineOf binding choice windowOf roster).sig.Strategy
      focal)
    (relay : P) (hrelay : relay ∈ roster) (hrelayOther : relay ≠ focal) :
    bound ≤ ((source.windowedGame plan deadlineOf binding choice windowOf roster).play
      (Profile.update
        (sig := (source.windowedGame plan deadlineOf binding choice windowOf roster).sig)
        (fun who => source.windowedCompilePolicy plan deadlineOf binding choice windowOf
          who (profile who)) focal replacement)).expect
      (fun out => value
        (source.windowedPublicResult plan deadlineOf binding choice windowOf out)) :=
  source.windowed_guarantee plan deadlineOf binding choice windowOf profile roster focal
    hinitial horigins hfallbacks hroster howners value bound hbound replacement relay hrelay
    hrelayOther

/-- Coordinatewise compilation preserves and reflects the same approximate-Nash
budget for utilities of completion and executable public terminal output. -/
theorem public_application_windowed_game_approximate_nash_iff
    {P : Type} [DecidableEq P] {L : IExpr}
    (source : WFProgram P L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (profile : SourceBehavioralProfile source.core.prog) (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (roster : List P) (focal : P)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins)
    (hfallbacks : plan.BlockFallbacks binding choice) (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ plan.instructions deadlineOf,
      ∀ actor, instruction.submitter = some actor → actor ∈ roster)
    (hrelays : ∀ player, ∃ relay ∈ roster, relay ≠ player)
    (value : (Bool × Option
      (Env L.Val (erasePubVCtx (compile source.core).terminalCtx))) → P → ℝ)
    (ε : ℝ) :
    IsεNash (source.windowedGame plan deadlineOf binding choice windowOf roster)
      (fun out player => value
        (source.windowedPublicResult plan deadlineOf binding choice windowOf out) player) ε
      (fun player => source.windowedCompilePolicy plan deadlineOf binding choice windowOf
        player (profile player)) ↔
      IsεNash (sourceGameForm source.core.prog source.core.env)
        (fun terminal player => value (source.publicResult terminal) player) ε profile :=
  source.windowed_approximate_nash_iff plan deadlineOf binding choice windowOf profile roster
    focal hinitial horigins hfallbacks hroster howners hrelays value ε

/-- Coordinatewise compilation preserves and reflects expected-utility Nash
for utilities of completion and executable public terminal output. -/
theorem public_application_windowed_game_nash_iff
    {P : Type} [DecidableEq P] {L : IExpr}
    (source : WFProgram P L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (profile : SourceBehavioralProfile source.core.prog) (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (roster : List P) (focal : P)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins)
    (hfallbacks : plan.BlockFallbacks binding choice) (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ plan.instructions deadlineOf,
      ∀ actor, instruction.submitter = some actor → actor ∈ roster)
    (hrelays : ∀ player, ∃ relay ∈ roster, relay ≠ player)
    (value : (Bool × Option
      (Env L.Val (erasePubVCtx (compile source.core).terminalCtx))) → P → ℝ) :
    IsNash (source.windowedGame plan deadlineOf binding choice windowOf roster)
      (euPreference (fun out player => value
        (source.windowedPublicResult plan deadlineOf binding choice windowOf out) player))
      (fun player => source.windowedCompilePolicy plan deadlineOf binding choice windowOf
        player (profile player)) ↔
      IsNash (sourceGameForm source.core.prog source.core.env)
        (euPreference (fun terminal player => value (source.publicResult terminal) player))
        profile :=
  source.windowed_nash_iff plan deadlineOf binding choice windowOf profile roster focal
    hinitial horigins hfallbacks hroster howners hrelays value

end WindowedDeviation

/-- A missing authenticated submission cannot be supplied by scheduling.
The generated code's submission requirement is an inspectable static premise. -/
theorem public_application_withholding (source : WFProgram Player L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (ToEventGraph.BuildState.fromInitial
        (ToEventGraph.initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat) (node : Nat) (who : Player)
    (required : (plan.image deadlineOf).RequiresSubmission node who)
    (hnode : node < (ToEventGraph.compile source.core).graph.nodeCount)
    (profile : SourceBehavioralProfile source.core.prog)
    (environment : (plan.image deadlineOf).application.EnvironmentPolicy)
    (schedule : List (@Interaction.MessageApplication.Invocation Player)) :
    (((plan.image deadlineOf).application.runPolicies
      (Profile.update
        (sig := Interaction.MessageApplication.policySignature Player
          (plan.image deadlineOf).application)
        (plan.liftProfile deadlineOf profile) who (fun _ _ => FinDist.pure .wait))
      environment schedule (plan.initialExecution deadlineOf)).map
        (fun out => out.native.application.memory.finished
          (ToEventGraph.compile source.core).graph.nodeCount)) = FinDist.pure false :=
  plan.withholding_finished_law source deadlineOf node who required hnode
    (plan.liftProfile deadlineOf profile) environment schedule

/-- At a ready generated conditional endpoint, one owner invocation followed
by the assumed inclusion action has exactly the supplied randomized source
law. Every supported inclusion advances the adjacent source pair and native
refinement under either accepted binding disposition. -/
theorem public_application_conditional_phase
    {Γ : VCtx Player L} {name publicName : VarId} {who : Player} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore Player L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (spec : ConditionalOpening guard)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : ToEventGraph.BuildState Player L Γ) (sourceSlot deadline : Nat)
    (current : ToEventGraph.CoupledAt
      (ToEventGraph.compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (image : ApplicationImage Player L)
    (sourcePolicy :
      (visible : Env L.Val (eraseVCtx (viewVCtx who Γ))) →
        FinDist { value : L.Val ty // evalGuard guard value visible = true })
    (players : Player → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (execution : image.application.PolicyExecution)
    (hrefines : execution.native.application.Refines current.current.graph.1)
    (heligible :
      (ConditionalPublicationSite.atHead name publicName who guard tail spec).PubliclyValidatable
        fresh build)
    (disposition : Interaction.BindingDisposition (Interaction.CommitmentHandle Player Nat)
      (L.Val spec.secretTy))
    (hbinding : ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
      fresh build sourceSlot deadline).binding? execution.native.application.memory =
        some disposition)
    (hcanonical : ∀ handle, disposition = .opaque handle → handle = (who, sourceSlot))
    (hcode : image.lookup
        ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
          fresh build sourceSlot deadline).endpoint.publicationNode = some (.conditional
      ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
        fresh build sourceSlot deadline)))
    (reads : ReadEnv L (ToEventGraph.eventGuardOf build who guard).choiceReads)
    (hpolicy : ∀ history,
      players who history
          (Interaction.MessageApplication.State.observe image.application execution.native who) =
        (ConditionalPublicationSite.atHead name publicName who guard tail spec).imagePolicy
          fresh build sourceSlot deadline image
          (image.ownerReadout? who (ToEventGraph.eventGuardOf build who guard).choiceReads)
          sourcePolicy (fun _ _ => false) history
            (Interaction.MessageApplication.State.observe
              image.application execution.native who))
    (henvironment : ∀ chosen ∈
        (sourcePolicy ((current.current.source.toView who).eraseEnv)).support,
      ∀ submitted ∈ (image.application.playerStep who execution
        (.submit (.conditional
          ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
            fresh build sourceSlot deadline).endpoint.publicationNode
          (ConditionalPublicationSite.sourceRequestPayload
            (ConditionalPublicationSite.atHead name publicName who guard tail spec)
            fresh build sourceSlot deadline disposition (spec.encoding chosen.1))))).support,
      environment submitted.environmentHistory
          (Interaction.MessageApplication.State.environmentView
            image.application submitted.native) =
        FinDist.pure (.include (who, execution.native.pool.nextSerial who)))
    (hlookupFresh : execution.native.pool.lookup
      (who, execution.native.pool.nextSerial who) = none)
    (hcache : Interaction.MessageApplication.ChoiceEncoding.cachedValue image.application
      ((ConditionalPublicationSite.choiceEncodingFor
        (ConditionalPublicationSite.atHead name publicName who guard tail spec)
        fresh build sourceSlot deadline disposition
        (ApplicationImage.conditionalTransport spec.secretTy)).submission image.application)
      (execution.principalHistory who) = none)
    (hreadout : image.ownerReadout? who
        (ToEventGraph.eventGuardOf build who guard).choiceReads
      (execution.principalHistory who)
      (Interaction.MessageApplication.State.observe image.application execution.native who) =
        some reads)
    (hreads : ReadEnv.ofStore? current.current.graph.1.store
      (ToEventGraph.eventGuardOf build who guard).choiceReads = some reads)
    (hfrozen : ∀ chosen ∈
        (sourcePolicy ((current.current.source.toView who).eraseEnv)).support,
      ∀ handle value, disposition = .opaque handle → spec.encoding chosen.1 = some value →
        (execution.native.application.frozen (build.fieldOf spec.binding)).bind
          (fun typed => typed.as? spec.secretTy) = some value) :
    let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
    let code := site.code fresh build sourceSlot deadline
    let id := (who, execution.native.pool.nextSerial who)
    (image.application.runPolicies players environment [.player who, .environment] execution =
      (sourcePolicy ((current.current.source.toView who).eraseEnv)).bind fun chosen =>
        (image.application.playerStep who execution
          (.submit (.conditional code.endpoint.publicationNode
            (site.sourceRequestPayload fresh build sourceSlot deadline disposition
              (spec.encoding chosen.1))))).bind
            fun submitted => image.application.environmentPolicyStep submitted (.include id)) ∧
    (∀ chosen ∈ (sourcePolicy ((current.current.source.toView who).eraseEnv)).support,
      ∀ submitted ∈ (image.application.playerStep who execution
        (.submit (.conditional code.endpoint.publicationNode
          (site.sourceRequestPayload fresh build sourceSlot deadline disposition
            (spec.encoding chosen.1))))).support,
      ∀ included ∈
        (image.application.environmentPolicyStep submitted (.include id)).support,
      ∃ next : ToEventGraph.CoupledAt
          (ToEventGraph.compileCore
            (.commit name who guard (.reveal publicName who name .here tail)) fresh build).graph
          (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
            publicName who .here fresh.2.1).1,
        next.current.source = (current.current.source.cons chosen.1).cons chosen.1 ∧
          included.native.application.Refines next.current.graph.1) ∧
    (image.activeAddress? execution.native.application.memory =
        some code.endpoint.publicationNode →
      image.orderedApplication.runPolicies players environment
          [.player who, .environment] execution =
        image.application.runPolicies players environment
          [.player who, .environment] execution) :=
  ConditionalPublicationSite.conditional_phase_source_law guard tail spec fresh build
    sourceSlot deadline current image sourcePolicy players environment execution hrefines
    heligible disposition hbinding hcanonical hcode reads hpolicy henvironment hlookupFresh
    hcache hreadout hreads hfrozen

/-- Inclusion of a legal generated conditional request advances the exact
adjacent source choice/reveal pair. Opaque dispositions require the canonical
handle and matching frozen opening; public defaults require neither premise. -/
theorem public_application_conditional_continuation
    {Γ : VCtx Player L} {name publicName : VarId} {who : Player} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore Player L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (spec : ConditionalOpening guard)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : ToEventGraph.BuildState Player L Γ) (sourceSlot deadline : Nat)
    (current : ToEventGraph.CoupledAt
      (ToEventGraph.compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (image : ApplicationImage Player L) (execution : image.application.State)
    (hrefines : execution.application.Refines current.current.graph.1)
    (heligible :
      (ConditionalPublicationSite.atHead name publicName who guard tail spec).PubliclyValidatable
        fresh build)
    (disposition : Interaction.BindingDisposition (Interaction.CommitmentHandle Player Nat)
      (L.Val spec.secretTy))
    (hbinding : ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
      fresh build sourceSlot deadline).binding? execution.application.memory = some disposition)
    (hcanonical : ∀ handle, disposition = .opaque handle → handle = (who, sourceSlot))
    (address serial : Nat)
    (hcode : image.lookup address = some (.conditional
      ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
        fresh build sourceSlot deadline)))
    (chosen : L.Val ty)
    (hlookup : execution.pool.lookup (who, serial) = some ⟨(who, serial), .conditional address
      ((ConditionalPublicationSite.atHead name publicName who guard tail spec).sourceRequestPayload
        fresh build sourceSlot deadline disposition (spec.encoding chosen))⟩)
    (hlegal : evalGuard guard chosen ((current.current.source.toView who).eraseEnv) = true)
    (hfrozen : ∀ handle value, disposition = .opaque handle →
      spec.encoding chosen = some value →
      (execution.application.frozen (build.fieldOf spec.binding)).bind
        (fun typed => typed.as? spec.secretTy) = some value) :
    ∃ next : ToEventGraph.CoupledAt
        (ToEventGraph.compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh build).graph
        (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1,
      next.current.source = (current.current.source.cons chosen).cons chosen ∧
        (image.application.includePending execution (who, serial)).application.Refines
          next.current.graph.1 :=
  ConditionalPublicationSite.include_source_coupling guard tail spec fresh build sourceSlot
    deadline current image execution hrefines heligible disposition hbinding hcanonical address
    serial hcode chosen hlookup hlegal hfrozen

/-- An included overdue expiry at a generated conditional endpoint implements
the existing source decline, with no requirement that its sender be the owner. -/
theorem public_application_conditional_expiry
    {Γ : VCtx Player L} {name publicName : VarId} {who : Player} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore Player L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (spec : ConditionalOpening guard)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : ToEventGraph.BuildState Player L Γ) (sourceSlot deadline : Nat)
    (current : ToEventGraph.CoupledAt
      (ToEventGraph.compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (image : ApplicationImage Player L)
    (execution included : image.application.PolicyExecution)
    (hrefines : execution.native.application.Refines current.current.graph.1)
    (disposition : Interaction.BindingDisposition (Interaction.CommitmentHandle Player Nat)
      (L.Val spec.secretTy))
    (hbinding : ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
      fresh build sourceSlot deadline).binding? execution.native.application.memory =
        some disposition)
    (hcanonical : ∀ handle, disposition = .opaque handle → handle = (who, sourceSlot))
    (hoverdue : deadline < execution.native.application.memory.clock)
    (address : Nat)
    (hcode : image.lookup address = some (.conditional
      ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
        fresh build sourceSlot deadline)))
    (id : Interaction.MessageId Player)
    (hlookup : execution.native.pool.lookup id = some ⟨id, .conditional address .expire⟩)
    (hincluded : included ∈
      (image.application.environmentPolicyStep execution (.include id)).support) :
    ∃ next : ToEventGraph.CoupledAt
        (ToEventGraph.compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh build).graph
        (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1,
      next.current.source = (current.current.source.cons (spec.encoding.symm none)).cons
        (spec.encoding.symm none) ∧
        included.native.application.Refines next.current.graph.1 :=
  (ConditionalPublicationSite.expiry_include_source_coupling guard tail spec fresh build
    sourceSlot deadline current image execution included hrefines disposition hbinding hcanonical
    hoverdue
    address hcode id hlookup hincluded).2.2.2

/-- An included public-choice expiry follows an explicitly annotated legal
public source expression, without supplying a command by the endpoint owner. -/
theorem public_application_choice_expiry
    {Γ : VCtx Player L} {name publicName : VarId} {who : Player} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore Player L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback
      (PublicChoiceSite.atHead name publicName who guard tail).decision)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : ToEventGraph.BuildState Player L Γ) (deadline : Nat)
    (current : ToEventGraph.CoupledAt
      (ToEventGraph.compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (image : ApplicationImage Player L)
    (execution included : image.application.PolicyExecution)
    (hrefines : execution.native.application.Refines current.current.graph.1)
    (heligible : (PublicChoiceSite.atHead name publicName who guard tail).PubliclyValidatable
      fresh build)
    (hoverdue : deadline < execution.native.application.memory.clock)
    (address : Nat)
    (hcode : image.lookup address = some (.publicChoice
      ((PublicChoiceSite.atHead name publicName who guard tail).timeoutCode
        fallback fresh build deadline)))
    (id : Interaction.MessageId Player)
    (hlookup : execution.native.pool.lookup id = some ⟨id, .expireChoice address⟩)
    (hincluded : included ∈
      (image.application.environmentPolicyStep execution (.include id)).support) :
    let chosen := L.eval fallback.expr current.current.source.erasePubEnv
    ∃ next : ToEventGraph.CoupledAt
        (ToEventGraph.compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh build).graph
        (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1,
      next.current.source = (current.current.source.cons chosen).cons chosen ∧
        included.native.application.Refines next.current.graph.1 :=
  (PublicChoiceSite.expiry_include_source_coupling guard tail fallback fresh build deadline
    current image execution included hrefines heligible hoverdue address hcode id hlookup
    hincluded).2.2.2.2

/-- Actual inclusion of source-authorized binding expiry advances the original
source decision to the public fallback without requiring private preparation. -/
theorem public_application_binding_expiry
    {Γ : VCtx Player L} {name : VarId} {who : Player} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore Player L ((name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : ToEventGraph.BuildState Player L Γ) (deadline : Nat)
    (current : ToEventGraph.CoupledAt
      (ToEventGraph.compileCore (.commit name who guard tail) fresh build).graph build)
    (image : ApplicationImage Player L) (execution : image.application.State)
    (hrefines : execution.application.Refines current.current.graph.1)
    (hoverdue : deadline < execution.application.memory.clock)
    (address : Nat)
    (hcode : image.lookup address = some (.bind
      (fallback.bindingTimeoutCode fresh build deadline)))
    (id : Interaction.MessageId Player)
    (hlookup : execution.pool.lookup id = some ⟨id, .expireBinding address⟩) :
    let chosen := L.eval fallback.expr current.current.source.erasePubEnv
    ∃ next : ToEventGraph.CoupledAt
        (ToEventGraph.compileCore (.commit name who guard tail) fresh build).graph
        (build.addCommitEvent name who guard fresh.1).1,
      next.current.source = current.current.source.cons chosen ∧
        (image.application.includePending execution id).application.Refines
          next.current.graph.1 ∧
        (image.application.includePending execution id).receipts =
          execution.receipts ++ [(id, true)] ∧
        (image.application.includePending execution id).pool.ledger =
          execution.pool.ledger ++ [⟨id, .expireBinding address⟩] ∧
        (image.application.includePending execution id).pool.sent = execution.pool.sent ∧
        (image.application.includePending execution id).pool.inbox = execution.pool.inbox :=
  fallback.expiry_include_source_coupling guard tail
    fresh build deadline current image execution hrefines hoverdue address hcode id hlookup

/-- info: 'Vegas.Paper.Source.committed_binding_accounted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.committed_binding_accounted

/-- info: 'Vegas.Paper.Source.initial_binding_accounted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.initial_binding_accounted

/-- info: 'Vegas.Paper.Source.binding_resolutions_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.binding_resolutions_nodup

/-- info: 'Vegas.Paper.Source.public_application_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_outcome

/-- info: 'Vegas.Paper.Source.public_application_policy_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_policy_outcome

/-- info: 'Vegas.Paper.Source.public_application_windowed_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_windowed_outcome

/-- info: 'Vegas.Paper.Source.public_application_reference_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_reference_law

/-- info: 'Vegas.Paper.Source.public_application_ordered_reference_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_ordered_reference_law

/-- info: 'Vegas.Paper.Source.public_application_windowed_reference_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_windowed_reference_law

/-- info: 'Vegas.Paper.Source.public_application_windowed_deviation_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_windowed_deviation_mixture

/-- info: 'Vegas.Paper.Source.public_application_windowed_game_honest_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_windowed_game_honest_law

/-- info: 'Vegas.Paper.Source.public_application_windowed_game_guarantee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_windowed_game_guarantee

/-- info: 'Vegas.Paper.Source.public_application_windowed_game_approximate_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_windowed_game_approximate_nash_iff

/-- info: 'Vegas.Paper.Source.public_application_windowed_game_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_windowed_game_nash_iff

/-- info: 'Vegas.Paper.Source.public_application_withholding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_withholding

/-- info: 'Vegas.Paper.Source.public_application_conditional_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_conditional_phase

/-- info: 'Vegas.Paper.Source.public_application_conditional_continuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_conditional_continuation

/-- info: 'Vegas.Paper.Source.public_application_conditional_expiry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_conditional_expiry

/-- info: 'Vegas.Paper.Source.public_application_choice_expiry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_choice_expiry

/-- info: 'Vegas.Paper.Source.public_application_binding_expiry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_binding_expiry

section PendingDelivery

open Vegas.ToEventGraph

/-! ## Open whole-program pending-message targets

These declarations specify the delivery edge currently under construction.
Messages are delivered before the raw player's reaction invocation. Opponents
use the coordinatewise source-policy embedding; the deviator is unrestricted.
The environment is the concrete deadline-aware delivery service, not an
arbitrary scheduler. The observation here is completion and public output.
-/

/-- error: declaration uses `sorry` -/
#guard_msgs (whitespace := lax) in
theorem public_application_delivery_reference_law
    {P : Type} [DecidableEq P] {L : IExpr}
    (source : WFProgram P L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (profile : SourceBehavioralProfile source.core.prog) (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (roster recipients : List P)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins)
    (hfallbacks : plan.BlockFallbacks binding choice)
    (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ plan.instructions deadlineOf,
      ∀ actor, instruction.submitter = some actor → actor ∈ roster) :
    let runtime := plan.windowed deadlineOf binding choice windowOf
    let service := runtime.deliveryService roster recipients
    (runtime.application.runPolicies
      (service.referencePlayers (plan.liftProfile deadlineOf profile))
      service.environment
      (List.replicate (plan.instructions deadlineOf).length service.invocations).flatten
      (plan.windowedInitialExecution deadlineOf binding choice windowOf)).map
        (source.windowedPublicResult plan deadlineOf binding choice windowOf) =
      ((sourceGameForm source.core.prog source.core.env).play profile).map
        source.publicResult := by
  sorry

/-- info: 'Vegas.Paper.Source.public_application_delivery_reference_law' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_delivery_reference_law

/-- error: declaration uses `sorry` -/
#guard_msgs (whitespace := lax) in
theorem public_application_delivery_deviation_mixture
    {P : Type} [DecidableEq P] {L : IExpr}
    (source : WFProgram P L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (profile : SourceBehavioralProfile source.core.prog) (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (roster recipients : List P) (focal : P)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins)
    (hfallbacks : plan.BlockFallbacks binding choice)
    (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ plan.instructions deadlineOf,
      ∀ actor, instruction.submitter = some actor → actor ∈ roster)
    (replacement : (plan.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (relay : P) (hrelay : relay ∈ roster) (hrelayOther : relay ≠ focal) :
    let runtime := plan.windowed deadlineOf binding choice windowOf
    let service := runtime.deliveryService roster recipients
    ∃ sourceMixture : FinDist (SourceBehavioralPolicy source.core.prog focal),
      (runtime.application.runPolicies
        (service.players (plan.liftProfile deadlineOf profile) focal replacement)
        service.environment
        (List.replicate (plan.instructions deadlineOf).length service.invocations).flatten
        (plan.windowedInitialExecution deadlineOf binding choice windowOf)).map
          (source.windowedPublicResult plan deadlineOf binding choice windowOf) =
        sourceMixture.bind fun sourceReplacement =>
          ((sourceGameForm source.core.prog source.core.env).play
            (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
              sourceReplacement)).map source.publicResult := by
  sorry

/-- info: 'Vegas.Paper.Source.public_application_delivery_deviation_mixture' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.public_application_delivery_deviation_mixture

end PendingDelivery

end Vegas.Paper.Source
