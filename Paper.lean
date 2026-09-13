/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheoryExtensions.Core.MixtureSimulation
import GameTheoryExtensions.Core.UtilitySimulation
import Interaction.SealedTimeoutDisclosure
import Vegas.Language.Nullable
import Vegas.Compile.SealedCompiler
import Vegas.Compile.SourceLaw
import Vegas.Core.AccountingIntegrity
import Vegas.EventGraph.Confluence
import Vegas.EventGraph.Fence
import Vegas.EventGraph.SourceOrder
import Vegas.Compile.SealedTimeoutRefinement
import Vegas.EventGraph.Strategic
import Vegas.Game.SealedMessages
import Vegas.Game.SealedRelease
import Vegas.Game.SealedStrategic

/-! # Paper theorem audit

This file is deliberately a thin audit surface. Every closed statement below
delegates directly to a theorem in the active source, graph, or sealed-message
tower. Strategic preservation is stated through the explicit
`StrategicCertificate`: the runtime must provide the honest law and the
finite-mixture law for its considered unilateral deviations.

The pending-message backtranslation for the concrete policy runtime is an open
research obligation. It is not represented here as a theorem with an
unjustified universal conclusion; the certificate interface records exactly
what that proof must construct. If the eventual runtime edge has a target-only
early-resolution action, a Nash theorem may instead use utility domination.
The comparison must concern feasible whole-program continuations with existing
commitments fixed at the information available when quitting is chosen. The
native disclosure bound below does not yet discharge that source-level law.
-/

namespace Vegas.Paper

open GameTheory Vegas EventGraph Interaction
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

theorem sealed_rule_count
    {source : WFProgram Player L} {ty : L.Ty}
    (compilation : SealedCompilation source ty) :
    compilation.program.rules.length =
      (ToEventGraph.compile source.core).graph.nodeCount :=
  compilation.program_rule_count

theorem sealed_source_prefix
    {source : WFProgram Player L} {ty : L.Ty}
    [DecidableEq (L.Val ty)]
    (compilation : SealedCompilation source ty)
    (actions : List (SealedProgram.Action Player (L.Val ty))) :
    ∃ cfg : Config (ToEventGraph.compile source.core).graph,
      (ToEventGraph.compile source.core).graph.decodeSealed ty
        (SealedProgram.run compilation.program
          (SealedProgram.State.empty Player (L.Val ty)) actions) = some cfg ∧
      Reachable (ToEventGraph.compile source.core).graph cfg := by
  obtain ⟨cfg, hdecode, hreachable, _⟩ := compilation.run_source actions
  exact ⟨cfg, hdecode, hreachable⟩

theorem sealed_policy_prefix
    {source : WFProgram Player L} {ty : L.Ty}
    [DecidableEq (L.Val ty)]
    (supported : SealedFragment (ToEventGraph.compile source.core).graph ty)
    (players : Player →
      (supported.compile.messageApplication (Value := L.Val ty)).PlayerPolicy)
    (environment :
      (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution :
      (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution)
    (hmem : execution ∈
      ((MessageApplication.policyGame
        (supported.compile.messageApplication (Value := L.Val ty)) environment schedule
        (MessageApplication.State.initial
          (supported.compile.messageApplication (Value := L.Val ty))
          ⟨IdealCommitments.empty, []⟩)).play players).support) :
    ∃ cfg : Config (ToEventGraph.compile source.core).graph,
      (ToEventGraph.compile source.core).graph.decodeSealed ty
        (supported.compile.eraseReceipts execution.native) = some cfg ∧
      Reachable (ToEventGraph.compile source.core).graph cfg := by
  obtain ⟨cfg, hdecode, hreachable, _⟩ :=
    WFProgram.sealed_policy_source source ty supported players environment schedule
      execution hmem
  exact ⟨cfg, hdecode, hreachable⟩

theorem sealed_cleartext_rejected
    {source : WFProgram Player L} {ty : L.Ty}
    [DecidableEq (L.Val ty)]
    (compilation : SealedCompilation source ty)
    (state : SealedProgram.State Player (L.Val ty))
    (message : Message Player (SealedProgram.Payload Player (L.Val ty)))
    (node : Nat) (value : L.Val ty)
    (hpayload : message.payload = .cleartext node value) :
    SealedProgram.handle compilation.program state message = state :=
  SealedProgram.handle_cleartext compilation.program state message node value hpayload

/-- The source surface has an explicit, always-legal nullable quit value. -/
theorem nullable_quit_is_legal
    {Γ : VCtx Player simpleExpr} {secret : VarId} {b : BaseTy}
    [DefaultVal b]
    (guard : Expr ((secret, b) :: eraseVCtx Γ) .bool)
    (visible : Env Val (eraseVCtx Γ)) :
    evalGuard (Player := Player) (L := simpleExpr)
        (Expr.nullableCommitGuard guard) Option.none visible = true :=
  VegasLang.nullableGuard_none_legal guard visible

theorem sealed_opening_prerequisites
    {source : WFProgram Player L} {ty : L.Ty}
    [DecidableEq (L.Val ty)]
    (supported : SealedFragment (ToEventGraph.compile source.core).graph ty)
    (owner : Player) (node : Fin (ToEventGraph.compile source.core).graph.nodeCount)
    (value : L.Val ty)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (hnonwait : SealedProgram.openingCommand supported.compile owner node.val value view ≠
      .wait) :
    ∀ prior, prior ∈ (ToEventGraph.compile source.core).graph.prereqs node →
      SealedProgram.done view.application prior.val = true :=
  supported.openingCommand_prerequisites owner node value view hnonwait

/-- The actual compiled opening barrier, through a complete native policy trace. -/
theorem sealed_opening_barrier
    {source : WFProgram Player L} {ty : L.Ty}
    [DecidableEq (L.Val ty)]
    (supported : SealedFragment (ToEventGraph.compile source.core).graph ty)
    (owner : Player) (node prior : Fin (ToEventGraph.compile source.core).graph.nodeCount)
    (players : Player → (supported.compile.messageApplication (Value := L.Val ty)).PlayerPolicy)
    (environment : (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (state : (supported.compile.messageApplication (Value := L.Val ty)).State)
    (invariant : SealedProgram.BindingInvariant supported.compile
      (supported.compile.eraseReceipts state))
    (trace : (supported.compile.messageApplication (Value := L.Val ty)).PolicyTrace)
    (htrace : trace ∈ ((supported.compile.messageApplication (Value := L.Val ty)).tracePolicies
      players environment schedule (MessageApplication.PolicyExecution.initial _ state)).support)
    (hready : SealedProgram.openingReady supported.compile
      (trace.firstRelease (fun (execution :
        (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution) =>
        SealedProgram.openingReady supported.compile execution.native.application.events
          owner node.val)).native.application.events owner node.val = true)
    (priorOwner : Player) (guard : EventGuard L)
    (hprior : ((ToEventGraph.compile source.core).graph.nodeRow prior).sem =
      .commit priorOwner guard)
    (hearlier : prior.val < node.val) :
    ∃ value,
      (trace.firstRelease (fun (execution :
        (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution) =>
        SealedProgram.openingReady supported.compile execution.native.application.events
          owner node.val)).native.application.service.lookup (priorOwner, prior.val) = some value ∧
      trace.last.native.application.service.lookup (priorOwner, prior.val) = some value :=
  supported.opening_barrier_trace owner node prior players environment schedule state
    invariant trace htrace hready priorOwner guard hprior hearlier

/-- The utility comparison needed for an informed, randomized quitting decision. -/
theorem selective_quitting_bound {State Outcome : Type*}
    (states : FinDist State) (stop : State → FinDist Bool)
    (quit proceed : State → FinDist Outcome) (utility : Outcome → ℝ) (margin : ℝ)
    (hmargin : ∀ state ∈ states.support, true ∈ (stop state).support →
      (quit state).expect utility + margin ≤ (proceed state).expect utility) :
    (states.bind fun state => (stop state).bind fun stops =>
      if stops then quit state else proceed state).expect utility +
        margin * (states.bind stop).prob true ≤ (states.bind proceed).expect utility :=
  FinDist.selective_stopping_bound states stop quit proceed utility margin hmargin

/-- Concrete pending-message disclosure, conditional on resolution of this checkpoint. -/
theorem sealed_disclosure_utility_bound {Value : Type} [DecidableEq Value]
    (timed : SealedTimeout Player) (initial : SealedTimeout.State Player Value)
    (owner : Player) (source : Nat) (value : Value) (requires : List Nat)
    (hrule : timed.program.rules[timed.openingNode]? = some ⟨.reveal owner source, requires⟩)
    (invariant : SealedTimeout.LockedOpening timed owner source value initial.application)
    (players : Player → (timed.messageApplication (Value := Value)).PlayerPolicy)
    (environment : (timed.messageApplication (Value := Value)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (hresolved : ∀ execution ∈ ((timed.messageApplication (Value := Value)).runPolicies
      players environment schedule
      (MessageApplication.PolicyExecution.initial _ (timed.toSharedState initial))).support,
      execution.native.application.application.resolution ≠ .pending)
    (utility : DisclosureResult Value → ℝ) (margin : ℝ)
    (hmargin : utility .expired + margin ≤ utility (.opened value)) :
    let law := (timed.messageApplication (Value := Value)).runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial _ (timed.toSharedState initial))
    (law.map (fun execution => timed.disclosureResult
        execution.native.application.application)).expect utility +
        margin * (law.map (fun execution => decide
          (execution.native.application.application.resolution = .expired))).prob true ≤
      utility (.opened value) :=
  SealedTimeout.resolved_policy_utility_bound timed initial owner source value requires hrule
    invariant players environment schedule hresolved utility margin hmargin

/-- Utility-specific simulation suffices even when exact outcome-law simulation fails. -/
theorem utility_approximate_nash_preservation
    {source target : GameForm Player}
    {sourceUtility : source.sig.Outcome → Player → ℝ}
    {targetUtility : target.sig.Outcome → Player → ℝ}
    (simulation : GameForm.UtilitySimulation source target sourceUtility targetUtility)
    (ε : ℝ) (profile : Profile source.sig) :
    IsεNash target targetUtility ε (simulation.compileProfile profile) ↔
      IsεNash source sourceUtility ε profile :=
  simulation.isεNash_compileProfile_iff ε profile

theorem sealed_nash_preservation
    {source : WFProgram Player L} {ty : L.Ty}
    (compilation : SealedCompilation source ty)
    {Observation : Type}
    {target : GameForm Player}
    (sourceObserve :
      (Vegas.sourceGameForm source.core.prog source.core.env).sig.Outcome → Observation)
    (targetObserve : target.sig.Outcome → Observation)
    (Considered : (who : Player) → target.sig.Strategy who → Prop)
    (certificate : compilation.StrategicCertificate target sourceObserve targetObserve Considered)
    (value : Observation → Player → ℝ) (ε : ℝ)
    (profile : Profile (Vegas.sourceGameForm source.core.prog source.core.env).sig)
    (hall : ∀ who strategy, Considered who strategy) :
    IsεNash target (fun outcome who => value (targetObserve outcome) who) ε
        (certificate.simulation.compileProfile profile) ↔
      IsεNash (Vegas.sourceGameForm source.core.prog source.core.env)
        (fun outcome who => value (sourceObserve outcome) who) ε profile :=
  certificate.isεNash_compileProfile_iff value ε profile hall

theorem sealed_quit_dominance_transfer
    {source : WFProgram Player L} {ty : L.Ty}
    (compilation : SealedCompilation source ty)
    {Observation : Type}
    {target : GameForm Player}
    (sourceObserve :
      (Vegas.sourceGameForm source.core.prog source.core.env).sig.Outcome → Observation)
    (targetObserve : target.sig.Outcome → Observation)
    (Considered : (who : Player) → target.sig.Strategy who → Prop)
    (certificate : compilation.StrategicCertificate target sourceObserve targetObserve Considered)
    (value : Observation → Player → ℝ)
    (profile : Profile (Vegas.sourceGameForm source.core.prog source.core.env).sig)
    (who : Player)
    (quit preferred : SourceBehavioralPolicy source.core.prog who)
    (quitTarget : target.sig.Strategy who)
    (hquit :
      (target.play (Profile.update (certificate.simulation.compileProfile profile)
        who quitTarget)).expect
          (fun outcome => value (targetObserve outcome) who) =
      ((Vegas.sourceGameForm source.core.prog source.core.env).play
        (Profile.update profile who quit)).expect
          (fun outcome => value (sourceObserve outcome) who))
    (hstrict :
      ((Vegas.sourceGameForm source.core.prog source.core.env).play
        (Profile.update profile who quit)).expect
          (fun outcome => value (sourceObserve outcome) who) <
      ((Vegas.sourceGameForm source.core.prog source.core.env).play
        (Profile.update profile who preferred)).expect
          (fun outcome => value (sourceObserve outcome) who)) :
    ¬ IsNash target
      (euPreference (fun outcome player => value (targetObserve outcome) player))
      (Profile.update (certificate.simulation.compileProfile profile)
        who quitTarget) :=
  certificate.compiled_quit_profile_not_isNash_of_quit_law
    value profile who quit preferred quitTarget hquit hstrict

/-! The graph-level strategic edge is complete under its explicit information
conditions. It is the reusable theorem a concrete runtime must instantiate
before pending messages, clocks, or settlement are added. -/

theorem graph_approximate_nash_preservation
    {G : EventGraph.Graph Player L}
    [Fintype Player]
    (hwf : G.WF) (hguards : EventGraph.GuardLive G)
    (hlocal : EventGraph.CommitInformationLocal G hwf hguards)
    (hsingle : ∀ (cfg : EventGraph.Config G) who first second,
      EventGraph.ReadyCommitNode G cfg who first →
      EventGraph.ReadyCommitNode G cfg who second → first = second)
    (value : EventGraph.ReachableConfig G → Player → ℝ) (ε : ℝ)
    (profile : Profile
      (EventGraph.Strategic.graphModel G hwf hguards).behavioralSignature) :
    IsεNash (EventGraph.policyGame G hwf hguards)
      (fun outcome who => value (EventGraph.Strategic.policyObserve G outcome) who) ε
      ((EventGraph.Strategic.simulation G hwf hguards hlocal hsingle).compileProfile profile) ↔
      IsεNash (EventGraph.behavioralGame G hwf hguards)
        (fun outcome who =>
          value (EventGraph.Strategic.behavioralObserve G hwf hguards outcome) who) ε profile :=
  EventGraph.Strategic.isεNash_compileProfile_iff G hwf hguards hlocal hsingle value ε profile

theorem graph_nash_preservation
    {G : EventGraph.Graph Player L}
    [Fintype Player]
    (hwf : G.WF) (hguards : EventGraph.GuardLive G)
    (hlocal : EventGraph.CommitInformationLocal G hwf hguards)
    (hsingle : ∀ (cfg : EventGraph.Config G) who first second,
      EventGraph.ReadyCommitNode G cfg who first →
      EventGraph.ReadyCommitNode G cfg who second → first = second)
    (value : EventGraph.ReachableConfig G → Player → ℝ)
    (profile : Profile
      (EventGraph.Strategic.graphModel G hwf hguards).behavioralSignature) :
    IsNash (EventGraph.policyGame G hwf hguards)
      (euPreference (fun outcome who =>
        value (EventGraph.Strategic.policyObserve G outcome) who))
      ((EventGraph.Strategic.simulation G hwf hguards hlocal hsingle).compileProfile profile) ↔
      IsNash (EventGraph.behavioralGame G hwf hguards)
        (euPreference (fun outcome who =>
          value (EventGraph.Strategic.behavioralObserve G hwf hguards outcome) who)) profile :=
  EventGraph.Strategic.isNash_compileProfile_iff G hwf hguards hlocal hsingle value profile

theorem graph_exact_deviation
    {G : EventGraph.Graph Player L}
    [Fintype Player]
    (hwf : G.WF) (hguards : EventGraph.GuardLive G)
    (hlocal : EventGraph.CommitInformationLocal G hwf hguards)
    (hsingle : ∀ (cfg : EventGraph.Config G) who first second,
      EventGraph.ReadyCommitNode G cfg who first →
      EventGraph.ReadyCommitNode G cfg who second → first = second)
    (profile : Profile
      (EventGraph.Strategic.graphModel G hwf hguards).behavioralSignature)
    (who : Player) (replacement : EventGraph.CommitPolicy G who) :
    ∃ sourceReplacement :
        (EventGraph.Strategic.graphModel G hwf hguards).behavioralSignature.Strategy who,
      ((EventGraph.policyGame G hwf hguards).play
        (Profile.update (sig := EventGraph.policySignature G)
          (fun player => EventGraph.CommitPolicy.fromBehavioral hwf hguards player
            (profile player)) who replacement)).map
          (EventGraph.Strategic.policyObserve G) =
        ((EventGraph.behavioralGame G hwf hguards).play
          (Profile.update profile who sourceReplacement)).map
          (EventGraph.Strategic.behavioralObserve G hwf hguards) :=
  EventGraph.Strategic.deviation_law G hwf hguards hlocal hsingle profile who replacement

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

namespace Source

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

end Source

end Vegas.Paper

/-- info: 'Vegas.Paper.source_strategy_support' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_strategy_support

/-- info: 'Vegas.Paper.source_decision_information' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_decision_information

/-- info: 'Vegas.Paper.source_publication_barrier' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_publication_barrier

/-- info: 'Vegas.Paper.source_decision_roundtrip' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_decision_roundtrip

/-- info: 'Vegas.Paper.graph_decision_roundtrip' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.graph_decision_roundtrip

/-- info: 'Vegas.Paper.schedule_confluence' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.schedule_confluence

/-- info: 'Vegas.Paper.schedule_observation_confluence' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.schedule_observation_confluence

/-- info: 'Vegas.Paper.execution_diamond' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.execution_diamond

/-- info: 'Vegas.Paper.commit_reveal_barrier' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.commit_reveal_barrier

/-- info: 'Vegas.Paper.ready_reveal_fence' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.ready_reveal_fence

/-- info: 'Vegas.Paper.Source.committed_binding_accounted' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.committed_binding_accounted

/-- info: 'Vegas.Paper.Source.initial_binding_accounted' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.initial_binding_accounted

/-- info: 'Vegas.Paper.Source.binding_resolutions_nodup' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.binding_resolutions_nodup

/-- info: 'Vegas.Paper.sealed_rule_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sealed_rule_count

/-- info: 'Vegas.Paper.sealed_source_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sealed_source_prefix

/-- info: 'Vegas.Paper.sealed_policy_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sealed_policy_prefix

/-- info: 'Vegas.Paper.sealed_cleartext_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sealed_cleartext_rejected

/-- info: 'Vegas.Paper.nullable_quit_is_legal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.nullable_quit_is_legal

/-- info: 'Vegas.Paper.sealed_opening_prerequisites' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sealed_opening_prerequisites

/-- info: 'Vegas.Paper.sealed_opening_barrier' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sealed_opening_barrier

/-- info: 'Vegas.Paper.selective_quitting_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.selective_quitting_bound

/-- info: 'Vegas.Paper.sealed_disclosure_utility_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sealed_disclosure_utility_bound

/-- info: 'Vegas.Paper.utility_approximate_nash_preservation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.utility_approximate_nash_preservation

/-- info: 'Vegas.Paper.sealed_nash_preservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sealed_nash_preservation

/-- info: 'Vegas.Paper.sealed_quit_dominance_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sealed_quit_dominance_transfer

/-- info: 'Vegas.Paper.graph_approximate_nash_preservation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.graph_approximate_nash_preservation

/-- info: 'Vegas.Paper.graph_nash_preservation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.graph_nash_preservation

/-- info: 'Vegas.Paper.graph_exact_deviation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.graph_exact_deviation
