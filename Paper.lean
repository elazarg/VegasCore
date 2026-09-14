/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheoryExtensions.Core.MixtureSimulation
import GameTheoryExtensions.Core.UtilitySimulation
import Interaction.SealedTimeoutDisclosure
import Interaction.MessageApplicationTraceLikelihood
import Vegas.Language.Nullable
import Vegas.Compile.SealedCompiler
import Vegas.Compile.SealedPolicy
import Vegas.Compile.SealedResolutionPolicy
import Vegas.Compile.SealedTermination
import Vegas.Compile.SealedResolutionReadBound
import Vegas.Compile.SealedSourceExtraction
import Vegas.Compile.SealedSourceRealization
import Vegas.Compile.SealedSourceAssignment
import Vegas.Compile.SealedSourceRestriction
import Vegas.Compile.SealedSourceCylinder
import Vegas.Compile.SealedNativeLikelihood
import Vegas.Compile.SealedRandomizedCoupling
import Vegas.Compile.SealedRoundCoupling
import Vegas.Compile.SealedResolutionCylinder
import Vegas.Compile.SourceLaw
import Vegas.Core.AccountingIntegrity
import Vegas.Core.SourceLikelihood
import Vegas.Core.SourceRestriction
import Vegas.EventGraph.Confluence
import Vegas.EventGraph.Fence
import Vegas.EventGraph.SourceOrder
import Vegas.Compile.SealedTimeoutRefinement
import Vegas.EventGraph.Strategic
import Vegas.Game.SealedMessages
import Vegas.Game.SealedRelease
import Vegas.Game.SealedStrategic
import Vegas.Game.SourceGraph

/-! # Paper theorem audit

This file is deliberately a thin audit surface. Every closed statement below
delegates directly to a theorem in the active source, graph, or sealed-message
tower. Source-to-declared-read-graph strategic preservation uses a concrete
compiler simulation. Pending-message preservation still uses an explicit
`StrategicCertificate`: the runtime must provide the honest law and the
finite-mixture law for its considered unilateral deviations.

The fixed-response source/native prefix law through first timeout is checked.
The full pending-message backtranslation for the concrete policy runtime is an open
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

/-- Source execution retains the conditional probability of every draw,
including samples and choices depending on earlier observations. -/
theorem source_point_probability {Γ : VCtx Player L} (prog : VegasCore Player L Γ)
    (profile : SourceBehavioralProfile prog) (env : VEnv L Γ)
    (final : VEnv L (sourceTerminalCtx prog)) :
    (denoteSource prog profile env).prob final = (sourcePointFactors prog profile env final).prod :=
  denoteSource_prob_eq_prod prog profile env final

/-- A normalized source execution with selected legal choices fixed computes
the original event probability by likelihood weighting. -/
theorem source_restriction_probability {Γ : VCtx Player L} (prog : VegasCore Player L Γ)
    (profile : SourceBehavioralProfile prog) (restriction : SourceChoiceRestriction prog)
    (env : VEnv L Γ) :
    (denoteSource prog profile env).probOf {final | restriction.Allows env final} =
      (denoteSource prog (restriction.apply profile) env).expect
        (restriction.weight profile env) :=
  denoteSource_restriction_probability prog profile restriction env

/-- The source summation step. Instantiating its likelihood-constancy premise
with pending-message replay is a separate compiler obligation. -/
theorem source_restriction_probability_of_constant {Γ : VCtx Player L}
    (prog : VegasCore Player L Γ) (profile : SourceBehavioralProfile prog)
    (restriction : SourceChoiceRestriction prog) (env : VEnv L Γ) (mass : ℝ)
    (hconstant : ∀ final ∈ (denoteSource prog (restriction.apply profile) env).support,
      restriction.weight profile env final = mass) :
    (denoteSource prog profile env).probOf {final | restriction.Allows env final} = mass :=
  denoteSource_restriction_probability_of_constant prog profile restriction env mass hconstant

/-- Exact native prefix probabilities, before any compiler-specific
identification with source cylinder masses. -/
theorem native_prefix_probability (app : MessageApplication Player)
    (players : Player → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (release : app.PolicyExecution → Bool)
    (schedule : List (@MessageApplication.Invocation Player)) (initial : app.PolicyExecution)
    (trace : app.PolicyTrace) :
    ((app.tracePolicies players environment schedule initial).map
      (MessageApplication.PolicyTrace.prefixThrough release)).prob trace =
        (app.stoppedPointFactors players environment release schedule initial trace).prod :=
  app.tracePolicies_prefixThrough_prob_eq_prod players environment release schedule initial trace

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

/-- The source-policy implementation never publishes a cleartext commitment. -/
theorem compiled_policy_no_cleartext
    {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
    (compilation : SealedCompilation source ty) (who : Player)
    (policy : SourceBehavioralPolicy source.core.prog who)
    (history : List (compilation.program.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (compilation.program.messageApplication (Value := L.Val ty)).View)
    (node : Nat) (value : L.Val ty) :
    .submit (.cleartext node value) ∉
      (compilation.compilePolicy who policy history view).support :=
  compilation.supported.playerPolicy_no_cleartext who _ history view node value

/-- The compiled source strategy checks the barrier before publishing an opening. -/
theorem compiled_policy_opening_ready
    {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
    (compilation : SealedCompilation source ty) (who : Player)
    (policy : SourceBehavioralPolicy source.core.prog who)
    (history : List (compilation.program.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (compilation.program.messageApplication (Value := L.Val ty)).View)
    (node : Nat) (handle : CommitmentHandle Player Nat) (value : L.Val ty)
    (hsubmit : .submit (.opening node handle value) ∈
      (compilation.compilePolicy who policy history view).support) :
    compilation.program.openingReady view.application who node = true :=
  compilation.supported.playerPolicy_opening_ready who _ history view node handle value hsubmit

/-- Deadline metadata has no effect on the compiled policy before timeout. -/
theorem compiled_resolving_policy_no_timeout
    {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (who : Player) (policy : SourceBehavioralPolicy source.core.prog who)
    (history : List
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry)
    (view : (compilation.supported.resolvingRuntime nullValue window).messageApplication.View)
    (htimeouts : view.application.timeouts = []) :
    compilation.compileResolvingPolicy nullValue window who policy history view =
      compilation.compilePolicy who policy
        ((compilation.supported.resolvingRuntime nullValue window).eventHistory history)
        ((compilation.supported.resolvingRuntime nullValue window).eventView view) :=
  compilation.supported.resolvingPolicy_no_timeout nullValue window who _ history view htimeouts

/-- Continuing after timeout retains sealed commitment submissions. -/
theorem compiled_resolving_policy_no_cleartext
    {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (who : Player) (policy : SourceBehavioralPolicy source.core.prog who)
    (history : List
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry)
    (view : (compilation.supported.resolvingRuntime nullValue window).messageApplication.View)
    (node : Nat) (value : L.Val ty) :
    .submit (.cleartext node value) ∉
      (compilation.compileResolvingPolicy nullValue window who policy history view).support :=
  compilation.supported.resolvingPolicy_no_cleartext nullValue window who _ history view node value

/-- Every compiled resolving runtime terminates within
`nodeCount * (window + 1)` rounds, for arbitrary player and wire policies. -/
theorem compiled_resolution_terminates
    {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (principals : List Player) (serviceSlots : Nat)
    (players : Player →
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (environment :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.WirePolicy)
    (next :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hnext : next ∈
      ((compilation.supported.resolvingRuntime nullValue window).runRounds
        principals serviceSlots players environment
        ((ToEventGraph.compile source.core).graph.nodeCount * (window + 1))
        (MessageApplication.PolicyExecution.initial _
          (MessageApplication.State.initial _
            (compilation.supported.resolvingRuntime nullValue window).initial))).support) :
    (compilation.supported.resolvingRuntime nullValue window).complete
      next.native.application.visible = true :=
  compilation.resolvingRuntime_runRounds_complete nullValue window principals serviceSlots
    players environment next hnext

/-- Whole-prefix registration hiding with randomized native players and
full-pool environment policies. Source-kernel coupling is a separate obligation. -/
theorem pending_binding_read_bound
    {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
    (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (focal : Player) (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard)
    (leftValues rightValues : Fin G.nodeCount → L.Val ty)
    (hvalues : ∀ who, who ≠ focal → ∀ node,
      supported.knownBefore focal decision (who, node.val) → leftValues node = rightValues node)
    (deviator : (supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (environment :
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player)) :
    supported.resolvingBindingLaw nullValue window leftValues focal decision
        deviator environment schedule =
      supported.resolvingBindingLaw nullValue window rightValues focal decision
        deviator environment schedule :=
  supported.resolvingBindingLaw_read_bound nullValue window focal decision guard
    hdecision leftValues rightValues hvalues deviator environment schedule

/-- Replay probabilities are exact honest-registration cylinder masses,
including stopped prefixes. This does not yet identify the assignment law
with the original state-dependent source kernels. -/
theorem pending_replay_cylinder
    {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
    (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (focal : Player)
    (deviator :
      List (supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry →
      (supported.resolvingRuntime nullValue window).messageApplication.View →
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerCommand)
    (environment :
      List (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentEntry →
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentObservation →
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicyCommand)
    (schedule : List (@MessageApplication.Invocation Player))
    (release :
      (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution → Bool)
    (assignments : FinDist (Fin G.nodeCount → L.Val ty))
    (reference : Fin G.nodeCount → L.Val ty) :
    (assignments.map (fun values =>
      (supported.resolvingReplay nullValue window values focal
        deviator environment schedule).prefixThrough release)).prob
        (supported.resolvingReplay nullValue window reference focal
          deviator environment schedule |>.prefixThrough release) =
      assignments.probOf {values | ∀ owner (node : Fin G.nodeCount) (value : L.Val ty),
        owner ≠ focal →
          (.privateCommand owner ⟨(node.val, value)⟩ :
            (supported.resolvingRuntime nullValue window).messageApplication.Action) ∈
              (supported.resolvingReplay nullValue window reference focal
                deviator environment schedule |>.prefixThrough release).last.nativeTrace →
                  reference node = values node} :=
  supported.resolvingReplay_cylinder_probability nullValue window focal deviator environment
    schedule release assignments reference

/-- Fixed native responses give a legal written-source policy with the same
local registration law at matching source disclosure inputs. -/
theorem pending_source_choice_law
    {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (focal : Player)
    (deviator :
      List
        (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry →
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.View →
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerCommand)
    (environment :
      List (MessageApplication.EnvironmentEntry
        (compilation.supported.resolvingRuntime nullValue window).messageApplication) →
      MessageApplication.EnvironmentObservation
        (compilation.supported.resolvingRuntime nullValue window).messageApplication →
      MessageApplication.EnvironmentPolicyCommand
        (compilation.supported.resolvingRuntime nullValue window).messageApplication)
    (schedule : List (@MessageApplication.Invocation Player)) (fallback : L.Val ty)
    (values : Fin (ToEventGraph.compile source.core).graph.nodeCount → L.Val ty)
    (decision : Fin (ToEventGraph.compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hdecision : ((ToEventGraph.compile source.core).graph.nodeRow decision).sem =
      .commit focal guard)
    (reads : ReadEnv L guard.choiceReads)
    (hinputs : compilation.disclosureInputs focal decision guard hdecision reads =
      fun coordinate => values coordinate.val) :
    (ToEventGraph.compileSourcePolicy source.core.prog source.core.fresh
      (ToEventGraph.BuildState.fromInitial
        (ToEventGraph.initialState source.core.Γ source.core.env source.core.wctx))
      rfl focal
      (compilation.extractedSourcePolicy nullValue window focal deviator environment schedule
        fallback) decision guard hdecision reads).map
          (fun value => cast
            (congrArg L.Val (compilation.supported.commitType decision focal guard hdecision))
            value.1) =
      FinDist.pure ((compilation.supported.resolvingBinding nullValue window values focal
        deviator environment schedule decision).getD fallback) :=
  compilation.extractedSourcePolicy_law nullValue window focal deviator environment schedule
    fallback values decision guard hdecision reads hinputs

/-- Own command memory reconstructs private registered values throughout
arbitrary resolving-runtime play, including execution after timeout. -/
theorem pending_registration_memory {Value : Type} [DecidableEq Value]
    (runtime : SealedResolution Player Value)
    (players : Player → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (final : runtime.messageApplication.PolicyExecution)
    (hfinal : final ∈ (runtime.messageApplication.runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial _
        (MessageApplication.State.initial _ runtime.initial))).support) :
    SealedResolution.RegistrationMemory runtime final :=
  SealedResolution.RegistrationMemory.runPolicies players environment schedule _ final
    SealedResolution.RegistrationMemory.initial hfinal

section SourceRealization

variable [Fintype Player] {source : WFProgram Player L} {ty : L.Ty}
variable [DecidableEq (L.Val ty)] (compilation : SealedCompilation source ty)
variable (nullValue : L.Val ty) (window : Nat) (focal : Player)
variable (deviator :
  List (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry →
  (compilation.supported.resolvingRuntime nullValue window).messageApplication.View →
  (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerCommand)
variable (environment :
  List
    (compilation.supported.resolvingRuntime nullValue window).messageApplication.EnvironmentEntry →
  MessageApplication.EnvironmentObservation
    (compilation.supported.resolvingRuntime nullValue window).messageApplication →
  MessageApplication.EnvironmentPolicyCommand
    (compilation.supported.resolvingRuntime nullValue window).messageApplication)
variable (schedule : List (@MessageApplication.Invocation Player)) (fallback : L.Val ty)

/-- The source side of the fixed-response coupling is exactly written-source
execution with the extracted policy and unchanged opponents. -/
theorem pending_extracted_source_law (profile : SourceBehavioralProfile source.core.prog) :
    (compilation.extractedSourceRun nullValue window focal deviator environment schedule
      fallback profile).map (ToEventGraph.observeSourceOutcome source.core) =
      (denoteSource source.core.prog
        (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
          (compilation.extractedSourcePolicy nullValue window focal deviator environment schedule
            fallback)) source.core.env).map some :=
  compilation.extractedSourceRun_source nullValue window focal deviator environment schedule
    fallback profile

/-- Every source-owned registration at the common first-timeout snapshot
is retained by the complete source realization, for every player. -/
theorem pending_locked_source_choices (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (ToEventGraph.compile source.core).graph)
    (hcfg : cfg ∈ (compilation.extractedSourceRun nullValue window focal deviator environment
      schedule fallback profile).support)
    (owner : Player)
    (decision : Fin (ToEventGraph.compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hdecision : ((ToEventGraph.compile source.core).graph.nodeRow decision).sem =
      .commit owner guard)
    (value : L.Val ty)
    (hregistered :
      (compilation.supported.resolvingStop nullValue window (cfg.1.nodeValues fallback) focal
        deviator environment schedule).native.application.service.lookup (owner, decision.val) =
          some value) :
    cfg.1.nodeValues fallback decision = value :=
  compilation.extractedSourceRun_registered nullValue window focal deviator environment schedule
    fallback profile cfg hcfg owner decision guard hdecision value hregistered

/-- Every included opening in a pre-timeout replay prefix has its complete
source value. This remains a value theorem, not a native probability law. -/
theorem pending_source_openings (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (ToEventGraph.compile source.core).graph)
    (hcfg : cfg ∈ (compilation.extractedSourceRun nullValue window focal deviator environment
      schedule fallback profile).support)
    (release :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
        Bool) :
    let stopped := ((compilation.supported.resolvingReplay nullValue window
      (cfg.1.nodeValues fallback) focal deviator environment schedule).prefixThrough
        (fun execution : (compilation.supported.resolvingRuntime
            nullValue window).messageApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)).firstRelease release
    stopped.native.application.visible.timeouts = [] → ∀ node value,
      SealedProgram.Event.opened node value ∈ stopped.native.application.visible.events →
      cfg.1.store ((ToEventGraph.compile source.core).graph.nodeTarget node) =
        some (⟨ty, value⟩ : TypedValue L) :=
  compilation.extractedSourceRun_opened nullValue window focal deviator environment schedule
    fallback profile cfg hcfg release

/-- Every assignment supplies the selected source kernel's exact inputs at
fresh honest replay registrations, including assignments of probability zero.
The native marginal law remains separate. -/
theorem pending_honest_registration_kernel
    (values : Fin (ToEventGraph.compile source.core).graph.nodeCount → L.Val ty)
    (release :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
        Bool) :
    let cfg := compilation.assignmentRealization nullValue window focal deviator environment
      schedule fallback values
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let stopped := ((compilation.supported.resolvingReplay nullValue window values focal
      deviator environment schedule).prefixThrough
        (fun execution : runtime.messageApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)).firstRelease release
    stopped.native.application.visible.timeouts = [] →
    ∀ who, who ≠ focal → ∀ slot value,
      .privateCommand ⟨(slot, value)⟩ ∈
        (compilation.supported.resolvingValuePlayers nullValue window values focal
          (fun history view => FinDist.pure (deviator history view)) who
          (stopped.principalHistory who)
          (MessageApplication.State.observe runtime.messageApplication
            stopped.native who)).support →
      ∀ policy : SourceBehavioralPolicy source.core.prog who,
      ∃ (node : Fin (ToEventGraph.compile source.core).graph.nodeCount) (guard : EventGuard L)
        (hsem : ((ToEventGraph.compile source.core).graph.nodeRow node).sem = .commit who guard)
        (reads : ReadEnv L guard.choiceReads),
        slot = node.val ∧ stopped.native.application.service.lookup (who, node.val) = none ∧
        ReadEnv.ofStore? cfg.1.store guard.choiceReads = some reads ∧
        compilation.compileResolvingPolicy nullValue window who policy
          (stopped.principalHistory who)
          (MessageApplication.State.observe runtime.messageApplication stopped.native who) =
          ((ToEventGraph.compileSourcePolicy source.core.prog source.core.fresh
            (ToEventGraph.BuildState.fromInitial (ToEventGraph.initialState
              source.core.Γ source.core.env source.core.wctx))
            rfl who policy) node guard hsem reads).map (fun choice =>
              .privateCommand ⟨(node.val, cast (congrArg L.Val
                (compilation.supported.commitType node who guard hsem)) choice.1)⟩) :=
  compilation.assignmentRealization_registration_kernel nullValue window focal deviator environment
    schedule fallback values release

/-- Fixing the honest registrations of a native prefix produces exactly the
ordinary restricted source law, with the extracted focal policy unchanged. -/
theorem pending_reference_source_law
    (service : IdealCommitments Player Nat (L.Val ty))
    (profile : SourceBehavioralProfile source.core.prog) :
    (compilation.extractedSourceRun nullValue window focal deviator environment schedule fallback
      ((compilation.registrationRestriction focal service).apply profile)).map
        (ToEventGraph.observeSourceOutcome source.core) =
      (denoteSource source.core.prog
        ((compilation.registrationRestriction focal service).apply
          (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
            (compilation.extractedSourcePolicy nullValue window focal deviator environment
              schedule fallback))) source.core.env).map some :=
  compilation.restrictedSourceRun_source nullValue window focal deviator environment schedule
    fallback service profile

/-- Every supported reference source execution reproduces the recorded native
prefix, including pending messages and histories. This reference law is for
probability calculation; it is not the coupling's original source marginal. -/
theorem pending_reference_replay_prefix
    (reference : Fin (ToEventGraph.compile source.core).graph.nodeCount → L.Val ty)
    (release :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
        Bool)
    (profile : SourceBehavioralProfile source.core.prog) :
    let stopped := (compilation.supported.resolvingReplay nullValue window reference focal
      deviator environment schedule).prefixThrough release
    ∀ cfg ∈ (compilation.extractedSourceRun nullValue window focal deviator environment schedule
      fallback ((compilation.registrationRestriction focal
        stopped.last.native.application.service).apply profile)).support,
      (compilation.supported.resolvingReplay nullValue window (cfg.1.nodeValues fallback) focal
        deviator environment schedule).prefixThrough release = stopped :=
  compilation.restrictedSourceRun_replay_prefix nullValue window focal deviator environment
    schedule fallback reference release profile

/-- Exact source-side mass of a stopped pending-message replay. The reference
law performs the cylinder sum without independence or a positive-mass premise;
identification with the original native execution law remains separate. -/
theorem pending_source_cylinder_likelihood
    (reference : Fin (ToEventGraph.compile source.core).graph.nodeCount → L.Val ty)
    (release :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
        Bool)
    (profile : SourceBehavioralProfile source.core.prog) :
    let stopped := (compilation.supported.resolvingReplay nullValue window reference focal
      deviator environment schedule).prefixThrough release
    let original : SourceBehavioralProfile source.core.prog :=
      Profile.update (sig := sourceGameSignature source.core.prog) profile focal
        (compilation.extractedSourcePolicy nullValue window focal deviator environment schedule
          fallback)
    let restriction := compilation.registrationRestriction focal
      stopped.last.native.application.service
    ((compilation.extractedSourceRun nullValue window focal deviator environment schedule fallback
      profile).map fun cfg =>
        (compilation.supported.resolvingReplay nullValue window (cfg.1.nodeValues fallback) focal
          deviator environment schedule).prefixThrough release).prob stopped =
      (denoteSource source.core.prog (restriction.apply original) source.core.env).expect
        (restriction.weight original source.core.env) :=
  compilation.extractedSourceRun_replay_likelihood nullValue window focal deviator environment
    schedule fallback reference release profile

/-- The source prefix probability is a product of original native registration
probabilities at fixed replay checkpoints. -/
theorem pending_source_prefix_product
    (reference : Fin (ToEventGraph.compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let stop := fun execution : runtime.messageApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let stopped := (compilation.supported.resolvingReplay nullValue window reference focal
      deviator environment schedule).prefixThrough stop
    ((compilation.extractedSourceRun nullValue window focal deviator environment schedule fallback
      profile).map fun cfg =>
        (compilation.supported.resolvingReplay nullValue window (cfg.1.nodeValues fallback) focal
          deviator environment schedule).prefixThrough stop).prob stopped =
      (source.core.prog.decisionPositions.map fun slot =>
        compilation.replayRegistrationFactor nullValue window focal deviator environment schedule
          reference profile slot.1 slot.2).prod :=
  compilation.extractedSourceRun_replay_prob_eq_product nullValue window focal deviator environment
    schedule fallback reference profile

/-- Exact native prefix law through the first timeout, from the ordinary source
run against the extracted focal policy and unchanged opponents. Focal and
environment responses are fixed functions; the utility comparison for informed
quitting is a separate obligation. -/
theorem pending_source_native_prefix_law (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := Profile.update
      (sig := MessageApplication.policySignature Player runtime.messageApplication)
      (fun who => compilation.compileResolvingPolicy nullValue window who (profile who)) focal
      (fun history view => FinDist.pure (deviator history view))
    let stop := fun execution : runtime.messageApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    (compilation.extractedSourceRun nullValue window focal deviator environment schedule fallback
      profile).map (fun cfg =>
        (compilation.supported.resolvingReplay nullValue window (cfg.1.nodeValues fallback) focal
          deviator environment schedule).prefixThrough stop) =
      (runtime.messageApplication.tracePolicies players
        (fun history view => FinDist.pure (environment history view)) schedule
        (MessageApplication.PolicyExecution.initial _
          (MessageApplication.State.initial _ runtime.initial))).map
            (MessageApplication.PolicyTrace.prefixThrough stop) :=
  compilation.extractedSourceRun_native_prefix_law nullValue window focal deviator environment
    schedule fallback profile

/-- Arbitrary randomized focal and environment policies admit a finite mixture
of deterministic-response source/native couplings. Both marginals and the
joint stopped-prefix/full-native-trace law are exact, including the actual timeout
suffix. The focal and environment responses may be correlated in the mixture.
Final outcome equality, termination, and the informed-quitting utility
comparison are not asserted by this marginal-law theorem. Normal completion is
identified separately. -/
theorem pending_randomized_source_coupling
    (profile : SourceBehavioralProfile source.core.prog)
    (replacement :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (randomizedEnvironment :
      (compilation.supported.resolvingRuntime nullValue
        window).messageApplication.EnvironmentPolicy) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := fun who =>
      compilation.compileResolvingPolicy nullValue window who (profile who)
    let initial := MessageApplication.PolicyExecution.initial runtime.messageApplication
      (MessageApplication.State.initial _ runtime.initial)
    let native := runtime.messageApplication.tracePolicies
      (Profile.update (sig := MessageApplication.policySignature Player runtime.messageApplication)
        players focal replacement) randomizedEnvironment schedule initial
    let stop := fun execution : runtime.messageApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let PlayerResponse := List runtime.messageApplication.PlayerEntry →
      runtime.messageApplication.View → runtime.messageApplication.PlayerCommand
    let EnvironmentResponse := List runtime.messageApplication.EnvironmentEntry →
      runtime.messageApplication.EnvironmentObservation →
        runtime.messageApplication.EnvironmentPolicyCommand
    ∃ responsePairs : FinDist (PlayerResponse × EnvironmentResponse),
      (responsePairs.bind fun responses =>
        (compilation.extractedSourceCoupling nullValue window focal responses.1 responses.2
          schedule fallback profile).map (fun pair =>
            ((compilation.supported.resolvingReplay nullValue window (pair.1.1.nodeValues fallback)
              focal responses.1 responses.2 schedule).prefixThrough stop, pair.2))) =
          native.map (fun trace => (trace.prefixThrough stop, trace)) ∧
      ((responsePairs.bind fun responses =>
        compilation.extractedSourceCoupling nullValue window focal responses.1 responses.2
          schedule fallback profile).map
            (fun pair => ToEventGraph.observeSourceOutcome source.core pair.1)) =
        responsePairs.bind (fun responses =>
          (denoteSource source.core.prog
            (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
              (compilation.extractedSourcePolicy nullValue window focal responses.1 responses.2
                schedule fallback)) source.core.env).map some) ∧
      ((responsePairs.bind fun responses =>
        compilation.extractedSourceCoupling nullValue window focal responses.1 responses.2
          schedule fallback profile).map Prod.snd) =
        runtime.messageApplication.tracePolicies
          (Profile.update
            (sig := MessageApplication.policySignature Player runtime.messageApplication)
            players focal replacement) randomizedEnvironment schedule initial :=
  compilation.exists_randomized_source_coupling nullValue window focal randomizedEnvironment
    schedule fallback profile replacement

/-- The explicit source coupling at resolving-round boundaries has the legal
written-source mixture as one marginal and the actual round driver as the
other. This is an execution-law statement, not an outcome or utility claim. -/
theorem pending_randomized_round_source_coupling
    (profile : SourceBehavioralProfile source.core.prog)
    (principals : List Player) (serviceSlots count : Nat)
    (replacement :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (wire :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.WirePolicy) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := fun who =>
      compilation.compileResolvingPolicy nullValue window who (profile who)
    let roundSchedule := Interaction.SealedResolution.roundSchedule
      principals serviceSlots count
    let initial := MessageApplication.PolicyExecution.initial runtime.messageApplication
      (MessageApplication.State.initial _ runtime.initial)
    let PlayerResponse := List runtime.messageApplication.PlayerEntry →
      runtime.messageApplication.View → runtime.messageApplication.PlayerCommand
    let EnvironmentResponse := List runtime.messageApplication.EnvironmentEntry →
      runtime.messageApplication.EnvironmentObservation →
        runtime.messageApplication.EnvironmentPolicyCommand
    ∃ responsePairs : FinDist (PlayerResponse × EnvironmentResponse),
      ((responsePairs.bind fun responses =>
        compilation.extractedRoundSourceCoupling nullValue window principals serviceSlots count
          focal responses.1 responses.2 fallback profile).map
            (fun pair => ToEventGraph.observeSourceOutcome source.core pair.1)) =
        responsePairs.bind (fun responses =>
          (denoteSource source.core.prog
            (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
              (compilation.extractedSourcePolicy nullValue window focal responses.1 responses.2
                roundSchedule fallback)) source.core.env).map some) ∧
      ((responsePairs.bind fun responses =>
        compilation.extractedRoundSourceCoupling nullValue window principals serviceSlots count
          focal responses.1 responses.2 fallback profile).map Prod.snd) =
        runtime.runRounds principals serviceSlots
          (Profile.update
            (sig := MessageApplication.policySignature Player runtime.messageApplication)
            players focal replacement) wire count initial :=
  compilation.exists_randomized_round_source_coupling nullValue window principals serviceSlots
    count focal fallback profile replacement wire

/-- Every normally completed timeout-free round-boundary readout in the
randomized response mixture decodes to its retained source realization. Later
scheduled traffic in the underlying full trace does not alter this result. -/
theorem pending_round_normal_completion
    (profile : SourceBehavioralProfile source.core.prog)
    (principals : List Player) (serviceSlots count : Nat)
    (responsePairs : FinDist
      ((List
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.PlayerEntry →
          (compilation.supported.resolvingRuntime nullValue window).messageApplication.View →
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.PlayerCommand) ×
        (List
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.EnvironmentEntry →
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.EnvironmentObservation →
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.EnvironmentPolicyCommand)))
    (cfg : ReachableConfig (ToEventGraph.compile source.core).graph)
    (selected :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hpair : (cfg, selected) ∈ (responsePairs.bind fun responses =>
      compilation.extractedRoundSourceCoupling nullValue window principals serviceSlots count
        focal responses.1 responses.2 fallback profile).support)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      selected.native.application.visible = true)
    (hclear : selected.native.application.visible.timeouts = []) :
    (ToEventGraph.compile source.core).graph.decodeSealedFrom ty
      selected.native.application.service (Config.initial _)
      selected.native.application.visible.events = some cfg.1 :=
  compilation.mixtureRoundSourceCoupling_decode_of_complete_clear nullValue window principals
    serviceSlots count focal fallback profile responsePairs cfg selected hpair hcomplete hclear

/-- A normally completed pair from any mixture of the constructed couplings
decodes to that exact source realization. This includes the mixture obtained
for an arbitrary randomized unilateral replacement. Completion itself and
source/native agreement after timeout are not assumed to follow from this law. -/
theorem pending_normal_completion
    (profile : SourceBehavioralProfile source.core.prog)
    (responsePairs : FinDist
      ((List
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.PlayerEntry →
          (compilation.supported.resolvingRuntime nullValue window).messageApplication.View →
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.PlayerCommand) ×
        (List
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.EnvironmentEntry →
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.EnvironmentObservation →
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.EnvironmentPolicyCommand)))
    (cfg : ReachableConfig (ToEventGraph.compile source.core).graph)
    (trace :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyTrace)
    (hpair : (cfg, trace) ∈ (responsePairs.bind fun responses =>
      compilation.extractedSourceCoupling nullValue window focal responses.1 responses.2 schedule
        fallback profile).support)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      trace.last.native.application.visible = true)
    (hclear : trace.last.native.application.visible.timeouts = []) :
    (ToEventGraph.compile source.core).graph.decodeSealedFrom ty
      trace.last.native.application.service (Config.initial _)
      trace.last.native.application.visible.events = some cfg.1 :=
  compilation.mixtureSourceCoupling_decode_of_complete_clear nullValue window focal schedule
    fallback profile responsePairs cfg trace hpair hcomplete hclear

/-- Each fresh honest registration before timeout has exactly the original
source decision probabilities at every reference realization's recorded view.
This identifies the individual probability factors used by the prefix law. -/
theorem pending_registration_source_probability
    (reference : Fin (ToEventGraph.compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog)
    (release :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
        Bool) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let tracePrefix := (compilation.supported.resolvingReplay nullValue window reference focal
      deviator environment schedule).prefixThrough (fun execution :
        runtime.messageApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)
    ∀ cfg ∈ (compilation.extractedSourceRun nullValue window focal deviator environment schedule
      fallback ((compilation.registrationRestriction focal
        tracePrefix.last.native.application.service).apply profile)).support,
    let stopped := tracePrefix.firstRelease release
    stopped.native.application.visible.timeouts = [] →
    ∀ who, who ≠ focal → ∀ slot value,
      .privateCommand ⟨(slot, value)⟩ ∈
        (compilation.supported.resolvingValuePlayers nullValue window reference focal
          (fun history view => FinDist.pure (deviator history view)) who
          (stopped.principalHistory who)
          (MessageApplication.State.observe runtime.messageApplication
            stopped.native who)).support →
    ∀ policy : SourceBehavioralPolicy source.core.prog who,
    ∃ final, ToEventGraph.observeSourceOutcome source.core cfg = some final ∧
      ∃ Δ name choiceTy guard, ∃ site :
        SourceDecisionSite who source.core.prog Δ name choiceTy guard,
        site.depth = slot ∧ ∀ chosen,
          (compilation.compileResolvingPolicy nullValue window who policy
            (stopped.principalHistory who)
            (MessageApplication.State.observe runtime.messageApplication stopped.native who)).prob
              (.privateCommand ⟨(slot, chosen)⟩) =
            ((policy site ((site.recorded final).tail.toView who).eraseEnv).map
              (fun choice => (⟨choiceTy, choice.1⟩ : TypedValue L))).prob ⟨ty, chosen⟩ :=
  compilation.restrictedSourceRun_registration_probability nullValue window focal deviator
    environment schedule fallback reference profile release

end SourceRealization

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

theorem source_graph_nash_iff [Fintype Player] (source : WFProgram Player L)
    (value : Option (VEnv L (sourceTerminalCtx source.core.prog)) → Player → ℝ)
    (profile : SourceBehavioralProfile source.core.prog) :
    IsNash (EventGraph.policyGame (ToEventGraph.compile source.core).graph
      (ToEventGraph.compile source.core).graphWF
      (ToEventGraph.compile_guardLive source.core source.legal))
      (euPreference (fun outcome who =>
        value (ToEventGraph.observeSourceOutcome source.core outcome) who))
      (source.sourceGraphSimulation.compileProfile profile) ↔
    IsNash (sourceGameForm source.core.prog source.core.env)
      (euPreference (fun outcome who => value (some outcome) who)) profile :=
  source.source_graph_nash_iff value profile

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

/-- info: 'Vegas.Paper.source_graph_honest_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_graph_honest_law

/-- info: 'Vegas.Paper.source_graph_deviation_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_graph_deviation_law

/-- info: 'Vegas.Paper.source_graph_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_graph_nash_iff

/-- info: 'Vegas.Paper.source_graph_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_graph_approximate_nash_iff

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

/-- info: 'Vegas.Paper.compiled_policy_no_cleartext' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_policy_no_cleartext

/-- info: 'Vegas.Paper.compiled_policy_opening_ready' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_policy_opening_ready

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

/-- info: 'Vegas.Paper.compiled_resolving_policy_no_timeout' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_resolving_policy_no_timeout

/-- info: 'Vegas.Paper.compiled_resolving_policy_no_cleartext' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_resolving_policy_no_cleartext

/-- info: 'Vegas.Paper.compiled_resolution_terminates' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.compiled_resolution_terminates

/-- info: 'Vegas.Paper.pending_binding_read_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_binding_read_bound

/-- info: 'Vegas.Paper.pending_source_choice_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_source_choice_law

/-- info: 'Vegas.Paper.pending_replay_cylinder' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_replay_cylinder

/-- info: 'Vegas.Paper.pending_extracted_source_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_extracted_source_law

/-- info: 'Vegas.Paper.pending_locked_source_choices' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_locked_source_choices

/-- info: 'Vegas.Paper.pending_source_openings' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_source_openings

/-- info: 'Vegas.Paper.pending_registration_memory' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_registration_memory

/-- info: 'Vegas.Paper.pending_honest_registration_kernel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_honest_registration_kernel

/-- info: 'Vegas.Paper.source_point_probability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_point_probability

/-- info: 'Vegas.Paper.native_prefix_probability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.native_prefix_probability

/-- info: 'Vegas.Paper.source_restriction_probability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_restriction_probability

/-- info: 'Vegas.Paper.source_restriction_probability_of_constant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.source_restriction_probability_of_constant

/-- info: 'Vegas.Paper.pending_reference_source_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_reference_source_law

/-- info: 'Vegas.Paper.pending_reference_replay_prefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_reference_replay_prefix

/-- info: 'Vegas.Paper.pending_source_cylinder_likelihood' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_source_cylinder_likelihood

/-- info: 'Vegas.Paper.pending_registration_source_probability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_registration_source_probability

/-- info: 'Vegas.Paper.pending_source_prefix_product' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_source_prefix_product

/-- info: 'Vegas.Paper.pending_source_native_prefix_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_source_native_prefix_law

/-- info: 'Vegas.Paper.pending_randomized_source_coupling' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_randomized_source_coupling

/-- info: 'Vegas.Paper.pending_randomized_round_source_coupling' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_randomized_round_source_coupling

/-- info: 'Vegas.Paper.pending_round_normal_completion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_round_normal_completion

/-- info: 'Vegas.Paper.pending_normal_completion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.pending_normal_completion
