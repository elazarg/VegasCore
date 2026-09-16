/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ContinuationPolicy
import Vegas.Pending.PrefixComposition

/-! # Residual outcome laws at actual runtime cursors

The continuation is defined only for executions whose application follows the
compiled graph. The witness recovers the typed residual graph; uniqueness of
graph prefixes makes the result independent of how that witness was proved.
No value is assigned to an off-graph execution.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- The honest residual outcome law at a graph-following native execution.
Preparation and disclosure caches have the same compiled-policy interpretation
as in `continuation`; this is not an extraction of arbitrary players' markers. -/
def continuationAt (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (profile : BehavioralProfile whole)
    (histories : Player → List (Entry runtime)) :
    (state : State Player L Δ) → state.Follows whole 0 → FinDist (VEnv L Δ)
  | .running suffix ideal values bindings candidates site clock enteredAt, follows =>
      let walk := Classical.choice (State.prefix_of_running_follows whole suffix
        ideal values bindings candidates site clock enteredAt follows)
      continuation runtime suffix (walk.profileTail profile) site ideal
        (fun who => projectLogicalHistory who (observe who ideal)
          (histories who) whole 0 site) histories

/-- A typed cursor exposes the residual law without any choice of prefix proof. -/
theorem continuationAt_running (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (profile : BehavioralProfile whole)
    (execution : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows whole 0)
    (suffix : Graph Player L Γ Δ) (site : Nat) (walk : Prefix Δ whole suffix site)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat)
    (atCursor : execution.native.application =
      .running suffix ideal values bindings candidates site clock enteredAt) :
    continuationAt runtime whole profile execution.principalHistory
        execution.native.application follows =
      continuation runtime suffix (walk.profileTail profile) site ideal
        (fun who => projectLogicalHistory who (observe who ideal)
          (execution.principalHistory who) whole 0 site) execution.principalHistory := by
  generalize stateEq : execution.native.application = state at follows ⊢
  have same : state = .running suffix ideal values bindings candidates site clock enteredAt :=
    stateEq.symm.trans atCursor
  clear stateEq atCursor
  subst state
  simp only [continuationAt]
  congr 2
  exact Subsingleton.elim _ walk

/-- At initialization the residual law is the graph's ordinary execution law. -/
theorem continuationAt_initial (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (profile : BehavioralProfile whole)
    (input : VEnv L Γ₀) :
    continuationAt runtime whole profile (fun _ => []) (State.initial whole input)
        (State.initial_follows whole input) = Graph.run whole profile input := by
  have atInitial := runtime.continuationAt_running whole profile
    (MessageApplication.PolicyExecution.initial runtime.application
      (MessageApplication.State.initial runtime.application (State.initial whole input)))
    (State.initial_follows whole input) whole 0 (.refl whole)
    input _ _ _ 0 0 rfl
  change continuationAt runtime whole profile (fun _ => []) (State.initial whole input) _ =
    continuation runtime whole profile 0 input
      (fun who => projectLogicalHistory who (observe who input) [] whole 0 0) (fun _ => [])
    at atInitial
  have empty : (fun who => projectLogicalHistory (runtime := runtime) who
      (observe who input) [] whole 0 0) = fun _ => [] := by
    funext who
    cases whole <;> rfl
  rw [empty] at atInitial
  exact atInitial.trans (runtime.continuation_initial_eq_run whole profile input)

/-- At a completed execution the residual law is its actual ideal outcome. -/
theorem continuationAt_terminal (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (profile : BehavioralProfile whole)
    (histories : Player → List (Entry runtime)) (state : State Player L Δ)
    (follows : state.Follows whole 0) (output : VEnv L Δ)
    (completed : state.outcome? = some output) :
    continuationAt runtime whole profile histories state follows = FinDist.pure output := by
  cases state with
  | running suffix ideal values bindings candidates site clock enteredAt =>
      cases suffix <;> simp only [State.outcome?] at completed <;> cases completed
      rfl

/-- One compiled player's actual invocation preserves the residual outcome
law in expectation. Only that player's policy is restricted; the other policies
are not invoked by this step. The continuation is read at each actual successor
state, rather than at a caller-supplied residual graph. -/
theorem continuationAt_compiled_player_invoke (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (profile : BehavioralProfile whole)
    (execution : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows whole 0)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy) (actor : Player)
    (compiled : players actor = runtime.compilePlayerPolicy whole actor (profile actor)) :
    continuationAt runtime whole profile execution.principalHistory
        execution.native.application follows =
      (runtime.application.invoke players environment execution (.player actor)).bindOnSupport
        fun after supported => continuationAt runtime whole profile after.principalHistory
          after.native.application
          (runtime.invoke_follows whole 0 players environment (.player actor)
            execution after follows supported) := by
  obtain ⟨target, suffix, site, ideal, values, bindings, candidates, clock, enteredAt,
      walk, atCursor⟩ := (show execution.native.application.Follows whole 0 from follows)
  simp only [Nat.zero_add] at atCursor
  rw [runtime.continuationAt_running whole profile execution follows suffix site walk
    ideal values bindings candidates clock enteredAt atCursor]
  rw [runtime.continuation_compiled_player_invoke whole profile suffix site walk
    ideal values bindings candidates clock enteredAt execution atCursor
    players environment actor compiled]
  symm
  apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
  intro after supported
  have stepSupport := supported
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at stepSupport
  obtain ⟨command, _commandMem, stepMem⟩ := stepSupport
  have phase := runtime.playerStep_phase actor execution after command stepMem
  rw [atCursor] at phase
  have runMem : after ∈ (runtime.application.runPolicies players environment
      [.player actor] execution).support := by
    simpa [MessageApplication.runPolicies] using supported
  obtain ⟨candidates', clock', enteredAt', atNext⟩ :=
    runtime.runPolicies_running_eq_of_phase_eq suffix ideal values bindings candidates
      site clock enteredAt players environment [.player actor] execution after
      atCursor runMem phase
  exact runtime.continuationAt_running whole profile after _ suffix site walk
    ideal values bindings candidates' clock' enteredAt' atNext

/-- A wire invocation preserves the residual law if each accepted pending
message preserves it. Submission provenance and typed acceptance are obligations
of the compiler-specific caller; delivery and rejected inclusion are handled
uniformly here. -/
theorem continuationAt_wire (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (profile : BehavioralProfile whole)
    (execution : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows whole 0)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (acceptedLaw : ∀ id message next, execution.native.pool.lookup id = some message →
      ∀ accepted : runtime.handle execution.native.application message = some next,
        runtime.continuationAt whole profile execution.principalHistory next
          (runtime.handle_follows whole 0 execution.native.application next message
            follows accepted) =
        runtime.continuationAt whole profile execution.principalHistory
          execution.native.application follows) :
    runtime.continuationAt whole profile execution.principalHistory
        execution.native.application follows =
      (runtime.application.invoke players (runtime.application.wireEnvironment wire)
        execution .environment).bindOnSupport fun after supported =>
          runtime.continuationAt whole profile after.principalHistory after.native.application
            (runtime.invoke_follows whole 0 players (runtime.application.wireEnvironment wire)
              .environment execution after follows supported) := by
  symm
  apply (FinDist.bindOnSupport_eq_bind_of_eq_on_support
    (g := fun _ => runtime.continuationAt whole profile execution.principalHistory
      execution.native.application follows) ?_).trans (FinDist.bind_const _ _)
  intro after supported
  have afterFollows := runtime.invoke_follows whole 0 players
    (runtime.application.wireEnvironment wire) .environment execution after follows supported
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at supported
  obtain ⟨command, commandMem, stepMem⟩ := supported
  simp only [MessageApplication.wireEnvironment, FinDist.support_map, Set.mem_image] at commandMem
  obtain ⟨wireCommand, _, rfl⟩ := commandMem
  have histories := runtime.application.environmentStep_principalHistory execution
    (wireCommand.toEnvironmentCommand runtime.application) after stepMem
  have transport (state : State Player L Δ) (valid : state.Follows whole 0)
      (same : after.native.application = state) :
      runtime.continuationAt whole profile after.principalHistory after.native.application
          afterFollows = runtime.continuationAt whole profile execution.principalHistory
            state valid := by
    exact congrArg₂
      (fun histories (state : { state : State Player L Δ // state.Follows whole 0 }) =>
        runtime.continuationAt whole profile histories state.val state.property)
      histories (show (⟨after.native.application, afterFollows⟩ :
        { state : State Player L Δ // state.Follows whole 0 }) = ⟨state, valid⟩ from
          Subtype.ext same)
  have nativeMem : after.native ∈ ((runtime.application.environmentPolicyStep execution
      (wireCommand.toEnvironmentCommand runtime.application)).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨after, stepMem, rfl⟩
  rw [runtime.application.environmentStep_native] at nativeMem
  cases wireCommand with
  | deliver observer id | wait =>
      simp only [WireCommand.toEnvironmentCommand,
        MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at nativeMem
      apply transport execution.native.application follows
      simpa only using
        congrArg (fun state : runtime.application.State => state.application) nativeMem
  | «include» id =>
      simp only [WireCommand.toEnvironmentCommand,
        MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at nativeMem
      cases lookup : execution.native.pool.lookup id with
      | none =>
          rw [runtime.application.includePending_missing execution.native id lookup] at nativeMem
          exact transport execution.native.application follows
            (congrArg (fun state => state.application) nativeMem)
      | some message =>
          cases handled : runtime.handle execution.native.application message with
          | none =>
              rw [runtime.application.includePending_reject execution.native id message
                lookup handled] at nativeMem
              apply transport execution.native.application follows
              exact congrArg (fun state => state.application) nativeMem
          | some next =>
              rw [runtime.application.includePending_accept execution.native id message next
                lookup handled] at nativeMem
              have nextFollows := runtime.handle_follows whole 0 execution.native.application
                next message follows handled
              exact (transport next nextFollows
                (congrArg (fun state => state.application) nativeMem)).trans
                  (acceptedLaw id message next lookup handled)

/-- Traffic which leaves the application unchanged also leaves its residual
law unchanged. This applies, in particular, while the graph is waiting for an
exogenous sample or has returned; it imposes no secrecy requirement on delivery. -/
theorem continuationAt_wire_of_handle_stutter (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (profile : BehavioralProfile whole)
    (execution : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows whole 0)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (stutters : ∀ message next, runtime.handle execution.native.application message = some next →
      next = execution.native.application) :
    runtime.continuationAt whole profile execution.principalHistory
        execution.native.application follows =
      (runtime.application.invoke players (runtime.application.wireEnvironment wire)
        execution .environment).bindOnSupport fun after supported =>
          runtime.continuationAt whole profile after.principalHistory after.native.application
            (runtime.invoke_follows whole 0 players (runtime.application.wireEnvironment wire)
              .environment execution after follows supported) := by
  apply runtime.continuationAt_wire whole profile execution follows players wire
  intro id message next _lookup accepted
  exact congrArg
    (fun state : { state : State Player L Δ // state.Follows whole 0 } =>
      runtime.continuationAt whole profile execution.principalHistory state.val state.property)
    (show (⟨next, runtime.handle_follows whole 0 execution.native.application next message
      follows accepted⟩ : { state : State Player L Δ // state.Follows whole 0 }) =
        ⟨execution.native.application, follows⟩ from Subtype.ext (stutters message next accepted))

end Vegas.GraphRuntime
