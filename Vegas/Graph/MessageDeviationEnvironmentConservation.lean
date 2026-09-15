/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageDeviationNormalization
import Vegas.Graph.MessageContinuationService

/-! # Environment conservation for deviation continuations -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Δ : VCtx Player L}

/-- A wire invocation preserves the sanitized residual law whenever each
accepted pending message does. Delivery, waiting, missing identifiers, and
rejected inclusions conserve it without further premises. -/
theorem deviationContinuationAt_wire (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (profile : BehavioralProfile whole)
    (focal : Player) (execution : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows whole 0)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (acceptedLaw : ∀ id message next, execution.native.pool.lookup id = some message →
      ∀ accepted : runtime.handle execution.native.application message = some next,
        runtime.deviationContinuationAt whole profile focal execution.principalHistory next
          (runtime.handle_follows whole 0 execution.native.application next message
            follows accepted) =
        runtime.deviationContinuationAt whole profile focal execution.principalHistory
          execution.native.application follows) :
    runtime.deviationContinuationAt whole profile focal execution.principalHistory
        execution.native.application follows =
      (runtime.application.invoke players (runtime.application.wireEnvironment wire)
        execution .environment).bindOnSupport fun after supported =>
          runtime.deviationContinuationAt whole profile focal after.principalHistory
            after.native.application
            (runtime.invoke_follows whole 0 players (runtime.application.wireEnvironment wire)
              .environment execution after follows supported) := by
  symm
  apply (FinDist.bindOnSupport_eq_bind_of_eq_on_support
    (g := fun _ => runtime.deviationContinuationAt whole profile focal
      execution.principalHistory execution.native.application follows) ?_).trans
    (FinDist.bind_const _ _)
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
      runtime.deviationContinuationAt whole profile focal after.principalHistory
          after.native.application afterFollows =
        runtime.deviationContinuationAt whole profile focal execution.principalHistory
          state valid := by
    exact congrArg₂
      (fun histories (state : { state : State Player L Δ // state.Follows whole 0 }) =>
        runtime.deviationContinuationAt whole profile focal histories state.val state.property)
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

/-- A deterministic environment wait preserves the sanitized residual law. -/
theorem deviationContinuationAt_environment_wait (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (profile : BehavioralProfile whole)
    (focal : Player) (execution : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows whole 0)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (waits : environment execution.environmentHistory
      (MessageApplication.State.environmentView runtime.application execution.native) =
        FinDist.pure .wait) :
    runtime.deviationContinuationAt whole profile focal execution.principalHistory
        execution.native.application follows =
      (runtime.application.invoke players environment execution .environment).bindOnSupport
        fun after supported => runtime.deviationContinuationAt whole profile focal
          after.principalHistory after.native.application
          (runtime.invoke_follows whole 0 players environment .environment
            execution after follows supported) := by
  have kernel : runtime.application.invoke players environment execution .environment =
      FinDist.pure { execution with
        environmentHistory := execution.environmentHistory ++
          [⟨MessageApplication.State.environmentView runtime.application execution.native,
            .wait⟩] } := by
    simp only [MessageApplication.invoke, waits, FinDist.pure_bind,
      MessageApplication.environmentPolicyStep, MessageApplication.advance,
      MessageApplication.EnvironmentPolicyCommand.toAction]
  suffices bridge : ∀ (preserved : ∀ after ∈ (runtime.application.invoke players environment
        execution .environment).support, after.native.application.Follows whole 0),
      runtime.deviationContinuationAt whole profile focal execution.principalHistory
          execution.native.application follows =
        (runtime.application.invoke players environment execution .environment).bindOnSupport
          fun after supported => runtime.deviationContinuationAt whole profile focal
            after.principalHistory after.native.application (preserved after supported) from
    bridge (fun after supported => runtime.invoke_follows whole 0 players environment
      .environment execution after follows supported)
  rw [kernel]
  intro preserved
  rw [FinDist.pure_bindOnSupport]

/-- A real tick at a typed sample cursor preserves the sanitized residual law
in expectation. -/
theorem Prefix.deviationContinuationAt_sample_tick
    {Γ : VCtx Player L} (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (profile : BehavioralProfile whole)
    (focal : Player) (independent : IgnoresOwnHistory whole profile focal)
    (site : Nat) (name : VarId) {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (law : PublicDist (L := L) Γ payload)
    (tail : Graph Player L ((name, .pub payload) :: Γ) Δ)
    (walk : Prefix Δ whole (.sample name fresh law tail) site)
    (execution : runtime.application.PolicyExecution)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat)
    (atCursor : execution.native.application =
      .running (.sample name fresh law tail) ideal values bindings candidates site clock enteredAt)
    (follows : execution.native.application.Follows whole 0)
    (agreement : (values : PublicValues Γ) = (PublicValues.ofVEnv ideal : PublicValues Γ))
    (unique : (Γ.map Prod.fst).Nodup)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (tick : environment execution.environmentHistory
      (MessageApplication.State.environmentView runtime.application execution.native) =
        FinDist.pure (.application .tick)) :
    runtime.deviationContinuationAt whole profile focal execution.principalHistory
        execution.native.application follows =
      (runtime.application.invoke players environment execution .environment).bindOnSupport
        fun after supported => runtime.deviationContinuationAt whole profile focal
          after.principalHistory after.native.application
          (runtime.invoke_follows whole 0 players environment .environment
            execution after follows supported) := by
  let advanced : L.Val payload → runtime.application.PolicyExecution := fun value =>
    { execution with
      native := { execution.native with
        application := .running tail (VEnv.cons value ideal) (PublicValues.consPublic value values)
          bindings candidates (site + 1) (clock + 1) (clock + 1) }
      environmentHistory := execution.environmentHistory ++
        [⟨MessageApplication.State.environmentView runtime.application execution.native,
          .application .tick⟩]
      nativeTrace := execution.nativeTrace ++ [.environment .tick] }
  have kernel : runtime.application.invoke players environment execution .environment =
      (law.evalPublic values).map advanced := by
    simp only [MessageApplication.invoke, tick, FinDist.pure_bind,
      MessageApplication.environmentPolicyStep, MessageApplication.advance,
      MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
      FinDist.bind_bind, FinDist.pure_bind]
    change ((runtime.tick execution.native.application).map _).bind _ = _
    rw [atCursor]
    simp only [GraphRuntime.tick, FinDist.bind_map]
    rfl
  suffices bridge : ∀ (preserved : ∀ after ∈ (runtime.application.invoke players environment
        execution .environment).support, after.native.application.Follows whole 0),
      runtime.deviationContinuationAt whole profile focal execution.principalHistory
          execution.native.application follows =
        (runtime.application.invoke players environment execution .environment).bindOnSupport
          fun after supported => runtime.deviationContinuationAt whole profile focal
            after.principalHistory after.native.application (preserved after supported) from
    bridge (fun after supported => runtime.invoke_follows whole 0 players environment
      .environment execution after follows supported)
  rw [kernel]
  intro preserved
  rw [FinDist.bindOnSupport_map]
  rw [runtime.deviationContinuationAt_running whole profile focal execution follows
    (.sample name fresh law tail) site walk ideal values bindings candidates clock enteredAt
    atCursor]
  rw [runtime.continuation_congr_focal_logical _ _ focal
    (walk.policyTail_ignoresOwnHistory profile focal independent) site ideal
    (eraseFocalLogical focal (fun who => projectLogicalHistory who (observe who ideal)
      (execution.principalHistory who) whole 0 site))
    (fun who => projectLogicalHistory who (observe who ideal)
      (eraseFocalHistory focal execution.principalHistory who) whole 0 site)
    (fun who different => by simp [eraseFocalLogical, eraseFocalHistory, different])
    (eraseFocalHistory focal execution.principalHistory) (by simp [eraseFocalHistory])]
  rw [(walk.continuation_sample_environmentStep runtime whole profile site
    name fresh law tail ideal values agreement bindings candidates clock enteredAt
    (eraseFocalHistory focal execution.principalHistory) unique).2]
  symm
  apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
  intro value supported
  rw [runtime.deviationContinuationAt_running whole profile focal (advanced value) _ tail
    (site + 1) (walk.trans (.sample (.refl tail))) (VEnv.cons value ideal)
    (PublicValues.consPublic value values) bindings candidates (clock + 1) (clock + 1) rfl]
  symm
  apply runtime.continuation_congr_focal_logical tail _ focal
    ((walk.trans (.sample (.refl tail))).policyTail_ignoresOwnHistory profile focal independent)
  · intro who different
    simp [advanced, eraseFocalLogical, eraseFocalHistory, different]
  · simp [eraseFocalHistory]

/-- info: 'Vegas.GraphRuntime.deviationContinuationAt_wire' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.deviationContinuationAt_wire

end Vegas.GraphRuntime
