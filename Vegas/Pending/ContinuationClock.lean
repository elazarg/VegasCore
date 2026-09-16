/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ContinuationAt
import Vegas.Pending.ContinuationStep
import GameTheoryExtensions.Math.Probability.FinDist

/-! # Actual chance invocations and residual outcome laws -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- A reserved slot which waits contributes no change to the residual law,
including its actual environment-history entry. -/
theorem continuationAt_environment_wait (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (profile : BehavioralProfile whole)
    (execution : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows whole 0)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (waits : environment execution.environmentHistory
      (MessageApplication.State.environmentView runtime.application execution.native) =
        FinDist.pure .wait) :
    runtime.continuationAt whole profile execution.principalHistory
        execution.native.application follows =
      (runtime.application.invoke players environment execution .environment).bindOnSupport
        fun after supported => runtime.continuationAt whole profile after.principalHistory
          after.native.application
          (runtime.invoke_follows whole 0 players environment .environment
            execution after follows supported) := by
  have kernel : runtime.application.invoke players environment execution .environment =
      FinDist.pure { execution with
        environmentHistory := execution.environmentHistory ++
          [⟨MessageApplication.State.environmentView runtime.application execution.native, .wait⟩] }
      := by
    simp only [MessageApplication.invoke, waits, FinDist.pure_bind,
      MessageApplication.environmentPolicyStep, MessageApplication.advance,
      MessageApplication.EnvironmentPolicyCommand.toAction]
  suffices bridge : ∀ (preserved : ∀ after ∈ (runtime.application.invoke players environment
        execution .environment).support, after.native.application.Follows whole 0),
      runtime.continuationAt whole profile execution.principalHistory
          execution.native.application follows =
        (runtime.application.invoke players environment execution .environment).bindOnSupport
          fun after supported => runtime.continuationAt whole profile after.principalHistory
            after.native.application (preserved after supported) from
    bridge (fun after supported => runtime.invoke_follows whole 0 players environment
      .environment execution after follows supported)
  rw [kernel]
  intro preserved
  rw [FinDist.pure_bindOnSupport]

/-- An actual environment tick at a sample cursor preserves the residual law
in expectation, with the same public chance kernel as graph execution. Player
policies are arbitrary because this invocation calls no player. -/
theorem Prefix.continuationAt_sample_tick
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (site : Nat)
    (name : VarId) {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (law : PublicDist (L := L) Γ payload)
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
    runtime.continuationAt whole profile execution.principalHistory
        execution.native.application follows =
      (runtime.application.invoke players environment execution .environment).bindOnSupport
        fun after supported => runtime.continuationAt whole profile after.principalHistory
          after.native.application
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
      runtime.continuationAt whole profile execution.principalHistory
          execution.native.application follows =
        (runtime.application.invoke players environment execution .environment).bindOnSupport
          fun after supported => runtime.continuationAt whole profile after.principalHistory
            after.native.application (preserved after supported) from
    bridge (fun after supported => runtime.invoke_follows whole 0 players environment
      .environment execution after follows supported)
  rw [kernel]
  intro preserved
  rw [FinDist.bindOnSupport_map]
  rw [runtime.continuationAt_running whole profile execution follows
    (.sample name fresh law tail) site walk ideal values bindings candidates clock enteredAt
    atCursor]
  rw [(walk.continuation_sample_environmentStep runtime whole profile site name fresh law tail
    ideal values agreement bindings candidates clock enteredAt execution.principalHistory unique).2]
  symm
  apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
  intro value supported
  exact runtime.continuationAt_running whole profile (advanced value) _ tail (site + 1)
    (walk.trans (.sample (.refl tail))) (VEnv.cons value ideal)
    (PublicValues.consPublic value values) bindings candidates (clock + 1) (clock + 1) rfl

end Vegas.GraphRuntime
