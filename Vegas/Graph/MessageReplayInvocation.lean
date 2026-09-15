/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageDeviationPrefixLocality

/-! # Player-invocation replay for actual compiled profiles -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- Full replay-invariant preservation for a player invocation. Hidden draws
of unchanged players remain unrelated; only their eventual cached publication
results are supplied by the endpoint coupling. -/
theorem NativeReplayInvariant.player_invoke
    {runtime : GraphRuntime Player L Δ} {whole : Graph Player L Γ₀ Δ}
    {focal : Player} {left right leftNext rightNext : runtime.application.PolicyExecution}
    (invariant : NativeReplayInvariant runtime whole focal left right)
    (suffix : Graph Player L Γ Δ)
    (checkpoint : FocalReplayCheckpoint runtime focal suffix left right)
    (profile : BehavioralProfile whole)
    (players : Player → runtime.application.PlayerPolicy)
    (compiled : ∀ actor, actor ≠ focal →
      players actor = runtime.compilePlayerPolicy whole actor (profile actor))
    (response : List (Entry runtime) → runtime.application.View → Command runtime)
    (pureFocal : players focal = fun history view => FinDist.pure (response history view))
    (environment : runtime.application.EnvironmentPolicy) (actor : Player)
    (leftAgreement : left.native.application.PublicAgreement)
    (rightAgreement : right.native.application.PublicAgreement)
    (results : actor ≠ focal → CachedResultsAgree runtime actor
      (left.principalHistory actor) (right.principalHistory actor) checkpoint.pc suffix
      checkpoint.leftIdeal checkpoint.rightIdeal)
    (leftSupported : leftNext ∈
      (runtime.application.invoke players environment left (.player actor)).support)
    (rightSupported : rightNext ∈
      (runtime.application.invoke players environment right (.player actor)).support) :
    NativeReplayInvariant runtime whole focal leftNext rightNext := by
  have replay :
      leftNext.principalHistory focal = rightNext.principalHistory focal ∧
        leftNext.environmentHistory = rightNext.environmentHistory ∧
        leftNext.native.application.focalReplayKey focal =
          rightNext.native.application.focalReplayKey focal ∧
        MessageApplication.State.environmentView runtime.application leftNext.native =
          MessageApplication.State.environmentView runtime.application rightNext.native ∧
        ∀ owner, owner ≠ focal →
          CacheShape (leftNext.principalHistory owner) (rightNext.principalHistory owner) := by
    by_cases own : actor = focal
    · subst actor
      exact checkpoint.focal_pure_invoke_replay runtime focal response players pureFocal
        environment invariant.cacheShape leftSupported rightSupported
    · have leftPublic : (checkpoint.publicValues : PublicValues Γ) =
          (PublicValues.ofVEnv checkpoint.leftIdeal : PublicValues Γ) := by
        rw [checkpoint.leftState] at leftAgreement
        exact leftAgreement
      have rightPublic : (checkpoint.publicValues : PublicValues Γ) =
          (PublicValues.ofVEnv checkpoint.rightIdeal : PublicValues Γ) := by
        rw [checkpoint.rightState] at rightAgreement
        exact rightAgreement
      have follows := invariant.leftFollows
      rw [checkpoint.leftState] at follows
      obtain ⟨walk⟩ := State.prefix_of_running_follows whole suffix checkpoint.leftIdeal
        checkpoint.publicValues checkpoint.bindings checkpoint.leftCandidates checkpoint.pc
        checkpoint.clock checkpoint.enteredAt follows
      obtain ⟨focalHistory, environmentHistory, focalKey, environmentView, actorShape⟩ :=
        checkpoint.compiled_nonfocal_invoke_replay runtime whole actor focal own suffix
          (profile actor) players (compiled actor own) environment left right leftNext rightNext
          walk leftPublic rightPublic (invariant.cacheShape actor own) (results own)
          leftSupported rightSupported
      refine ⟨focalHistory, environmentHistory, focalKey, environmentView, ?_⟩
      intro owner different
      by_cases same : owner = actor
      · subst owner
        exact actorShape
      · simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion]
          at leftSupported rightSupported
        obtain ⟨leftCommand, _, leftStep⟩ := leftSupported
        obtain ⟨rightCommand, _, rightStep⟩ := rightSupported
        rw [runtime.application.playerStep_other_history actor owner same left leftCommand
            leftNext leftStep,
          runtime.application.playerStep_other_history actor owner same right rightCommand
            rightNext rightStep]
        exact invariant.cacheShape owner different
  obtain ⟨focalHistory, environmentHistory, focalKey, environmentView, shapes⟩ := replay
  have phase : leftNext.native.application.phase = rightNext.native.application.phase := by
    have publicPhase := congrArg
      (fun view : runtime.application.EnvironmentObservation => view.application.pc)
      environmentView
    change leftNext.native.application.publicView.pc =
      rightNext.native.application.publicView.pc at publicPhase
    simpa only [State.publicView_pc] using publicPhase
  exact invariant.afterInvoke players environment (.player actor) leftSupported rightSupported
    phase focalKey environmentView focalHistory environmentHistory shapes

/-- info: 'Vegas.GraphRuntime.NativeReplayInvariant.player_invoke' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.NativeReplayInvariant.player_invoke

end Vegas.GraphRuntime
