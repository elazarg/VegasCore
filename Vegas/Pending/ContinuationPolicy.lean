/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ContinuationFrame
import Vegas.Pending.PolicyLaws
import Vegas.Pending.PolicyCommands
import Vegas.Pending.PhaseFrame

/-! # Compiled-policy continuation identities -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- At an arbitrary typed bind cursor, invoking the owner under the policy
compiled from the original graph satisfies the continuation Bellman identity. -/
private theorem continuation_bind_compiled_invoke
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (site : Nat)
    (name : VarId) (owner : Player) {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (walk : Prefix Δ whole (.bind name owner fresh next) site)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat)
    (execution : runtime.application.PolicyExecution)
    (atCursor : execution.native.application =
      .running (.bind name owner fresh next) ideal values bindings candidates site clock enteredAt)
    (environment : runtime.application.EnvironmentPolicy) :
    let residual := walk.profileTail profile
    let logical : History Player L := fun who =>
      projectLogicalHistory who (observe who ideal) (execution.principalHistory who) whole 0 site
    continuation runtime (.bind name owner fresh next) residual site ideal logical
        execution.principalHistory =
      (runtime.application.invoke (runtime.compileProfile whole profile) environment execution
        (.player owner)).bind fun after =>
          continuation runtime (.bind name owner fresh next) residual site ideal logical
            after.principalHistory := by
  dsimp only
  have atSite : (Interaction.MessageApplication.State.observe runtime.application
      execution.native owner).application.publicState.pc = site := by
    change (State.playerView execution.native.application owner).publicState.pc = site
    rw [atCursor]
    rfl
  by_cases submitted : submittedAt (execution.principalHistory owner) site = true
  · apply continuation_invoke_nonprivate
    intro command supported privateAction
    change command ∈ (compileAt runtime owner whole whole (profile owner) 0
      (execution.principalHistory owner)
      (Interaction.MessageApplication.State.observe runtime.application
        execution.native owner)).support at supported
    rw [compileAt_wait_of_submitted runtime owner whole whole (profile owner) 0 _ _
      (by simpa [atSite] using submitted)] at supported
    simp_all
  have unsubmitted : submittedAt (execution.principalHistory owner) site = false :=
    Bool.eq_false_iff.mpr submitted
  by_cases missing : preparedRaw (execution.principalHistory owner) site = none
  swap
  · obtain ⟨raw, prepared⟩ := Option.ne_none_iff_exists'.mp missing
    apply continuation_invoke_nonprivate
    intro command supported privateAction
    change command ∈ (runtime.compilePlayerPolicy whole owner (profile owner)
      (execution.principalHistory owner)
      (Interaction.MessageApplication.State.observe runtime.application
        execution.native owner)).support at supported
    rw [Prefix.compilePlayerPolicy_eq_suffix walk owner (profile owner) _ _ atSite,
      compileAt_bind_prepared runtime whole site name owner fresh next
        (walk.policyTail owner (profile owner)) _ _ raw atSite prepared unsubmitted] at supported
    simp_all
  rcases execution with ⟨⟨application, pool, receipts⟩, principalHistory,
    environmentHistory, nativeTrace⟩
  dsimp only at atCursor ⊢
  subst application
  let execution : runtime.application.PolicyExecution :=
    ⟨⟨.running (.bind name owner fresh next) ideal values bindings candidates site clock enteredAt,
      pool, receipts⟩, principalHistory, environmentHistory, nativeTrace⟩
  apply continuation_bind_invoke runtime name owner fresh next (walk.profileTail profile) site
    ideal _ (runtime.compileProfile whole profile) environment execution missing
  let view := Interaction.MessageApplication.State.observe runtime.application
    execution.native owner
  have hpc : view.application.publicState.pc = site := by
    simp [view, execution, Interaction.MessageApplication.State.observe,
      GraphRuntime.application, State.playerView]
  have hwho : view.application.who = owner := by
    simp [view, execution, Interaction.MessageApplication.State.observe,
      GraphRuntime.application, State.playerView]
  have hΓ : view.application.publicState.Γ = Γ := by
    simp [view, execution, Interaction.MessageApplication.State.observe,
      GraphRuntime.application, State.playerView]
  have hobs : hΓ ▸ (hwho ▸ view.application.privateObservation) = observe owner ideal := by
    simp [view, execution, Interaction.MessageApplication.State.observe,
      GraphRuntime.application, State.playerView]
  rw [show runtime.compileProfile whole profile owner =
      runtime.compilePlayerPolicy whole owner (profile owner) by rfl]
  rw [Prefix.compilePlayerPolicy_eq_suffix walk owner (profile owner)
    (execution.principalHistory owner) view hpc]
  rw [compileAt_bind_fresh runtime whole site name owner fresh next
    (walk.policyTail owner (profile owner)) _ view hpc hwho hΓ missing unsubmitted]
  rw [hobs]
  rfl

/-- At an arbitrary typed resolve cursor, invoking the owner under the policy
compiled from the original graph satisfies the continuation Bellman identity.

Like the bind theorem, this is an honest compiled-policy law. An arbitrary
focal deviation may forge private cache markers, so deviation backtranslation
must validate or extract its graph action rather than apply this cached
continuation theorem unchanged. -/
private theorem continuation_resolve_compiled_invoke
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (site : Nat)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck ((outputName, .pub (R.result payload)) :: Γ)))
    (next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (walk : Prefix Δ whole
      (.resolve outputName owner bindingName fresh source checks next) site)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat)
    (execution : runtime.application.PolicyExecution)
    (atCursor : execution.native.application =
      .running (.resolve outputName owner bindingName fresh source checks next)
        ideal values bindings candidates site clock enteredAt)
    (environment : runtime.application.EnvironmentPolicy) :
    let residual := walk.profileTail profile
    let logical : History Player L := fun who =>
      projectLogicalHistory who (observe who ideal) (execution.principalHistory who) whole 0 site
    continuation runtime
        (.resolve outputName owner bindingName fresh source checks next)
        residual site ideal logical execution.principalHistory =
      (runtime.application.invoke (runtime.compileProfile whole profile) environment execution
        (.player owner)).bind fun after =>
          continuation runtime
            (.resolve outputName owner bindingName fresh source checks next)
            residual site ideal logical after.principalHistory := by
  dsimp only
  have atSite : (Interaction.MessageApplication.State.observe runtime.application
      execution.native owner).application.publicState.pc = site := by
    change (State.playerView execution.native.application owner).publicState.pc = site
    rw [atCursor]
    rfl
  by_cases submitted : submittedAt (execution.principalHistory owner) site = true
  · apply continuation_invoke_nonprivate
    intro command supported privateAction
    change command ∈ (compileAt runtime owner whole whole (profile owner) 0
      (execution.principalHistory owner)
      (Interaction.MessageApplication.State.observe runtime.application
        execution.native owner)).support at supported
    rw [compileAt_wait_of_submitted runtime owner whole whole (profile owner) 0 _ _
      (by simpa [atSite] using submitted)] at supported
    simp_all
  have unsubmitted : submittedAt (execution.principalHistory owner) site = false :=
    Bool.eq_false_iff.mpr submitted
  by_cases missing : rememberedDisclosure (execution.principalHistory owner) site = none
  swap
  · obtain ⟨disclose, remembered⟩ := Option.ne_none_iff_exists'.mp missing
    apply continuation_invoke_nonprivate
    intro command supported privateAction
    change command ∈ (runtime.compilePlayerPolicy whole owner (profile owner)
      (execution.principalHistory owner)
      (Interaction.MessageApplication.State.observe runtime.application
        execution.native owner)).support at supported
    rw [Prefix.compilePlayerPolicy_eq_suffix walk owner (profile owner) _ _ atSite] at supported
    rcases execution with ⟨⟨application, pool, receipts⟩, principalHistory,
      environmentHistory, nativeTrace⟩
    dsimp only at atCursor ⊢
    subst application
    simp only [compileAt, Interaction.MessageApplication.State.observe,
      GraphRuntime.application, State.playerView, ↓reduceDIte, ↓reduceIte,
      unsubmitted, Bool.false_eq_true, remembered] at supported
    split at supported
    · simp only [disclosureCommand] at supported
      split at supported
      · simp_all
      · split at supported <;> simp_all
    · simp_all
  rcases execution with ⟨⟨application, pool, receipts⟩, principalHistory,
    environmentHistory, nativeTrace⟩
  dsimp only at atCursor ⊢
  subst application
  let execution : runtime.application.PolicyExecution :=
    ⟨⟨.running (.resolve outputName owner bindingName fresh source checks next)
      ideal values bindings candidates site clock enteredAt, pool, receipts⟩,
      principalHistory, environmentHistory, nativeTrace⟩
  apply continuation_resolve_invoke runtime outputName bindingName owner fresh source checks next
    (walk.profileTail profile) site ideal _ (runtime.compileProfile whole profile) environment
    execution missing
  · simp [execution, Interaction.MessageApplication.State.observe,
      GraphRuntime.application, State.playerView]
  let view := Interaction.MessageApplication.State.observe runtime.application
    execution.native owner
  have hpc : view.application.publicState.pc = site := by
    simp [view, execution, Interaction.MessageApplication.State.observe,
      GraphRuntime.application, State.playerView]
  have hwho : view.application.who = owner := by
    simp [view, execution, Interaction.MessageApplication.State.observe,
      GraphRuntime.application, State.playerView]
  have hΓ : view.application.publicState.Γ = Γ := by
    simp [view, execution, Interaction.MessageApplication.State.observe,
      GraphRuntime.application, State.playerView]
  have hobs : hΓ ▸ (hwho ▸ view.application.privateObservation) = observe owner ideal := by
    simp [view, execution, Interaction.MessageApplication.State.observe,
      GraphRuntime.application, State.playerView]
  rw [show runtime.compileProfile whole profile owner =
      runtime.compilePlayerPolicy whole owner (profile owner) by rfl]
  rw [Prefix.compilePlayerPolicy_eq_suffix walk owner (profile owner)
    (execution.principalHistory owner) view hpc]
  rw [compileAt_resolve_fresh runtime whole site outputName bindingName owner fresh source checks
    next (walk.policyTail owner (profile owner)) _ view hpc hwho hΓ missing unsubmitted]
  rw [hobs]
  rfl

/-- Every player invocation of the actual compiled profile preserves the
residual graph law in expectation. This covers every graph constructor and
every cache/submission state: only a fresh owner decision samples a graph
kernel; submission and waiting retain the already sampled choice.

Player commands do not advance the graph cursor. The continuation on the
right uses the resulting authenticated history, including its projected
logical decisions; packet acceptance and sample ticks are covered by the
continuation transition laws. -/
theorem continuation_compiled_player_invoke
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (graph : Graph Player L Γ Δ) (site : Nat)
    (walk : Prefix Δ whole graph site)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat)
    (execution : runtime.application.PolicyExecution)
    (atCursor : execution.native.application =
      .running graph ideal values bindings candidates site clock enteredAt)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy) (actor : Player)
    (compiled : players actor = runtime.compilePlayerPolicy whole actor (profile actor)) :
    let residual := walk.profileTail profile
    let logical : History Player L := fun who =>
      projectLogicalHistory who (observe who ideal) (execution.principalHistory who) whole 0 site
    continuation runtime graph residual site ideal logical execution.principalHistory =
      (runtime.application.invoke players environment execution
        (.player actor)).bind fun after =>
          continuation runtime graph residual site ideal
            (fun who => projectLogicalHistory who (observe who ideal)
              (after.principalHistory who) whole 0 site) after.principalHistory := by
  dsimp only
  have sameInvocation : runtime.application.invoke players environment execution (.player actor) =
      runtime.application.invoke (runtime.compileProfile whole profile)
        environment execution (.player actor) := by
    simp only [Interaction.MessageApplication.invoke, compiled, compileProfile]
  rw [sameInvocation]
  have histories : ∀ after ∈ (runtime.application.invoke (runtime.compileProfile whole profile)
      environment execution (.player actor)).support,
      (fun who => projectLogicalHistory who (observe who ideal)
        (after.principalHistory who) whole 0 site) =
      (fun who => projectLogicalHistory who (observe who ideal)
        (execution.principalHistory who) whole 0 site) := by
    intro after supported
    funext who
    apply runtime.runPolicies_projectLogicalHistory_before whole who (observe who ideal) 0 site
      (runtime.compileProfile whole profile) environment [.player actor] execution after
    · rw [atCursor]
      simp [State.phase]
    · simpa [Interaction.MessageApplication.runPolicies] using supported
  trans (runtime.application.invoke (runtime.compileProfile whole profile) environment execution
    (.player actor)).bind fun after =>
      continuation runtime graph (walk.profileTail profile) site ideal
        (fun who => projectLogicalHistory who (observe who ideal)
          (execution.principalHistory who) whole 0 site) after.principalHistory
  swap
  · apply FinDist.bind_congr
    intro after supported
    rw [histories after supported]
  have atSite : (Interaction.MessageApplication.State.observe runtime.application
      execution.native actor).application.publicState.pc = site := by
    change (State.playerView execution.native.application actor).publicState.pc = site
    rw [atCursor]
    rfl
  cases graph with
  | bind name owner fresh next =>
      by_cases owned : owner = actor
      · subst actor
        exact continuation_bind_compiled_invoke runtime whole profile site name owner fresh next
          walk ideal values bindings candidates clock enteredAt execution atCursor environment
      · apply continuation_invoke_nonprivate
        intro command supported privateAction
        change command ∈ (runtime.compilePlayerPolicy whole actor (profile actor)
          (execution.principalHistory actor)
          (Interaction.MessageApplication.State.observe runtime.application
            execution.native actor)).support at supported
        rw [Prefix.compilePlayerPolicy_eq_suffix walk actor (profile actor) _ _ atSite] at supported
        simp_all [compileAt]
  | resolve outputName owner bindingName fresh source checks next =>
      by_cases owned : owner = actor
      · subst actor
        exact continuation_resolve_compiled_invoke runtime whole profile site outputName bindingName
          owner fresh source checks next walk ideal values bindings candidates clock enteredAt
          execution atCursor environment
      · apply continuation_invoke_nonprivate
        intro command supported privateAction
        change command ∈ (runtime.compilePlayerPolicy whole actor (profile actor)
          (execution.principalHistory actor)
          (Interaction.MessageApplication.State.observe runtime.application
            execution.native actor)).support at supported
        rw [Prefix.compilePlayerPolicy_eq_suffix walk actor (profile actor) _ _ atSite] at supported
        simp_all [compileAt]
  | sample name fresh law next =>
      apply continuation_invoke_nonprivate
      intro command supported privateAction
      change command ∈ (runtime.compilePlayerPolicy whole actor (profile actor)
        (execution.principalHistory actor)
        (Interaction.MessageApplication.State.observe runtime.application
          execution.native actor)).support at supported
      rw [Prefix.compilePlayerPolicy_eq_suffix walk actor (profile actor) _ _ atSite] at supported
      simp_all [compileAt]
  | ret payoffs =>
      simp [continuation]

end Vegas.GraphRuntime
