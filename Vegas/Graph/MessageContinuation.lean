/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageHistoryExtension

/-! # Typed continuation law for compiled message executions

This evaluator treats cached private prepare and remember commands as the
choices already sampled by the corresponding graph policy. That interpretation
is valid for honest compiled policies. Arbitrary focal deviations require a
separate validated action extraction and must not reuse their untrusted cache
markers as graph actions.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- Decode the prepared command cached at a binding site. Reachability laws
later show that compiler-produced preparations always have the expected tag. -/
def preparedChoice {runtime : GraphRuntime Player L Δ} (history : List (Entry runtime))
    (site : Nat) (payload : L.Ty) : Option (PublicationResult (L.Val payload)) :=
  (preparedRaw history site).bind fun raw =>
    (raw.as? (R.result payload)).map (R.valueEquiv payload)

/-- Proof-side residual graph law. The logical history is kept explicitly so
that an unfixed head draw can be appended before recursively evaluating later
decisions. Runtime histories are consulted only for a choice already cached by
an actual prepare/remember command at the current site. -/
def continuation (runtime : GraphRuntime Player L Δ) :
    {Γ : VCtx Player L} → (graph : Graph Player L Γ Δ) →
    BehavioralProfile graph → Nat → VEnv L Γ → History Player L →
    (Player → List (Entry runtime)) → FinDist (VEnv L Δ)
  | _, .ret _, _, _, env, _, _ => FinDist.pure env
  | _, .sample _ _ law next, profile, site, env, logical, histories =>
      (law.eval env).bind fun value =>
        continuation runtime next (afterSample profile) (site + 1)
          (VEnv.cons value env) logical histories
  | _, .bind name owner (payload := payload) _ next, profile, site, env, logical, histories =>
      let proceed := fun choice =>
        let logical' := Function.update logical owner
          (logical owner ++ [OwnAction.bind owner name payload choice])
        continuation runtime next (afterBind profile) (site + 1)
          (VEnv.cons ((R.valueEquiv payload).symm choice) env) logical' histories
      match preparedChoice (histories owner) site payload with
      | some choice => proceed choice
      | none => (bindKernel profile (observe owner env, logical owner)).bind proceed
  | _, .resolve _outputName owner bindingName (payload := payload) _ source checks next,
      profile, site, env, logical, histories =>
      let proceed := fun disclose =>
        let accepted := acceptedResult source checks env disclose
        let logical' := Function.update logical owner
          (logical owner ++ [OwnAction.resolve owner bindingName disclose])
        continuation runtime next (afterResolve profile) (site + 1)
          (VEnv.cons ((R.valueEquiv payload).symm accepted) env) logical' histories
      match rememberedDisclosure (histories owner) site with
      | some disclose => proceed disclose
      | none => (resolveKernel profile (observe owner env, logical owner)).bind proceed

@[simp] theorem preparedChoice_nil (runtime : GraphRuntime Player L Δ)
    (site : Nat) (payload : L.Ty) :
    preparedChoice (runtime := runtime) [] site payload = none := by
  simp [preparedChoice, preparedRaw]

@[simp] theorem rememberedDisclosure_nil (runtime : GraphRuntime Player L Δ) (site : Nat) :
    rememberedDisclosure (runtime := runtime) [] site = none := by
  simp [rememberedDisclosure]


/-- Continuation laws inspect runtime histories only through the two cache
projections at the current and later sites. -/
theorem continuation_congr_histories (runtime : GraphRuntime Player L Δ)
    (graph : Graph Player L Γ Δ) (profile : BehavioralProfile graph)
    (site : Nat) (env : VEnv L Γ) (logical : History Player L)
    (left right : Player → List (Entry runtime))
    (prepared : ∀ who queried, site ≤ queried →
      ∀ payload, preparedChoice (left who) queried payload =
        preparedChoice (right who) queried payload)
    (remembered : ∀ who queried, site ≤ queried →
      rememberedDisclosure (left who) queried = rememberedDisclosure (right who) queried) :
    continuation runtime graph profile site env logical left =
      continuation runtime graph profile site env logical right := by
  induction graph generalizing site logical with
  | ret payoffs => rfl
  | sample name fresh law next ih =>
      simp only [continuation]
      apply FinDist.bind_congr
      intro value _
      apply ih
      · intro who queried lower payload
        exact prepared who queried (by omega) payload
      · intro who queried lower
        exact remembered who queried (by omega)
  | bind name owner fresh next ih =>
      simp only [continuation]
      rw [prepared owner site (by omega)]
      split
      · apply ih
        · intro who queried lower payload
          exact prepared who queried (by omega) payload
        · intro who queried lower
          exact remembered who queried (by omega)
      · apply FinDist.bind_congr
        intro choice _
        apply ih
        · intro who queried lower payload
          exact prepared who queried (by omega) payload
        · intro who queried lower
          exact remembered who queried (by omega)
  | resolve outputName owner bindingName fresh source checks next ih =>
      simp only [continuation]
      rw [remembered owner site (by omega)]
      split
      · apply ih
        · intro who queried lower payload
          exact prepared who queried (by omega) payload
        · intro who queried lower
          exact remembered who queried (by omega)
      · apply FinDist.bind_congr
        intro disclose _
        apply ih
        · intro who queried lower payload
          exact prepared who queried (by omega) payload
        · intro who queried lower
          exact remembered who queried (by omega)

/-- Recording the actual prepare command turns an unfixed bind continuation
into the branch selected by that command's publication result. -/
theorem continuation_bind_after_prepare (runtime : GraphRuntime Player L Δ)
    (name : VarId) (owner : Player) {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (profile : BehavioralProfile (.bind name owner fresh next)) (site : Nat)
    (env : VEnv L Γ) (logical : History Player L)
    (histories : Player → List (Entry runtime)) (before : runtime.application.View)
    (choice : PublicationResult (L.Val payload))
    (missing : preparedRaw (histories owner) site = none) :
    let raw : Raw L := ⟨R.result payload, (R.valueEquiv payload).symm choice⟩
    let histories' := Function.update histories owner
      (histories owner ++ [⟨before, .privateCommand (.prepare site raw)⟩])
    continuation runtime (.bind name owner fresh next) profile site env logical histories' =
      continuation runtime next (afterBind profile) (site + 1)
        (VEnv.cons ((R.valueEquiv payload).symm choice) env)
        (Function.update logical owner
          (logical owner ++ [OwnAction.bind owner name payload choice])) histories' := by
  dsimp only
  simp [continuation, preparedChoice, preparedRaw_append_prepare runtime _ before site _ missing]

/-- Recording the actual remember command similarly fixes the resolve branch. -/
theorem continuation_resolve_after_remember (runtime : GraphRuntime Player L Δ)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck ((outputName, .pub (R.result payload)) :: Γ)))
    (next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (profile : BehavioralProfile
      (.resolve outputName owner bindingName fresh source checks next))
    (site : Nat) (env : VEnv L Γ) (logical : History Player L)
    (histories : Player → List (Entry runtime)) (before : runtime.application.View)
    (disclose : Bool) (missing : rememberedDisclosure (histories owner) site = none)
    (atSite : before.application.publicState.pc = site) :
    let histories' := Function.update histories owner
      (histories owner ++ [⟨before, .privateCommand (.rememberDisclosure disclose)⟩])
    continuation runtime (.resolve outputName owner bindingName fresh source checks next)
        profile site env logical histories' =
      continuation runtime next (afterResolve profile) (site + 1)
        (VEnv.cons ((R.valueEquiv payload).symm
          (acceptedResult source checks env disclose)) env)
        (Function.update logical owner
          (logical owner ++ [OwnAction.resolve owner bindingName disclose])) histories' := by
  dsimp only
  simp [continuation, rememberedDisclosure_append_remember runtime _ before site disclose
    missing atSite]

/-- An uncached bind is exactly the graph kernel averaged over continuations
whose real prepare entry records the sampled result. -/
theorem continuation_bind_average_recorded (runtime : GraphRuntime Player L Δ)
    (name : VarId) (owner : Player) {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (profile : BehavioralProfile (.bind name owner fresh next)) (site : Nat)
    (env : VEnv L Γ) (logical : History Player L)
    (histories : Player → List (Entry runtime)) (before : runtime.application.View)
    (missing : preparedRaw (histories owner) site = none) :
    continuation runtime (.bind name owner fresh next) profile site env logical histories =
      (bindKernel profile (observe owner env, logical owner)).bind fun choice =>
        let raw : Raw L := ⟨R.result payload, (R.valueEquiv payload).symm choice⟩
        continuation runtime (.bind name owner fresh next) profile site env logical
          (Function.update histories owner
            (histories owner ++ [⟨before, .privateCommand (.prepare site raw)⟩])) := by
  have noChoice : preparedChoice (histories owner) site payload = none := by
    simp [preparedChoice, missing]
  simp only [continuation, noChoice]
  apply FinDist.bind_congr
  intro choice _
  simp only [Function.update_self]
  rw [show preparedChoice
      (histories owner ++
        [⟨before, .privateCommand (.prepare site
          ⟨R.result payload, (R.valueEquiv payload).symm choice⟩)⟩]) site payload =
      some choice by
    simp [preparedChoice, preparedRaw_append_prepare runtime _ before site _ missing]]
  apply continuation_congr_histories
  · intro who queried lower queriedPayload
    by_cases same : who = owner
    · subst same
      simp only [Function.update_self]
      unfold preparedChoice
      rw [preparedRaw_append_prepare_ne runtime _ before site queried _ (by omega)]
    · simp [Function.update, same]
  · intro who queried lower
    by_cases same : who = owner
    · subst same
      simp only [Function.update_self]
      rw [rememberedDisclosure_append_prepare runtime _ before site _ queried]
    · simp [Function.update, same]

/-- An uncached resolve is exactly the disclosure kernel averaged over
continuations whose real remember entry records the sampled Boolean. -/
theorem continuation_resolve_average_recorded (runtime : GraphRuntime Player L Δ)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck ((outputName, .pub (R.result payload)) :: Γ)))
    (next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (profile : BehavioralProfile
      (.resolve outputName owner bindingName fresh source checks next))
    (site : Nat) (env : VEnv L Γ) (logical : History Player L)
    (histories : Player → List (Entry runtime)) (before : runtime.application.View)
    (missing : rememberedDisclosure (histories owner) site = none)
    (atSite : before.application.publicState.pc = site) :
    continuation runtime (.resolve outputName owner bindingName fresh source checks next)
        profile site env logical histories =
      (resolveKernel profile (observe owner env, logical owner)).bind fun disclose =>
        continuation runtime (.resolve outputName owner bindingName fresh source checks next)
          profile site env logical
          (Function.update histories owner
            (histories owner ++
              [⟨before, .privateCommand (.rememberDisclosure disclose)⟩])) := by
  simp only [continuation, missing]
  apply FinDist.bind_congr
  intro disclose _
  simp only [Function.update_self]
  rw [rememberedDisclosure_append_remember runtime _ before site disclose missing atSite]
  apply continuation_congr_histories
  · intro who queried lower queriedPayload
    by_cases same : who = owner
    · subst same
      simp only [Function.update_self]
      unfold preparedChoice
      rw [preparedRaw_append_remember runtime _ before disclose queried]
    · simp [Function.update, same]
  · intro who queried lower
    by_cases same : who = owner
    · subst same
      simp only [Function.update_self]
      rw [rememberedDisclosure_append_remember_ne runtime _ before site queried disclose atSite
        (by omega)]
    · simp [Function.update, same]

/-- Actual invocation form of bind averaging. This is the local Bellman
identity used by the whole-run proof once `compileAt_bind_fresh` supplies the
policy-kernel premise. -/
theorem continuation_bind_invoke (runtime : GraphRuntime Player L Δ)
    (name : VarId) (owner : Player) {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (profile : BehavioralProfile (.bind name owner fresh next)) (site : Nat)
    (env : VEnv L Γ) (logical : History Player L)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (execution : runtime.application.PolicyExecution)
    (missing : preparedRaw (execution.principalHistory owner) site = none)
    (policyKernel :
      players owner (execution.principalHistory owner)
          (Interaction.MessageApplication.State.observe runtime.application
            execution.native owner) =
        (bindKernel profile (observe owner env, logical owner)).map fun choice =>
          .privateCommand (.prepare site
            ⟨R.result payload, (R.valueEquiv payload).symm choice⟩)) :
    continuation runtime (.bind name owner fresh next) profile site env logical
        execution.principalHistory =
      (runtime.application.invoke players environment execution (.player owner)).bind fun after =>
        continuation runtime (.bind name owner fresh next) profile site env logical
          after.principalHistory := by
  rw [continuation_bind_average_recorded runtime name owner fresh next profile site env logical
    execution.principalHistory
    (Interaction.MessageApplication.State.observe runtime.application execution.native owner)
    missing]
  simp only [Interaction.MessageApplication.invoke, policyKernel, FinDist.map_eq_bind,
    FinDist.bind_bind]
  apply FinDist.bind_congr
  intro choice _
  simp only [Interaction.MessageApplication.playerStep,
    Interaction.MessageApplication.advance,
    Interaction.MessageApplication.PlayerCommand.toAction,
    Interaction.MessageApplication.step, FinDist.pure_bind]
  congr 1
  funext other
  simp [Function.update]

/-- Actual invocation form of resolve averaging. The policy-kernel premise is
the conclusion of `compileAt_resolve_fresh` after typed-prefix transport. -/
theorem continuation_resolve_invoke (runtime : GraphRuntime Player L Δ)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck ((outputName, .pub (R.result payload)) :: Γ)))
    (next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (profile : BehavioralProfile
      (.resolve outputName owner bindingName fresh source checks next))
    (site : Nat) (env : VEnv L Γ) (logical : History Player L)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (execution : runtime.application.PolicyExecution)
    (missing : rememberedDisclosure (execution.principalHistory owner) site = none)
    (atSite :
      (Interaction.MessageApplication.State.observe runtime.application
        execution.native owner).application.publicState.pc = site)
    (policyKernel :
      players owner (execution.principalHistory owner)
          (Interaction.MessageApplication.State.observe runtime.application
            execution.native owner) =
        (resolveKernel profile (observe owner env, logical owner)).map fun disclose =>
          .privateCommand (.rememberDisclosure disclose)) :
    continuation runtime (.resolve outputName owner bindingName fresh source checks next)
        profile site env logical execution.principalHistory =
      (runtime.application.invoke players environment execution (.player owner)).bind fun after =>
        continuation runtime (.resolve outputName owner bindingName fresh source checks next)
          profile site env logical after.principalHistory := by
  rw [continuation_resolve_average_recorded runtime outputName bindingName owner fresh source checks
    next profile site env logical execution.principalHistory
    (Interaction.MessageApplication.State.observe runtime.application execution.native owner)
    missing atSite]
  simp only [Interaction.MessageApplication.invoke, policyKernel, FinDist.map_eq_bind,
    FinDist.bind_bind]
  apply FinDist.bind_congr
  intro disclose _
  simp only [Interaction.MessageApplication.playerStep,
    Interaction.MessageApplication.advance,
    Interaction.MessageApplication.PlayerCommand.toAction,
    Interaction.MessageApplication.step, FinDist.pure_bind]
  congr 1
  funext other
  simp [Function.update]

/-- With no cached runtime commands, the continuation is exactly the ordinary
graph execution kernel, including all later behavioral and graph randomness. -/
theorem continuation_empty_eq_runWith (runtime : GraphRuntime Player L Δ)
    (graph : Graph Player L Γ Δ) (profile : BehavioralProfile graph)
    (site : Nat) (env : VEnv L Γ) (logical : History Player L) :
    continuation runtime graph profile site env logical (fun _ => []) =
      Graph.runWith graph profile env logical := by
  induction graph generalizing site logical with
  | ret payoffs => rfl
  | sample name fresh law next ih =>
      simp only [continuation, Graph.runWith]
      apply FinDist.bind_congr
      intro value _
      exact ih runtime (afterSample profile) (site + 1) _ _
  | bind name owner fresh next ih =>
      simp only [continuation, preparedChoice_nil, Graph.runWith]
      apply FinDist.bind_congr
      intro choice _
      exact ih runtime (afterBind profile) (site + 1) _ _
  | resolve outputName owner bindingName fresh source checks next ih =>
      simp only [continuation, rememberedDisclosure_nil, Graph.runWith]
      apply FinDist.bind_congr
      intro disclose _
      exact ih runtime (afterResolve profile) (site + 1) _ _

/-- The initial continuation is the standard graph law. -/
theorem continuation_initial_eq_run (runtime : GraphRuntime Player L Δ)
    (graph : Graph Player L Γ Δ) (profile : BehavioralProfile graph)
    (env : VEnv L Γ) :
    continuation runtime graph profile 0 env (fun _ => []) (fun _ => []) =
      Graph.run graph profile env :=
  continuation_empty_eq_runWith runtime graph profile 0 env (fun _ => [])

end Vegas.GraphRuntime
