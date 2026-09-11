/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPredraw
import Vegas.Compile.WindowedDeviationLaw

/-! # Randomized windowed deviations

Predrawing a finite execution preserves its complete native law and leaves
every opponent unchanged. Applying the source theorem to each pure branch
gives a finite mixture of original sequential source deviations. No closure
of source behavioral policies under mixed strategies is assumed.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory GameTheory.Math.Probability

/-- Every randomized unilateral raw policy has the joint completion/public
outcome law of a finite mixture of legal source deviations. The service and
backend conditions are those of the pure-deviation compiler theorem. -/
theorem windowed_deviation_source_public_mixture
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
                terminal).erasePubEnv) := by
  classical
  let runtime := plan.windowed deadlineOf binding choice windowOf
  let players := plan.windowedReferencePlayers profile deadlineOf binding choice windowOf
  let schedule := (List.replicate (plan.instructions deadlineOf).length
    (WindowedApplication.blockInvocations roster)).flatten
  let initial := plan.windowedInitialExecution deadlineOf binding choice windowOf
  let nativeLaw := fun policy : runtime.application.PlayerPolicy =>
    runtime.application.runPolicies
      (plan.windowedPlayers profile deadlineOf binding choice windowOf focal policy)
      (runtime.blockEnvironment roster) schedule initial
  let observe := fun out : runtime.application.PolicyExecution =>
    (out.native.application.base.memory.finished (compile source.core).graph.nodeCount,
      (compile source.core).readPublicTerminal? out.native.application.base.memory)
  let sourceLaw := fun policy : SourceBehavioralPolicy source.core.prog focal =>
    (denoteSource source.core.prog
      (Profile.update (sig := sourceGameSignature source.core.prog) profile focal policy)
        source.core.env).map fun terminal =>
      (true, some (cast (congrArg (VEnv L)
        (compileCore_terminalCtx_eq_sourceTerminalCtx source.core.prog source.core.fresh
          (BuildState.fromInitial
            (initialState source.core.Γ source.core.env source.core.wctx))).symm)
          terminal).erasePubEnv)
  obtain ⟨nativeMixture, hpure, hmixture⟩ :=
    runtime.application.exists_native_policy_mixture_runPolicies players
      (runtime.blockEnvironment roster) focal schedule initial replacement
  have hnative : nativeMixture.bind nativeLaw = nativeLaw replacement := hmixture
  have hsource : ∀ policy ∈ nativeMixture.support,
      ∃ alternative : SourceBehavioralPolicy source.core.prog focal,
        (nativeLaw policy).map observe = sourceLaw alternative := by
    intro policy hpolicy
    let command history view := (hpure policy hpolicy history view).choose
    have hcommand : policy = fun history view => FinDist.pure (command history view) :=
      funext fun history => funext fun view => (hpure policy hpolicy history view).choose_spec
    refine ⟨plan.extractedSourcePolicy profile deadlineOf binding choice windowOf roster focal
      (fun history view => FinDist.pure (command history view))
      (compiledInitialCoupled source.core) hinitial horigins hroster howners command rfl
      relay hrelay hrelayOther, ?_⟩
    rw [hcommand]
    exact plan.windowed_pure_deviation_source_public_law source profile deadlineOf binding
      choice windowOf roster focal hinitial horigins hfallbacks hroster howners command
      relay hrelay hrelayOther
  let translate : runtime.application.PlayerPolicy →
      SourceBehavioralPolicy source.core.prog focal :=
    fun policy => if hpolicy : policy ∈ nativeMixture.support then
      (hsource policy hpolicy).choose else profile focal
  refine ⟨nativeMixture.map translate, ?_⟩
  change (nativeLaw replacement).map observe = (nativeMixture.map translate).bind sourceLaw
  rw [← hnative, FinDist.map_bind, FinDist.bind_map]
  apply FinDist.bind_congr
  intro policy hpolicy
  simpa only [translate, dif_pos hpolicy] using (hsource policy hpolicy).choose_spec

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.windowed_deviation_source_public_mixture'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.windowed_deviation_source_public_mixture
