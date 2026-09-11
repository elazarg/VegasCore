/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockLaw
import Vegas.Compile.WindowedConditionalContinuation
import Vegas.Compile.WindowedReferenceCaches

/-! # Source laws for the fixed windowed reference execution

The native execution uses the same block environment and invocation schedule
as the arbitrary-deviation theorem. Every owner draws from its original source
kernel. Full cache freshness, including at the distinguished coordinate, is
preserved through the actual successor distribution.
-/

noncomputable section

namespace Vegas.ApplicationPlan.WindowedSourcePrefix

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- From an actual source prefix with fresh reference caches, the remaining
fixed-service run has the original source profile's public result law. -/
theorem reference_public_law
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext} {prog : VegasCore P L Γ}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {accounted : CommitmentAccounting pending prog}
    {rootFresh : FreshBindings rootProg} {fresh : FreshBindings prog}
    {rootState : BuildState P L rootContext} {state : BuildState P L Γ}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
    {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
    {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
    {windowOf : Nat → Nat} {roster : List P} {focal : P}
    {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
    {initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState}
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hfallbacks : root.BlockFallbacks binding choice) (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ root.instructions deadlineOf,
      ∀ actor, instruction.submitter = some actor → actor ∈ roster)
    (hreplacement : replacement =
      root.windowedReferencePlayers rootProfile deadlineOf binding choice windowOf focal)
    (blockIndex : Nat) (plan : ApplicationPlan accounted fresh state)
    (profile : SourceBehavioralProfile prog)
    (current : CoupledAt (compileCore prog fresh state).graph state)
    (execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (trace : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) focal
      replacement initial blockIndex plan profile current execution)
    (hcaches : plan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf
      ((root.windowed deadlineOf binding choice windowOf).eraseExecution execution)) :
    let compiled := compileCore prog fresh state
    (((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (List.replicate (plan.instructions deadlineOf).length
        (WindowedApplication.blockInvocations roster)).flatten execution).map fun out =>
          (out.native.application.base.memory.finished compiled.graph.nodeCount,
            compiled.readPublicTerminal? out.native.application.base.memory)) =
      (denoteSource prog profile current.current.source).map fun terminal =>
        (true, some (cast (congrArg (VEnv L)
          (compileCore_terminalCtx_eq_sourceTerminalCtx prog fresh state).symm)
            terminal).erasePubEnv) := by
  dsimp only
  revert blockIndex profile current execution trace hcaches
  induction plan with
  | ret empty fresh state =>
      intro blockIndex profile current execution trace hcaches
      simp only [instructions, List.length_nil, List.replicate_zero, List.flatten_nil,
        MessageApplication.runPolicies, FinDist.map_pure, denoteSource]
      exact congrArg FinDist.pure (Prod.ext
        (current.finished_public_readout _ execution.native.application.base
          trace.checkpoint.refines).1
        (current.finished_public_readout _ execution.native.application.base
          trace.checkpoint.refines).2)
  | sample nextPlan ih =>
      intro blockIndex profile current execution trace hcaches
      simp only [instructions, List.length_cons, List.replicate_succ, List.flatten_cons,
        MessageApplication.runPolicies_append, FinDist.map_bind, denoteSource_sample]
      refine sample_bind nextPlan profile current execution trace hroster _
        (fun env => (denoteSource _ profile.afterSample env).map _) ?_
      intro sourceNext final nextTrace hfull
      apply ih (blockIndex + 1) profile.afterSample sourceNext final nextTrace
      exact trace.checkpoint.block_reference_caches (.sample nextPlan) nextPlan profile
        deadlineOf _ rfl binding choice windowOf roster hroster focal replacement hreplacement
        blockIndex current execution final hcaches hfull
  | @binding Γ pending name owner ty guard tail newName accounted fresh state unrestricted
      nextPlan ih =>
      intro blockIndex profile current execution trace hcaches
      have howner : owner ∈ roster :=
        howners _ (List.mem_of_getElem? (trace.checkpoint.instruction_at _ _ rfl)) owner rfl
      simp only [instructions, List.length_cons, List.replicate_succ, List.flatten_cons,
        MessageApplication.runPolicies_append, FinDist.map_bind, denoteSource_commit]
      refine reference_binding_bind unrestricted nextPlan profile current execution trace
        hfallbacks hinitial hroster howner
        (trace.checkpoint.referenceOwner_of_caches hreplacement hcaches owner) _
        (fun env => (denoteSource _ profile.afterCommit env).map _) ?_
      intro sourceNext final nextTrace hfull
      apply ih (blockIndex + 1) profile.afterCommit sourceNext final nextTrace
      exact trace.checkpoint.block_reference_caches
        (.binding (newName := newName) unrestricted nextPlan) nextPlan profile
        deadlineOf _ rfl binding choice windowOf roster hroster focal replacement hreplacement
        blockIndex current execution final hcaches hfull
  | @publicChoice Γ pending name publicName owner ty guard tail newName unresolved accounted fresh
      state publicGuard nextPlan ih =>
      intro blockIndex profile current execution trace hcaches
      have howner : owner ∈ roster :=
        howners _ (List.mem_of_getElem? (trace.checkpoint.instruction_at _ _ rfl)) owner rfl
      simp only [instructions, List.length_cons, List.replicate_succ, List.flatten_cons,
        MessageApplication.runPolicies_append, FinDist.map_bind, denoteSource_commit,
        denoteSource_reveal, VEnv.cons_get_here]
      refine reference_publicChoice_bind publicGuard nextPlan profile current execution trace
        hfallbacks hinitial hroster howner
        (trace.checkpoint.referenceOwner_of_caches hreplacement hcaches owner) _
        (fun env => (denoteSource _ profile.afterCommit.afterReveal env).map _) ?_
      intro sourceNext final nextTrace hfull
      apply ih (blockIndex + 1) profile.afterCommit.afterReveal sourceNext final nextTrace
      exact trace.checkpoint.block_reference_caches
        (.publicChoice (newName := newName) (unresolved := unresolved) publicGuard nextPlan)
        nextPlan profile deadlineOf _ rfl binding choice windowOf roster hroster focal replacement
        hreplacement blockIndex current execution final hcaches hfull
  | @conditional Γ pending name publicName owner ty guard tail spec unresolved newName accounted
      fresh state publicGuard nextPlan ih =>
      intro blockIndex profile current execution trace hcaches
      have howner : owner ∈ roster :=
        howners _ (List.mem_of_getElem? (trace.checkpoint.instruction_at _ _ rfl)) owner rfl
      simp only [instructions, List.length_cons, List.replicate_succ, List.flatten_cons,
        MessageApplication.runPolicies_append, FinDist.map_bind, denoteSource_commit,
        denoteSource_reveal, VEnv.cons_get_here]
      refine reference_conditional_bind publicGuard nextPlan profile current execution trace
        hinitial horigins hroster howner
        (trace.checkpoint.referenceOwner_of_caches hreplacement hcaches owner) _
        (fun env => (denoteSource _ profile.afterCommit.afterReveal env).map _) ?_
      intro sourceNext final nextTrace hfull
      apply ih (blockIndex + 1) profile.afterCommit.afterReveal sourceNext final nextTrace
      exact trace.checkpoint.block_reference_caches
        (.conditional (newName := newName) (unresolved := unresolved) publicGuard nextPlan)
        nextPlan profile deadlineOf _ rfl binding choice windowOf roster hroster focal replacement
        hreplacement blockIndex current execution final hcaches hfull
  | @conditionalCopy Γ pending name publicName owner ty guard tail spec newName unresolved accounted
      fresh state publicGuard nextPlan ih =>
      intro blockIndex profile current execution trace hcaches
      have howner : owner ∈ roster :=
        howners _ (List.mem_of_getElem? (trace.checkpoint.instruction_at _ _ rfl)) owner rfl
      simp only [instructions, List.length_cons, List.replicate_succ, List.flatten_cons,
        MessageApplication.runPolicies_append, FinDist.map_bind, denoteSource_commit,
        denoteSource_reveal, VEnv.cons_get_here]
      refine reference_conditionalCopy_bind publicGuard nextPlan profile current execution trace
        hinitial horigins hroster howner
        (trace.checkpoint.referenceOwner_of_caches hreplacement hcaches owner) _
        (fun env => (denoteSource _ profile.afterCommit.afterReveal env).map _) ?_
      intro sourceNext final nextTrace hfull
      apply ih (blockIndex + 1) profile.afterCommit.afterReveal sourceNext final nextTrace
      exact trace.checkpoint.block_reference_caches
        (.conditionalCopy (newName := newName) (unresolved := unresolved) spec publicGuard nextPlan)
        nextPlan profile deadlineOf _ rfl binding choice windowOf roster hroster focal replacement
        hreplacement blockIndex current execution final hcaches hfull

end Vegas.ApplicationPlan.WindowedSourcePrefix

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

/-- A checked program's original source profile has exactly the public result
law of its native reference profile under the fixed block service. The player
argument only indexes the proof; no extra player or distinct relay is required. -/
theorem windowed_reference_source_public_law
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
    (((plan.windowed deadlineOf binding choice windowOf).application.runPolicies
      (plan.windowedReferencePlayers profile deadlineOf binding choice windowOf)
      ((plan.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (List.replicate (plan.instructions deadlineOf).length
        (WindowedApplication.blockInvocations roster)).flatten
      (plan.windowedInitialExecution deadlineOf binding choice windowOf)).map fun out =>
        (out.native.application.base.memory.finished (compile source.core).graph.nodeCount,
          (compile source.core).readPublicTerminal? out.native.application.base.memory)) =
      (denoteSource source.core.prog profile source.core.env).map fun terminal =>
        (true, some (cast (congrArg (VEnv L)
          (compileCore_terminalCtx_eq_sourceTerminalCtx source.core.prog source.core.fresh
            (BuildState.fromInitial
              (initialState source.core.Γ source.core.env source.core.wctx))).symm)
            terminal).erasePubEnv) := by
  have hlaw := WindowedSourcePrefix.reference_public_law hinitial horigins hfallbacks hroster
    howners rfl 0 plan profile (compiledInitialCoupled source.core)
    (plan.windowedInitialExecution deadlineOf binding choice windowOf)
    (.initial (WindowedCheckpoint.initial source plan profile deadlineOf binding choice windowOf
      ((plan.windowed deadlineOf binding choice windowOf).blockService roster) focal
      (plan.windowedReferencePlayers profile deadlineOf binding choice windowOf focal)))
    (plan.remainingCachesEmpty_of_empty_histories (plan.image deadlineOf) deadlineOf
      ((plan.windowed deadlineOf binding choice windowOf).eraseExecution
        (plan.windowedInitialExecution deadlineOf binding choice windowOf)) (fun _ => rfl))
  simp only [windowedPlayers, Function.update_eq_self] at hlaw
  exact hlaw

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.WindowedSourcePrefix.reference_public_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedSourcePrefix.reference_public_law

/-- info: 'Vegas.ApplicationPlan.windowed_reference_source_public_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.windowed_reference_source_public_law
