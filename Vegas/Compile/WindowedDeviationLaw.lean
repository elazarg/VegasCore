/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockLaw
import Vegas.Compile.WindowedConditionalContinuation
import Vegas.Compile.WindowedFocalBindingLaw
import Vegas.Compile.WindowedFocalPublicLaw

/-! # Sequential source laws for windowed unilateral deviations

The source side uses the original written-order evaluator, changing only the
focal player's policy. The runtime side retains that player's raw commands.
The service fixes polling, inclusion, clock advancement, and relay opportunities;
it does not deliver pending packets to player inboxes.
-/

noncomputable section

namespace Vegas.ApplicationPlan.WindowedSourcePrefix

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The remaining native execution has the original sequential source law
under the checkpoint-extracted focal policy. Completion and the executable
public-terminal readout are observed jointly. -/
theorem pure_deviation_public_law
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
    (hfallbacks : root.BlockFallbacks binding choice)
    (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ root.instructions deadlineOf,
      ∀ actor, instruction.submitter = some actor → actor ∈ roster)
    (command : List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (root.windowed deadlineOf binding choice windowOf).application.View →
        (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (relay : P) (hrelay : relay ∈ roster) (hrelayOther : relay ≠ focal)
    (blockIndex : Nat) (plan : ApplicationPlan accounted fresh state)
    (profile : SourceBehavioralProfile prog)
    (current : CoupledAt (compileCore prog fresh state).graph state)
    (execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (trace : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf roster focal
      replacement initial blockIndex plan profile current execution) :
    let checkpoints : SourcePolicyCheckpoints prog focal :=
      sourcePolicyCheckpointsFrom root rootProfile deadlineOf binding choice
      windowOf roster focal replacement initial hinitial horigins hroster howners command hpure
      relay hrelay hrelayOther blockIndex plan profile
    let sourceProfile := Profile.update (sig := sourceGameSignature prog) profile focal
      (SourcePolicyCheckpoints.extend checkpoints (profile focal))
    let compiled := compileCore prog fresh state
    (((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (List.replicate (plan.instructions deadlineOf).length
        (WindowedApplication.blockInvocations roster)).flatten execution).map fun out =>
          (out.native.application.base.memory.finished compiled.graph.nodeCount,
            compiled.readPublicTerminal? out.native.application.base.memory)) =
      (denoteSource prog sourceProfile current.current.source).map fun terminal =>
        (true, some (cast (congrArg (VEnv L)
          (compileCore_terminalCtx_eq_sourceTerminalCtx prog fresh state).symm)
            terminal).erasePubEnv) := by
  dsimp only
  revert blockIndex profile current execution trace
  induction plan with
  | ret empty fresh state =>
      intro blockIndex profile current execution trace
      simp only [instructions, List.length_nil, List.replicate_zero, List.flatten_nil,
        MessageApplication.runPolicies, FinDist.map_pure, denoteSource]
      exact congrArg FinDist.pure (Prod.ext
        (current.finished_public_readout _ execution.native.application.base
          trace.checkpoint.refines).1
        (current.finished_public_readout _ execution.native.application.base
          trace.checkpoint.refines).2)
  | sample nextPlan ih =>
      intro blockIndex profile current execution trace
      let child : SourcePolicyCheckpoints _ focal := sourcePolicyCheckpointsFrom
        root rootProfile deadlineOf binding choice windowOf roster focal replacement initial
        hinitial horigins hroster howners command hpure relay hrelay hrelayOther
        (blockIndex + 1) nextPlan profile.afterSample
      let childProfile : SourceBehavioralProfile _ :=
        Profile.update (sig := sourceGameSignature _) profile.afterSample focal
          (SourcePolicyCheckpoints.extend child (profile.afterSample focal))
      simp only [instructions, List.length_cons, List.replicate_succ, List.flatten_cons,
        MessageApplication.runPolicies_append, FinDist.map_bind, denoteSource_sample,
        sourcePolicyCheckpointsFrom, SourcePolicyCheckpoints.update_extend_afterSample]
      refine sample_bind nextPlan profile current execution trace hroster _
        (fun env => (denoteSource _ childProfile env).map _) ?_
      intro sourceNext final nextTrace
      exact ih (blockIndex + 1) profile.afterSample sourceNext final nextTrace
  | @binding Γ pending name owner ty guard tail newName accounted fresh state unrestricted
      nextPlan ih =>
      intro blockIndex profile current execution trace
      let child : SourcePolicyCheckpoints tail focal := sourcePolicyCheckpointsFrom
        root rootProfile deadlineOf binding choice windowOf roster focal replacement initial
        hinitial horigins hroster howners command hpure relay hrelay hrelayOther
        (blockIndex + 1) nextPlan profile.afterCommit
      let childProfile : SourceBehavioralProfile tail :=
        Profile.update (sig := sourceGameSignature tail) profile.afterCommit focal
          (SourcePolicyCheckpoints.extend child (profile.afterCommit focal))
      have hownerRoster : owner ∈ roster :=
        howners _ (List.mem_of_getElem? (trace.checkpoint.instruction_at _ _ rfl)) owner rfl
      by_cases howner : owner = focal
      · subst owner
        simp only [instructions, List.length_cons, List.replicate_succ, List.flatten_cons,
          MessageApplication.runPolicies_append, FinDist.map_bind, denoteSource_commit,
          sourcePolicyCheckpointsFrom, dite_true,
          SourcePolicyCheckpoints.update_ownedCommit_afterCommit,
          SourcePolicyCheckpoints.update_ownedCommit_here]
        obtain ⟨fallback, deadline, hselect⟩ :=
          (trace.checkpoint.continuation.blockFallbacks binding choice hfallbacks).1
        obtain ⟨anchorFinal, hanchor⟩ := ((root.windowed deadlineOf binding choice windowOf)
          |>.application.runPolicies
            (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
            ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
            (WindowedApplication.blockInvocations roster) execution).support_nonempty
        let anchor : BindingDecision (newName := newName) (fresh := fresh)
            root rootProfile deadlineOf binding choice windowOf roster focal replacement initial
            blockIndex unrestricted nextPlan profile :=
          ⟨current, execution, anchorFinal, trace, fallback, deadline, hselect, hanchor⟩
        refine BindingDecision.continuation_bind hinitial horigins hroster howners command hpure
          hrelay hrelayOther anchor _ (fun env => (denoteSource _ childProfile env).map _) ?_
        intro sourceNext final nextTrace
        exact ih (blockIndex + 1) profile.afterCommit sourceNext final nextTrace
      · simp only [instructions, List.length_cons, List.replicate_succ, List.flatten_cons,
          MessageApplication.runPolicies_append, FinDist.map_bind, denoteSource_commit,
          sourcePolicyCheckpointsFrom, dif_neg howner,
          SourcePolicyCheckpoints.update_otherCommit_afterCommit,
          SourcePolicyCheckpoints.update_otherCommit_here]
        refine unchanged_binding_bind unrestricted nextPlan profile current execution trace
          hfallbacks hinitial hroster hownerRoster howner _
          (fun env => (denoteSource _ childProfile env).map _) ?_
        intro sourceNext final nextTrace
        exact ih (blockIndex + 1) profile.afterCommit sourceNext final nextTrace
  | @publicChoice Γ pending name publicName owner ty guard tail newName unresolved accounted fresh
      state publicGuard nextPlan ih =>
      intro blockIndex profile current execution trace
      let child : SourcePolicyCheckpoints tail focal := sourcePolicyCheckpointsFrom
        root rootProfile deadlineOf binding choice windowOf roster focal replacement initial
        hinitial horigins hroster howners command hpure relay hrelay hrelayOther
        (blockIndex + 1) nextPlan profile.afterCommit.afterReveal
      let childProfile : SourceBehavioralProfile tail :=
        Profile.update (sig := sourceGameSignature tail) profile.afterCommit.afterReveal focal
          (SourcePolicyCheckpoints.extend child (profile.afterCommit.afterReveal focal))
      have hownerRoster : owner ∈ roster :=
        howners _ (List.mem_of_getElem? (trace.checkpoint.instruction_at _ _ rfl)) owner rfl
      by_cases howner : owner = focal
      · subst owner
        simp only [instructions, List.length_cons, List.replicate_succ, List.flatten_cons,
          MessageApplication.runPolicies_append, FinDist.map_bind, denoteSource_commit,
          denoteSource_reveal, VEnv.cons_get_here,
          sourcePolicyCheckpointsFrom, dite_true,
          SourcePolicyCheckpoints.update_ownedCommit_afterCommit,
          SourcePolicyCheckpoints.update_extend_afterReveal,
          SourcePolicyCheckpoints.update_ownedCommit_here]
        refine PublicDecision.continuation_bind_of_successors (nextPlan := nextPlan)
          hinitial horigins hroster howners command hpure
          (.publicChoice
            ((PublicChoiceSite.atHead name publicName focal guard tail).code fresh state))
          (nextPlan.instructions deadlineOf) rfl rfl
          current execution trace _ (fun env => (denoteSource _ childProfile env).map _) ?_ ?_
        · intro final hfinal
          obtain ⟨fallback, deadline, hselect⟩ :=
            (trace.checkpoint.continuation.blockFallbacks binding choice hfallbacks).1
          obtain ⟨value, sourceNext, hsource, hlegal, _, hnext, _⟩ :=
            trace.checkpoint.publicChoice_block publicGuard nextPlan profile fallback deadline
              hselect current execution final hroster relay hrelay hrelayOther hfinal
          exact ⟨value, hlegal, sourceNext, hsource, hnext.refines,
            .step trace hfinal (.publicChoice value hsource hlegal) hnext⟩
        · intro sourceNext final nextTrace
          exact ih (blockIndex + 1) profile.afterCommit.afterReveal sourceNext final nextTrace
      · simp only [instructions, List.length_cons, List.replicate_succ, List.flatten_cons,
          MessageApplication.runPolicies_append, FinDist.map_bind, denoteSource_commit,
          denoteSource_reveal, VEnv.cons_get_here,
          sourcePolicyCheckpointsFrom, dif_neg howner,
          SourcePolicyCheckpoints.update_otherCommit_afterCommit,
          SourcePolicyCheckpoints.update_extend_afterReveal,
          SourcePolicyCheckpoints.update_otherCommit_here]
        refine unchanged_publicChoice_bind publicGuard nextPlan profile current execution trace
          hfallbacks hinitial hroster hownerRoster howner _
          (fun env => (denoteSource _ childProfile env).map _) ?_
        intro sourceNext final nextTrace
        exact ih (blockIndex + 1) profile.afterCommit.afterReveal sourceNext final nextTrace
  | @conditional Γ pending name publicName owner ty guard tail spec unresolved newName accounted
      fresh state publicGuard nextPlan ih =>
      intro blockIndex profile current execution trace
      let child : SourcePolicyCheckpoints tail focal := sourcePolicyCheckpointsFrom
        root rootProfile deadlineOf binding choice windowOf roster focal replacement initial
        hinitial horigins hroster howners command hpure relay hrelay hrelayOther
        (blockIndex + 1) nextPlan profile.afterCommit.afterReveal
      let childProfile : SourceBehavioralProfile tail :=
        Profile.update (sig := sourceGameSignature tail) profile.afterCommit.afterReveal focal
          (SourcePolicyCheckpoints.extend child (profile.afterCommit.afterReveal focal))
      have hownerRoster : owner ∈ roster :=
        howners _ (List.mem_of_getElem? (trace.checkpoint.instruction_at _ _ rfl)) owner rfl
      by_cases howner : owner = focal
      · subst owner
        simp only [instructions, List.length_cons, List.replicate_succ, List.flatten_cons,
          MessageApplication.runPolicies_append, FinDist.map_bind, denoteSource_commit,
          denoteSource_reveal, VEnv.cons_get_here,
          sourcePolicyCheckpointsFrom, dite_true,
          SourcePolicyCheckpoints.update_ownedCommit_afterCommit,
          SourcePolicyCheckpoints.update_extend_afterReveal,
          SourcePolicyCheckpoints.update_ownedCommit_here]
        let site := ConditionalPublicationSite.atHead name publicName focal guard tail spec
        refine PublicDecision.continuation_bind_of_successors (nextPlan := nextPlan)
          hinitial horigins hroster howners command hpure
          (.conditional (site.code fresh state (site.sourceField fresh state)
            (deadlineOf (site.choice.publicationNode fresh state))))
          (nextPlan.instructions deadlineOf) rfl rfl
          current execution trace _ (fun env => (denoteSource _ childProfile env).map _) ?_ ?_
        · intro final hfinal
          obtain ⟨result, sourceNext, hadmissible, hsource, hlegal, _, hnext, _⟩ :=
            trace.checkpoint.conditional_block publicGuard nextPlan profile horigins current
              execution final hroster relay hrelay hrelayOther hfinal
          exact ⟨spec.encoding.symm result, hlegal, sourceNext, hsource, hnext.refines,
            .step trace hfinal (.conditional result hadmissible hsource hlegal) hnext⟩
        · intro sourceNext final nextTrace
          exact ih (blockIndex + 1) profile.afterCommit.afterReveal sourceNext final nextTrace
      · simp only [instructions, List.length_cons, List.replicate_succ, List.flatten_cons,
          MessageApplication.runPolicies_append, FinDist.map_bind, denoteSource_commit,
          denoteSource_reveal, VEnv.cons_get_here,
          sourcePolicyCheckpointsFrom, dif_neg howner,
          SourcePolicyCheckpoints.update_otherCommit_afterCommit,
          SourcePolicyCheckpoints.update_extend_afterReveal,
          SourcePolicyCheckpoints.update_otherCommit_here]
        refine unchanged_conditional_bind publicGuard nextPlan profile current execution trace
          hinitial horigins hroster hownerRoster howner _
          (fun env => (denoteSource _ childProfile env).map _) ?_
        intro sourceNext final nextTrace
        exact ih (blockIndex + 1) profile.afterCommit.afterReveal sourceNext final nextTrace
  | @conditionalCopy Γ pending name publicName owner ty guard tail spec newName unresolved accounted
      fresh state publicGuard nextPlan ih =>
      intro blockIndex profile current execution trace
      let child : SourcePolicyCheckpoints tail focal := sourcePolicyCheckpointsFrom
        root rootProfile deadlineOf binding choice windowOf roster focal replacement initial
        hinitial horigins hroster howners command hpure relay hrelay hrelayOther
        (blockIndex + 1) nextPlan profile.afterCommit.afterReveal
      let childProfile : SourceBehavioralProfile tail :=
        Profile.update (sig := sourceGameSignature tail) profile.afterCommit.afterReveal focal
          (SourcePolicyCheckpoints.extend child (profile.afterCommit.afterReveal focal))
      have hownerRoster : owner ∈ roster :=
        howners _ (List.mem_of_getElem? (trace.checkpoint.instruction_at _ _ rfl)) owner rfl
      by_cases howner : owner = focal
      · subst owner
        simp only [instructions, List.length_cons, List.replicate_succ, List.flatten_cons,
          MessageApplication.runPolicies_append, FinDist.map_bind, denoteSource_commit,
          denoteSource_reveal, VEnv.cons_get_here,
          sourcePolicyCheckpointsFrom, dite_true,
          SourcePolicyCheckpoints.update_ownedCommit_afterCommit,
          SourcePolicyCheckpoints.update_extend_afterReveal,
          SourcePolicyCheckpoints.update_ownedCommit_here]
        let site := ConditionalPublicationSite.atHead name publicName focal guard tail spec
        refine PublicDecision.continuation_bind_of_successors (nextPlan := nextPlan)
          hinitial horigins hroster howners command hpure
          (.conditional (site.code fresh state (site.sourceField fresh state)
            (deadlineOf (site.choice.publicationNode fresh state))))
          (nextPlan.instructions deadlineOf) rfl rfl
          current execution trace _ (fun env => (denoteSource _ childProfile env).map _) ?_ ?_
        · intro final hfinal
          obtain ⟨result, sourceNext, hadmissible, hsource, hlegal, _, hnext, _⟩ :=
            trace.checkpoint.conditionalCopy_block publicGuard nextPlan profile horigins current
              execution final hroster relay hrelay hrelayOther hfinal
          exact ⟨spec.encoding.symm result, hlegal, sourceNext, hsource, hnext.refines,
            .step trace hfinal (.conditionalCopy result hadmissible hsource hlegal) hnext⟩
        · intro sourceNext final nextTrace
          exact ih (blockIndex + 1) profile.afterCommit.afterReveal sourceNext final nextTrace
      · simp only [instructions, List.length_cons, List.replicate_succ, List.flatten_cons,
          MessageApplication.runPolicies_append, FinDist.map_bind, denoteSource_commit,
          denoteSource_reveal, VEnv.cons_get_here,
          sourcePolicyCheckpointsFrom, dif_neg howner,
          SourcePolicyCheckpoints.update_otherCommit_afterCommit,
          SourcePolicyCheckpoints.update_extend_afterReveal,
          SourcePolicyCheckpoints.update_otherCommit_here]
        refine unchanged_conditionalCopy_bind publicGuard nextPlan profile current execution trace
          hinitial horigins hroster hownerRoster howner _
          (fun env => (denoteSource _ childProfile env).map _) ?_
        intro sourceNext final nextTrace
        exact ih (blockIndex + 1) profile.afterCommit.afterReveal sourceNext final nextTrace

end Vegas.ApplicationPlan.WindowedSourcePrefix

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory GameTheory.Math.Probability

/-- From a checked source program to its initialized windowed runtime: every
pure unilateral raw-command policy has exactly the public outcome law of the
extracted legal source deviation against the original opponents. The fixed
block service finishes; no conditioning on successful runs is used. -/
theorem windowed_pure_deviation_source_public_law
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
    (command : List (plan.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (plan.windowed deadlineOf binding choice windowOf).application.View →
        (plan.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (relay : P) (hrelay : relay ∈ roster) (hrelayOther : relay ≠ focal) :
    let replacement := fun history view => FinDist.pure (command history view)
    let sourceReplacement : SourceBehavioralPolicy source.core.prog focal :=
      plan.extractedSourcePolicy profile deadlineOf binding choice windowOf
      roster focal replacement (compiledInitialCoupled source.core) hinitial horigins hroster
      howners command rfl relay hrelay hrelayOther
    (((plan.windowed deadlineOf binding choice windowOf).application.runPolicies
      (plan.windowedPlayers profile deadlineOf binding choice windowOf focal replacement)
      ((plan.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (List.replicate (plan.instructions deadlineOf).length
        (WindowedApplication.blockInvocations roster)).flatten
      (plan.windowedInitialExecution deadlineOf binding choice windowOf)).map fun out =>
        (out.native.application.base.memory.finished (compile source.core).graph.nodeCount,
          (compile source.core).readPublicTerminal? out.native.application.base.memory)) =
      (denoteSource source.core.prog
        (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
          sourceReplacement) source.core.env).map fun terminal =>
        (true, some (cast (congrArg (VEnv L)
          (compileCore_terminalCtx_eq_sourceTerminalCtx source.core.prog source.core.fresh
            (BuildState.fromInitial
              (initialState source.core.Γ source.core.env source.core.wctx))).symm)
            terminal).erasePubEnv) := by
  dsimp only
  exact WindowedSourcePrefix.pure_deviation_public_law hinitial horigins hfallbacks hroster
    howners command rfl relay hrelay hrelayOther 0 plan profile (compiledInitialCoupled source.core)
    (plan.windowedInitialExecution deadlineOf binding choice windowOf)
    (.initial (WindowedCheckpoint.initial source plan profile deadlineOf binding choice windowOf
      roster focal (fun history view => FinDist.pure (command history view))))

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.WindowedSourcePrefix.pure_deviation_public_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedSourcePrefix.pure_deviation_public_law

/-- info: 'Vegas.ApplicationPlan.windowed_pure_deviation_source_public_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.windowed_pure_deviation_source_public_law
