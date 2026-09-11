/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedSourcePrefix

/-! # Coverage of actual windowed block prefixes

Every supported complete-block prefix of the fixed emitted service has a
canonical sequential source witness. Timeout certificates are checked against the source, and the
roster contains an unchanged relay. The replacement policy is unrestricted,
including randomized raw commands. Coverage asserts neither source-policy
reconstruction nor equality of probability laws.
-/

noncomputable section

namespace Vegas.ApplicationPlan.WindowedSourcePrefix

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
variable {rootProg : VegasCore P L rootContext} {prog : VegasCore P L Γ}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {accounted : CommitmentAccounting pending prog}
variable {rootFresh : FreshBindings rootProg} {fresh : FreshBindings prog}
variable {rootState : BuildState P L rootContext} {state : BuildState P L Γ}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
variable {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
variable {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
variable {windowOf : Nat → Nat} {roster : List P} {focal : P}
variable {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState}
variable {blockIndex : Nat} {plan : ApplicationPlan accounted fresh state}
variable {profile : SourceBehavioralProfile prog}
variable {current : CoupledAt (compileCore prog fresh state).graph state}
variable {execution :
  (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}

/-- One more actual block extends the source witness for every emitted
instruction kind. No settlement or accepted-message premise is imposed on the
runtime execution; those facts follow from the service and source fallbacks. -/
theorem extend
    (trace : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf roster focal
      replacement initial blockIndex plan profile current execution)
    (hfallbacks : root.BlockFallbacks binding choice)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup) (relay : P) (hrelay : relay ∈ roster) (hunchanged : relay ≠ focal)
    (hremaining : 0 < (plan.instructions deadlineOf).length)
    (final : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hfinal : final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).support) :
    ∃ (Δ : VCtx P L) (nextPending : Finset VarId) (nextProg : VegasCore P L Δ)
      (nextAccounted : CommitmentAccounting nextPending nextProg)
      (nextFresh : FreshBindings nextProg) (nextState : BuildState P L Δ)
      (nextPlan : ApplicationPlan nextAccounted nextFresh nextState)
      (nextProfile : SourceBehavioralProfile nextProg)
      (sourceNext : CoupledAt (compileCore nextProg nextFresh nextState).graph nextState),
      WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf roster focal
        replacement initial (blockIndex + 1) nextPlan nextProfile sourceNext final := by
  have checkpoint := trace.checkpoint
  have hlocal := checkpoint.continuation.blockFallbacks binding choice hfallbacks
  have hrelayReference :
      root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement relay =
        root.windowedReferencePlayers rootProfile deadlineOf binding choice windowOf relay := by
    simp only [windowedPlayers, Function.update_of_ne hunchanged]
  cases plan with
  | ret => simp only [ApplicationPlan.instructions, List.length_nil] at hremaining; omega
  | sample nextPlan =>
      obtain ⟨value, sourceNext, hdraw, hsource, hnext, _⟩ :=
        WindowedCheckpoint.sample_block_successor nextPlan profile current execution final
          checkpoint hroster hfinal
      refine ⟨_, _, _, _, _, _, nextPlan, profile.afterSample, sourceNext, ?_⟩
      exact .step trace hfinal (.sample value hdraw hsource) hnext
  | binding unrestricted nextPlan =>
      obtain ⟨fallback, deadline, hselect⟩ := hlocal.1
      obtain ⟨value, sourceNext, hsource, hnext, hresolved, _, _⟩ :=
        WindowedCheckpoint.binding_block unrestricted nextPlan profile fallback deadline hselect
          current execution final checkpoint hroster relay hrelay hrelayReference hfinal
      refine ⟨_, _, _, _, _, _, nextPlan, profile.afterCommit, sourceNext, ?_⟩
      exact .step trace hfinal (.binding fallback deadline hselect value hsource hresolved) hnext
  | publicChoice publicGuard nextPlan =>
      obtain ⟨fallback, deadline, hselect⟩ := hlocal.1
      obtain ⟨value, sourceNext, hsource, hlegal, _, hnext, _⟩ :=
        WindowedCheckpoint.publicChoice_block publicGuard nextPlan profile fallback deadline hselect
          current
          execution final checkpoint hroster relay hrelay hrelayReference hfinal
      refine ⟨_, _, _, _, _, _, nextPlan, profile.afterCommit.afterReveal, sourceNext, ?_⟩
      exact .step trace hfinal (.publicChoice value hsource hlegal) hnext
  | conditional publicGuard nextPlan =>
      obtain ⟨result, sourceNext, hadmissible, hsource, hlegal, _, hnext, _⟩ :=
        WindowedCheckpoint.conditional_block publicGuard nextPlan profile horigins current execution
          final checkpoint hroster relay hrelay hrelayReference hfinal
      refine ⟨_, _, _, _, _, _, nextPlan, profile.afterCommit.afterReveal, sourceNext, ?_⟩
      exact .step trace hfinal (.conditional result hadmissible hsource hlegal) hnext
  | conditionalCopy spec publicGuard nextPlan =>
      obtain ⟨result, sourceNext, hadmissible, hsource, hlegal, _, hnext, _⟩ :=
        WindowedCheckpoint.conditionalCopy_block publicGuard nextPlan profile horigins current
          execution final checkpoint hroster relay hrelay hrelayReference hfinal
      refine ⟨_, _, _, _, _, _, nextPlan, profile.afterCommit.afterReveal, sourceNext, ?_⟩
      exact .step trace hfinal (.conditionalCopy result hadmissible hsource hlegal) hnext

/-- All supported initialized block prefixes, up to the emitted instruction
count, have canonical source evidence. In particular, the prefix carrier does
not filter runtime deviations by assuming an already-selected source action. -/
theorem covers
    (hinitial : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement 0 root rootProfile initial
        (root.windowedInitialExecution deadlineOf binding choice windowOf))
    (hfallbacks : root.BlockFallbacks binding choice)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup) (relay : P) (hrelay : relay ∈ roster) (hunchanged : relay ≠ focal)
    (blocks : Nat) (hblocks : blocks ≤ (root.instructions deadlineOf).length)
    (final : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hfinal : final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (List.replicate blocks (WindowedApplication.blockInvocations roster)).flatten
      (root.windowedInitialExecution deadlineOf binding choice windowOf)).support) :
    ∃ (Δ : VCtx P L) (nextPending : Finset VarId) (nextProg : VegasCore P L Δ)
      (nextAccounted : CommitmentAccounting nextPending nextProg)
      (nextFresh : FreshBindings nextProg) (nextState : BuildState P L Δ)
      (nextPlan : ApplicationPlan nextAccounted nextFresh nextState)
      (nextProfile : SourceBehavioralProfile nextProg)
      (sourceNext : CoupledAt (compileCore nextProg nextFresh nextState).graph nextState),
      WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf roster focal
        replacement initial blocks nextPlan nextProfile sourceNext final := by
  induction blocks generalizing final with
  | zero =>
      have heq : final = root.windowedInitialExecution deadlineOf binding choice windowOf := by
        simpa only [List.replicate_zero, List.flatten_nil, MessageApplication.runPolicies,
          FinDist.mem_support_pure] using hfinal
      subst final
      exact ⟨_, _, _, _, _, _, root, rootProfile, initial, .initial hinitial⟩
  | succ blocks ih =>
      rw [List.replicate_succ', List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, MessageApplication.runPolicies_append, FinDist.support_bind] at hfinal
      simp only [Set.mem_iUnion] at hfinal
      obtain ⟨before, hbefore, hblock⟩ := hfinal
      obtain ⟨Δ, nextPending, nextProg, nextAccounted, nextFresh, nextState,
          nextPlan, nextProfile, sourceNext, trace⟩ := ih (by omega) before hbefore
      have hcount := trace.checkpoint.blockCount
      exact trace.extend hfallbacks horigins hroster relay hrelay hunchanged (by omega) final hblock

/-- The full emitted block count reaches a terminal sequential source state
and finishes the native graph. The source witness is the canonical prefix
constructed from these actual blocks, not a reconstruction from an arbitrary
terminal graph configuration. -/
theorem terminates
    (hinitial : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement 0 root rootProfile initial
        (root.windowedInitialExecution deadlineOf binding choice windowOf))
    (hfallbacks : root.BlockFallbacks binding choice)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup) (relay : P) (hrelay : relay ∈ roster) (hunchanged : relay ≠ focal)
    (final : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hfinal : final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (List.replicate (root.instructions deadlineOf).length
        (WindowedApplication.blockInvocations roster)).flatten
      (root.windowedInitialExecution deadlineOf binding choice windowOf)).support) :
    (∃ terminal : SourceConfig P L,
      SmallStep.Star ⟨rootContext, initial.current.source, rootProg⟩ terminal ∧
        terminal.IsTerminal) ∧
      final.native.application.base.memory.finished
        (compileCore rootProg rootFresh rootState).graph.nodeCount = true := by
  obtain ⟨Δ, nextPending, nextProg, nextAccounted, nextFresh, nextState,
      nextPlan, nextProfile, sourceNext, trace⟩ :=
    covers hinitial hfallbacks horigins hroster relay hrelay hunchanged _
      (Nat.le_refl _) final hfinal
  have checkpoint := trace.checkpoint
  have hcount := checkpoint.blockCount
  have hempty : (nextPlan.instructions deadlineOf).length = 0 := by omega
  cases nextPlan with
  | ret empty fresh state =>
      refine ⟨⟨_, trace.source_steps, ⟨_, rfl⟩⟩, ?_⟩
      rw [checkpoint.continuation.compile_eq]
      exact (sourceNext.finished_public_readout _ final.native.application.base
        checkpoint.refines).1
  | sample next => simp only [ApplicationPlan.instructions, List.length_cons] at hempty; omega
  | binding unrestricted next =>
      simp only [ApplicationPlan.instructions, List.length_cons] at hempty; omega
  | publicChoice publicGuard next =>
      simp only [ApplicationPlan.instructions, List.length_cons] at hempty; omega
  | conditional publicGuard next =>
      simp only [ApplicationPlan.instructions, List.length_cons] at hempty; omega
  | conditionalCopy spec publicGuard next =>
      simp only [ApplicationPlan.instructions, List.length_cons] at hempty; omega

end Vegas.ApplicationPlan.WindowedSourcePrefix

/-- info: 'Vegas.ApplicationPlan.WindowedSourcePrefix.covers' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedSourcePrefix.covers

/-- info: 'Vegas.ApplicationPlan.WindowedSourcePrefix.terminates' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedSourcePrefix.terminates
