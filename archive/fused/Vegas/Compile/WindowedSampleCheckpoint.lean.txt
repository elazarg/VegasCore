/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedCheckpoint
import Vegas.Compile.WindowedBlockSample
import Vegas.Compile.WindowedSampleCaches
import Vegas.Compile.ApplicationSourcePublicAgreement

/-! # Source chance through an actual generated service block

The source checkpoint supplies the generated instruction, handler lookup,
active address, and service alignment. No chance or completion premise is
added to the native replacement policy.
-/

noncomputable section

namespace Vegas.ApplicationPlan.WindowedCheckpoint

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

variable {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
variable {rootProg : VegasCore P L rootContext}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
variable {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
variable {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
variable {windowOf : Nat → Nat} {roster : List P} {who : P}
variable {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {blockIndex : Nat} {name : VarId} {ty : L.Ty}
variable {dist : L.DistExpr (erasePubVCtx Γ) ty}
variable {tail : VegasCore P L ((name, .pub ty) :: Γ)}
variable {accounted : CommitmentAccounting pending tail}
variable {fresh : FreshBindings (.sample name dist tail)} {state : BuildState P L Γ}

/-- At a source sample checkpoint, the entire generated block has the exact
source chance kernel jointly with the raw policy execution. Every supported
successor refines the corresponding source successor, including after all
remaining relay slots. This is a chance-step law, not yet the whole-program
construction of source strategies at player-owned checkpoints. -/
theorem sample_block
    (nextPlan : ApplicationPlan accounted fresh.2 (state.addSampleEvent name dist fresh.1).1)
    (profile : SourceBehavioralProfile (.sample name dist tail))
    (current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state)
    (execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      who replacement blockIndex (.sample (fresh := fresh) nextPlan) profile current execution) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf who
      replacement
    let before := roster.flatMap (fun actor => [Invocation.player actor, .player actor])
    let suffix := Invocation.environment ::
      roster.flatMap (fun actor => [Invocation.player actor, .environment])
    (runtime.application.runPolicies players (runtime.blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) execution =
      (runtime.application.runPolicies players (runtime.blockEnvironment roster)
        before execution).bind fun middle =>
          (L.evalDist dist current.current.source.eraseSampleEnv).bind fun value =>
            runtime.application.runPolicies players (runtime.blockEnvironment roster) suffix
              (runtime.sampleExecution middle (headSampleCode fresh state) value)) ∧
    ∀ middle ∈ (runtime.application.runPolicies players
        (runtime.blockEnvironment roster) before execution).support,
      ∀ value, value ∈ (L.evalDist dist current.current.source.eraseSampleEnv).support →
        ∃ next : CoupledAt (compileCore (.sample name dist tail) fresh state).graph
            (state.addSampleEvent name dist fresh.1).1,
          next.current.source = current.current.source.cons value ∧
          ∀ final, final ∈ (runtime.application.runPolicies players
              (runtime.blockEnvironment roster) suffix
              (runtime.sampleExecution middle (headSampleCode fresh state) value)).support →
            final.native.application.base.Refines next.current.graph.1 ∧
              final.native.application.FreshActivation := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let code := headSampleCode fresh state
  have hhead : (ApplicationPlan.sample (fresh := fresh) nextPlan).instructions deadlineOf =
      .sample code :: nextPlan.instructions deadlineOf := rfl
  have hindexOriginal := checkpoint.instruction_at (.sample code) _ hhead
  have hmem : .sample code ∈ root.instructions deadlineOf :=
    List.mem_of_getElem? hindexOriginal
  have hlookupOriginal := root.image_lookup_of_mem deadlineOf (.sample code) hmem
  change (root.image deadlineOf).lookup state.nodes.length = some (.sample code)
    at hlookupOriginal
  have hlookup : runtime.image.lookup state.nodes.length = some (.sample code) := by
    simp only [runtime, windowed, ApplicationImage.lookup_withChoiceTimeouts,
      ApplicationImage.lookup_withBindingTimeouts, hlookupOriginal, Option.map_some,
      ApplicationInstruction.withBindingTimeouts, ApplicationInstruction.withChoiceTimeouts]
  have hlength := checkpoint.environmentHistory_length
  have hquotient : execution.environmentHistory.length / (roster.length + 2) = blockIndex := by
    rw [hlength, Nat.mul_div_cancel]
    omega
  have hindex : runtime.image.instructions[execution.environmentHistory.length /
      (roster.length + 2)]? = some (.sample code) := by
    simp only [hquotient, runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts]
  have hactive := checkpoint.activeAddress?_head (.sample code) _ hhead
  exact runtime.runPolicies_full_block_sample_source_coupling roster dist tail fresh state
    current (root.windowedPlayers rootProfile deadlineOf binding choice windowOf who replacement)
    execution hlookup hindex (by rw [hlength]; exact Nat.mul_mod_left _ _)
    hactive checkpoint.refines checkpoint.consistent

/-- An actual chance block reaching a recorded source successor must have drawn
that successor's public value. The witnesses are branches of the real policy
execution, recovered from its exact chance law and shared public readout. -/
theorem sample_block_support_at_source
    (nextPlan : ApplicationPlan accounted fresh.2 (state.addSampleEvent name dist fresh.1).1)
    (profile : SourceBehavioralProfile (.sample name dist tail))
    (current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      who replacement blockIndex (.sample (fresh := fresh) nextPlan) profile current execution)
    (recorded : CoupledAt
      (compileCore tail fresh.2 (state.addSampleEvent name dist fresh.1).1).graph
      (state.addSampleEvent name dist fresh.1).1)
    (value : L.Val ty)
    (hsource : recorded.current.source = current.current.source.cons value)
    (hrefines : final.native.application.base.Refines recorded.current.graph.1)
    (hfinal : final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf who replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).support) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf who
      replacement
    value ∈ (L.evalDist dist current.current.source.eraseSampleEnv).support ∧
      ∃ middle,
        middle ∈ (runtime.application.runPolicies players (runtime.blockEnvironment roster)
          (roster.flatMap fun actor => [Invocation.player actor, .player actor])
          execution).support ∧
        final ∈ (runtime.application.runPolicies players (runtime.blockEnvironment roster)
          (Invocation.environment :: roster.flatMap
            (fun actor => [Invocation.player actor, .environment]))
          (runtime.sampleExecution middle (headSampleCode fresh state) value)).support := by
  obtain ⟨hlaw, hcoupling⟩ := sample_block nextPlan profile current execution checkpoint
  rw [hlaw] at hfinal
  simp only [FinDist.support_bind, Set.mem_iUnion] at hfinal
  obtain ⟨middle, hmiddle, drawn, hdrawn, hsuffix⟩ := hfinal
  obtain ⟨drawnNext, hdrawnSource, hnext⟩ := hcoupling middle hmiddle drawn hdrawn
  have hpublic :
      (compileCore tail fresh.2 (state.addSampleEvent name dist fresh.1).1).graph.fieldRefPublic
        ⟨(state.addSampleEvent name dist fresh.1).1.fieldOf
          (VHasVar.here (x := name) (τ := .pub ty)), ty⟩ := by
    obtain ⟨spec, hfield, htype, howner⟩ :=
      compileCore_fieldOf_spec tail fresh.2 (state.addSampleEvent name dist fresh.1).1
        (VHasVar.here (x := name) (τ := .pub ty))
    exact ⟨spec, hfield, htype, howner⟩
  have hvalue := ApplicationImage.State.publicSourceValue_eq_of_memory_eq
    (leftCurrent := drawnNext.current) (rightCurrent := recorded.current)
    (hnext final hsuffix).1 hrefines rfl VHasVar.here hpublic hpublic
  have heq : drawn = value := by
    simpa only [hdrawnSource, hsource, VEnv.cons_get_here] using hvalue
  subst drawn
  exact ⟨hdrawn, middle, hmiddle, hsuffix⟩

/-- Construct the initialized next checkpoint from the actual chance block's
source coupling, retaining all native histories and future cache invariants. -/
theorem sample_successor
    (nextPlan : ApplicationPlan accounted fresh.2 (state.addSampleEvent name dist fresh.1).1)
    (profile : SourceBehavioralProfile (.sample name dist tail))
    (current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state)
    (execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      who replacement blockIndex (.sample (fresh := fresh) nextPlan) profile current execution)
    (hroster : roster.Nodup)
    (next : CoupledAt (compileCore (.sample name dist tail) fresh state).graph
      (state.addSampleEvent name dist fresh.1).1)
    (final : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hfinal : final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf who replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).support)
    (hrefines : final.native.application.base.Refines next.current.graph.1)
    (hactivation : final.native.application.FreshActivation) :
    WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) who replacement
      (blockIndex + 1) nextPlan profile.afterSample next final := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let code := headSampleCode fresh state
  have hhead : (ApplicationPlan.sample (fresh := fresh) nextPlan).instructions deadlineOf =
      .sample code :: nextPlan.instructions deadlineOf := rfl
  have hindexOriginal := checkpoint.instruction_at (.sample code) _ hhead
  have hlookupOriginal := root.image_lookup_of_mem deadlineOf (.sample code)
    (List.mem_of_getElem? hindexOriginal)
  change (root.image deadlineOf).lookup state.nodes.length = some (.sample code)
    at hlookupOriginal
  have hlookup : runtime.image.lookup code.node = some (.sample code) := by
    change runtime.image.lookup state.nodes.length = some (.sample code)
    simp only [runtime, windowed, ApplicationImage.lookup_withChoiceTimeouts,
      ApplicationImage.lookup_withBindingTimeouts, hlookupOriginal, Option.map_some,
      ApplicationInstruction.withBindingTimeouts, ApplicationInstruction.withChoiceTimeouts]
  have hindex : runtime.image.instructions[blockIndex]? = some (.sample code) := by
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts]
  refine ⟨.sample checkpoint.continuation, ?_, hrefines,
    checkpoint.reached_after_block final hfinal, ?_, hactivation⟩
  · have hcount := checkpoint.blockCount
    rw [hhead, List.length_cons] at hcount
    omega
  · have hfresh : RemainingUnchangedCachesEmpty (root.image deadlineOf) deadlineOf nextPlan who
        (runtime.eraseExecution execution) :=
      (List.forall_cons _ _ _).mp checkpoint.unchangedCaches |>.2
    exact runPolicies_full_sample_block_preserves_unchangedCaches runtime (root.image deadlineOf)
      deadlineOf nextPlan
      roster hroster who
      (fun actor => runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile actor))
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf who replacement)
      (fun actor hactor => by
        simp only [windowedPlayers, Function.update_of_ne hactor, windowedReferencePlayers]
        rfl)
      blockIndex code execution final hlookup hindex
      (fun actor hactor => (checkpoint.historyAlignment hroster actor hactor).1) hfresh hfinal

/-- Every supported complete chance block admits its actual source draw and
an initialized successor checkpoint. The draw is recovered from the exact
joint block law; it is not chosen from an arbitrary refinement witness. -/
theorem sample_block_successor
    (nextPlan : ApplicationPlan accounted fresh.2 (state.addSampleEvent name dist fresh.1).1)
    (profile : SourceBehavioralProfile (.sample name dist tail))
    (current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      who replacement blockIndex (.sample (fresh := fresh) nextPlan) profile current execution)
    (hroster : roster.Nodup)
    (hfinal : final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf who replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).support) :
    ∃ (value : L.Val ty)
      (next : CoupledAt (compileCore (.sample name dist tail) fresh state).graph
        (state.addSampleEvent name dist fresh.1).1),
      value ∈ (L.evalDist dist current.current.source.eraseSampleEnv).support ∧
      next.current.source = current.current.source.cons value ∧
      WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) who replacement
        (blockIndex + 1) nextPlan profile.afterSample next final ∧
      SmallStep ⟨Γ, current.current.source, .sample name dist tail⟩
        ⟨(name, .pub ty) :: Γ, next.current.source, tail⟩ := by
  obtain ⟨hlaw, hcoupling⟩ := sample_block nextPlan profile current execution checkpoint
  have hdecomposed := hfinal
  rw [hlaw] at hdecomposed
  simp only [FinDist.support_bind, Set.mem_iUnion] at hdecomposed
  obtain ⟨middle, hmiddle, value, hvalue, hsuffix⟩ := hdecomposed
  obtain ⟨next, hsource, hnext⟩ := hcoupling middle hmiddle value hvalue
  obtain ⟨hrefines, hfresh⟩ := hnext final hsuffix
  refine ⟨value, next, hvalue, hsource,
    sample_successor nextPlan profile current execution checkpoint hroster next final hfinal
      hrefines hfresh, ?_⟩
  rw [hsource]
  exact .sample dist tail value hvalue

/-- The actual chance block composes with any continuation that agrees at
genuine successor source checkpoints. Player traffic is unrestricted for the
focal principal, and chance retains its source law after marginalizing that
traffic. Cache freshness and initialized reachability of each successor are
proved from the generated block, not supplied by the continuation premise. -/
theorem sample_bind
    (nextPlan : ApplicationPlan accounted fresh.2 (state.addSampleEvent name dist fresh.1).1)
    (profile : SourceBehavioralProfile (.sample name dist tail))
    (current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state)
    (execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      who replacement blockIndex (.sample (fresh := fresh) nextPlan) profile current execution)
    (hroster : roster.Nodup)
    {Ω : Type*}
    (after : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution →
      FinDist Ω)
    (sourceAfter : VEnv L ((name, .pub ty) :: Γ) → FinDist Ω)
    (hafter : ∀ next native,
      WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) who replacement
        (blockIndex + 1) nextPlan profile.afterSample next native →
        after native = sourceAfter next.current.source) :
    (((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf who replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).bind after) =
      (L.evalDist dist current.current.source.eraseSampleEnv).bind
        (fun value => sourceAfter (current.current.source.cons value)) := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf who replacement
  let before := roster.flatMap (fun actor => [Invocation.player actor, .player actor])
  let suffix := Invocation.environment ::
    roster.flatMap (fun actor => [Invocation.player actor, .environment])
  obtain ⟨hrun, hcoupling⟩ := sample_block nextPlan profile current execution checkpoint
  rw [hrun, FinDist.bind_bind]
  calc
    _ = (runtime.application.runPolicies players (runtime.blockEnvironment roster)
        before execution).bind (fun _ =>
          (L.evalDist dist current.current.source.eraseSampleEnv).bind
            (fun value => sourceAfter (current.current.source.cons value))) := by
      apply FinDist.bind_congr
      intro middle hmiddle
      rw [FinDist.bind_bind]
      apply FinDist.bind_congr
      intro value hvalue
      obtain ⟨next, hsource, hrefines⟩ := hcoupling middle hmiddle value hvalue
      calc
        _ = (runtime.application.runPolicies players (runtime.blockEnvironment roster) suffix
            (runtime.sampleExecution middle (headSampleCode fresh state) value)).bind
              (fun _ => sourceAfter (current.current.source.cons value)) := by
          apply FinDist.bind_congr
          intro final hfinal
          have hwhole : final ∈ (runtime.application.runPolicies players
              (runtime.blockEnvironment roster) (WindowedApplication.blockInvocations roster)
              execution).support := by
            apply (congrArg (fun law => final ∈ law.support) hrun).mpr
            simp only [FinDist.support_bind, Set.mem_iUnion]
            exact ⟨middle, hmiddle, value, hvalue, hfinal⟩
          have hnext := sample_successor nextPlan profile current execution checkpoint hroster
            next final hwhole (hrefines final hfinal).1 (hrefines final hfinal).2
          rw [hafter next final hnext, hsource]
        _ = _ := FinDist.bind_const _ _
    _ = _ := FinDist.bind_const _ _

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.sample_block' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.sample_block

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.sample_block_support_at_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.sample_block_support_at_source

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.sample_block_successor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.sample_block_successor

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.sample_bind' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.sample_bind
