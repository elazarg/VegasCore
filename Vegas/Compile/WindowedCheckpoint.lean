/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationForwardCheckpoint
import Vegas.Compile.ApplicationOrderCheckpoint
import Vegas.Compile.WindowedBlockAlignment
import Vegas.Compile.WindowedActivationFreshness
import Vegas.Compile.WindowedBlockService
import Vegas.Compile.WindowedPolicyProjection
import Vegas.Compile.WindowedSourceSafety
import Vegas.Compile.WindowedBlockProvenance
import Interaction.MessageApplicationCounters

/-! # Actual windowed source checkpoints

This is a proof certificate over the single emitted windowed interpreter. It
indexes an actual repeated-block policy prefix by the source suffix which that
prefix represents. No paired execution or information-equivalence claim is
stored in the certificate.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Future caches belonging to unchanged owners remain fresh. The focal raw
replacement is intentionally unrestricted and may submit an anticipatory
payload for one of its own later instructions. -/
def RemainingUnchangedCachesEmpty
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    (plan : ApplicationPlan accounted fresh state) (focal : P)
    (execution : image.application.PolicyExecution) : Prop :=
  (plan.instructions deadlineOf).Forall fun instruction =>
    instruction.submitter = some focal ∨ instruction.CacheEmpty image execution

def windowedInitialExecution
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (root : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) :
    (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution :=
  let runtime := root.windowed deadlineOf binding choice windowOf
  PolicyExecution.initial runtime.application
    (MessageApplication.State.initial runtime.application
      (runtime.initial
        (ApplicationImage.State.initial
          (ApplicationImage.Memory.initial (compileCore prog fresh state).graph))))

def windowedReferencePlayers
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (root : ApplicationPlan accounted fresh state)
    (rootProfile : SourceBehavioralProfile prog) (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) :
    P → (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy :=
  let runtime := root.windowed deadlineOf binding choice windowOf
  fun actor => runtime.blockPlayer actor
    (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile actor))

def windowedPlayers
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (root : ApplicationPlan accounted fresh state)
    (rootProfile : SourceBehavioralProfile prog) (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (who : P)
    (replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy) :
    P → (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy :=
  Function.update
    (root.windowedReferencePlayers rootProfile deadlineOf binding choice windowOf)
    who replacement

structure WindowedCheckpoint
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext} {prog : VegasCore P L Γ}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {accounted : CommitmentAccounting pending prog}
    {rootFresh : FreshBindings rootProg} {fresh : FreshBindings prog}
    {rootState : BuildState P L rootContext} {state : BuildState P L Γ}
    (root : ApplicationPlan rootAccounted rootFresh rootState)
    (rootProfile : SourceBehavioralProfile rootProg)
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (roster : List P) (who : P)
    (replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (blockIndex : Nat) (plan : ApplicationPlan accounted fresh state)
    (profile : SourceBehavioralProfile prog)
    (current : CoupledAt (compileCore prog fresh state).graph state)
    (execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution) :
    Prop where
  continuation : ProfileContinuation root rootProfile plan profile
  blockCount : blockIndex + (plan.instructions deadlineOf).length =
    (root.instructions deadlineOf).length
  refines : execution.native.application.base.Refines current.current.graph.1
  reached : execution ∈
    ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf who replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (List.replicate blockIndex
        (WindowedApplication.blockInvocations roster)).flatten
      (root.windowedInitialExecution deadlineOf binding choice windowOf)).support
  unchangedCaches : RemainingUnchangedCachesEmpty (root.image deadlineOf) deadlineOf
    plan who ((root.windowed deadlineOf binding choice windowOf).eraseExecution execution)
  activationFresh : execution.native.application.FreshActivation

namespace WindowedCheckpoint

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
variable {windowOf : Nat → Nat} {roster : List P} {who : P}
variable {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {blockIndex : Nat} {plan : ApplicationPlan accounted fresh state}
variable {profile : SourceBehavioralProfile prog}
variable {current : CoupledAt (compileCore prog fresh state).graph state}
variable {execution :
  (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}

/-- Reference-policy behavior and fresh future caches for one owner. This
certificate applies both to an unchanged opponent and to an honest player at
the distinguished coordinate. -/
structure ReferenceOwner
    (_checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      who replacement blockIndex plan profile current execution) (owner : P) : Prop where
  policy : root.windowedPlayers rootProfile deadlineOf binding choice windowOf who replacement
    owner = root.windowedReferencePlayers rootProfile deadlineOf binding choice windowOf owner
  caches : ∀ instruction ∈ plan.instructions deadlineOf,
    instruction.submitter = some owner → instruction.CacheEmpty (root.image deadlineOf)
      ((root.windowed deadlineOf binding choice windowOf).eraseExecution execution)

/-- Every unchanged owner has the reference policy and fresh owned caches. -/
theorem referenceOwner_of_ne
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      who replacement blockIndex plan profile current execution)
    (owner : P) (hother : owner ≠ who) : checkpoint.ReferenceOwner owner := by
  refine ⟨by simp only [windowedPlayers, Function.update_of_ne hother], ?_⟩
  intro instruction hinstruction howner
  have hcache := List.forall_iff_forall_mem.mp checkpoint.unchangedCaches instruction hinstruction
  exact hcache.resolve_left (fun heq => hother (Option.some.inj (howner.symm.trans heq)))

/-- Full reference execution supplies the owner certificate at every player,
including the distinguished coordinate. -/
theorem referenceOwner_of_caches
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      who replacement blockIndex plan profile current execution)
    (hreplacement : replacement =
      root.windowedReferencePlayers rootProfile deadlineOf binding choice windowOf who)
    (hcaches : plan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf
      ((root.windowed deadlineOf binding choice windowOf).eraseExecution execution))
    (owner : P) : checkpoint.ReferenceOwner owner := by
  refine ⟨by simp only [windowedPlayers, hreplacement, Function.update_eq_self], ?_⟩
  intro instruction hinstruction _
  exact List.forall_iff_forall_mem.mp hcaches instruction hinstruction

/-- The reference owner's current head cache is fresh. -/
theorem ReferenceOwner.head_cacheEmpty
    {checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      who replacement blockIndex plan profile current execution}
    {owner : P} (reference : checkpoint.ReferenceOwner owner)
    (instruction : ApplicationInstruction P L) (rest : List (ApplicationInstruction P L))
    (hhead : plan.instructions deadlineOf = instruction :: rest)
    (howner : instruction.submitter = some owner) :
    instruction.CacheEmpty (root.image deadlineOf)
      ((root.windowed deadlineOf binding choice windowOf).eraseExecution execution) :=
  reference.caches instruction (by rw [hhead]; exact List.mem_cons_self) howner

/-- The head cache is fresh when its submitter is not the replaced player.
The instruction may be any emitted application instruction. -/
theorem head_cacheEmpty (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding
    choice windowOf roster who replacement blockIndex plan profile current execution)
    (instruction : ApplicationInstruction P L) (rest : List (ApplicationInstruction P L))
    (hhead : plan.instructions deadlineOf = instruction :: rest)
    (hother : instruction.submitter ≠ some who) :
    instruction.CacheEmpty (root.image deadlineOf)
      ((root.windowed deadlineOf binding choice windowOf).eraseExecution execution) := by
  have hall := checkpoint.unchangedCaches
  rw [RemainingUnchangedCachesEmpty, hhead] at hall
  exact ((List.forall_cons _ _ _).mp hall |>.1).resolve_left hother

/-- The source continuation occupies exactly the unexecuted instruction
suffix. Block coordinates count application instructions, not graph nodes. -/
theorem instructions_suffix (checkpoint : WindowedCheckpoint root rootProfile deadlineOf
    binding choice windowOf roster who replacement blockIndex plan profile current execution) :
    ∃ before, before.length = blockIndex ∧
      root.instructions deadlineOf = before ++ plan.instructions deadlineOf := by
  obtain ⟨before, hbefore⟩ := checkpoint.continuation.instructions_suffix deadlineOf
  refine ⟨before, ?_, hbefore⟩
  have hlength := congrArg List.length hbefore
  have hcount := checkpoint.blockCount
  simp only [List.length_append] at hlength
  omega

/-- The next source instruction is selected by the actual completed-block
count. A paired commit/publication occupies one slot even though it lowers
to two graph nodes. -/
theorem instruction_at (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding
    choice windowOf roster who replacement blockIndex plan profile current execution)
    (instruction : ApplicationInstruction P L) (rest : List (ApplicationInstruction P L))
    (hhead : plan.instructions deadlineOf = instruction :: rest) :
    (root.instructions deadlineOf)[blockIndex]? = some instruction := by
  obtain ⟨before, hlength, hbefore⟩ := checkpoint.instructions_suffix
  rw [hbefore, ← hlength, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, hhead]
  rfl

/-- The source checkpoint determines the completed emitted prefix, including
its actual block length. This is derived from graph refinement, not added to
the checkpoint as an independent history assumption. -/
theorem completed_instructions (checkpoint : WindowedCheckpoint root rootProfile deadlineOf
    binding choice windowOf roster who replacement blockIndex plan profile current execution) :
    ∃ before, before.length = blockIndex ∧
      root.instructions deadlineOf = before ++ plan.instructions deadlineOf ∧
      (∀ instruction ∈ before,
        execution.native.application.base.memory.done instruction.address = true) ∧
      (∀ instruction ∈ plan.instructions deadlineOf,
        execution.native.application.base.memory.done instruction.address = false) := by
  obtain ⟨before, hroot, hbefore, hpending⟩ :=
    checkpoint.continuation.instruction_completion execution.native.application.base
      checkpoint.refines
  refine ⟨before, ?_, hroot, hbefore, hpending⟩
  have hlength := congrArg List.length hroot
  have hcount := checkpoint.blockCount
  simp only [List.length_append] at hlength
  omega

/-- Timeout decoration preserves the active source instruction. The current
address follows from source refinement even under a raw unilateral policy. -/
theorem activeAddress?_head (checkpoint : WindowedCheckpoint root rootProfile deadlineOf
    binding choice windowOf roster who replacement blockIndex plan profile current execution)
    (instruction : ApplicationInstruction P L) (rest : List (ApplicationInstruction P L))
    (hhead : plan.instructions deadlineOf = instruction :: rest) :
    (root.windowed deadlineOf binding choice windowOf).image.activeAddress?
      execution.native.application.base.memory = some instruction.address := by
  simpa only [windowed, ApplicationImage.activeAddress?_withChoiceTimeouts,
    ApplicationImage.activeAddress?_withBindingTimeouts] using
      checkpoint.continuation.activeAddress?_head execution.native.application.base
        checkpoint.refines instruction rest hhead

/-- The environment's block coordinate follows from actual execution, whether
or not any particular principal belongs to the polling roster. -/
theorem environmentHistory_length (checkpoint : WindowedCheckpoint root rootProfile deadlineOf
    binding choice windowOf roster who replacement blockIndex plan profile current execution) :
    execution.environmentHistory.length = blockIndex * (roster.length + 2) := by
  have hlength := (root.windowed deadlineOf binding choice windowOf).application
    |>.runPolicies_environmentHistory_length
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf who replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (List.replicate blockIndex (WindowedApplication.blockInvocations roster)).flatten
      (root.windowedInitialExecution deadlineOf binding choice windowOf) execution
      checkpoint.reached
  simpa only [windowedInitialExecution, PolicyExecution.initial, List.length_nil, Nat.zero_add,
    WindowedApplication.repeatedBlockInvocations_environment_count] using hlength

/-- Appending the next actual block gives the initialized-run witness required
by a successor checkpoint. Source advancement and cache preservation are
separate obligations. -/
theorem reached_after_block (checkpoint : WindowedCheckpoint root rootProfile deadlineOf
    binding choice windowOf roster who replacement blockIndex plan profile current execution)
    (next : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hnext : next ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf who replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).support) :
    next ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf who replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (List.replicate (blockIndex + 1)
        (WindowedApplication.blockInvocations roster)).flatten
      (root.windowedInitialExecution deadlineOf binding choice windowOf)).support := by
  rw [List.replicate_succ', List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, MessageApplication.runPolicies_append, FinDist.support_bind]
  exact Set.mem_iUnion.mpr ⟨execution, Set.mem_iUnion.mpr ⟨checkpoint.reached, hnext⟩⟩

theorem noDeliveryProvenance
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      who replacement blockIndex plan profile current execution) :
    execution.native.pool.NoDeliveryProvenance := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  apply runtime.application.runPolicies_noDeliveryProvenance
    (root.windowedPlayers rootProfile deadlineOf binding choice windowOf who replacement)
    (runtime.blockEnvironment roster) (runtime.blockEnvironment_noDelivery roster)
    _ (root.windowedInitialExecution deadlineOf binding choice windowOf) execution
  · exact MessagePool.noDeliveryProvenance_empty
  · exact checkpoint.reached

theorem serialsBeforeNext
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      who replacement blockIndex plan profile current execution) :
    execution.native.pool.SerialsBeforeNext := by
  exact (root.windowed deadlineOf binding choice windowOf).application
    |>.runPolicies_initial_serialsBeforeNext _ _ _ _ execution checkpoint.reached

theorem consistent
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      who replacement blockIndex plan profile current execution) :
    (root.windowed deadlineOf binding choice windowOf).Consistent
      execution.native.application := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  apply runtime.runPolicies_consistent _ _ _
    (root.windowedInitialExecution deadlineOf binding choice windowOf) execution
  · exact runtime.initial_consistent _
  · exact checkpoint.reached

/-- The next emitted obligation starts with its complete relative window.
Freshness is an inductive checkpoint invariant; mere monotonicity of the
public clock would not imply this ordinary-service opportunity. -/
theorem active_origin_clock
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      who replacement blockIndex plan profile current execution)
    (instruction : ApplicationInstruction P L) (rest : List (ApplicationInstruction P L))
    (hhead : plan.instructions deadlineOf = instruction :: rest) :
    ∃ activation,
      execution.native.application.active = some activation ∧
      activation.key = instruction.address ∧
      activation.since = execution.native.application.base.memory.clock := by
  have hmap := checkpoint.consistent.1.trans (checkpoint.activeAddress?_head instruction rest hhead)
  cases hactive : execution.native.application.active with
  | none => simp [hactive] at hmap
  | some activation =>
      refine ⟨activation, rfl, ?_, checkpoint.activationFresh activation hactive⟩
      exact Option.some.inj ((congrArg (Option.map Activation.key) hactive).symm.trans hmap)

/-- Every completed binding has an actual disposition. Opaque dispositions
have their generated owner and slot; timeout defaults remain public defaults.
This follows from initialized execution and is not an extra checkpoint field. -/
theorem resolvedBindings
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      who replacement blockIndex plan profile current execution) :
    (root.windowed deadlineOf binding choice windowOf).image.ResolvedBindings
      execution.native.application.base := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  have hnodup : (runtime.image.instructions.flatMap
      ApplicationInstruction.coveredNodes).Nodup := by
    dsimp only [runtime, windowed]
    rw [ApplicationImage.coveredNodes_withChoiceTimeouts,
      ApplicationImage.coveredNodes_withBindingTimeouts]
    exact root.coveredNodes_nodup deadlineOf
  have hallocated : ∀ instruction ∈ runtime.image.instructions,
      instruction.AllocatedAt rootState.initialFields.length := by
    apply ApplicationImage.instructions_allocated_withChoiceTimeouts
    apply ApplicationImage.instructions_allocated_withBindingTimeouts
    exact root.instructions_allocated deadlineOf
  exact runtime.runPolicies_resolvedBindings rootState.initialFields.length hnodup hallocated
    (root.windowedPlayers rootProfile deadlineOf binding choice windowOf who replacement)
    (runtime.blockEnvironment roster)
    (List.replicate blockIndex (WindowedApplication.blockInvocations roster)).flatten
    (root.windowedInitialExecution deadlineOf binding choice windowOf) execution
    (ApplicationImage.ResolvedBindings.initial runtime.image
      (compileCore rootProg rootFresh rootState).graph) checkpoint.reached

/-- At an initialized checkpoint, preparation is exactly the first private
registration recorded in each owner's history, including under raw deviations. -/
theorem registrationConsistent
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      who replacement blockIndex plan profile current execution) :
    (root.windowed deadlineOf binding choice windowOf).RegistrationConsistent execution := by
  apply (root.windowed deadlineOf binding choice windowOf).runPolicies_registrationConsistent
    (root.windowedPlayers rootProfile deadlineOf binding choice windowOf who replacement)
    ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
    (List.replicate blockIndex (WindowedApplication.blockInvocations roster)).flatten
    (root.windowedInitialExecution deadlineOf binding choice windowOf) execution
    (by intro owner slot; rfl) checkpoint.reached

/-- An owner using its reference policy retains typed registration provenance.
The condition applies equally to an unchanged opponent and to a reference
replacement at the distinguished coordinate. -/
theorem registeredBindings
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      who replacement blockIndex plan profile current execution)
    (owner : P)
    (hpolicy :
      root.windowedPlayers rootProfile deadlineOf binding choice windowOf who replacement owner =
        root.windowedReferencePlayers rootProfile deadlineOf binding choice windowOf owner) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    runtime.image.RegisteredBindings owner
      (fun slot typed => ∃ fieldSpec : FieldSpec P L,
        (compileCore prog fresh state).graph.field? slot = some fieldSpec ∧
          typed.ty = fieldSpec.ty)
      ((execution.principalHistory owner).map fun entry =>
        show runtime.image.application.PlayerEntry from runtime.erasePlayerEntry entry)
      execution.native.application.base := by
  intro runtime
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf who
    replacement
  have hbindings := root.windowedBlock_registeredBindings deadlineOf binding choice windowOf
    rootProfile owner players hpolicy (runtime.blockEnvironment roster)
    (List.replicate blockIndex (WindowedApplication.blockInvocations roster)).flatten
    execution checkpoint.reached
  rw [← checkpoint.continuation.compile_eq]
  exact hbindings

theorem historyAlignment (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding
    choice windowOf roster who replacement blockIndex plan profile current execution)
    (hroster : roster.Nodup) (actor : P) (hactor : actor ∈ roster) :
    (execution.principalHistory actor).length = 3 * blockIndex ∧
      execution.environmentHistory.length = blockIndex * (roster.length + 2) ∧
      (execution.principalHistory actor).length / 3 = blockIndex ∧
      execution.environmentHistory.length / (roster.length + 2) = blockIndex := by
  exact (root.windowed deadlineOf binding choice windowOf)
    |>.runPolicies_repeatedBlocks_history_alignment roster hroster actor hactor _ _ blockIndex _
      execution checkpoint.reached

/-- The canonical zero-block execution is a windowed checkpoint. Initial
source reads remain the separate boundary condition of later kernel theorems;
the certificate itself needs no such assumption. -/
theorem initial (source : WFProgram P L)
    (root : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (rootProfile : SourceBehavioralProfile source.core.prog)
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (roster : List P) (who : P)
    (replacement :
      (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy) :
    WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster who
      replacement 0 root rootProfile (compiledInitialCoupled source.core)
      (root.windowedInitialExecution deadlineOf binding choice windowOf) := by
  refine ⟨.refl, Nat.zero_add _, ApplicationImage.State.initial_refines _, ?_, ?_, ?_⟩
  · exact FinDist.mem_support_pure.mpr rfl
  · apply List.forall_iff_forall_mem.mpr
    intro instruction _
    right
    exact instruction.cacheEmpty_of_empty_histories (root.image deadlineOf)
      ((root.windowed deadlineOf binding choice windowOf).eraseExecution
        (root.windowedInitialExecution deadlineOf binding choice windowOf)) (fun _ => rfl)
  · exact WindowedApplication.State.freshActivation_initial _ _

end WindowedCheckpoint

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.registeredBindings'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.registeredBindings
