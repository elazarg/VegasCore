/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationOrder
import Vegas.Compile.ApplicationForwardCheckpoint

/-! # Ordered admission at source-forward checkpoints

The proof-side source cursor is not runtime data. At an existing forward
checkpoint, exact generated node coverage and native refinement nevertheless
show that the ordered application's public selector points to the current
emitted instruction.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem ProfileContinuation.instructions_prefix_coverage
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext} {prog : VegasCore P L Γ}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {accounted : CommitmentAccounting pending prog}
    {rootFresh : FreshBindings rootProg} {fresh : FreshBindings prog}
    {rootState : BuildState P L rootContext} {state : BuildState P L Γ}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg}
    {plan : ApplicationPlan accounted fresh state}
    {profile : SourceBehavioralProfile prog}
    (continuation : ProfileContinuation root rootProfile plan profile)
    (deadlineOf : Nat → Nat) :
    ∃ before,
      root.instructions deadlineOf = before ++ plan.instructions deadlineOf ∧
      List.range rootState.nodes.length ++
          before.flatMap ApplicationInstruction.coveredNodes =
        List.range state.nodes.length := by
  obtain ⟨before, hbefore⟩ := continuation.instructions_suffix deadlineOf
  refine ⟨before, hbefore, ?_⟩
  have hroot := root.coveredNodes_eq_range deadlineOf
  have hplan := plan.coveredNodes_eq_range deadlineOf
  rw [continuation.compile_eq] at hroot
  have hcancel :
      (List.range rootState.nodes.length ++
          before.flatMap ApplicationInstruction.coveredNodes) ++
          (plan.instructions deadlineOf).flatMap
            ApplicationInstruction.coveredNodes =
        List.range state.nodes.length ++
          (plan.instructions deadlineOf).flatMap
            ApplicationInstruction.coveredNodes := by
    calc
      _ = List.range (compileCore prog fresh state).nodes.length := by
        simpa only [hbefore, List.flatMap_append, List.append_assoc] using hroot
      _ = _ := hplan.symm
  exact List.append_cancel_right hcancel

private theorem instruction_address_bounds
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat) (instruction : ApplicationInstruction P L)
    (hmem : instruction ∈ plan.instructions deadlineOf) :
    state.nodes.length ≤ instruction.address ∧
      instruction.address < (compileCore prog fresh state).graph.nodeCount := by
  have hcovered : instruction.address ∈
      (plan.instructions deadlineOf).flatMap ApplicationInstruction.coveredNodes := by
    exact List.mem_flatMap.mpr
      ⟨instruction, hmem, instruction.address_mem_coveredNodes⟩
  have hcoverage := plan.coveredNodes_eq_range deadlineOf
  have hfull : instruction.address ∈
      List.range (compileCore prog fresh state).nodes.length := by
    rw [← hcoverage]
    exact List.mem_append_right _ hcovered
  have hlt : instruction.address <
      (compileCore prog fresh state).graph.nodeCount := by
    simpa only [BuildResult.graph, Graph.nodeCount] using List.mem_range.mp hfull
  refine ⟨?_, hlt⟩
  by_contra hge
  have hprefix : instruction.address ∈ List.range state.nodes.length :=
    List.mem_range.mpr (Nat.lt_of_not_ge hge)
  have hnodup :
      (List.range state.nodes.length ++
        (plan.instructions deadlineOf).flatMap
          ApplicationInstruction.coveredNodes).Nodup := by
    rw [hcoverage]
    exact List.nodup_range
  exact (List.nodup_append.mp hnodup).2.2 _ hprefix _ hcovered rfl

namespace ProfileContinuation

variable {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
variable {rootProg : VegasCore P L rootContext} {prog : VegasCore P L Γ}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {accounted : CommitmentAccounting pending prog}
variable {rootFresh : FreshBindings rootProg} {fresh : FreshBindings prog}
variable {rootState : BuildState P L rootContext} {state : BuildState P L Γ}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
variable {plan : ApplicationPlan accounted fresh state}
variable {profile : SourceBehavioralProfile prog}
variable {current : CoupledAt (compileCore prog fresh state).graph state}

/-- Exact source refinement identifies completed and pending application
instructions, without any reference-policy or service assumption. -/
theorem instruction_completion
    (continuation : ProfileContinuation root rootProfile plan profile)
    (native : ApplicationImage.State P L)
    (hrefines : native.Refines current.current.graph.1) :
    ∃ before,
      root.instructions deadlineOf = before ++ plan.instructions deadlineOf ∧
      (∀ prior ∈ before, native.memory.done prior.address = true) ∧
      (∀ pending ∈ plan.instructions deadlineOf, native.memory.done pending.address = false) := by
  obtain ⟨before, hroot, hcoverage⟩ := continuation.instructions_prefix_coverage deadlineOf
  have hstateBound : state.nodes.length ≤
      (compileCore prog fresh state).graph.nodeCount := by
    change state.nodes.length ≤ (compileCore prog fresh state).nodes.length
    exact (compileCore_nodes_prefix prog fresh state).length_le
  refine ⟨before, hroot, ?_, ?_⟩
  · intro prior hprior
    have hcovered : prior.address ∈ before.flatMap ApplicationInstruction.coveredNodes :=
      List.mem_flatMap.mpr ⟨prior, hprior, prior.address_mem_coveredNodes⟩
    have hlt : prior.address < state.nodes.length := by
      apply List.mem_range.mp
      rw [← hcoverage]
      exact List.mem_append_right _ hcovered
    let node : Fin (compileCore prog fresh state).graph.nodeCount :=
      ⟨prior.address, hlt.trans_le hstateBound⟩
    exact (hrefines.memory.completed node).mpr ((current.completedPrefix node).mpr hlt)
  · intro instruction hmem
    obtain ⟨hge, hlt⟩ := instruction_address_bounds plan deadlineOf instruction hmem
    let node : Fin (compileCore prog fresh state).graph.nodeCount :=
      ⟨instruction.address, hlt⟩
    apply Bool.eq_false_iff.mpr
    intro hdone
    have hprior := (current.completedPrefix node).mp ((hrefines.memory.completed node).mp hdone)
    exact (Nat.not_lt_of_ge hge) hprior

/-- Ordered admission follows the independent source cursor whenever the
native state refines that cursor. Reachability and policy lifting are separate
obligations of the calling checkpoint. -/
theorem activeAddress?_head
    (continuation : ProfileContinuation root rootProfile plan profile)
    (native : ApplicationImage.State P L)
    (hrefines : native.Refines current.current.graph.1)
    (instruction : ApplicationInstruction P L) (rest : List (ApplicationInstruction P L))
    (hhead : plan.instructions deadlineOf = instruction :: rest) :
    (root.image deadlineOf).activeAddress? native.memory = some instruction.address := by
  obtain ⟨before, hroot, hbefore, hpending⟩ :=
    continuation.instruction_completion native hrefines
  have hnotDone := hpending instruction (by rw [hhead]; exact List.mem_cons_self)
  rw [hhead] at hroot
  change (ApplicationImage.mk (root.instructions deadlineOf)).activeAddress?
    native.memory = some instruction.address
  rw [hroot, ApplicationImage.activeAddress?_after_completed
    before ⟨instruction :: rest⟩ native.memory hbefore]
  exact ApplicationImage.activeAddress?_head instruction rest native.memory hnotDone

end ProfileContinuation

namespace ForwardCheckpoint

variable {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
variable {rootProg : VegasCore P L rootContext} {prog : VegasCore P L Γ}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {accounted : CommitmentAccounting pending prog}
variable {rootFresh : FreshBindings rootProg} {fresh : FreshBindings prog}
variable {rootState : BuildState P L rootContext} {state : BuildState P L Γ}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
variable {plan : ApplicationPlan accounted fresh state}
variable {profile : SourceBehavioralProfile prog}
variable {current : CoupledAt (compileCore prog fresh state).graph state}
variable {execution : (root.image deadlineOf).application.PolicyExecution}

/-- At an exact source-forward checkpoint, ordered admission selects the
current generated instruction. This is derived from generated coverage and
the coupled completion prefix, not stored cursor state. -/
theorem activeAddress?_head
    (checkpoint : ForwardCheckpoint root rootProfile deadlineOf
      plan profile current execution)
    (instruction : ApplicationInstruction P L)
    (rest : List (ApplicationInstruction P L))
    (hhead : plan.instructions deadlineOf = instruction :: rest) :
    (root.image deadlineOf).activeAddress?
        execution.native.application.memory = some instruction.address :=
  checkpoint.continuation.activeAddress?_head execution.native.application
    checkpoint.refines instruction rest hhead

/-- Including a real envelope for the current emitted instruction has exactly
the original policy-step law, including observations, history, and receipts.
The handler's own validation remains in force in both applications. -/
theorem ordered_include_eq
    (checkpoint : ForwardCheckpoint root rootProfile deadlineOf
      plan profile current execution)
    (instruction : ApplicationInstruction P L)
    (rest : List (ApplicationInstruction P L))
    (hhead : plan.instructions deadlineOf = instruction :: rest)
    (id : MessageId P) (message : Message P (ApplicationImage.Payload P L))
    (hlookup : execution.native.pool.lookup id = some message)
    (haddress : message.payload.address? = some instruction.address) :
    (root.image deadlineOf).orderedApplication.environmentPolicyStep execution (.include id) =
      (root.image deadlineOf).application.environmentPolicyStep execution (.include id) := by
  apply (root.image deadlineOf).application.environmentPolicyStep_withAdmission_eq
    (root.image deadlineOf).admitsMessage (root.image deadlineOf).admitsEnvironment
  change ∀ candidate, execution.native.pool.lookup id = some candidate →
    (root.image deadlineOf).admitsMessage execution.native.application.memory candidate = true
  intro candidate hcandidate
  have heq : candidate = message := Option.some.inj (hcandidate.symm.trans hlookup)
  subst candidate
  have hactive := checkpoint.activeAddress?_head instruction rest hhead
  simp [ApplicationImage.admitsMessage, haddress, ApplicationImage.admitsAddress, hactive]

/-- A chance invocation at the generated source head retains the complete
original stochastic policy-step law. -/
theorem ordered_sample_eq
    (checkpoint : ForwardCheckpoint root rootProfile deadlineOf
      plan profile current execution)
    (code : SampleCode L) (rest : List (ApplicationInstruction P L))
    (hhead : plan.instructions deadlineOf = .sample code :: rest) :
    (root.image deadlineOf).orderedApplication.environmentPolicyStep execution
        (.application (.sample code.node)) =
      (root.image deadlineOf).application.environmentPolicyStep execution
        (.application (.sample code.node)) := by
  apply (root.image deadlineOf).application.environmentPolicyStep_withAdmission_eq
    (root.image deadlineOf).admitsMessage (root.image deadlineOf).admitsEnvironment
  change (root.image deadlineOf).admitsAddress execution.native.application.memory code.node = true
  exact ApplicationImage.admitsAddress_iff _ _ _ |>.mpr
    (checkpoint.activeAddress?_head (.sample code) rest hhead)

end ForwardCheckpoint

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.ForwardCheckpoint.activeAddress?_head' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ForwardCheckpoint.activeAddress?_head

/-- info: 'Vegas.ApplicationPlan.ForwardCheckpoint.ordered_include_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ForwardCheckpoint.ordered_include_eq

/-- info: 'Vegas.ApplicationPlan.ForwardCheckpoint.ordered_sample_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ForwardCheckpoint.ordered_sample_eq
