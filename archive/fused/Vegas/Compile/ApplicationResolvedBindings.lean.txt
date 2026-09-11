/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationCompletion
import Vegas.Compile.ApplicationBindingOrigins
import Vegas.Compile.ApplicationImageCoverage
import Interaction.MessageApplicationPolicyLaws

/-! # Resolved generated bindings

A completed binding instruction has an accepted public disposition. Opaque
dispositions retain the compiler-generated owner and slot; public defaults do
not manufacture a commitment handle. The invariant is native and survives
arbitrary policies. It relies only on disjoint instruction footprints and the
generated allocation relation, not on a source profile or private readout.
-/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Every completed binding instruction has a disposition, and every opaque
disposition at that instruction is its canonical generated handle. -/
def ResolvedBindings (image : ApplicationImage P L) (state : State P L) : Prop :=
  ∀ code, .bind code ∈ image.instructions → state.memory.done code.node = true →
    ∃ disposition, state.memory.accepted code.sourceField = some disposition ∧
      ∀ handle, disposition = .opaque handle →
        handle = (code.owner, code.sourceSlot)

omit [DecidableEq P] in
private theorem coveredNodes_disjoint
    (image : ApplicationImage P L)
    (hnodup : (image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup)
    (first second : ApplicationInstruction P L)
    (hfirst : first ∈ image.instructions) (hsecond : second ∈ image.instructions)
    (hne : first ≠ second) : List.Disjoint first.coveredNodes second.coveredNodes := by
  have hpairwise := (List.nodup_flatMap.mp hnodup).2
  let : Std.Symm (fun a b : ApplicationInstruction P L =>
      List.Disjoint a.coveredNodes b.coveredNodes) :=
    ⟨fun _ _ h => h.symm⟩
  exact hpairwise.forall hfirst hsecond hne

omit [DecidableEq P] in
private theorem State.sample_resolvedBindings
    (image : ApplicationImage P L)
    (hnodup : (image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup)
    (state : State P L) (code : SampleCode L)
    (hcode : (.sample (P := P) code : ApplicationInstruction P L) ∈ image.instructions)
    (value : L.Val code.dist.ty) (hresolved : image.ResolvedBindings state) :
    image.ResolvedBindings (state.sample code value) := by
  intro binding hbinding hdone
  have hne : (ApplicationInstruction.bind binding : ApplicationInstruction P L) ≠
      .sample code := by intro h; cases h
  have hdisjoint := coveredNodes_disjoint image hnodup (.bind binding) (.sample code)
    hbinding hcode hne
  have hnode : binding.node ≠ code.node := by
    intro heq
    exact (List.disjoint_left.mp hdisjoint)
      (show binding.node ∈ (ApplicationInstruction.bind binding).coveredNodes from
        by simp [ApplicationInstruction.coveredNodes])
      (by simp [ApplicationInstruction.coveredNodes, heq])
  have hprior : state.memory.done binding.node = true := by
    simpa [State.sample, hnode] using hdone
  exact hresolved binding hbinding hprior

omit [DecidableEq P] in
private theorem State.publish_resolvedBindings
    (image : ApplicationImage P L)
    (hnodup : (image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup)
    (state : State P L) (code : PublicChoiceCode P L)
    (hcode : .publicChoice code ∈ image.instructions)
    (value : L.Val code.guard.ty) (hresolved : image.ResolvedBindings state) :
    image.ResolvedBindings (state.publish code value) := by
  intro binding hbinding hdone
  have hne : (ApplicationInstruction.bind binding : ApplicationInstruction P L) ≠
      .publicChoice code := by intro h; cases h
  have hdisjoint := coveredNodes_disjoint image hnodup (.bind binding) (.publicChoice code)
    hbinding hcode hne
  have hchoice : binding.node ≠ code.endpoint.choiceNode := by
    intro heq
    exact (List.disjoint_left.mp hdisjoint)
      (show binding.node ∈ (ApplicationInstruction.bind binding).coveredNodes from
        by simp [ApplicationInstruction.coveredNodes])
      (by simp [ApplicationInstruction.coveredNodes, heq])
  have hpublication : binding.node ≠ code.endpoint.publicationNode := by
    intro heq
    exact (List.disjoint_left.mp hdisjoint)
      (show binding.node ∈ (ApplicationInstruction.bind binding).coveredNodes from
        by simp [ApplicationInstruction.coveredNodes])
      (by simp [ApplicationInstruction.coveredNodes, heq])
  have hprior : state.memory.done binding.node = true := by
    simpa [State.publish, Memory.publish, hchoice, hpublication] using hdone
  exact hresolved binding hbinding hprior

omit [DecidableEq P] in
private theorem State.publishConditional_resolvedBindings
    (image : ApplicationImage P L)
    (hnodup : (image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup)
    (state : State P L) (code : ConditionalCode P L)
    (hcode : .conditional code ∈ image.instructions)
    (value : Option (L.Val code.secretTy))
    (hresolved : image.ResolvedBindings state) :
    image.ResolvedBindings (state.publishConditional code value) := by
  intro binding hbinding hdone
  have hne : (ApplicationInstruction.bind binding : ApplicationInstruction P L) ≠
      .conditional code := by intro h; cases h
  have hdisjoint := coveredNodes_disjoint image hnodup (.bind binding) (.conditional code)
    hbinding hcode hne
  have hchoice : binding.node ≠ code.endpoint.choiceNode := by
    intro heq
    exact (List.disjoint_left.mp hdisjoint)
      (show binding.node ∈ (ApplicationInstruction.bind binding).coveredNodes from
        by simp [ApplicationInstruction.coveredNodes])
      (by simp [ApplicationInstruction.coveredNodes, heq])
  have hpublication : binding.node ≠ code.endpoint.publicationNode := by
    intro heq
    exact (List.disjoint_left.mp hdisjoint)
      (show binding.node ∈ (ApplicationInstruction.bind binding).coveredNodes from
        by simp [ApplicationInstruction.coveredNodes])
      (by simp [ApplicationInstruction.coveredNodes, heq])
  have hprior : state.memory.done binding.node = true := by
    simpa [State.publishConditional, hchoice, hpublication] using hdone
  exact hresolved binding hbinding hprior

omit [DecidableEq P] in
private theorem State.bind_resolvedBindings
    (image : ApplicationImage P L) (initialFields : Nat)
    (hnodup : (image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup)
    (hallocated : ∀ instruction ∈ image.instructions,
      instruction.AllocatedAt initialFields)
    (state : State P L) (code : BindingCode P L) (hcode : .bind code ∈ image.instructions)
    (handle : CommitmentHandle P Nat) (hhandle : handle = (code.owner, code.sourceSlot))
    (hresolved : image.ResolvedBindings state) :
    image.ResolvedBindings (state.bind code handle) := by
  intro binding hbinding hdone
  by_cases heq : (ApplicationInstruction.bind binding : ApplicationInstruction P L) = .bind code
  · cases heq
    refine ⟨.opaque handle, ?_, ?_⟩
    · simp [State.bind]
    · intro accepted haccepted
      cases haccepted
      exact hhandle
  · have hdisjoint := coveredNodes_disjoint image hnodup (.bind binding) (.bind code)
      hbinding hcode heq
    have hnode : binding.node ≠ code.node := by
      intro hnode
      exact (List.disjoint_left.mp hdisjoint)
        (show binding.node ∈ (ApplicationInstruction.bind binding).coveredNodes from
          by simp [ApplicationInstruction.coveredNodes])
        (by simp [ApplicationInstruction.coveredNodes, hnode])
    have hprior : state.memory.done binding.node = true := by
      simpa [State.bind, hnode] using hdone
    obtain ⟨disposition, haccepted, hcanonical⟩ := hresolved binding hbinding hprior
    have hbindingAllocation := hallocated (.bind binding) hbinding
    have hcodeAllocation := hallocated (.bind code) hcode
    have hfield : binding.sourceField ≠ code.sourceField := by
      change binding.sourceField = initialFields + binding.node ∧
        binding.sourceSlot = binding.sourceField at hbindingAllocation
      change code.sourceField = initialFields + code.node ∧
        code.sourceSlot = code.sourceField at hcodeAllocation
      rw [hbindingAllocation.1, hcodeAllocation.1]
      omega
    exact ⟨disposition, by simpa [State.bind, hfield] using haccepted, hcanonical⟩

omit [DecidableEq P] in
private theorem State.defaultBind_resolvedBindings
    (image : ApplicationImage P L) (initialFields : Nat)
    (hnodup : (image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup)
    (hallocated : ∀ instruction ∈ image.instructions,
      instruction.AllocatedAt initialFields)
    (state : State P L) (code : BindingCode P L) (hcode : .bind code ∈ image.instructions)
    (value : TypedValue L) (hresolved : image.ResolvedBindings state) :
    image.ResolvedBindings (state.defaultBind code value) := by
  intro binding hbinding hdone
  by_cases heq : (ApplicationInstruction.bind binding : ApplicationInstruction P L) = .bind code
  · cases heq
    exact ⟨.publicDefault value, by simp [State.defaultBind], by
      intro _ h; cases h⟩
  · have hdisjoint := coveredNodes_disjoint image hnodup (.bind binding) (.bind code)
      hbinding hcode heq
    have hnode : binding.node ≠ code.node := by
      intro hnode
      exact (List.disjoint_left.mp hdisjoint)
        (show binding.node ∈ (ApplicationInstruction.bind binding).coveredNodes from
          by simp [ApplicationInstruction.coveredNodes])
        (by simp [ApplicationInstruction.coveredNodes, hnode])
    have hprior : state.memory.done binding.node = true := by
      simpa [State.defaultBind, hnode] using hdone
    obtain ⟨disposition, haccepted, hcanonical⟩ := hresolved binding hbinding hprior
    have hbindingAllocation := hallocated (.bind binding) hbinding
    have hcodeAllocation := hallocated (.bind code) hcode
    have hfield : binding.sourceField ≠ code.sourceField := by
      change binding.sourceField = initialFields + binding.node ∧
        binding.sourceSlot = binding.sourceField at hbindingAllocation
      change code.sourceField = initialFields + code.node ∧
        code.sourceSlot = code.sourceField at hcodeAllocation
      rw [hbindingAllocation.1, hcodeAllocation.1]
      omega
    exact ⟨disposition, by simpa [State.defaultBind, hfield] using haccepted, hcanonical⟩

theorem handle_resolvedBindings
    (image : ApplicationImage P L) (initialFields : Nat)
    (hnodup : (image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup)
    (hallocated : ∀ instruction ∈ image.instructions,
      instruction.AllocatedAt initialFields)
    (state next : State P L) (message : Message P (Payload P L))
    (hresolved : image.ResolvedBindings state)
    (hnext : image.handle state message = some next) : image.ResolvedBindings next := by
  rcases message with ⟨id, payload⟩
  cases payload with
  | malformed data => simp [ApplicationImage.handle] at hnext
  | choice address typed =>
      cases hlookup : image.lookup address with
      | none => simp [ApplicationImage.handle, hlookup] at hnext
      | some instruction =>
          have hmem := List.mem_of_find?_eq_some hlookup
          cases instruction with
          | sample code | bind code | conditional code =>
              simp [ApplicationImage.handle, hlookup] at hnext
          | publicChoice code =>
              simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind,
                Option.bind_some] at hnext
              cases htyped : typed.as? code.guard.ty with
              | none => simp [htyped] at hnext
              | some value =>
                  simp only [htyped, Option.bind_some] at hnext
                  cases hresult : code.endpoint.resolve? state.memory.done
                      (code.guard.validate state.memory.store) ⟨id, value⟩ with
                  | none => simp [hresult] at hnext
                  | some accepted =>
                      simp only [hresult, Option.bind_some] at hnext
                      cases hnext
                      exact state.publish_resolvedBindings image hnodup code hmem accepted hresolved
  | expireChoice address =>
      cases hlookup : image.lookup address with
      | none => simp [ApplicationImage.handle, hlookup] at hnext
      | some instruction =>
          have hmem := List.mem_of_find?_eq_some hlookup
          cases instruction with
          | sample code | bind code | conditional code =>
              simp [ApplicationImage.handle, hlookup] at hnext
          | publicChoice code =>
              rw [image.handle_expireChoice state address code hlookup id] at hnext
              obtain ⟨value, _, rfl⟩ := Option.map_eq_some_iff.mp hnext
              exact state.publish_resolvedBindings image hnodup code hmem value hresolved
  | binding address handle =>
      cases hlookup : image.lookup address with
      | none => simp [ApplicationImage.handle, hlookup] at hnext
      | some instruction =>
          have hmem := List.mem_of_find?_eq_some hlookup
          cases instruction with
          | sample code | publicChoice code | conditional code =>
              simp [ApplicationImage.handle, hlookup] at hnext
          | bind code =>
              simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind,
                Option.bind_some] at hnext
              split at hnext
              · rename_i hadmitted
                cases hnext
                exact state.bind_resolvedBindings image initialFields hnodup hallocated code hmem
                  handle hadmitted.2.1 hresolved
              · contradiction
  | expireBinding address =>
      cases hlookup : image.lookup address with
      | none => simp [ApplicationImage.handle, hlookup] at hnext
      | some instruction =>
          have hmem := List.mem_of_find?_eq_some hlookup
          cases instruction with
          | sample code | publicChoice code | conditional code =>
              simp [ApplicationImage.handle, hlookup] at hnext
          | bind code =>
              rw [image.handle_expireBinding state address code hlookup id] at hnext
              obtain ⟨value, _, rfl⟩ := Option.map_eq_some_iff.mp hnext
              exact state.defaultBind_resolvedBindings image initialFields hnodup hallocated code
                hmem ⟨code.ty, value⟩ hresolved
  | conditional address payload =>
      cases hlookup : image.lookup address with
      | none => simp [ApplicationImage.handle, hlookup] at hnext
      | some instruction =>
          have hmem := List.mem_of_find?_eq_some hlookup
          cases instruction with
          | sample code | publicChoice code | bind code =>
              simp [ApplicationImage.handle, hlookup] at hnext
          | conditional code =>
              simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind,
                Option.bind_some] at hnext
              cases hdecoded : code.decode payload with
              | none => simp [hdecoded] at hnext
              | some decoded =>
                  simp only [hdecoded, Option.bind_some] at hnext
                  cases hresult : code.endpoint.resolveDisposition? state.memory.clock
                      (state.verify code) (code.binding? state.memory) state.memory.done
                      (code.canOpen state.memory.store) ⟨id, decoded⟩ with
                  | none => simp [hresult] at hnext
                  | some result =>
                      simp only [hresult, Option.bind_some] at hnext
                      cases hnext
                      exact state.publishConditional_resolvedBindings image hnodup code hmem
                        result hresolved

theorem environmentStep_resolvedBindings
    (image : ApplicationImage P L)
    (hnodup : (image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup)
    (state next : State P L) (command : EnvironmentCommand)
    (hresolved : image.ResolvedBindings state)
    (hnext : next ∈ (image.application.environmentStep state command).support) :
    image.ResolvedBindings next := by
  cases command with
  | advance clock =>
      simp only [ApplicationImage.application, FinDist.mem_support_pure] at hnext
      subst next
      exact hresolved
  | sample address =>
      change next ∈ (image.sample state address).support at hnext
      rcases image.sample_support state address next hnext with rfl | hsample
      · exact hresolved
      · obtain ⟨code, reads, value, hlookup, _, _, _, _, rfl⟩ := hsample
        exact state.sample_resolvedBindings image hnodup code
          (List.mem_of_find?_eq_some hlookup) value hresolved

/-- Canonical initialization has no completed binding obligations. -/
theorem ResolvedBindings.initial (image : ApplicationImage P L) (graph : Graph P L) :
    image.ResolvedBindings (State.initial (Memory.initial graph)) := by
  intro code _ hdone
  change false = true at hdone
  contradiction

/-- Resolved dispositions survive arbitrary supported policies. Successful
binding and binding-expiry handlers establish the invariant at newly completed
binding nodes; all other transitions preserve it. -/
theorem runPolicies_resolvedBindings
    (image : ApplicationImage P L) (initialFields : Nat)
    (hnodup : (image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup)
    (hallocated : ∀ instruction ∈ image.instructions,
      instruction.AllocatedAt initialFields)
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (execution next : image.application.PolicyExecution)
    (hresolved : image.ResolvedBindings execution.native.application)
    (hnext : next ∈ (image.application.runPolicies players environment schedule
      execution).support) : image.ResolvedBindings next.native.application := by
  exact image.application.runPolicies_application_invariant
    image.ResolvedBindings
    (fun state who command h => by cases command; exact h)
    (fun state message next hstate hnext =>
      handle_resolvedBindings image initialFields hnodup hallocated
        state next message hstate hnext)
    (fun state command next hstate hnext =>
      environmentStep_resolvedBindings image hnodup state next command hstate hnext)
    players environment schedule execution next hresolved hnext

/-- Ordered admission preserves the same resolved-binding invariant. Disabled
environment commands stutter, while every successful admitted handler call is
an actual successful call of the underlying generated image. -/
theorem ordered_runPolicies_resolvedBindings
    (image : ApplicationImage P L) (initialFields : Nat)
    (hnodup : (image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup)
    (hallocated : ∀ instruction ∈ image.instructions,
      instruction.AllocatedAt initialFields)
    (players : P → image.orderedApplication.PlayerPolicy)
    (environment : image.orderedApplication.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (execution next : image.orderedApplication.PolicyExecution)
    (hresolved : image.ResolvedBindings execution.native.application)
    (hnext : next ∈ (image.orderedApplication.runPolicies players environment schedule
      execution).support) : image.ResolvedBindings next.native.application := by
  apply image.orderedApplication.runPolicies_application_invariant image.ResolvedBindings
    (fun state who command h => by cases command; exact h) _ _
    players environment schedule execution next hresolved hnext
  · intro state message result hstate hresult
    change (image.application.withAdmission image.admitsMessage
      image.admitsEnvironment).handle state message = some result at hresult
    apply handle_resolvedBindings image initialFields hnodup hallocated
      state result message hstate
    exact image.application.withAdmission_handle_some image.admitsMessage
      image.admitsEnvironment state result message hresult
  · intro state command result hstate hresult
    change result ∈ ((image.application.withAdmission image.admitsMessage
      image.admitsEnvironment).environmentStep state command).support at hresult
    rcases image.application.withAdmission_environment_support image.admitsMessage
      image.admitsEnvironment state result command hresult with rfl | hbase
    · exact hstate
    · exact environmentStep_resolvedBindings image hnodup state result command hstate hbase

namespace ResolvedBindings

omit [DecidableEq P] in
/-- Completion of the statically earlier binding supplies the disposition used
by a conditional instruction. Only an opaque disposition carries a canonical
owner-slot obligation; a public default is returned unchanged. -/
theorem conditionalDisposition
    {image : ApplicationImage P L} {state : State P L}
    (hresolved : image.ResolvedBindings state)
    (horigins : image.HasBindingOrigins) (conditional : ConditionalCode P L)
    (hconditional : .conditional conditional ∈ image.instructions)
    (bound : Nat) (hboundary : conditional.endpoint.choiceNode = bound)
    (hcompleted : ∀ node, node < bound → state.memory.done node = true) :
    ∃ disposition, state.memory.accepted conditional.sourceField = some disposition ∧
      ∀ handle, disposition = .opaque handle →
        handle = (conditional.endpoint.owner, conditional.endpoint.sourceSlot) := by
  obtain ⟨before, binding, after, himage, _, horigin⟩ :=
    horigins.origin_of_mem conditional hconditional
  have hbinding : .bind binding ∈ image.instructions := by
    rw [himage]
    simp
  have hdone : state.memory.done binding.node = true :=
    hcompleted binding.node (by rw [← hboundary]; exact horigin.2.2.2)
  obtain ⟨disposition, haccepted, hcanonical⟩ :=
    hresolved binding hbinding hdone
  refine ⟨disposition, ?_, ?_⟩
  · simpa only [horigin.1] using haccepted
  · intro handle hopaque
    simpa only [horigin.2.1, horigin.2.2.1] using hcanonical handle hopaque

end ResolvedBindings

end Vegas.ApplicationImage

/-- info: 'Vegas.ApplicationImage.ResolvedBindings.initial' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.ResolvedBindings.initial

/-- info: 'Vegas.ApplicationImage.runPolicies_resolvedBindings' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.runPolicies_resolvedBindings

/-- info: 'Vegas.ApplicationImage.ordered_runPolicies_resolvedBindings' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.ordered_runPolicies_resolvedBindings

/-- info: 'Vegas.ApplicationImage.ResolvedBindings.conditionalDisposition' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.ResolvedBindings.conditionalDisposition
