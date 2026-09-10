/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationCompletion
import Vegas.Compile.ApplicationPlanAllocation

/-! # Native frame facts for generated chance instructions -/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph Interaction GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

omit [DecidableEq P] in
private theorem instruction_footprints_disjoint
    (image : ApplicationImage P L)
    (footprint : ApplicationInstruction P L → List Nat)
    (hnodup : (image.instructions.flatMap footprint).Nodup)
    (first second : ApplicationInstruction P L)
    (hfirst : first ∈ image.instructions) (hsecond : second ∈ image.instructions)
    (hne : first ≠ second) : List.Disjoint (footprint first) (footprint second) := by
  have hpairwise := (List.nodup_flatMap.mp hnodup).2
  let : Std.Symm (fun a b : ApplicationInstruction P L =>
      List.Disjoint (footprint a) (footprint b)) :=
    ⟨fun _ _ h => h.symm⟩
  exact hpairwise.forall hfirst hsecond hne

omit [DecidableEq P] in
private theorem ne_of_mem_of_disjoint {a b : Nat} {rest : List Nat}
    (hdisjoint : List.Disjoint [a] rest) (hmem : b ∈ rest) : a ≠ b := by
  intro heq
  subst b
  exact (List.disjoint_left.mp hdisjoint) (by simp) hmem

omit [DecidableEq P] in
/-- Sampling a distinct instruction changes neither the selected sample's
completion bit nor its allocated output field. -/
theorem State.sample_frame_of_ne (state : State P L)
    (selected other : SampleCode L) (value : L.Val other.dist.ty)
    (hnode : selected.node ≠ other.node)
    (hfield : selected.outputField ≠ other.outputField) :
    (state.sample other value).memory.done selected.node =
        state.memory.done selected.node ∧
      (state.sample other value).memory.store selected.outputField =
        state.memory.store selected.outputField := by
  simp [State.sample, hnode, Store.set_ne, hfield]

omit [DecidableEq P] in
/-- Generated footprint separation supplies the raw node and field inequalities
needed by `State.sample_frame_of_ne`. -/
theorem sample_frame_other (image : ApplicationImage P L)
    (selected : SampleCode L)
    (hselected : (.sample (P := P) selected : ApplicationInstruction P L) ∈
      image.instructions)
    (hcovered : (image.instructions.flatMap
      ApplicationInstruction.coveredNodes).Nodup)
    (hallocated : (image.instructions.flatMap
      ApplicationInstruction.allocatedFields).Nodup)
    (other : SampleCode L)
    (hother : (.sample (P := P) other : ApplicationInstruction P L) ∈
      image.instructions)
    (hne : other ≠ selected)
    (state : State P L) (value : L.Val other.dist.ty) :
    (state.sample other value).memory.done selected.node =
        state.memory.done selected.node ∧
      (state.sample other value).memory.store selected.outputField =
        state.memory.store selected.outputField := by
  have hinstruction : (ApplicationInstruction.sample (P := P) selected) ≠ .sample other := by
    intro heq
    cases heq
    exact hne rfl
  have hnodes := instruction_footprints_disjoint image
    ApplicationInstruction.coveredNodes hcovered _ _ hselected hother hinstruction
  have hfields := instruction_footprints_disjoint image
    ApplicationInstruction.allocatedFields hallocated _ _ hselected hother hinstruction
  apply state.sample_frame_of_ne selected other value
  · apply ne_of_mem_of_disjoint hnodes
    simp [ApplicationInstruction.coveredNodes]
  · apply ne_of_mem_of_disjoint hfields
    simp [ApplicationInstruction.allocatedFields]

omit [DecidableEq P] in
private theorem State.publish_sample_frame (state : State P L)
    (selected : SampleCode L) (code : PublicChoiceCode P L)
    (value : L.Val code.guard.ty)
    (hnodes : List.Disjoint
      (ApplicationInstruction.sample (P := P) selected).coveredNodes
      (ApplicationInstruction.publicChoice code).coveredNodes)
    (hfields : List.Disjoint
      (ApplicationInstruction.sample (P := P) selected).allocatedFields
      (ApplicationInstruction.publicChoice code).allocatedFields) :
    (state.publish code value).memory.done selected.node = state.memory.done selected.node ∧
      (state.publish code value).memory.store selected.outputField =
        state.memory.store selected.outputField := by
  have hchoiceNode : selected.node ≠ code.endpoint.choiceNode := by
    apply ne_of_mem_of_disjoint hnodes
    simp [ApplicationInstruction.coveredNodes]
  have hpublicationNode : selected.node ≠ code.endpoint.publicationNode := by
    apply ne_of_mem_of_disjoint hnodes
    simp [ApplicationInstruction.coveredNodes]
  have hchoiceField : selected.outputField ≠ code.choiceField := by
    apply ne_of_mem_of_disjoint hfields
    simp [ApplicationInstruction.allocatedFields]
  have hpublicationField : selected.outputField ≠ code.publicationField := by
    apply ne_of_mem_of_disjoint hfields
    simp [ApplicationInstruction.allocatedFields]
  simp [State.publish, Memory.publish, hchoiceNode, hpublicationNode,
    Store.set_ne, hchoiceField, hpublicationField]

omit [DecidableEq P] in
private theorem State.bind_sample_frame (state : State P L)
    (selected : SampleCode L) (code : BindingCode P L)
    (handle : CommitmentHandle P Nat)
    (hnodes : List.Disjoint
      (ApplicationInstruction.sample (P := P) selected).coveredNodes
      (ApplicationInstruction.bind code).coveredNodes) :
    (state.bind code handle).memory.done selected.node = state.memory.done selected.node ∧
      (state.bind code handle).memory.store selected.outputField =
        state.memory.store selected.outputField := by
  have hnode : selected.node ≠ code.node := by
    apply ne_of_mem_of_disjoint hnodes
    simp [ApplicationInstruction.coveredNodes]
  simp [State.bind, hnode]

omit [DecidableEq P] in
private theorem State.defaultBind_sample_frame (state : State P L)
    (selected : SampleCode L) (code : BindingCode P L) (value : TypedValue L)
    (hnodes : List.Disjoint
      (ApplicationInstruction.sample (P := P) selected).coveredNodes
      (ApplicationInstruction.bind code).coveredNodes) :
    (state.defaultBind code value).memory.done selected.node = state.memory.done selected.node ∧
      (state.defaultBind code value).memory.store selected.outputField =
        state.memory.store selected.outputField := by
  have hnode : selected.node ≠ code.node := by
    apply ne_of_mem_of_disjoint hnodes
    simp [ApplicationInstruction.coveredNodes]
  simp [State.defaultBind, hnode]

omit [DecidableEq P] in
private theorem State.publishConditional_sample_frame (state : State P L)
    (selected : SampleCode L) (code : ConditionalCode P L)
    (value : Option (L.Val code.secretTy))
    (hnodes : List.Disjoint
      (ApplicationInstruction.sample (P := P) selected).coveredNodes
      (ApplicationInstruction.conditional code).coveredNodes)
    (hfields : List.Disjoint
      (ApplicationInstruction.sample (P := P) selected).allocatedFields
      (ApplicationInstruction.conditional code).allocatedFields) :
    (state.publishConditional code value).memory.done selected.node =
        state.memory.done selected.node ∧
      (state.publishConditional code value).memory.store selected.outputField =
        state.memory.store selected.outputField := by
  have hchoiceNode : selected.node ≠ code.endpoint.choiceNode := by
    apply ne_of_mem_of_disjoint hnodes
    simp [ApplicationInstruction.coveredNodes]
  have hpublicationNode : selected.node ≠ code.endpoint.publicationNode := by
    apply ne_of_mem_of_disjoint hnodes
    simp [ApplicationInstruction.coveredNodes]
  have hchoiceField : selected.outputField ≠ code.choiceField := by
    apply ne_of_mem_of_disjoint hfields
    simp [ApplicationInstruction.allocatedFields]
  have hpublicationField : selected.outputField ≠ code.publicationField := by
    apply ne_of_mem_of_disjoint hfields
    simp [ApplicationInstruction.allocatedFields]
  simp [State.publishConditional, hchoiceNode, hpublicationNode,
    Store.set_ne, hchoiceField, hpublicationField]

/-- Arbitrary accepted public messages cannot complete or overwrite a generated
sample instruction. Message payloads have no chance constructor, and generated
node/field footprints are disjoint. -/
theorem handle_sample_frame (image : ApplicationImage P L) (selected : SampleCode L)
    (hselected : (.sample (P := P) selected : ApplicationInstruction P L) ∈
      image.instructions)
    (hcovered : (image.instructions.flatMap
      ApplicationInstruction.coveredNodes).Nodup)
    (hallocated : (image.instructions.flatMap
      ApplicationInstruction.allocatedFields).Nodup)
    (before : State P L) (message : Message P (Payload P L)) (after : State P L)
    (hafter : image.handle before message = some after) :
    after.memory.done selected.node = before.memory.done selected.node ∧
      after.memory.store selected.outputField = before.memory.store selected.outputField := by
  rcases message with ⟨id, payload⟩
  cases payload with
  | malformed data => simp [handle] at hafter
  | choice address typed =>
      cases hlookup : image.lookup address with
      | none => simp [handle, hlookup] at hafter
      | some instruction =>
          have hmem := List.mem_of_find?_eq_some hlookup
          cases instruction with
          | sample code | bind code | conditional code => simp [handle, hlookup] at hafter
          | publicChoice code =>
              cases htyped : typed.as? code.guard.ty with
              | none => simp [handle, hlookup, htyped] at hafter
              | some value =>
                  cases hresolve : code.endpoint.resolve? before.memory.done
                      (code.guard.validate before.memory.store) ⟨id, value⟩ with
                  | none => simp [handle, hlookup, htyped, hresolve] at hafter
                  | some accepted =>
                      simp only [handle, hlookup, htyped, hresolve, Option.bind_eq_bind,
                        Option.bind_some, Option.pure_def, Option.some.injEq] at hafter
                      subst after
                      apply before.publish_sample_frame selected code accepted
                      · exact instruction_footprints_disjoint image _ hcovered _ _ hselected
                          hmem (by intro h; cases h)
                      · exact instruction_footprints_disjoint image _ hallocated _ _ hselected
                          hmem (by intro h; cases h)
  | expireChoice address =>
      cases hlookup : image.lookup address with
      | none => simp [handle, hlookup] at hafter
      | some instruction =>
          have hmem := List.mem_of_find?_eq_some hlookup
          cases instruction with
          | sample code | bind code | conditional code => simp [handle, hlookup] at hafter
          | publicChoice code =>
              cases hresolve : code.resolveTimeout? before.memory with
              | none => simp [handle, hlookup, hresolve] at hafter
              | some value =>
                  simp only [handle, hlookup, hresolve, Option.bind_eq_bind,
                    Option.bind_some, Option.map_some, Option.some.injEq] at hafter
                  subst after
                  apply before.publish_sample_frame selected code value
                  · exact instruction_footprints_disjoint image _ hcovered _ _ hselected
                      hmem (by intro h; cases h)
                  · exact instruction_footprints_disjoint image _ hallocated _ _ hselected
                      hmem (by intro h; cases h)
  | binding address handleValue =>
      cases hlookup : image.lookup address with
      | none => simp [handle, hlookup] at hafter
      | some instruction =>
          have hmem := List.mem_of_find?_eq_some hlookup
          cases instruction with
          | sample code | publicChoice code | conditional code => simp [handle, hlookup] at hafter
          | bind code =>
              simp only [handle, hlookup, Option.bind_eq_bind, Option.bind_some,
                Option.pure_def] at hafter
              split at hafter
              · cases hafter
                apply before.bind_sample_frame selected code handleValue
                exact instruction_footprints_disjoint image _ hcovered _ _ hselected
                  hmem (by intro h; cases h)
              · contradiction
  | expireBinding address =>
      cases hlookup : image.lookup address with
      | none => simp [handle, hlookup] at hafter
      | some instruction =>
          have hmem := List.mem_of_find?_eq_some hlookup
          cases instruction with
          | sample code | publicChoice code | conditional code => simp [handle, hlookup] at hafter
          | bind code =>
              cases hresolve : code.resolveTimeout? before.memory with
              | none => simp [handle, hlookup, hresolve] at hafter
              | some value =>
                  simp only [handle, hlookup, hresolve, Option.bind_eq_bind,
                    Option.bind_some, Option.map_some, Option.some.injEq] at hafter
                  subst after
                  apply before.defaultBind_sample_frame selected code ⟨code.ty, value⟩
                  exact instruction_footprints_disjoint image _ hcovered _ _ hselected
                    hmem (by intro h; cases h)
  | conditional address payload =>
      cases hlookup : image.lookup address with
      | none => simp [handle, hlookup] at hafter
      | some instruction =>
          have hmem := List.mem_of_find?_eq_some hlookup
          cases instruction with
          | sample code | publicChoice code | bind code => simp [handle, hlookup] at hafter
          | conditional code =>
              cases hdecoded : code.decode payload with
              | none => simp [handle, hlookup, hdecoded] at hafter
              | some decoded =>
                  cases hresolve : code.endpoint.resolveDisposition? before.memory.clock
                      (before.verify code) (code.binding? before.memory) before.memory.done
                      (code.canOpen before.memory.store) ⟨id, decoded⟩ with
                  | none => simp [handle, hlookup, hdecoded, hresolve] at hafter
                  | some result =>
                      simp only [handle, hlookup, hdecoded, hresolve, Option.bind_eq_bind,
                        Option.bind_some, Option.pure_def, Option.some.injEq] at hafter
                      subst after
                      apply before.publishConditional_sample_frame selected code result
                      · exact instruction_footprints_disjoint image _ hcovered _ _ hselected
                          hmem (by intro h; cases h)
                      · exact instruction_footprints_disjoint image _ hallocated _ _ hselected
                          hmem (by intro h; cases h)

end Vegas.ApplicationImage

/-- info: 'Vegas.ApplicationImage.sample_frame_other' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.sample_frame_other

/-- info: 'Vegas.ApplicationImage.handle_sample_frame' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.handle_sample_frame
