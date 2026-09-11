/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors.
-/

import Vegas.Compile.ApplicationOrder
import Vegas.Compile.ApplicationPlanCoverage
import Vegas.Compile.ApplicationImageSamples

/-! # Completion footprints of generated application transitions -/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph Interaction GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

omit [DecidableEq P] in
private theorem publish_done_eq (before : State P L)
    (code : PublicChoiceCode P L) (value : L.Val code.guard.ty) (node : Nat) :
    (before.publish code value).memory.done node =
      (decide (node ∈ (ApplicationInstruction.publicChoice code).coveredNodes) ||
        before.memory.done node) := by
  apply Bool.eq_iff_iff.mpr
  simp [State.publish, Memory.publish, ApplicationInstruction.coveredNodes,
    beq_iff_eq, or_assoc]

omit [DecidableEq P] in
private theorem bind_done_eq (before : State P L) (code : BindingCode P L)
    (handle : CommitmentHandle P Nat) (node : Nat) :
    (before.bind code handle).memory.done node =
      (decide (node ∈ (ApplicationInstruction.bind code).coveredNodes) ||
        before.memory.done node) := by
  apply Bool.eq_iff_iff.mpr
  simp [State.bind, ApplicationInstruction.coveredNodes, beq_iff_eq]

omit [DecidableEq P] in
private theorem defaultBind_done_eq (before : State P L) (code : BindingCode P L)
    (value : TypedValue L) (node : Nat) :
    (before.defaultBind code value).memory.done node =
      (decide (node ∈ (ApplicationInstruction.bind code).coveredNodes) ||
        before.memory.done node) := by
  apply Bool.eq_iff_iff.mpr
  simp [State.defaultBind, ApplicationInstruction.coveredNodes, beq_iff_eq]

omit [DecidableEq P] in
private theorem publishConditional_done_eq (before : State P L)
    (code : ConditionalCode P L) (value : Option (L.Val code.secretTy)) (node : Nat) :
    (before.publishConditional code value).memory.done node =
      (decide (node ∈ (ApplicationInstruction.conditional code).coveredNodes) ||
        before.memory.done node) := by
  apply Bool.eq_iff_iff.mpr
  simp [State.publishConditional, ApplicationInstruction.coveredNodes,
    beq_iff_eq, or_assoc]

omit [DecidableEq P] in
private theorem lookup_address_eq (image : ApplicationImage P L) (address : Nat)
    (instruction : ApplicationInstruction P L)
    (hlookup : image.lookup address = some instruction) :
    instruction.address = address := by
  have hfound := List.find?_some hlookup
  simpa only [beq_iff_eq] using hfound

/-- Every successful public handler call completes exactly the nodes covered by
the emitted instruction selected by its payload address. -/
theorem handle_completion_effect (image : ApplicationImage P L)
    (before after : State P L) (message : Message P (Payload P L))
    (hafter : image.handle before message = some after) :
    ∃ instruction ∈ image.instructions,
      message.payload.address? = some instruction.address ∧
      ∀ node, after.memory.done node =
        (decide (node ∈ instruction.coveredNodes) || before.memory.done node) := by
  cases message with
  | mk id payload =>
    cases payload with
    | malformed data => simp [handle] at hafter
    | choice address typed =>
      cases hlookup : image.lookup address with
      | none => simp [handle, hlookup] at hafter
      | some instruction =>
        cases instruction with
        | sample code | bind code | conditional code => simp [handle, hlookup] at hafter
        | publicChoice code =>
          have haddress := lookup_address_eq image address (.publicChoice code) hlookup
          cases htyped : typed.as? code.guard.ty with
          | none => simp [handle, hlookup, htyped] at hafter
          | some value =>
            cases hresolve : code.endpoint.resolve? before.memory.done
                (code.guard.validate before.memory.store) ⟨id, value⟩ with
            | none => simp [handle, hlookup, htyped, hresolve] at hafter
            | some accepted =>
              simp only [handle, hlookup, htyped, hresolve, Option.bind_eq_bind,
                Option.bind_some,
                Option.pure_def, Option.some.injEq] at hafter
              subst after
              exact ⟨.publicChoice code, List.mem_of_find?_eq_some hlookup,
                congrArg some haddress.symm,
                publish_done_eq before code accepted⟩
    | expireChoice address =>
      cases hlookup : image.lookup address with
      | none => simp [handle, hlookup] at hafter
      | some instruction =>
        cases instruction with
        | sample code | bind code | conditional code => simp [handle, hlookup] at hafter
        | publicChoice code =>
          have haddress := lookup_address_eq image address (.publicChoice code) hlookup
          cases hresolve : code.resolveTimeout? before.memory with
          | none => simp [handle, hlookup, hresolve] at hafter
          | some value =>
            simp only [handle, hlookup, hresolve, Option.bind_eq_bind,
              Option.bind_some, Option.map_some,
              Option.some.injEq] at hafter
            subst after
            exact ⟨.publicChoice code, List.mem_of_find?_eq_some hlookup,
              congrArg some haddress.symm,
              publish_done_eq before code value⟩
    | binding address handleValue =>
      cases hlookup : image.lookup address with
      | none => simp [handle, hlookup] at hafter
      | some instruction =>
        cases instruction with
        | sample code | publicChoice code | conditional code => simp [handle, hlookup] at hafter
        | bind code =>
          have haddress := lookup_address_eq image address (.bind code) hlookup
          simp only [handle, hlookup, Option.bind_eq_bind, Option.bind_some,
            Option.pure_def] at hafter
          split at hafter
          · have heq := Option.some.inj hafter
            subst after
            exact ⟨.bind code, List.mem_of_find?_eq_some hlookup,
              congrArg some haddress.symm,
              bind_done_eq before code handleValue⟩
          · contradiction
    | expireBinding address =>
      cases hlookup : image.lookup address with
      | none => simp [handle, hlookup] at hafter
      | some instruction =>
        cases instruction with
        | sample code | publicChoice code | conditional code => simp [handle, hlookup] at hafter
        | bind code =>
          have haddress := lookup_address_eq image address (.bind code) hlookup
          cases hresolve : code.resolveTimeout? before.memory with
          | none => simp [handle, hlookup, hresolve] at hafter
          | some value =>
            simp only [handle, hlookup, hresolve, Option.bind_eq_bind,
              Option.bind_some, Option.map_some,
              Option.some.injEq] at hafter
            subst after
            exact ⟨.bind code, List.mem_of_find?_eq_some hlookup,
              congrArg some haddress.symm,
              defaultBind_done_eq before code ⟨code.ty, value⟩⟩
    | conditional address payload =>
      cases hlookup : image.lookup address with
      | none => simp [handle, hlookup] at hafter
      | some instruction =>
        cases instruction with
        | sample code | publicChoice code | bind code => simp [handle, hlookup] at hafter
        | conditional code =>
          have haddress := lookup_address_eq image address (.conditional code) hlookup
          cases hdecoded : code.decode payload with
          | none => simp [handle, hlookup, hdecoded] at hafter
          | some decoded =>
            cases hresolve : code.endpoint.resolveDisposition? before.memory.clock
                (before.verify code) (code.binding? before.memory) before.memory.done
                (code.canOpen before.memory.store) ⟨id, decoded⟩ with
            | none => simp [handle, hlookup, hdecoded, hresolve] at hafter
            | some result =>
              simp only [handle, hlookup, hdecoded, hresolve, Option.bind_eq_bind,
                Option.bind_some,
                Option.pure_def, Option.some.injEq] at hafter
              subst after
              exact ⟨.conditional code, List.mem_of_find?_eq_some hlookup,
                congrArg some haddress.symm,
                publishConditional_done_eq before code result⟩

omit [DecidableEq P] in
/-- A supported sample either stutters or completes exactly the singleton
footprint of the selected emitted sample instruction. -/
theorem sample_completion_effect (image : ApplicationImage P L)
    (before after : State P L) (address : Nat)
    (hafter : after ∈ (image.sample before address).support) :
    after = before ∨
      ∃ code, image.lookup address = some (.sample code) ∧
        (.sample (P := P) code : ApplicationInstruction P L) ∈ image.instructions ∧
        ∀ node, after.memory.done node =
          (decide (node ∈ (ApplicationInstruction.sample (P := P) code).coveredNodes) ||
            before.memory.done node) := by
  rcases image.sample_support before address after hafter with rfl | hsample
  · exact Or.inl rfl
  · obtain ⟨code, reads, value, hlookup, _, _, _, _, rfl⟩ := hsample
    refine Or.inr ⟨code, hlookup, List.mem_of_find?_eq_some hlookup, ?_⟩
    intro node
    apply Bool.eq_iff_iff.mpr
    simp [State.sample, ApplicationInstruction.coveredNodes, beq_iff_eq]

end Vegas.ApplicationImage

/-- info: 'Vegas.ApplicationImage.handle_completion_effect' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.handle_completion_effect

/-- info: 'Vegas.ApplicationImage.sample_completion_effect' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.sample_completion_effect
