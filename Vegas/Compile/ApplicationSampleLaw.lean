/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationSampleFrames
import Interaction.MessageApplicationHarmonic

/-! # Fixed chance laws under arbitrary public-message policies

An emitted sample has a fixed law when its distribution evaluator returns the
same law at every read environment. Before resolution its continuation is that
law; afterwards it is the actual stored draw. Disjoint instruction footprints
prevent other handlers or sample sites from changing this continuation.

The whole-run result retains unresolved executions. A marginal theorem for
the actual stored value requires the sample to have resolved on all support;
it does not condition on successful runs or assert a service guarantee.
-/

noncomputable section

namespace Vegas

open EventGraph Interaction GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace SampleCode

def read? (code : SampleCode L) (memory : ApplicationImage.Memory P L) :
    Option (L.Val code.dist.ty) :=
  (memory.store code.outputField).bind (fun value => value.as? code.dist.ty)

def continuation (code : SampleCode L) (law : FinDist (L.Val code.dist.ty))
    (memory : ApplicationImage.Memory P L) : FinDist (Option (L.Val code.dist.ty)) :=
  if memory.done code.node then FinDist.pure (code.read? memory) else law.map some

omit [DecidableEq P] in
theorem continuation_of_frame (code : SampleCode L) (law : FinDist (L.Val code.dist.ty))
    (before after : ApplicationImage.Memory P L)
    (hdone : after.done code.node = before.done code.node)
    (hstore : after.store code.outputField = before.store code.outputField) :
    code.continuation law after = code.continuation law before := by
  simp only [continuation, read?, hdone, hstore]

omit [DecidableEq P] in
theorem continuation_sample (code : SampleCode L) (law : FinDist (L.Val code.dist.ty))
    (state : ApplicationImage.State P L) (value : L.Val code.dist.ty) :
    code.continuation law (state.sample code value).memory = FinDist.pure (some value) := by
  simp [continuation, read?, ApplicationImage.State.sample, TypedValue.as?]

end SampleCode

namespace ApplicationImage

omit [DecidableEq P] in
/-- Any chance invocation preserves the selected site's continuation law.
The environment may select another site, invoke too early, or retry a completed
site; none of these operations offers a fresh draw of the selected sample. -/
theorem sample_harmonic (image : ApplicationImage P L) (code : SampleCode L)
    (hcode : .sample code ∈ image.instructions)
    (hcovered : (image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup)
    (hallocated : (image.instructions.flatMap ApplicationInstruction.allocatedFields).Nodup)
    (law : FinDist (L.Val code.dist.ty))
    (hfixed : ∀ reads, code.dist.eval reads = law)
    (state : State P L) (address : Nat) :
    (image.sample state address).bind (fun next => code.continuation law next.memory) =
      code.continuation law state.memory := by
  classical
  cases hlookup : image.lookup address with
  | none => simp only [sample, hlookup, FinDist.pure_bind]
  | some instruction =>
      cases instruction with
      | publicChoice other | bind other | conditional other =>
          simp only [sample, hlookup, FinDist.pure_bind]
      | sample other =>
          simp only [sample, hlookup]
          split
          · rename_i hready
            cases hreads : ReadEnv.ofStoreExec? state.memory.store other.dist.reads with
            | none => simp only [FinDist.pure_bind]
            | some reads =>
                rw [FinDist.bind_map]
                by_cases heq : other = code
                · subst other
                  have hnotDone : state.memory.done code.node = false := by
                    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hready
                    exact hready.1
                  rw [hfixed]
                  calc
                    _ = law.bind (fun value => FinDist.pure (some value)) := by
                      apply FinDist.bind_congr
                      intro value _
                      exact code.continuation_sample law state value
                    _ = _ := by
                      simp only [SampleCode.continuation, hnotDone,
                        Bool.false_eq_true, ↓reduceIte]
                      rfl
                · have hother : .sample other ∈ image.instructions :=
                    List.mem_of_find?_eq_some hlookup
                  calc
                    _ = (other.dist.eval reads).bind
                        (fun _ => code.continuation law state.memory) := by
                      apply FinDist.bind_congr
                      intro value _
                      have hframe := image.sample_frame_other code hcode hcovered hallocated
                        other hother heq state value
                      exact code.continuation_of_frame law _ _ hframe.1 hframe.2
                    _ = _ := FinDist.bind_const _ _
          · exact FinDist.pure_bind _ _

/-- A fixed emitted chance law is invariant through arbitrary randomized raw
players, adaptive environment policies, and finite invocation schedules. -/
theorem runPolicies_sample_continuation (image : ApplicationImage P L) (code : SampleCode L)
    (hcode : .sample code ∈ image.instructions)
    (hcovered : (image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup)
    (hallocated : (image.instructions.flatMap ApplicationInstruction.allocatedFields).Nodup)
    (law : FinDist (L.Val code.dist.ty)) (hfixed : ∀ reads, code.dist.eval reads = law)
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation P))
    (execution : image.application.PolicyExecution) :
    (image.application.runPolicies players environment schedule execution).bind
        (fun next => code.continuation law next.native.application.memory) =
      code.continuation law execution.native.application.memory := by
  apply image.application.runPolicies_application_harmonic
    (fun state => code.continuation law state.memory)
  · intro state who command
    cases command
    rfl
  · intro state message next hnext
    have hframe := image.handle_sample_frame code hcode hcovered hallocated state message next hnext
    exact code.continuation_of_frame law _ _ hframe.1 hframe.2
  · intro state command
    cases command with
    | advance clock =>
        simp only [application, FinDist.pure_bind, SampleCode.continuation,
          SampleCode.read?, State.advance]
    | sample address =>
        exact image.sample_harmonic code hcode hcovered hallocated law hfixed state address

/-- If the selected sample resolves everywhere, its actual typed readout has
the fixed emitted law. The completion premise is about the whole distribution,
not a conditioned subset. No restriction is imposed on the message policies. -/
theorem runPolicies_sample_law (image : ApplicationImage P L) (code : SampleCode L)
    (hcode : .sample code ∈ image.instructions)
    (hcovered : (image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup)
    (hallocated : (image.instructions.flatMap ApplicationInstruction.allocatedFields).Nodup)
    (law : FinDist (L.Val code.dist.ty)) (hfixed : ∀ reads, code.dist.eval reads = law)
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation P))
    (execution : image.application.PolicyExecution)
    (hnotDone : execution.native.application.memory.done code.node = false)
    (hresolved : ∀ next ∈
        (image.application.runPolicies players environment schedule execution).support,
      next.native.application.memory.done code.node = true) :
    (image.application.runPolicies players environment schedule execution).map
        (fun next => code.read? next.native.application.memory) = law.map some := by
  rw [FinDist.map_eq_bind]
  calc
    _ = (image.application.runPolicies players environment schedule execution).bind
        (fun next => code.continuation law next.native.application.memory) := by
      apply FinDist.bind_congr
      intro next hnext
      simp only [SampleCode.continuation, hresolved next hnext, ↓reduceIte]
    _ = _ := by
      rw [image.runPolicies_sample_continuation code hcode hcovered hallocated law hfixed]
      simp only [SampleCode.continuation, hnotDone, Bool.false_eq_true, ↓reduceIte]

end ApplicationImage

end Vegas

/-- info: 'Vegas.ApplicationImage.runPolicies_sample_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.runPolicies_sample_law
