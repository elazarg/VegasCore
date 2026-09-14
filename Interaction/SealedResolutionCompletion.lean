/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionRounds

/-! # Persistence after normal sealed resolution

Once every rule has completed without a timeout, later native traffic cannot
change the public event log or introduce a timeout. Private commands may still
fill previously empty commitment slots, and clock commands still advance the
clock; neither operation changes the completed public result.
-/

noncomputable section

namespace Interaction.SealedResolution

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

theorem complete_node (runtime : SealedResolution Principal Value)
    (state : PublicState Principal Value) (node : Nat)
    (hcomplete : runtime.complete state = true) (hnode : node < runtime.program.rules.length) :
    state.completed node = true :=
  List.all_eq_true.mp hcomplete node (List.mem_range.mpr hnode)

theorem visit_of_completed (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (node : Nat)
    (hcompleted : state.completed node = true) :
    runtime.visit resolveExpired state node = state := by
  unfold visit
  split
  · rfl
  · simp [hcompleted]

theorem refresh_of_complete (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (hcomplete : runtime.complete state = true) :
    runtime.refresh resolveExpired state = state := by
  unfold refresh
  have hall : (List.range runtime.program.rules.length).all state.completed = true := hcomplete
  generalize List.range runtime.program.rules.length = nodes at hall ⊢
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
      have hnode := List.all_eq_true.mp hall node (List.mem_cons_self)
      have hrest : rest.all state.completed = true := by
        apply List.all_eq_true.mpr
        intro target htarget
        exact List.all_eq_true.mp hall target (List.mem_cons_of_mem node htarget)
      simp only [List.foldl_cons]
      rw [runtime.visit_of_completed resolveExpired state node hnode]
      exact ih hrest

theorem tick_visible_of_complete (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value) (hcomplete : runtime.complete state.visible = true) :
    (runtime.tick state).visible = { state.visible with clock := state.visible.clock + 1 } := by
  unfold tick
  apply runtime.refresh_of_complete
  cases state with
  | mk service visible =>
      cases visible
      exact hcomplete

variable [DecidableEq Principal] [DecidableEq Value]

/-- A normally completed application rejects every later application payload.
Pool delivery and inclusion may still be recorded by the surrounding runner. -/
theorem validateMessage?_eq_none_of_complete_clear
    (runtime : SealedResolution Principal Value) (state : ApplicationState Principal Value)
    (hcomplete : runtime.complete state.visible = true) (hclear : state.visible.timeouts = [])
    (message : Message Principal (SealedProgram.Payload Principal Value)) :
    runtime.validateMessage? state message = none := by
  rw [runtime.validateMessage?_no_timeout state hclear message]
  rcases message with ⟨id, payload⟩
  cases payload with
  | malformed => rfl
  | cleartext node value => rfl
  | commitment node handle =>
      cases hrule : runtime.program.rules[node]? with
      | none => simp [SealedProgram.validateMessage?, hrule]
      | some rule =>
          have hindex : node < runtime.program.rules.length :=
            (List.getElem?_eq_some_iff.mp hrule).1
          have hdone : SealedProgram.done state.visible.events node = true := by
            have hcompleted := runtime.complete_node state.visible node hcomplete hindex
            simpa [PublicState.completed, hclear] using hcompleted
          cases hkind : rule.kind <;>
            simp [SealedProgram.validateMessage?, hrule, hkind, hdone]
  | opening node handle claimed =>
      cases hrule : runtime.program.rules[node]? with
      | none => simp [SealedProgram.validateMessage?, hrule]
      | some rule =>
          have hindex : node < runtime.program.rules.length :=
            (List.getElem?_eq_some_iff.mp hrule).1
          have hdone : SealedProgram.done state.visible.events node = true := by
            have hcompleted := runtime.complete_node state.visible node hcomplete hindex
            simpa [PublicState.completed, hclear] using hcompleted
          cases hkind : rule.kind <;>
            simp [SealedProgram.validateMessage?, hrule, hkind, hdone]

theorem handle_eq_none_of_complete_clear
    (runtime : SealedResolution Principal Value) (state : ApplicationState Principal Value)
    (hcomplete : runtime.complete state.visible = true) (hclear : state.visible.timeouts = [])
    (message : Message Principal (SealedProgram.Payload Principal Value)) :
    runtime.handle state message = none := by
  simp [handle, runtime.validateMessage?_eq_none_of_complete_clear state hcomplete hclear message]

/-- Arbitrary later policies preserve a normally completed public result.
They may advance the clock, update histories and receipts, or register unused
private slots. -/
theorem runPolicies_complete_clear
    (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (initial next : runtime.messageApplication.PolicyExecution)
    (hcomplete : runtime.complete initial.native.application.visible = true)
    (hclear : initial.native.application.visible.timeouts = [])
    (hnext : next ∈ (runtime.messageApplication.runPolicies players environment schedule
      initial).support) :
    next.native.application.visible.events = initial.native.application.visible.events ∧
      next.native.application.visible.timeouts = [] ∧
      runtime.complete next.native.application.visible = true := by
  apply runtime.messageApplication.runPolicies_application_invariant
    (fun state => state.visible.events = initial.native.application.visible.events ∧
      state.visible.timeouts = [] ∧ runtime.complete state.visible = true)
    ?_ ?_ ?_ players environment schedule initial next ⟨rfl, hclear, hcomplete⟩ hnext
  · intro state who command hstate
    exact hstate
  · intro state message after hstate hafter
    change runtime.handle state message = some after at hafter
    rw [runtime.handle_eq_none_of_complete_clear state hstate.2.2 hstate.2.1 message] at hafter
    contradiction
  · intro state command after hstate hafter
    simp only [messageApplication, FinDist.mem_support_pure] at hafter
    subst after
    rw [runtime.tick_visible_of_complete state hstate.2.2]
    exact ⟨hstate.1, hstate.2.1, hstate.2.2⟩

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.runPolicies_complete_clear' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runPolicies_complete_clear
