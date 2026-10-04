/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingFrameRounds
import Vegas.Pending.ReactivePlayerWindow

/-! # Joint binding repair through an arbitrary foreign roster

Every passive sample and raw foreign response remains in the existing service
law. Equal complete foreign inputs permit the same response draw on both sides.
The private repair is not invoked while its owner has no response opportunity.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

private theorem foreign_invoke_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (actor : Player) (different : actor ≠ owner) :
    let app := runtime.reactiveApplication leaks
    ∃ coupling : PMF (app.Execution × app.Execution),
      coupling.map Prod.fst = app.invoke players actor original ∧
      coupling.map Prod.snd = app.invoke players actor repaired ∧
      ∀ next ∈ coupling.support, Frame runtime leaks memory owner next.1 next.2 := by
  let app := runtime.reactiveApplication leaks
  let law := players actor (original.recall actor) (original.observe app actor)
  let coupling := law.map fun response =>
    (original.respond app actor response, repaired.respond app actor response)
  refine ⟨coupling, ?_, ?_, ?_⟩
  · rw [PMF.map_comp]
    rfl
  · rw [PMF.map_comp]
    change law.map _ = (players actor (repaired.recall actor)
      (repaired.observe app actor)).map _
    rw [← frame.recall actor different, ← frame.foreign_observed actor different]
    rfl
  · intro next supported
    obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ supported
    exact frame.foreign_response actor different response

/-- One foreign activation shares the existing passive draw and its complete
response law. No restriction is imposed on the foreign player's raw response. -/
theorem foreign_activation_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (actor : Player) (different : actor ≠ owner) :
    let app := runtime.reactiveApplication leaks
    ∃ coupling : PMF (app.Execution × app.Execution),
      coupling.map Prod.fst = app.dispatch players (.activate actor) original ∧
      coupling.map Prod.snd = app.dispatch players (.activate actor) repaired ∧
      ∀ next ∈ coupling.support, Frame runtime leaks memory owner next.1 next.2 := by
  classical
  let app := runtime.reactiveApplication leaks
  let sample := leaks actor original.network.pending
  have existsStep selected :=
    (frame.activate actor selected).foreign_invoke_coupling players actor different
  let step := fun selected => (existsStep selected).choose
  refine ⟨sample.bind step, ?_, ?_, ?_⟩
  · rw [PMF.map_bind]
    change _ = (original.environmentStep app (.activate actor)).bind _
    rw [ReactiveApplication.Execution.activation_samples, PMF.bind_map]
    apply bind_congr_on_support _
    intro selected _
    exact (existsStep selected).choose_spec.1
  · rw [PMF.map_bind]
    change _ = (repaired.environmentStep app (.activate actor)).bind _
    rw [ReactiveApplication.Execution.activation_samples, PMF.bind_map]
    have same : leaks actor repaired.network.pending = sample := by rw [← frame.network]
    change _ = (leaks actor repaired.network.pending).bind _
    rw [same]
    apply bind_congr_on_support _
    intro selected _
    exact (existsStep selected).choose_spec.2.1
  · intro next supported
    obtain ⟨selected, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
    exact (existsStep selected).choose_spec.2.2 next reached

/-- A whole response tail after the focal owner's last visit preserves the
joint repair frame. Raw foreign actions, pending samples and recall are kept,
and the private implementation memory is unchanged throughout this tail. -/
theorem foreign_window_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (visits : List Player)
    (absent : owner ∉ visits) :
    let app := runtime.reactiveApplication leaks
    ∃ coupling : PMF (app.Execution × app.Execution),
      coupling.map Prod.fst = runtime.runInteractionPlan leaks players network
        (visits.map ServiceInstruction.player) original ∧
      coupling.map Prod.snd = runtime.runInteractionPlan leaks players network
        (visits.map ServiceInstruction.player) repaired ∧
      ∀ next ∈ coupling.support, Frame runtime leaks memory owner next.1 next.2 := by
  classical
  let app := runtime.reactiveApplication leaks
  induction visits generalizing original repaired with
  | nil =>
      exact ⟨PMF.pure (original, repaired), PMF.pure_map .., PMF.pure_map ..,
        fun next member => by cases (PMF.mem_support_pure_iff _ _).mp member; exact frame⟩
  | cons actor rest ih =>
      have different : actor ≠ owner := fun equal => absent (by
        simp only [equal, List.mem_cons_self])
      have restAbsent : owner ∉ rest := fun member => absent (List.mem_cons_of_mem _ member)
      obtain ⟨step, first, second, related⟩ :=
        frame.foreign_activation_coupling players actor different
      have existsTail next (supported : next ∈ step.support) :=
        ih (related next supported) restAbsent
      let tail := fun next supported => (existsTail next supported).choose
      refine ⟨step.bindOnSupport tail, ?_, ?_, ?_⟩
      · rw [map_bindOnSupport]
        calc
          _ = step.bind (fun next => runtime.runInteractionPlan leaks players network
              (rest.map ServiceInstruction.player) next.1) := by
            apply bindOnSupport_eq_bind_of_eq_on_support _
            intro next supported
            exact (existsTail next supported).choose_spec.1
          _ = (step.map Prod.fst).bind (runtime.runInteractionPlan leaks players network
              (rest.map ServiceInstruction.player)) := (PMF.bind_map ..).symm
          _ = _ := by
            rw [first]
            simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
              PMF.pure_bind]
      · rw [map_bindOnSupport]
        calc
          _ = step.bind (fun next => runtime.runInteractionPlan leaks players network
              (rest.map ServiceInstruction.player) next.2) := by
            apply bindOnSupport_eq_bind_of_eq_on_support _
            intro next supported
            exact (existsTail next supported).choose_spec.2.1
          _ = (step.map Prod.snd).bind (runtime.runInteractionPlan leaks players network
              (rest.map ServiceInstruction.player)) := (PMF.bind_map ..).symm
          _ = _ := by
            rw [second]
            simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
              PMF.pure_bind]
      · intro final supported
        obtain ⟨next, chosen, reached⟩ :=
          Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ supported)
        exact (existsTail next chosen).choose_spec.2.2 final reached

end Vegas.EventGraphRuntime.BindingMemory.Frame
