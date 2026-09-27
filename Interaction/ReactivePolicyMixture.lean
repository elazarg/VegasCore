/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveImplementation

/-! # Behavioral realization of a finite family of response policies

A latent choice selects an existing response policy. Its behavioral realization
conditions that choice on actual own recall. This adds no state to the runtime;
the implementation is the existing private-strategy construction.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal) {Index : Type}

def policyMixture (initial : FinDist Index) (policies : Index → app.Policy) :
    app.Implementation Index where
  initial := initial
  respond index input := (policies index input.1 input.2).map fun action => (action, index)

theorem policyMixture_policy (initial : FinDist Index) (policies : Index → app.Policy)
    (past : List app.PlayerEntry) (view : app.PlayerView) :
    (app.policyMixture initial policies).policy past view =
      ((app.policyMixture initial policies).posterior past).bind
        (fun index => policies index past view) := by
  simp only [Implementation.policy_eq, policyMixture, FinDist.map_bind,
    FinDist.map_comp, Function.comp_def]
  apply FinDist.bind_congr
  intro index _
  exact FinDist.map_id _

/-- A response whose law does not use the latent choice cannot update it. -/
theorem policyMixture_posterior_snoc (initial : FinDist Index) (policies : Index → app.Policy)
    (past : List app.PlayerEntry) (entry : app.PlayerEntry) (law : FinDist app.Action)
    (same : ∀ index, policies index past entry.beforeView = law) :
    (app.policyMixture initial policies).posterior (past ++ [entry]) =
      (app.policyMixture initial policies).posterior past := by
  rw [Implementation.posterior_snoc]
  change (((app.policyMixture initial policies).posterior past).bind
    (fun index => (policies index past entry.beforeView).map fun action => (action, index))
      |>.condOnFibre Prod.fst entry.action).map Prod.snd = _
  have joint : ((app.policyMixture initial policies).posterior past).bind
      (fun index => (policies index past entry.beforeView).map fun action => (action, index)) =
        FinDist.product law ((app.policyMixture initial policies).posterior past) := by
    simp_rw [same, FinDist.map_eq_bind]
    rw [FinDist.bind_comm]
    rfl
  rw [joint, FinDist.conditional_snd_product]

/-- A policy family that is identical before a phase retains its initial
mixing law at that phase, including at zero-probability own transcripts. -/
theorem policyMixture_posterior_dormant (initial : FinDist Index)
    (policies : Index → app.Policy) (baseline : app.Policy) (offset : Nat)
    (same : ∀ index past view, past.length < offset →
      policies index past view = baseline past view)
    (past : List app.PlayerEntry) (before : past.length ≤ offset) :
    (app.policyMixture initial policies).posterior past = initial := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      have earlier : past.length < offset := by
        simp only [List.length_append, List.length_singleton] at before
        omega
      rw [app.policyMixture_posterior_snoc initial policies past entry
        (baseline past entry.beforeView) (fun index => same index _ _ earlier)]
      exact ih (by omega)

/-- Select a single owner opportunity using its actual response count. Every
other response uses the supplied policy, including after the selected visit. -/
def scheduledPolicy (offset : Nat) {slots : Nat} (selected : Option (Fin slots))
    (opening waiting : app.Policy) : app.Policy := fun past view =>
  if selected.map (fun slot => offset + slot.val) = some past.length then
    opening past view else waiting past view

theorem scheduledPolicy_before (offset : Nat) {slots : Nat}
    (selected : Option (Fin slots)) (opening waiting : app.Policy)
    (past : List app.PlayerEntry) (view : app.PlayerView) (before : past.length < offset) :
    app.scheduledPolicy offset selected opening waiting past view = waiting past view := by
  unfold scheduledPolicy
  apply ite_eq_right
  cases selected with
  | none => simp
  | some slot =>
      simp only [Option.map_some, Option.some.injEq]
      omega

end Interaction.ReactiveApplication
