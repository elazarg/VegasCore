/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.FinDist

/-! # Coalescing a response with no incoming information

A deterministic response can be sampled as a complete action transcript when
each local observation is computable from the previous observation and the
player's action. The transcript law is uniform across indistinguishable
starting states. Applying it preserves the full endpoint state, hence every
subsequent observation and environment continuation.

This is an execution theorem. It does not identify the SPE predicates of the
split and coalesced games: the latter has no internal decision roots.
-/

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe us uv ua

/-- A local response has no incoming information between its constituent
choices. `observe` may include private memory and own-action recall. -/
structure LocalResponse (State : Type us) (View : Type uv) (Action : Type ua) where
  observe : State → View
  step : State → Action → State
  update : View → Action → View
  observe_step : ∀ state action, observe (step state action) = update (observe state) action

namespace LocalResponse

variable {State : Type us} {View : Type uv} {Action : Type ua}
  (response : LocalResponse State View Action)

def applyActions (state : State) (actions : List Action) : State :=
  actions.foldl response.step state

/-- The player samples a complete finite response using its entry view alone. -/
def transcript (policy : View → FinDist Action) : Nat → View → FinDist (List Action)
  | 0, _ => FinDist.pure []
  | count + 1, view => (policy view).bind fun action =>
      (transcript policy count (response.update view action)).map (action :: ·)

theorem transcript_length (policy : View → FinDist Action) :
    ∀ count view actions, actions ∈ (response.transcript policy count view).support →
      actions.length = count := by
  intro count
  induction count with
  | zero =>
      intro view actions reached
      cases FinDist.mem_support_pure.mp reached
      rfl
  | succ count ih =>
      intro view actions reached
      rw [transcript, FinDist.support_bind] at reached
      obtain ⟨action, _, reached⟩ := Set.mem_iUnion₂.mp reached
      rw [FinDist.support_map] at reached
      obtain ⟨rest, supported, rfl⟩ := reached
      simp only [List.length_cons, ih _ _ supported]

private theorem iterate_bind (kernel : State → FinDist State) (count : Nat)
    (law : FinDist State) :
    (fun law => law.bind kernel)^[count] law =
      law.bind (fun state => (fun law => law.bind kernel)^[count] (FinDist.pure state)) := by
  induction count with
  | zero => simp only [Function.iterate_zero_apply, FinDist.bind_pure]
  | succ count ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih, FinDist.bind_bind]

/-- Exact equality with successive policy invocations. No utility, scheduler
cursor, or hidden component of the entry state is supplied to the transcript. -/
theorem transcript_eq_iteration (policy : View → FinDist Action) (count : Nat) (state : State) :
    (response.transcript policy count (response.observe state)).map
        (response.applyActions state) =
      (fun law => law.bind (fun current =>
        (policy (response.observe current)).map (response.step current)))^[count]
          (FinDist.pure state) := by
  induction count generalizing state with
  | zero => simp only [transcript, FinDist.map_pure, Function.iterate_zero_apply, applyActions,
      List.foldl_nil]
  | succ count ih =>
      rw [transcript, FinDist.map_bind]
      calc
        _ = (policy (response.observe state)).bind (fun action =>
            (response.transcript policy count (response.observe (response.step state action))).map
              (response.applyActions (response.step state action))) := by
          apply FinDist.bind_congr
          intro action _
          rw [FinDist.map_comp, response.observe_step]
          rfl
        _ = (policy (response.observe state)).bind (fun action =>
            (fun law => law.bind (fun current =>
              (policy (response.observe current)).map (response.step current)))^[count]
                (FinDist.pure (response.step state action))) := by simp only [ih]
        _ = (fun law => law.bind (fun current =>
              (policy (response.observe current)).map (response.step current)))^[count]
                ((policy (response.observe state)).map (response.step state)) := by
          rw [iterate_bind, FinDist.bind_map]
        _ = _ := by rw [Function.iterate_succ_apply, FinDist.pure_bind]

/-- Every continuation kernel sees exactly the same complete endpoint law. -/
theorem continuation_eq {Result : Type*} (policy : View → FinDist Action)
    (count : Nat) (state : State) (continuation : State → FinDist Result) :
    ((response.transcript policy count (response.observe state)).map
      (response.applyActions state)).bind continuation =
      ((fun law => law.bind (fun current =>
        (policy (response.observe current)).map (response.step current)))^[count]
          (FinDist.pure state)).bind continuation := by
  rw [response.transcript_eq_iteration]

end LocalResponse

end GameTheory.Protocol
