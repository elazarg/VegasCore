/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveServiceRecall
import GameTheoryExtensions.Math.Probability.ObservationRetraction

/-! # Selecting a local response by conditioning the actual continuation

Own recall preserves the current response throughout every later service step.
Conditioning a supported response out of the full execution law therefore gives
exactly its continuation. This lets compiler proofs derive local deviations
from a joint execution law without a separate runner for each response.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Fixing a supported current response is conditioning on that response's
persistent own-recall entry. Later policies and network behavior are arbitrary. -/
theorem runInteractionPlan_response_conditioning (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (plan : List (ServiceInstruction graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (responses : FinDist (runtime.reactiveApplication leaks).Action)
    (response : (runtime.reactiveApplication leaks).Action)
    (supported : response ∈ responses.support) :
    let app := runtime.reactiveApplication leaks
    let continued := fun action => runtime.runInteractionPlan leaks players network plan
      (execution.respond app who action)
    (responses.bind continued).condOnFibre
      (fun final => ((final.recall who)[(execution.recall who).length]?).map
        ReactiveApplication.PlayerEntry.action) (some response) = continued response := by
  intro app continued
  let observe := fun final : app.Execution =>
    ((final.recall who)[(execution.recall who).length]?).map
      ReactiveApplication.PlayerEntry.action
  have recorded (action : app.Action) (final : app.Execution)
      (reached : final ∈ (continued action).support) : observe final = some action := by
    obtain ⟨entry, recalled, _, chosen⟩ := runtime.response_recall_entry leaks execution who action
    obtain ⟨suffix, same⟩ := runtime.runInteractionPlan_recall_prefix leaks players network plan
      (execution.respond app who action) final reached who
    dsimp only [observe]
    rw [← same, recalled]
    simp only [ List.append_assoc, List.singleton_append, List.getElem?_append_right
      (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.map_some, chosen]
  have present : some response ∈ (responses.map some).support :=
    FinDist.support_map .. ▸ ⟨response, supported, rfl⟩
  have law := FinDist.conditional_bind_of_observation responses continued some observe
    (fun action _ final member => recorded action final member) (some response) present
  have fixed : responses.condOnFibre some (some response) = FinDist.pure response := by
    have meets : ∃ action ∈ some ⁻¹' {some response}, action ∈ responses.support :=
      ⟨response, rfl, supported⟩
    rw [FinDist.condOnFibre, dite_eq_left meets]
    apply FinDist.eq_pure_of_support_subset_singleton
    intro action member
    exact Option.some.inj (FinDist.support_condOn _ _ _ member).1
  rw [fixed, FinDist.pure_bind] at law
  exact law

end Vegas.EventGraphRuntime
