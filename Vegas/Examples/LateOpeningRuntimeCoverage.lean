/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeService
import Vegas.Pending.ReactiveBoundedValues
import Vegas.Pending.ReactiveCompiledMenu
import Vegas.Pending.PrivateInputs

/-! # The finite native alphabet covers the initialized source

The actual source's answer choices and initial committed values fit the
declared message alphabet. Its ordinary private preference input has no
commitment handle. These are compiler side conditions, without a service
contract or an equilibrium premise.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeService

open SourceProgram EventGraph EventGraphRuntime Interaction
  GameTheory.Math.Probability
open LateOpeningRuntimeSource

theorem binding_values_covered : bounds.CoversBindingValues := by
  intro event
  change Fin 3 at event
  fin_cases event
  · trivial
  · change ∀ value : Answer, (⟨.range 0 5, value⟩ : Raw simpleExpr) ∈ bounds.values
    intro value
    have within : 0 ≤ value.val ∧ value.val ≤ 5 := value.property
    let chosen : Fin 6 := ⟨value.val.toNat, by omega⟩
    have same : answerValue chosen = value := by
      apply Subtype.ext
      dsimp only [answerValue, chosen]
      omega
    simpa only [same] using answer_covered chosen
  · trivial

theorem initialized_candidate_values (bit : Bool) (label : Fin 3) :
    bounds.CandidateValues (EventGraphRuntime.State.initial (graph := nativeGraph)
      (setup.eventInputs (sourceInitial bit label))) := by
  rintro ⟨who, slot⟩ raw opened
  rw [EventGraphRuntime.State.initial_candidate] at opened
  cases slot with
  | prepared serial => cases opened
  | initial input =>
      change Fin 2 at input
      fin_cases input
      · fin_cases who
        · change CommitmentCandidate.openable (⟨.bool, bit⟩ : Raw simpleExpr) =
            .openable raw at opened
          injection opened with same
          rw [← same]
          exact bool_covered bit
        · change CommitmentCandidate.fresh = .openable raw at opened
          cases opened
      · change CommitmentCandidate.fresh = .openable raw at opened
        cases opened

theorem initial_values_covered : ∀ state ∈ initial.support, bounds.CandidateValues state := by
  intro state supported
  change state ∈ (setup.initialLaw.map (fun source =>
    EventGraphRuntime.State.initial (graph := nativeGraph)
      (setup.eventInputs source))).support at supported
  obtain ⟨source, selected, rfl⟩ := PMF.support_map .. ▸ supported
  obtain ⟨bit, label, rfl⟩ := (initialLaw_support source).mp selected
  exact initialized_candidate_values bit label

theorem candidate_capacity : nativeGraph.order.eventCount ≤ bounds.candidateCount := by
  decide

end Vegas.Examples.LateOpeningRuntimeService
