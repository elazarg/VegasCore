/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveFiniteResponses
import Vegas.Pending.ReactivePolicy
import Interaction.ReactiveMenuRestriction

/-! # Covering initialized commitment values in finite response bounds

A finite initial law and finitely many initial handles supply a finite set of
opening values, even when their source types are infinite. Extending a declared
message alphabet with this set retains its other signaling values and prepared
handle bound. No equilibrium or prescribed policy enters the construction.

This proves coverage of initialized values, not a bound on fresh commitments or
all later computed source values. A reveal-only compiler must separately prove
that its openings retain these initialized meanings.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.MessageBounds

open Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

open Classical in
/-- The opening values of the initialized handles across a finitely supported
initial law. A law of infinite support contributes none; coverage below assumes
finite support. -/
def initialValues (initial : PMF (State graph)) : Finset (Raw L) :=
  if finite : initial.support.Finite then
    finite.toFinset.biUnion fun state => Finset.univ.biUnion fun who =>
      Finset.univ.biUnion fun input : graph.InputId =>
        ((state.candidates.lookup (who, .initial input)).opening?).toList.toFinset
  else ∅

theorem mem_initialValues (initial : PMF (State graph)) (finite : initial.support.Finite)
    (raw : Raw L) :
    raw ∈ initialValues initial ↔
      ∃ state ∈ initial.support, ∃ who input,
        state.candidates.lookup (who, .initial input) = .openable raw := by
  classical
  simp [initialValues, finite]

open Classical in
def withInitialValues (bounds : MessageBounds graph) (initial : PMF (State graph)) :
    MessageBounds graph :=
  { bounds with values := bounds.values ∪ initialValues initial }

theorem withInitialValues_preserves_values (bounds : MessageBounds graph)
    (initial : PMF (State graph)) :
    bounds.values ⊆ (bounds.withInitialValues initial).values :=
  Finset.subset_union_left

theorem withInitialValues_candidateCount (bounds : MessageBounds graph)
    (initial : PMF (State graph)) :
    (bounds.withInitialValues initial).candidateCount = bounds.candidateCount := rfl

theorem initial_value_covered (bounds : MessageBounds graph) (initial : PMF (State graph))
    (finite : initial.support.Finite) (state : State graph) (supported : state ∈ initial.support)
    (who : Player) (input : graph.InputId) (raw : Raw L)
    (fixed : state.candidates.lookup (who, .initial input) = .openable raw) :
    raw ∈ (bounds.withInitialValues initial).values := by
  classical
  apply Finset.mem_union_right
  exact (mem_initialValues initial finite raw).mpr ⟨state, supported, who, input, fixed⟩

/-- Completing the alphabet retains every previously admitted raw response,
including malformed traffic and independently attached evidence. -/
theorem withInitialValues_rawMenu [DecidableEq Player] (bounds : MessageBounds graph)
    (initial : PMF (State graph)) (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    (bounds.rawMenu runtime leaks).IncludedIn
      ((bounds.withInitialValues initial).rawMenu runtime leaks) := by
  intro who past view response member
  rw [rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem] at member ⊢
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => trivial
  | some submission =>
      have allowed := (bounds.submissions_mem _ submission).mp member
      apply ((bounds.withInitialValues initial).submissions_mem _ submission).mpr
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · cases packet : submission.call.packet <;>
          simp only [packet, AllowsPacket] at allowed ⊢
        · exact allowed.1.1
        · exact ⟨allowed.1.1.1, bounds.withInitialValues_preserves_values initial allowed.1.1.2⟩
        · exact bounds.withInitialValues_preserves_values initial allowed.1.1
      · cases opening : submission.call.opening with
        | none => trivial
        | some raw =>
            have present : raw ∈ bounds.values := by
              simpa only [opening, AllowsOpening] using allowed.1.2
            exact bounds.withInitialValues_preserves_values initial present
      · cases request : submission.evidence with
        | none => trivial
        | owned fact =>
            have permitted : bounds.AllowsHandle fact.handle ∧ fact.raw ∈ bounds.values := by
              simpa only [request, AllowsEvidence] using allowed.2
            exact ⟨permitted.1, bounds.withInitialValues_preserves_values initial permitted.2⟩
        | forward id =>
            simpa only [request, AllowsEvidence] using allowed.2

/-- Every initialized opening remains an available normalized response at every
local view. Availability does not assert that the packet will be accepted. -/
theorem initialized_opening_available [DecidableEq Player] (bounds : MessageBounds graph)
    (initial : PMF (State graph)) (finite : initial.support.Finite) (state : State graph)
    (supported : state ∈ initial.support) (who : Player) (input : graph.InputId) (raw : Raw L)
    (fixed : state.candidates.lookup (who, .initial input) = .openable raw)
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) (event : graph.EventId) :
    (runtime.reactiveNormalization leaks).action who past view
        ⟨some (disclosureSubmission (.opening event (who, .initial input) raw))⟩ ∈
      ((bounds.withInitialValues initial).menu runtime leaks).actions who past view := by
  have covered := bounds.initial_value_covered initial finite state supported who input raw
    fixed
  apply (bounds.withInitialValues initial).normalized_submission_available runtime leaks who
    past view _
  · exact ⟨trivial, covered⟩
  · simp only [disclosureSubmission, Submission.normalizeReactive_none, AllowsOpening]
  · apply (bounds.withInitialValues initial).normalize_evidence_mem
    exact ⟨trivial, covered⟩

end Vegas.EventGraphRuntime.MessageBounds
