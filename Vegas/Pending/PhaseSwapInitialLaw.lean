/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSwapFiber
import Vegas.Pending.ValueSwapPairs

/-! # Exact initialized laws for swaps of computed private bindings -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace HiddenSwap

/-- Computed binding swaps leave the actual input configuration and its
initial opaque handles unchanged. Prepared slots are still fresh. -/
theorem initial_native_eq (swap : HiddenSwap graph) (inputs : graph.Inputs)
    (inputFixed : ∀ input, swap.values.value (.inl input) = id)
    (handleFixed : ∀ owner input, swap.raw (owner, .initial input) = id) :
    (State.initial inputs).swap swap = State.initial inputs := by
  have config : (State.initial inputs).config.swap swap.values =
      (State.initial inputs).config := by
    apply Config.ext_fields
    · funext input
      exact congrFun (inputFixed input) (inputs input)
    · rfl
    · rfl
    · rfl
  have candidates : swap.candidates (State.initial inputs).candidates =
      (State.initial inputs).candidates := by
    change CommitmentCandidates.mk _ = CommitmentCandidates.mk _
    congr 1
    funext owner slot
    change swapCandidate (swap.raw (owner, slot))
      ((State.initial inputs).candidates.lookup (owner, slot)) =
        (State.initial inputs).candidates.lookup (owner, slot)
    cases slot with
    | initial input =>
        rw [handleFixed owner input]
        cases (State.initial inputs).candidates.lookup (owner, .initial input) <;> rfl
    | prepared serial =>
        rw [State.initial_candidate]
        rfl
  simp only [State.swap, config, candidates]

/-- The real phase initializer, including automatic normalization, is fixed
pointwise. No invariance or factorization of the input prior is required. -/
theorem initial_phase_eq (swap : HiddenSwap graph) (plan : RuntimePhasePlan graph)
    (inputs : graph.Inputs) (inputFixed : ∀ input, swap.values.value (.inl input) = id)
    (handleFixed : ∀ owner input, swap.raw (owner, .initial input) = id)
    (expiry : ∀ event, swap.values.ExpiryFixed event) :
    (PhaseRuntimeState.initial plan inputs).swap swap =
      PhaseRuntimeState.initial plan inputs := by
  have native := swap.initial_native_eq inputs inputFixed handleFixed
  have recovery : (⟨State.initial inputs, ∅⟩ : RecoveryState graph).swap swap =
      ⟨State.initial inputs, ∅⟩ := congrArg (fun state => RecoveryState.mk state ∅) native
  unfold PhaseRuntimeState.initial
  rw [← PhaseRuntimeState.settle_swap swap plan.phases 0 _ _ [] expiry, recovery]
  rfl

/-- Exact initial masses are preserved, not merely membership in prior support. -/
theorem initial_phase_law (swap : HiddenSwap graph) (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (inputFixed : ∀ input, swap.values.value (.inl input) = id)
    (handleFixed : ∀ owner input, swap.raw (owner, .initial input) = id)
    (expiry : ∀ event, swap.values.ExpiryFixed event) :
    (inputs.map (PhaseRuntimeState.initial plan)).map (PhaseRuntimeState.swap swap) =
      inputs.map (PhaseRuntimeState.initial plan) := by
  rw [PMF.map_comp]
  apply congrArg (fun f => inputs.map f)
  funext draw
  exact swap.initial_phase_eq plan draw inputFixed handleFixed expiry

/-- The actual initialized phase prior supplies the support premise of the
guarded native history exchange. -/
theorem initial_phase_support (swap : HiddenSwap graph) (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (inputFixed : ∀ input, swap.values.value (.inl input) = id)
    (handleFixed : ∀ owner input, swap.raw (owner, .initial input) = id)
    (expiry : ∀ event, swap.values.ExpiryFixed event)
    (state : PhaseRuntimeState graph)
    (member : state ∈ (inputs.map (PhaseRuntimeState.initial plan)).support) :
    state.swap swap ∈ (inputs.map (PhaseRuntimeState.initial plan)).support := by
  obtain ⟨draw, _drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  rw [swap.initial_phase_eq plan draw inputFixed handleFixed expiry]
  exact member

/-- Swapping computed private fields and prepared handles fixes the genuine
initialized joint law for every input prior. -/
theorem ofPairs_initial_phase_law (pairs : graph.SwapPairs)
    (handlePairs : Handle graph → Option (Raw L × Raw L))
    (inputNone : ∀ input, pairs.pair (.inl input) = none)
    (handleNone : ∀ owner input, handlePairs (owner, .initial input) = none)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) :
    (inputs.map (PhaseRuntimeState.initial plan)).map
        (PhaseRuntimeState.swap (HiddenSwap.ofPairs pairs handlePairs)) =
      inputs.map (PhaseRuntimeState.initial plan) := by
  apply (HiddenSwap.ofPairs pairs handlePairs).initial_phase_law plan inputs
  · intro input
    change pairSwap (pairs.pair (.inl input)) = id
    rw [inputNone]
    rfl
  · intro owner input
    change pairSwap (handlePairs (owner, .initial input)) = id
    rw [handleNone]
    rfl
  · exact ValueSwap.ofPairs_expiryFixed pairs

end HiddenSwap
end Vegas.EventGraphRuntime
