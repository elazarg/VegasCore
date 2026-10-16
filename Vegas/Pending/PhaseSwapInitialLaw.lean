/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSwapFiber
import Vegas.Pending.ValueSwapPairs

/-! # Initialized phase priors and input-restricted hidden swaps -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Allowed original tuples are exactly those whose supported initialized
phase state has a supported swapped image. Correlations within a player's
complete tuple impose no closure requirement on other supported tuples. -/
def phaseSwapAllowed (swap : HiddenSwap graph) (initial : PMF (PhaseRuntimeState graph)) :
    Set graph.Inputs :=
  {inputs | ∃ state ∈ initial.support, state.current.native.config.inputs = inputs ∧
    state.swap swap ∈ initial.support}

/-- The actual mapped phase initializer supplies the physical native-invariant
support premise of guarded history replay, for an arbitrary original prior. -/
theorem phase_initial_support_invariant (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) :
    ∀ state ∈ (inputs.map (PhaseRuntimeState.initial plan)).support,
      ∃ draw, state.Invariant draw := by
  intro state member
  obtain ⟨draw, _present, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  exact ⟨draw, (PhaseRuntimeState.initial_invariant plan draw).1⟩

private theorem phase_initial_of_support (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (state : PhaseRuntimeState graph)
    (member : state ∈ (inputs.map (PhaseRuntimeState.initial plan)).support) :
    state = PhaseRuntimeState.initial plan state.current.native.config.inputs := by
  obtain ⟨draw, _present, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  rw [(PhaseRuntimeState.initial_invariant plan draw).1.active.reachable.inputs_eq]

/-- Actual initialized support is closed at the allowed tuples; no global
support closure or independent input cells are assumed. -/
theorem phase_initialClosed_swapAllowed (swap : HiddenSwap graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) :
    ∀ state ∈ (inputs.map (PhaseRuntimeState.initial plan)).support,
      state.current.native.config.inputs ∈
        phaseSwapAllowed swap (inputs.map (PhaseRuntimeState.initial plan)) →
      state.swap swap ∈ (inputs.map (PhaseRuntimeState.initial plan)).support := by
  rintro state member ⟨other, otherMember, sameInputs, swapped⟩
  rw [phase_initial_of_support plan inputs state member, ← sameInputs,
    ← phase_initial_of_support plan inputs other otherMember]
  exact swapped

omit [DecidableEq Player] in
/-- The input-domain guard is itself involutive, even when the original input
prior correlates cells within a player's private tuple. -/
theorem phaseSwapAllowed_closed (swap : HiddenSwap graph)
    (initial : PMF (PhaseRuntimeState graph)) :
    ∀ inputs ∈ phaseSwapAllowed swap initial,
      (fun input => swap.values.value (.inl input) (inputs input)) ∈
        phaseSwapAllowed swap initial := by
  rintro inputs ⟨state, member, rfl, swapped⟩
  exact ⟨state.swap swap, swapped, rfl, by
    rw [PhaseRuntimeState.swap_involutive]
    exact member⟩

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

/-- Native initial-state compatibility lifts through the actual automatic
phase normalization, permitting an entire original private tuple to change. -/
theorem initial_phase_of_native_swap (swap : HiddenSwap graph) (plan : RuntimePhasePlan graph)
    (before after : graph.Inputs)
    (native : (State.initial before).swap swap = State.initial after)
    (expiry : ∀ event, swap.values.ExpiryFixed event) :
    (PhaseRuntimeState.initial plan before).swap swap =
      PhaseRuntimeState.initial plan after := by
  have recovery : (⟨State.initial before, ∅⟩ : RecoveryState graph).swap swap =
      ⟨State.initial after, ∅⟩ := congrArg (fun state => RecoveryState.mk state ∅) native
  unfold PhaseRuntimeState.initial
  rw [← PhaseRuntimeState.settle_swap swap plan.phases 0 _ _ [] expiry, recovery]
  rfl

/-- A pair of supported complete input tuples and actual native initializer
compatibility establish the permitted replay domain. Other supported tuples
need not be closed under this coordinatewise swap. -/
theorem initial_inputs_mem_phaseSwapAllowed (swap : HiddenSwap graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (before after : graph.Inputs)
    (beforeSupported : before ∈ inputs.support) (afterSupported : after ∈ inputs.support)
    (native : (State.initial before).swap swap = State.initial after)
    (expiry : ∀ event, swap.values.ExpiryFixed event) :
    before ∈ phaseSwapAllowed swap (inputs.map (PhaseRuntimeState.initial plan)) := by
  refine ⟨PhaseRuntimeState.initial plan before,
    (PMF.mem_support_map_iff _ _ _).mpr ⟨before, beforeSupported, rfl⟩, ?_, ?_⟩
  · exact (PhaseRuntimeState.initial_invariant plan before).1.active.reachable.inputs_eq
  · rw [swap.initial_phase_of_native_swap plan before after native expiry]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨after, afterSupported, rfl⟩

/-- The real phase initializer, including automatic normalization, is fixed
pointwise. No invariance or factorization of the input prior is required. -/
theorem initial_phase_eq (swap : HiddenSwap graph) (plan : RuntimePhasePlan graph)
    (inputs : graph.Inputs) (inputFixed : ∀ input, swap.values.value (.inl input) = id)
    (handleFixed : ∀ owner input, swap.raw (owner, .initial input) = id)
    (expiry : ∀ event, swap.values.ExpiryFixed event) :
    (PhaseRuntimeState.initial plan inputs).swap swap =
      PhaseRuntimeState.initial plan inputs := by
  exact swap.initial_phase_of_native_swap plan inputs inputs
    (swap.initial_native_eq inputs inputFixed handleFixed) expiry

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
