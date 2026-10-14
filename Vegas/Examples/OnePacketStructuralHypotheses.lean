/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommittedResolutionService
import Vegas.Game.OnePacketCertificateAssembly

/-! # The structural hypotheses of one-packet preservation on a concrete program

The committed-resolution program has two players, each holding an initial
commitment, a public sample, and a reveal of each commitment, on the default
sequential runtime with a concrete public scheduler. It satisfies the
structural hypotheses of the one-packet preservation theorem
(`Vegas.onePacket_intended_sequentialEquilibrium_of_blindInputs`): the setup is
well formed, the asynchronous contract and its timeliness hold for concrete
delays and inclusion bounds, the canonical menu retains first covered canonical
packets, the message bounds cover every output value with spare candidate
capacity, the late options cover the bounded slots, and a constant utility is
bounded with an exclusion payoff below every intended outcome.
-/

noncomputable section

namespace Vegas.Examples.OnePacketStructuralHypotheses

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol
open CommittedResolutionService

theorem wellFormed : setup.WellFormed where
  initialValues := by
    intro initial supported name owner payload cell
    have choices := support_mix_subset (1 / 4) (by norm_num) (by norm_num)
      (PMF.pure (sourceInitial true)) (PMF.pure (sourceInitial false)) supported
    have initialEq : ∃ high, initial = sourceInitial high := by
      rcases choices with high | low
      · exact ⟨true, (PMF.mem_support_pure_iff _ _).mp high⟩
      · exact ⟨false, (PMF.mem_support_pure_iff _ _).mp low⟩
    obtain ⟨high, rfl⟩ := initialEq
    cases cell with
    | here => exact ⟨high, rfl⟩
    | there cell => cases cell with
      | here => exact ⟨true, rfl⟩
      | there cell => cases cell
  guardsSatisfiable := by
    intro initial _ value _
    trivial

open Classical in
/-- Message bounds with one prepared slot and every Boolean value. -/
def bounds : MessageBounds nativeGraph where
  candidateCount := 1
  values := Finset.univ.image fun bit : Bool => (⟨.bool, bit⟩ : Raw simpleExpr)

theorem covers : bounds.CoversOutputValues := by
  intro event
  change Fin 3 at event
  fin_cases event <;> first
    | trivial
    | (intro value
       exact Finset.mem_image.mpr ⟨value, Finset.mem_univ _, rfl⟩)

theorem coversInputs : bounds.CoversInputValues := by
  intro input owner payload layoutEq value
  change Fin 2 at input
  fin_cases input <;> cases layoutEq <;>
    exact Finset.mem_image.mpr ⟨value, Finset.mem_univ _, rfl⟩

/-- Only Alice's commitment varies under the initial law, so the hidden
initial cells are independent. -/
theorem privateInputsIndependent : setup.PrivateInputsIndependent :=
  setup.privateInputsIndependent_of_single_owner alice (sourceInitial true)
    fun state member name τ cell notAlice => by
      have pure : state = sourceInitial true ∨ state = sourceInitial false := by
        rcases mem_support_mix_cases (h0 := by norm_num) (h1 := by norm_num) member with
          first | second
        · exact Or.inl ((PMF.mem_support_pure_iff _ _).mp first)
        · exact Or.inr ((PMF.mem_support_pure_iff _ _).mp second)
      cases cell with
      | here => exact absurd rfl notAlice
      | there cell =>
          cases cell with
          | here => rcases pure with rfl | rfl <;> rfl
          | there cell => cases cell

theorem capacity : ∀ who, bindingEventCount nativeGraph who < bounds.candidateCount := by
  intro who
  change (Finset.univ.filter fun event => bindingOwnedBy nativeGraph who event = true).card < 1
  rw [Nat.lt_one_iff, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro event _
  change Fin 3 at event
  fin_cases event <;> simp [bindingOwnedBy, nativeGraph] <;> rfl

theorem retains : RetainsCoveredCanonical setup leaks bounds CommittedResolutionService.horizon
    CommittedResolutionService.scheduler bound :=
  retainsCoveredCanonical_of_adequate bounds covers capacity CommittedResolutionService.horizon
    CommittedResolutionService.scheduler bound

/-- One late slot: as many as the bounded prepared slots. -/
abbrev slots : Nat := 1

theorem slots_pos : 0 < slots := Nat.one_pos

theorem slotsCover : bounds.candidateCount ≤ slots := le_rfl

theorem slotsLe : slots ≤ bounds.candidateCount := le_rfl

theorem oneSlot : 1 ≤ bounds.candidateCount := le_rfl

/-- A constant utility. -/
def utility : Bool × PublicOutcome program → Player → ℝ := fun _ _ => 0

/-- An exclusion payoff below every utility. -/
def excludedPayoff : Player → ℝ := fun _ => -1

theorem lower_le : ∀ outcome who, (fun _ => (0 : ℝ)) who ≤ utility outcome who :=
  fun _ _ => le_rfl

theorem le_upper : ∀ outcome who, utility outcome who ≤ (fun _ => (0 : ℝ)) who :=
  fun _ _ => le_rfl

theorem below (parameter : State simpleExpr setup.context → Bool) :
    ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who := by
  intro _ _ _ _
  norm_num [excludedPayoff, utility]

/-- **The structural hypotheses hold together.** -/
theorem structural (parameter : State simpleExpr setup.context → Bool) :
    setup.WellFormed ∧
      AsyncContract (runtime setup) leaks (initialLaw setup) CommittedResolutionService.horizon
        CommittedResolutionService.scheduler delay bound ∧
      AsyncTimely (runtime setup) delay bound ∧
      RetainsCoveredCanonical setup leaks bounds CommittedResolutionService.horizon
        CommittedResolutionService.scheduler bound ∧
      bounds.CoversOutputValues ∧
      bounds.CoversInputValues ∧
      (∀ who, bindingEventCount nativeGraph who < bounds.candidateCount) ∧
      0 < slots ∧ bounds.candidateCount ≤ slots ∧ slots ≤ bounds.candidateCount ∧
      1 ≤ bounds.candidateCount ∧
      (∀ (final : setup.intendedProtocol.History) terminal,
        setup.protocolReadout final.state = some terminal →
          ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who) :=
  ⟨wellFormed, contract, timely, retains, covers, coversInputs, capacity, slots_pos, slotsCover,
    slotsLe, oneSlot, below parameter⟩

open Classical in
/-- The one-packet preservation theorem applies to the program: its structural
hypotheses and instance requirements are met, leaving the intended sequential
equilibrium and the inputs by value blindness. -/
example (parameter : State simpleExpr setup.context → Bool) :=
  have : Finite setup.intendedProtocol.History := setup.intended_finite_history trivial
  onePacket_intended_sequentialEquilibrium_of_blindInputs setup leaks bounds
    CommittedResolutionService.horizon CommittedResolutionService.scheduler parameter utility
    excludedPayoff wellFormed privateInputsIndependent contract timely retains (fun _ => 0)
    (fun _ => 0) lower_le le_upper (below parameter)

end Vegas.Examples.OnePacketStructuralHypotheses
