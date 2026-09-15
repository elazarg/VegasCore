/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.LogicalCommitment
import GameTheoryExtensions.Math.Probability.SequentialDecisionObservation

/-! # Sequential decisions with private recall and pending disclosures

This experiment uses two logical bindings with different owners. One owner
prepares a candidate, observes the other binding's pending or included opening,
then chooses an opening claim or withholding. Failed claims resolve by an
attributed fallback. These are logical transitions, not a realization by the
candidate runtime's queues, service or timeout rules.

The positive law erases auxiliary metadata while retaining the owner's first
action and the disclosure's inclusion status. The negative test forgets the
first action: every blind randomized opening then has utility at most one half,
whereas the owner with recall opens with certainty.
-/

noncomputable section

namespace InteractionTests.LogicalCommitmentSequential

open Interaction GameTheory.Math.Probability

private def binding (owner : Bool) : LogicalCommitment Bool Bool := ⟨owner, id⟩

private def selected (owner value : Bool) : LogicalCommitment.State Bool Bool Bool :=
  (binding owner).run .empty
    [.prepare owner owner value,
      .submit owner (.select owner owner), .include (.select owner owner)]

/-- The disclosed value and whether its opening has entered the ledger. -/
structure Disclosure where
  value : Bool
  included : Bool

private def disclosed (disclosure : Disclosure) : LogicalCommitment.State Bool Bool Bool :=
  let pending := (selected true disclosure.value).submit true
    (.open true true disclosure.value)
  let exposed := pending.expose false (.open true true disclosure.value)
  if disclosure.included then
    exposed.recordInclusion (binding true) (.open true true disclosure.value)
  else exposed

private def resolve (value : Bool) (response : Option Bool) : LogicalCommitment.Result Bool :=
  let attempted := match response with
    | none => selected false value
    | some claimed => (selected false value).recordInclusion (binding false)
        (.open false false claimed)
  (attempted.settleQuit (binding false) false).result

private theorem resolve_eq (value : Bool) (response : Option Bool) :
    resolve value response =
      if response = some value then .opened value else .quit := by
  cases value <;> cases response with
  | none => decide
  | some claimed => cases claimed <;> decide

/-- An exposed opening is visible in the observer's inbox while its binding is
still unresolved and its public ledger contains only the accepted selection. -/
theorem pending_opening_view (value : Bool) :
    (disclosed ⟨value, false⟩).observe false =
      ⟨[], [.open true true value], [.select true true],
        [(.select true true, true)], some true, .pending⟩ := by
  cases value <;> rfl

/-- Inclusion records the opening and its accepting receipt, without replacing
the earlier recipient-local delivery observation. -/
theorem included_opening_view (value : Bool) :
    (disclosed ⟨value, true⟩).observe false =
      ⟨[], [.open true true value], [.select true true, .open true true value],
        [(.select true true, true), (.open true true value, true)],
        some true, .opened value⟩ := by
  cases value <;> rfl

/-- The summary given to the logical response is recoverable from the actual
observer view; it does not reveal any additional private state. -/
theorem disclosure_recoverable_from_view :
    ∃ readDisclosure : LogicalCommitment.State.View Bool Bool Bool → Option Disclosure,
      ∀ disclosure, readDisclosure ((disclosed disclosure).observe false) = some disclosure := by
  refine ⟨fun view => view.inbox.head?.bind (fun claim => match claim with
    | .open _ _ value => some ⟨value, match view.result with
        | .opened _ => true
        | .pending | .quit => false⟩
    | .select _ _ | .malformed _ => none), ?_⟩
  rintro ⟨value, included⟩
  cases value <;> cases included <;> rfl

private def finish (value : Bool) (disclosure : Disclosure) (response : Option Bool) :
    FinDist (LogicalCommitment.Result Bool × LogicalCommitment.Result Bool) :=
  FinDist.pure ((disclosed disclosure).result, resolve value response)

/-- Arbitrary two-stage responses to auxiliary metadata have an exact logical
response law. The second logical policy retains the chosen value and the
pending-versus-included disclosure. Both executions use the same disclosure
law and the same actual logical settlement transitions.

The auxiliary bit is also retained in native memory at stage two, so it is not
assumed to be freshly independent at each decision. It does not affect the
fixed disclosure or settlement kernels. -/
theorem two_decision_commitment_law
    (metadata : FinDist (Fin 2)) (disclosures : FinDist Disclosure)
    (first : Fin 2 → FinDist Bool)
    (second : Fin 2 × Bool × (Disclosure × Fin 2) → FinDist (Option Bool)) :
    ∃ logicalFirst : Unit → FinDist Bool,
      ∃ logicalSecond : Unit × Bool × Disclosure → FinDist (Option Bool),
        (metadata.bind fun info => (first info).bind fun value =>
          disclosures.bind fun disclosure =>
            (second (info, value, disclosure, info)).bind (finish value disclosure)) =
        ((metadata.map fun _ => ()).bind fun info => (logicalFirst info).bind fun value =>
          disclosures.bind fun disclosure =>
            (logicalSecond (info, value, disclosure)).bind (finish value disclosure)) := by
  have hlaw := FinDist.exists_two_decision_policy_law metadata (fun _ => ())
    (fun next : Disclosure × Fin 2 => next.1)
    (fun info (_ : Bool) => disclosures.map fun disclosure => (disclosure, info))
    (fun (_ : Unit) (_ : Bool) => disclosures)
    (fun _ _ _ => by
      rw [FinDist.map_comp]
      exact FinDist.map_id disclosures)
    (fun history response => finish history.2.1 history.2.2.1 response)
    (fun history response => finish history.2.1 history.2.2 response)
    (fun _ _ _ _ _ _ => rfl) first second
  simpa only [FinDist.bind_map] using hlaw

private def fairChoice : FinDist Bool := (FinDist.uniformFin 2).map (fun bit => bit == 0)

private def openingUtility : LogicalCommitment.Result Bool → ℝ
  | .opened _ => 1
  | .pending | .quit => 0

/-- Remembering one's own randomly chosen value permits opening it for every
draw; the private candidate catalog is not queried by the response policy. -/
theorem recall_opening_value :
    (fairChoice.map fun value => resolve value (some value)).expect openingUtility = 1 := by
  simp [FinDist.expect_map, resolve_eq, openingUtility]

/-- Forgetting the first action prevents a later independent randomized claim
from opening a fair Boolean commitment with probability greater than one half.
Withholding and incompatible opening claims are both allowed by this response space. -/
theorem blind_opening_value_le (blind : FinDist (Option Bool)) :
    (fairChoice.bind fun value => blind.map (resolve value)).expect openingUtility ≤ 1 / 2 := by
  simp only [FinDist.map_eq_bind]
  rw [FinDist.bind_comm, FinDist.expect_bind]
  apply FinDist.expect_le_of_forall
  intro response _
  simp only [FinDist.expect_bind, FinDist.expect_pure, fairChoice, FinDist.expect_map,
    FinDist.expect_uniformFin]
  cases response with
  | none =>
      simp only [resolve_eq, reduceCtorEq, ↓reduceIte, openingUtility]
      norm_num
  | some claimed =>
      cases claimed <;> norm_num [Fin.sum_univ_succ, resolve_eq, openingUtility]

/-- Private action recall matters strategically, not just for reconstructing
an operational state. -/
theorem forgetting_choice_strict_value_gap (blind : FinDist (Option Bool)) :
    (fairChoice.bind fun value => blind.map (resolve value)).expect openingUtility <
      (fairChoice.map fun value => resolve value (some value)).expect openingUtility := by
  rw [recall_opening_value]
  exact (blind_opening_value_le blind).trans_lt (by norm_num)

end InteractionTests.LogicalCommitmentSequential

/-- info: 'InteractionTests.LogicalCommitmentSequential.two_decision_commitment_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InteractionTests.LogicalCommitmentSequential.two_decision_commitment_law

/-- info: 'InteractionTests.LogicalCommitmentSequential.forgetting_choice_strict_value_gap'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InteractionTests.LogicalCommitmentSequential.forgetting_choice_strict_value_gap
