/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.TerminalAudit

/-! # Monetary settlement evaluated by quasi-linear utility

The transfer vector records money received by each player. Valuations are
separate analysis data and are added only when evaluating a realized outcome.
Audit randomness changes transfers, not valuations; the identities below retain
the joint realized vector and require no independence between verdicts.
-/

noncomputable section

namespace GameTheory

open Math.Probability

/-- Sum all transfer entries belonging to a player, including duplicates. -/
def transferAmount {Player : Type*} [DecidableEq Player]
    (entries : List (Player × Int)) (who : Player) : Int :=
  (entries.map fun entry => if entry.1 = who then entry.2 else 0).sum

@[simp] theorem transferAmount_nil {Player : Type*} [DecidableEq Player] (who : Player) :
    transferAmount ([] : List (Player × Int)) who = 0 := rfl

@[simp] theorem transferAmount_cons {Player : Type*} [DecidableEq Player]
    (entry : Player × Int) (entries : List (Player × Int)) (who : Player) :
    transferAmount (entry :: entries) who =
      (if entry.1 = who then entry.2 else 0) + transferAmount entries who := rfl

/-- Appending transfer instructions adds their monetary effects. -/
theorem transferAmount_append {Player : Type*} [DecidableEq Player]
    (first second : List (Player × Int)) (who : Player) :
    transferAmount (first ++ second) who =
      transferAmount first who + transferAmount second who := by
  simp only [transferAmount, List.map_append, List.sum_append]

/-- Utility of an outcome paired with its realized monetary receipts. -/
def monetaryUtility {Player Outcome : Type*} (valuation : Outcome → Player → ℝ)
    (realized : Outcome × (Player → ℝ)) (who : Player) : ℝ :=
  valuation realized.1 who + realized.2 who

namespace Enforcement.TerminalAudit

variable {Player Outcome Observation : Type}

/-- Adding valuation after monetary settlement gives exactly the same realized
utility law as settling the sum of valuation and transfers. -/
theorem settlement_add_valuation (valuation transfer : Outcome → Player → ℝ)
    (observe : Outcome → Observation) (audit : Observation → PMF (Player → Bool))
    (deposit : Player → ℝ) (outcome : Outcome) :
    (settlement transfer observe audit deposit outcome).map
        (fun receipts who => valuation outcome who + receipts who) =
      settlement (fun result who => valuation result who + transfer result who)
        observe audit deposit outcome := by
  simp only [settlement, PMF.map_comp]
  congr 1
  funext verdict who
  simp only [Function.comp_def]
  ring

/-- Expected quasi-linear utility is computed from the actual monetary audit
settlement, with no assumption about correlation between player verdicts. -/
theorem settlement_expect_monetaryUtility (valuation transfer : Outcome → Player → ℝ)
    (observe : Outcome → Observation) (audit : Observation → PMF (Player → Bool))
    (deposit : Player → ℝ) (outcome : Outcome) (who : Player) :
    expect (settlement transfer observe audit deposit outcome)
        (fun receipts => monetaryUtility valuation (outcome, receipts) who) =
      utility (fun result owner => valuation result owner + transfer result owner)
        observe audit deposit outcome who := by
  have mapped := settlement_add_valuation valuation transfer observe audit deposit outcome
  have integrated := congrArg (fun law : PMF (Player → ℝ) => expect law (fun values => values who))
    mapped
  rw [expect_map, settlement_expect] at integrated
  exact integrated

/-- The full outcome and transfer-vector law, before private valuation. -/
def jointSettlement (law : PMF Outcome) (transfer : Outcome → Player → ℝ)
    (observe : Outcome → Observation) (audit : Observation → PMF (Player → Bool))
    (deposit : Player → ℝ) : PMF (Outcome × (Player → ℝ)) :=
  law.bind fun outcome =>
    (settlement transfer observe audit deposit outcome).map fun receipts => (outcome, receipts)

/-- A clean audit preserves the joint outcome and monetary transfer law. -/
theorem jointSettlement_clean (law : PMF Outcome) (transfer : Outcome → Player → ℝ)
    (observe : Outcome → Observation) (audit : Observation → PMF (Player → Bool))
    (deposit : Player → ℝ)
    (clean : ∀ outcome ∈ law.support, ∀ who, charge observe audit outcome who = 0) :
    jointSettlement law transfer observe audit deposit =
      law.map (fun outcome => (outcome, transfer outcome)) := by
  exact (settlement_transport_of_normalized_law law law id (PMF.map_id law)
    transfer observe audit deposit (fun _ => rfl) (fun _ => rfl) clean).2

end Enforcement.TerminalAudit
end GameTheory
