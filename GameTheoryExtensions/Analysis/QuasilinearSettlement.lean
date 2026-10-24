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

/-- Retain the entire outcome while converting actual receipts to utility. -/
def utilityReadout {Player Outcome : Type*} (valuation : Outcome → Player → ℝ)
    (realized : Outcome × (Player → ℝ)) : Outcome × (Player → ℝ) :=
  (realized.1, monetaryUtility valuation realized)

/-- Recover actual receipts from utility without discarding any outcome data. -/
def receiptReadout {Player Outcome : Type*} (valuation : Outcome → Player → ℝ)
    (realized : Outcome × (Player → ℝ)) : Outcome × (Player → ℝ) :=
  (realized.1, fun who => realized.2 who - valuation realized.1 who)

@[simp] theorem receiptReadout_utilityReadout {Player Outcome : Type*}
    (valuation : Outcome → Player → ℝ) (realized : Outcome × (Player → ℝ)) :
    receiptReadout valuation (utilityReadout valuation realized) = realized := by
  dsimp only [receiptReadout, utilityReadout, monetaryUtility]
  apply Prod.ext
  · rfl
  · funext who
    ring

@[simp] theorem utilityReadout_receiptReadout {Player Outcome : Type*}
    (valuation : Outcome → Player → ℝ) (realized : Outcome × (Player → ℝ)) :
    utilityReadout valuation (receiptReadout valuation realized) = realized := by
  dsimp only [receiptReadout, utilityReadout, monetaryUtility]
  apply Prod.ext
  · rfl
  · funext who
    change valuation realized.1 who + (realized.2 who - valuation realized.1 who) =
      realized.2 who
    ring

/-- The joint utility law retains enough information to recover the receipt law. -/
@[simp] theorem map_utilityReadout_receiptReadout {Player Outcome : Type*}
    (valuation : Outcome → Player → ℝ) (law : PMF (Outcome × (Player → ℝ))) :
    (law.map (utilityReadout valuation)).map (receiptReadout valuation) = law := by
  have inverse : receiptReadout valuation ∘ utilityReadout valuation = id := by
    funext realized
    exact receiptReadout_utilityReadout valuation realized
  rw [PMF.map_comp, inverse, PMF.map_id]

/-- Converting receipts to utility also recovers every joint utility law. -/
@[simp] theorem map_receiptReadout_utilityReadout {Player Outcome : Type*}
    (valuation : Outcome → Player → ℝ) (law : PMF (Outcome × (Player → ℝ))) :
    (law.map (receiptReadout valuation)).map (utilityReadout valuation) = law := by
  have inverse : utilityReadout valuation ∘ receiptReadout valuation = id := by
    funext realized
    exact utilityReadout_receiptReadout valuation realized
  rw [PMF.map_comp, inverse, PMF.map_id]

/-- Equality of joint utility laws is equivalent to equality of receipt laws.
No independence or integrability assumptions are needed. -/
theorem map_utilityReadout_injective {Player Outcome : Type*}
    (valuation : Outcome → Player → ℝ) :
    Function.Injective (PMF.map (utilityReadout valuation)) := by
  intro first second equal
  have recovered := congrArg (PMF.map (receiptReadout valuation)) equal
  simpa only [map_utilityReadout_receiptReadout] using recovered

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

/-- Actual randomized monetary settlement determines the full joint utility
law. Correlations among outcomes, transfers and all audit verdicts are retained. -/
theorem jointSettlement_add_valuation (law : PMF Outcome)
    (valuation transfer : Outcome → Player → ℝ)
    (observe : Outcome → Observation) (audit : Observation → PMF (Player → Bool))
    (deposit : Player → ℝ) :
    (jointSettlement law transfer observe audit deposit).map (utilityReadout valuation) =
      jointSettlement law (fun outcome who => valuation outcome who + transfer outcome who)
        observe audit deposit := by
  unfold jointSettlement
  rw [PMF.map_bind]
  congr 1
  funext outcome
  rw [← settlement_add_valuation valuation transfer observe audit deposit outcome]
  rw [PMF.map_comp, PMF.map_comp]
  rfl

/-- Subtracting valuation from realized utility recovers the actual monetary
settlement law, including its correlation with every retained outcome coordinate. -/
theorem jointSettlement_sub_valuation (law : PMF Outcome)
    (valuation transfer : Outcome → Player → ℝ)
    (observe : Outcome → Observation) (audit : Observation → PMF (Player → Bool))
    (deposit : Player → ℝ) :
    (jointSettlement law
        (fun outcome who => valuation outcome who + transfer outcome who)
        observe audit deposit).map (receiptReadout valuation) =
      jointSettlement law transfer observe audit deposit := by
  rw [← jointSettlement_add_valuation law valuation transfer observe audit deposit]
  exact map_utilityReadout_receiptReadout valuation _

/-- A retained observation recovers actual cash when the
declared valuation factors through it on the realized outcome support. Audit
verdicts may remain correlated, and no clean-settlement assumption is required. -/
theorem jointSettlement_readout_sub_valuation {Retained : Type}
    (law : PMF Outcome) (valuation transfer : Outcome → Player → ℝ)
    (retain : Outcome → Retained) (retainedValuation : Retained → Player → ℝ)
    (factors : ∀ outcome ∈ law.support, valuation outcome = retainedValuation (retain outcome))
    (observe : Outcome → Observation) (audit : Observation → PMF (Player → Bool))
    (deposit : Player → ℝ) :
    (jointSettlement law (fun outcome who => valuation outcome who + transfer outcome who)
        observe audit deposit).map
        (receiptReadout retainedValuation ∘ fun realized => (retain realized.1, realized.2)) =
      (jointSettlement law transfer observe audit deposit).map
        (fun realized => (retain realized.1, realized.2)) := by
  unfold jointSettlement
  rw [PMF.map_bind, PMF.map_bind]
  apply bind_congr_on_support _
  intro outcome supported
  rw [← settlement_add_valuation valuation transfer observe audit deposit outcome]
  simp only [PMF.map_comp, Function.comp_def]
  congr 1
  funext receipts
  apply Prod.ext
  · rfl
  · funext who
    change (valuation outcome who + receipts who) -
      retainedValuation (retain outcome) who = receipts who
    rw [factors outcome supported]
    ring

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
