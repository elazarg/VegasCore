/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.PublicUtility

/-! # Public payout interpretation

Payout evaluation depends only on its declared typed reads. Public-read payout
expressions therefore define a public-outcome utility under any supplied
valuation, with an arbitrary extension for incomplete stores.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

private theorem evalPayoffEntries?_eq_of_getAs_eq
    (payoffs : List (Player × EventPayoff L)) (left right : Store L)
    (heq : ∀ payoff, payoff ∈ payoffs → ∀ ref, ref ∈ payoff.2.reads →
      Store.getAs left ref.field ref.ty = Store.getAs right ref.field ref.ty) :
    evalPayoffEntries? payoffs left = evalPayoffEntries? payoffs right := by
  induction payoffs with
  | nil => rfl
  | cons payoff rest ih =>
      have hhead : ∀ ref, ref ∈ payoff.2.reads →
          Store.getAs left ref.field ref.ty = Store.getAs right ref.field ref.ty := by
        intro ref href
        exact heq payoff (by simp) ref href
      have htail : evalPayoffEntries? rest left = evalPayoffEntries? rest right :=
        ih (by
          intro tailPayoff htailPayoff ref href
          exact heq tailPayoff (by simp [htailPayoff]) ref href)
      cases hleft : ReadEnv.ofStore? left payoff.2.reads with
      | none =>
          cases hright : ReadEnv.ofStore? right payoff.2.reads with
          | none => simp [evalPayoffEntries?, hleft, hright]
          | some rightEnv =>
              have hback := ReadEnv.ofStore?_eq_of_getAs_eq hright
                (fun ref href ↦ (hhead ref href).symm)
              rw [hleft] at hback
              contradiction
      | some leftEnv =>
          have hright := ReadEnv.ofStore?_eq_of_getAs_eq hleft hhead
          simp [evalPayoffEntries?, hleft, hright, htail]

theorem evalPayoffs?_eq_of_getAs_eq
    (payoffs : List (Player × EventPayoff L)) (left right : Store L)
    (heq : ∀ payoff, payoff ∈ payoffs → ∀ ref, ref ∈ payoff.2.reads →
      Store.getAs left ref.field ref.ty = Store.getAs right ref.field ref.ty) :
    evalPayoffs? payoffs left = evalPayoffs? payoffs right := by
  unfold evalPayoffs?
  rw [evalPayoffEntries?_eq_of_getAs_eq payoffs left right heq]

/-- A valuation of public payout expressions is one public-outcome utility.
The incomplete-store extension has no strategic significance when payout
evaluation is total on the game's supported outcomes. -/
def Graph.PublicUtility.ofPayoffs (G : Graph Player L)
    (payoffs : List (Player × EventPayoff L))
    (hpublic : ∀ payoff, payoff ∈ payoffs → ∀ ref, ref ∈ payoff.2.reads →
      G.fieldRefPublic ref)
    (valuation : Payout Player → Player → ℝ) (missing : Player → ℝ) : G.PublicUtility where
  eval store who :=
    (evalPayoffs? payoffs store).elim (missing who) (fun payout => valuation payout who)
  congr left right hagrees who := by
    rw [evalPayoffs?_eq_of_getAs_eq payoffs left right
      (fun payoff hpayoff ref href => hagrees ref (hpublic payoff hpayoff ref href))]

end Vegas.EventGraph
