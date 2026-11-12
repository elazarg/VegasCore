module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import GameTheory.Protocol.Information

@[expose] public section

/-! # Joint behavioral laws and their player marginals -/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {ι : Type*} {E : ExecutionProtocol ι} (M : InformationModel E)

/-- For finitely many players, forgetting legality gives the product of their
local action laws, including the forced choices of inactive players. -/
theorem behavioralJoint_map_val_eq_product [Fintype ι]
    (policies : ∀ i, M.BehavioralPolicy i) {state : E.State}
    (trace : E.Trace state) (running : ¬ E.terminal state) :
    (M.behavioralJoint policies trace running).map Subtype.val =
      independentProduct (fun i => (policies i (M.infoOf i trace)).map Subtype.val) := by
  rw [M.behavioralJoint_eq_independentProduct, PMF.map_comp, ← independentProduct_map]
  rfl

/-- Each player's marginal is its local law, even with infinitely many players
and only finitely many active movers. -/
theorem behavioralJoint_map_player [E.FiniteMovers]
    (policies : ∀ i, M.BehavioralPolicy i) {state : E.State}
    (trace : E.Trace state) (running : ¬ E.terminal state) (who : ι) :
    (M.behavioralJoint policies trace running).map (fun joint => joint.1 who) =
      (policies who (M.infoOf who trace)).map Subtype.val := by
  rw [behavioralJoint, PMF.map_comp]
  change (finitaryProduct _ (E.movers state)).map
    (Subtype.val ∘ fun choices : ∀ i, M.Choice i (M.infoOf i trace) => choices who) = _
  rw [← PMF.map_comp, finitaryProduct_map_eval]
  by_cases moving : who ∈ E.movers state
  · exact Or.inl moving
  · exact Or.inr (M.isPointMass_of_not_mem_movers policies trace who moving)

end GameTheory.Protocol.InformationModel
