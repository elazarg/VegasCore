/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.Information

/-! # Projecting canonical randomized histories

Independent behavioral draws expose a product law on their underlying joint
actions. A history map commuting with one complete protocol step then commutes
with every finite continuation, directly on the existing history runners.
-/

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

variable {Player : Type} {E T : ExecutionProtocol Player}

theorem InformationModel.behavioralJoint_map_val (M : InformationModel E) [Fintype Player]
    (profile : ∀ who, M.BehavioralPolicy who) {state} (history : E.Trace state)
    (running : ¬ E.terminal state) :
    (M.behavioralJoint profile history running).map Subtype.val =
      FinDist.pi (fun who => (profile who (M.infoOf who history)).map Subtype.val) := by
  rw [InformationModel.behavioralJoint, FinDist.map_comp, FinDist.pi_map]
  rfl

theorem ExecutionProtocol.runRandomizedFor_map_of_oneStep
    (raw : E.RandomizedChooser) (normalized : T.RandomizedChooser)
    (project : E.History → T.History)
    (oneStep : ∀ history,
      (E.runRandomizedFor raw 1 history).map project =
        T.runRandomizedFor normalized 1 (project history)) :
    ∀ fuel history, (E.runRandomizedFor raw fuel history).map project =
      T.runRandomizedFor normalized fuel (project history) := by
  intro fuel
  induction fuel with
  | zero => intro history; simp only [runRandomizedFor_zero, FinDist.map_pure]
  | succ fuel ih =>
      intro history
      rw [show fuel + 1 = 1 + fuel by omega, runRandomizedFor_add, runRandomizedFor_add,
        FinDist.map_bind]
      calc
        _ = (E.runRandomizedFor raw 1 history).bind fun next =>
            T.runRandomizedFor normalized fuel (project next) :=
          FinDist.bind_congr fun next _ => ih next
        _ = ((E.runRandomizedFor raw 1 history).map project).bind
            (T.runRandomizedFor normalized fuel) := (FinDist.bind_map ..).symm
        _ = _ := by rw [oneStep]

end GameTheory.Protocol
