/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.BehavioralAssessment

/-! # Facts determined by an information set

Knowledge here means truth at every compatible legal history. It constrains
every belief on that information set, without a Bayes-consistency assumption.
In particular, authenticated evidence cannot be ignored by choosing beliefs
that give weight to incompatible histories.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {Player : Type} {E : ExecutionProtocol Player} (M : InformationModel E)

def Knows (who : Player) (info : M.InfoState who) (fact : E.History → Prop) : Prop :=
  ∀ history : M.InformationHistory who info, fact history.1

variable {M}

theorem Knows.mono {who : Player} {info : M.InfoState who} {first second : E.History → Prop}
    (known : M.Knows who info first) (implies : ∀ history, first history → second history) :
    M.Knows who info second := fun history => implies history.1 (known history)

theorem Knows.belief_map_eq_pure {who : Player} {info : M.InfoState who}
    {Value : Type*} (read : E.History → Value) (value : Value)
    (known : M.Knows who info (fun history => read history = value))
    (belief : FinDist (M.InformationHistory who info)) :
    belief.map (fun history => read history.1) = FinDist.pure value := by
  calc
    _ = belief.map (fun _ => value) := FinDist.map_congr_of_eq_on_support
      (fun history _ => known history)
    _ = _ := FinDist.map_const _ _

end GameTheory.Protocol.InformationModel
