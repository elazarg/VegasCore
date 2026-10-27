/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ConditionedInitialLaw

/-! # Transporting actual source policies under initial-law conditioning -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  {Signal : Type*} (signal : State L setup.context → Signal) (value : Signal)

/-- Conditioning the initializer preserves each actual intended choice,
including its local menu-membership evidence. -/
def conditionInitial_choiceEquiv (who : Player) (view : setup.ProtocolView who) :
    (setup.conditionInitial signal value).intendedModel.Choice who view ≃
      setup.intendedModel.Choice who view where
  toFun choice := ⟨choice.1, by
    change choice.1 ∈ setup.intendedMenu who view
    rw [← setup.conditionInitial_intendedMenu signal value who view]
    exact choice.2⟩
  invFun choice := ⟨choice.1, by
    change choice.1 ∈ (setup.conditionInitial signal value).intendedMenu who view
    rw [setup.conditionInitial_intendedMenu signal value who view]
    exact choice.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

@[simp] theorem conditionInitial_choiceEquiv_val (who : Player) (view : setup.ProtocolView who)
    (choice : (setup.conditionInitial signal value).intendedModel.Choice who view) :
    (setup.conditionInitial_choiceEquiv signal value who view choice).1 = choice.1 := rfl

/-- The same local source action law, transported through the unchanged menu.
The policy obtains no new observation of the conditioning signal. -/
def conditionInitial_policy (who : Player) (policy : setup.intendedModel.BehavioralPolicy who) :
    (setup.conditionInitial signal value).intendedModel.BehavioralPolicy who :=
  fun view => (policy view).map (setup.conditionInitial_choiceEquiv signal value who view).symm

theorem conditionInitial_policy_apply (who : Player)
    (policy : setup.intendedModel.BehavioralPolicy who) (view : setup.ProtocolView who)
    (choice : (setup.conditionInitial signal value).intendedModel.Choice who view) :
    setup.conditionInitial_policy signal value who policy view choice =
      policy view (setup.conditionInitial_choiceEquiv signal value who view choice) := by
  let equivalence := setup.conditionInitial_choiceEquiv signal value who view
  simpa only [conditionInitial_policy, Equiv.symm_apply_apply] using
    pmf_map_apply_of_injective (policy view) equivalence.symm.injective (equivalence choice)

/-- Erasing menu-membership proofs gives exactly the same source action law. -/
theorem conditionInitial_policy_map_val (who : Player)
    (policy : setup.intendedModel.BehavioralPolicy who) (view : setup.ProtocolView who) :
    (setup.conditionInitial_policy signal value who policy view).map Subtype.val =
      (policy view).map Subtype.val := by
  rw [conditionInitial_policy, PMF.map_comp]
  congr 1

end Vegas.SourceProgram.Setup
