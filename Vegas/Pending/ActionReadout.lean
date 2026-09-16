/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReplayApplication

/-! # Reading normalized actions from their observed immutable effect -/

noncomputable section
namespace Vegas.GraphRuntime

open Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- At a known graph head, the owner's successor observation identifies its
effective binding choice or normalized publication decision. -/
def actionReadout (suffix : Graph Player L Γ Δ) (view : PlayerView Player L) :
    Option (OwnAction Player L) :=
  match suffix with
  | .bind name owner (payload := payload) _ _ =>
      some (.bind owner name payload
        (observedBindChoice view.who view.privateObservation name payload))
  | .resolve outputName owner bindingName (payload := payload) _ _ _ _ =>
      match findVar view.publicState.Γ outputName (.pub (R.result payload)) with
      | none => none
      | some source =>
          some (.resolve owner bindingName
            (R.valueEquiv payload (view.privateObservation.cells.get source)).isSuccess)
  | _ => none

private def realizedReadout (focal : Player) :
    State Player L Δ → OwnAction Player L → State Player L Δ → Prop
  | .running suffix _ _ _ _ _ _ _, action, after =>
      (match action with
        | .bind owner _ _ _ | .resolve owner _ _ => owner = focal) →
      actionReadout suffix (after.playerView focal) = some action

private theorem State.RealizesOwnAction.readout
    {before after : State Player L Δ} {action : OwnAction Player L}
    (realizes : State.RealizesOwnAction before action after) (focal : Player) :
    realizedReadout focal before action after := by
  cases realizes with
  | bind choice =>
      intro owned
      simp only at owned
      subst focal
      simp [actionReadout, State.playerView, observedBindChoice,
        findVar, Graph.observe, VEnv.get, Env.get, VEnv.cons]
  | resolveFailure =>
      intro owned
      simp only at owned
      subst focal
      simp [actionReadout, State.playerView, findVar, Graph.observe,
        VEnv.get, Env.get, VEnv.cons, PublicationResult.isSuccess]
  | resolveSuccess =>
      intro owned
      simp only at owned
      subst focal
      simp [actionReadout, State.playerView, findVar, Graph.observe,
        VEnv.get, Env.get, VEnv.cons, PublicationResult.isSuccess]

/-- Normalized actions at the same graph cursor agree whenever the owner's
successor player views agree. No private cache markers are consulted. -/
theorem State.RealizesOwnAction.eq_of_playerView_eq
    (focal : Player) (suffix : Graph Player L Γ Δ)
    (leftIdeal rightIdeal : VEnv L Γ) (leftValues rightValues : PublicValues Γ)
    (leftBindings rightBindings : Bindings Player)
    (leftCandidates rightCandidates : CommitmentCandidates Player Slot (Raw L))
    (leftPc leftClock leftEntered rightPc rightClock rightEntered : Nat)
    (leftAfter rightAfter : State Player L Δ) (leftAction rightAction : OwnAction Player L)
    (leftRealizes : State.RealizesOwnAction
      (.running suffix leftIdeal leftValues leftBindings leftCandidates
        leftPc leftClock leftEntered) leftAction leftAfter)
    (rightRealizes : State.RealizesOwnAction
      (.running suffix rightIdeal rightValues rightBindings rightCandidates
        rightPc rightClock rightEntered) rightAction rightAfter)
    (leftOwned : match leftAction with
      | .bind owner _ _ _ | .resolve owner _ _ => owner = focal)
    (rightOwned : match rightAction with
      | .bind owner _ _ _ | .resolve owner _ _ => owner = focal)
    (visible : leftAfter.playerView focal = rightAfter.playerView focal) :
    leftAction = rightAction := by
  have leftReadout := leftRealizes.readout focal (by cases leftAction <;> exact leftOwned)
  have rightReadout := rightRealizes.readout focal (by cases rightAction <;> exact rightOwned)
  change actionReadout suffix (leftAfter.playerView focal) = some leftAction at leftReadout
  change actionReadout suffix (rightAfter.playerView focal) = some rightAction at rightReadout
  rw [visible] at leftReadout
  exact Option.some.inj (leftReadout.symm.trans rightReadout)

end Vegas.GraphRuntime
