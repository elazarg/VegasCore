/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventInvariant

/-! # Observations across private preparation and submission

Private preparation by another player preserves the focal player's contract
view, and equal focal views stay equal under the same private or submission
step. These are equalities of the actual contract projections, not
restrictions on what a deviator may inspect.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- The same outgoing commitment seals equal owner catalogues in the same way. -/
theorem submitStep_candidates_congr (left right : State graph) (who : Player)
    (packet : Payload graph)
    (same : (fun slot => left.candidates.lookup (who, slot)) =
      fun slot => right.candidates.lookup (who, slot)) :
    (fun slot => (submitStep left who packet).candidates.lookup (who, slot)) =
      fun slot => (submitStep right who packet).candidates.lookup (who, slot) := by
  funext slot
  cases packet with
  | commitment event candidate =>
      by_cases owned : candidate.1 = who
      · by_cases selected : (who, slot) = candidate
        · rw [show candidate = (who, slot) from selected.symm]
          simp only [submitStep, ↓reduceIte, CommitmentCandidates.lookup_freeze_self,
            congrFun same slot]
        · simp only [submitStep, owned, ↓reduceIte,
            CommitmentCandidates.lookup_freeze_other _ _ _ selected, congrFun same slot]
      · simpa only [submitStep, owned, ↓reduceIte] using congrFun same slot
  | opening event candidate raw | malformed raw => exact congrFun same slot

/-- Another player's arbitrary private command preserves every component of
the observer's application view, including its own candidate catalogue. -/
theorem privateStep_other_playerView (state : State graph) (owner observer : Player)
    (different : observer ≠ owner) (command : PrivateCommand graph) :
    (privateStep state owner command).playerView observer = state.playerView observer := by
  cases command with
  | prepare serial raw =>
      have candidates :
          (fun slot => (state.candidates.prepare owner (.prepared serial) raw).lookup
            (observer, slot)) = (fun slot => state.candidates.lookup (observer, slot)) := by
        funext slot
        apply CommitmentCandidates.lookup_prepare_other
        exact fun same => different (congrArg Prod.fst same)
      simp only [privateStep, State.playerView]
      rw [candidates]
      rfl
  | remember event action =>
      by_cases owned : graph.actor? event = some owner
      · rw [privateStep, dite_eq_left owned]
        cases cached : state.remembered event with
        | some prior => rfl
        | none =>
            have memory :
                (fun query => if graph.actor? query = some observer then
                  Function.update state.remembered event (some action) query else none) =
                (fun query => if graph.actor? query = some observer then
                  state.remembered query else none) := by
              funext query
              by_cases same : query = event
              · subst query
                simp [owned, Ne.symm different]
              · simp [Function.update_of_ne same]
            simp only [State.playerView]
            rw [memory]
            rfl
      · rw [privateStep, dite_eq_right owned]

/-- Private commands do not advance the semantic event configuration. -/
theorem privateStep_config (state : State graph) (owner : Player)
    (command : PrivateCommand graph) :
    (privateStep state owner command).config = state.config := by
  cases command with
  | prepare => rfl
  | remember event action =>
      by_cases owned : graph.actor? event = some owner
      · rw [privateStep, dite_eq_left owned]
        cases state.remembered event <;> rfl
      · rw [privateStep, dite_eq_right owned]

/-- Equal authenticated focal views remain equal after applying the same
focal private command. Foreign candidate meanings and remembered actions are
not compared. -/
theorem privateStep_focal_playerView_congr
    (left right : State graph) (focal : Player) (command : PrivateCommand graph)
    (publicEq : left.publicView = right.publicView)
    (observationEq : graph.playerObserve focal left.config =
      graph.playerObserve focal right.config)
    (rememberedEq : (fun event => if graph.actor? event = some focal then
      left.remembered event else none) = fun event =>
        if graph.actor? event = some focal then right.remembered event else none)
    (candidatesEq : (fun slot => left.candidates.lookup (focal, slot)) =
      fun slot => right.candidates.lookup (focal, slot)) :
    (privateStep left focal command).playerView focal =
      (privateStep right focal command).playerView focal := by
  cases command with
  | prepare serial raw =>
      unfold State.playerView
      congr 1
      funext slot
      by_cases same : (focal, slot) = (focal, Slot.prepared serial)
      · have slotEq : slot = Slot.prepared serial := congrArg Prod.snd same
        subst slot
        simp only [privateStep, CommitmentCandidates.lookup_prepare_self]
        rw [congrFun candidatesEq (Slot.prepared serial)]
      · simp only [privateStep]
        rw [left.candidates.lookup_prepare_other focal (.prepared serial) raw
            (focal, slot) same,
          right.candidates.lookup_prepare_other focal (.prepared serial) raw
            (focal, slot) same,
          congrFun candidatesEq slot]
  | remember event action =>
      by_cases owned : graph.actor? event = some focal
      · have cachedEq : left.remembered event = right.remembered event := by
          have atEvent := congrFun rememberedEq event
          simpa [State.playerView, owned] using atEvent
        rw [privateStep, dite_eq_left owned, privateStep, dite_eq_left owned]
        cases leftCached : left.remembered event with
        | none =>
            have rightCached : right.remembered event = none := cachedEq.symm.trans leftCached
            simp only [rightCached]
            unfold State.playerView
            congr 1
            funext query
            by_cases same : query = event
            · subst query
              simp [owned]
            · simp only
              rw [Function.update_of_ne same, Function.update_of_ne same]
              exact congrFun rememberedEq query
        | some prior =>
            have rightCached : right.remembered event = some prior := cachedEq.symm.trans leftCached
            simp only [rightCached]
            unfold State.playerView
            congr 1
      · rw [privateStep, dite_eq_right owned, privateStep, dite_eq_right owned]
        unfold State.playerView
        congr 1


end Vegas.EventGraphRuntime
