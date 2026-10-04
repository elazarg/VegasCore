/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingSelectedInput
import Vegas.Game.SourceServiceBindingNoAttempt

/-! # The actual continuation after the family's selected owned input

Responding at the selected input increases the owner's actual counted turn
index. Every later owner recall extends that recall, so the selected family
cannot select the event again. Its complete stopped execution is therefore the
same as the owner-silent execution, including all public and foreign traffic.
This fact holds for a transmitted decision and for closed-gate silence alike.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem family_silent_after_selected_input
    (bound : (graph setup).EventId → Nat) (profile : BehavioralProfile setup.program)
    (owner : Player) (event : (graph setup).EventId) (turns : Nat) (slot : Fin (turns + 1))
    (middle : (application setup leaks).Execution)
    (selected : sourceServiceTurn setup leaks owner event (middle.recall owner)
      (middle.observe (application setup leaks) owner) = some slot.val)
    (response : (application setup leaks).Action)
    (current : (application setup leaks).Execution)
    (retained : (middle.respond (application setup leaks) owner response).recall owner <+:
      current.recall owner) :
    sourceServiceTurnFamily setup leaks bound profile owner event turns slot (current.recall owner)
        (current.observe (application setup leaks) owner) =
      (application setup leaks).silentPolicy (current.recall owner)
        (current.observe (application setup leaks) owner) := by
  let app := application setup leaks
  have turn : middle.application.publicView.ownTurn? owner = some event := by
    unfold sourceServiceTurn at selected
    split at selected
    · assumption
    · cases selected
  have turnView : (middle.observe (application setup leaks) owner).application.publicView.ownTurn?
      owner = some event := turn
  have counted : (middle.recall owner).countP (fun entry =>
      decide (entry.beforeView.application.publicView.ownTurn? owner = some event)) = slot.val := by
    simpa only [sourceServiceTurn, turnView, ↓reduceIte, Option.some.injEq] using selected
  obtain ⟨emitted, recallEq, _⟩ := respond_recall_self setup leaks middle owner response
  obtain ⟨later, prefixEq⟩ := retained
  have laterCount : slot.val < (current.recall owner).countP (fun entry =>
      decide (entry.beforeView.application.publicView.ownTurn? owner = some event)) := by
    rw [← prefixEq, recallEq, List.countP_append, List.countP_append, List.countP_cons,
      List.countP_nil]
    simp only [turnView, decide_true, ↓reduceIte]
    omega
  apply app.turnScheduledPolicy_unselected
  intro other equal
  cases Option.some.inj equal
  intro selectedAgain
  unfold sourceServiceTurn at selectedAgain
  split at selectedAgain
  · have sameCount := Option.some.inj selectedAgain
    omega
  · cases selectedAgain

/-- The selected family makes no second decision at its event. The equality
retains the whole actual stopped execution law, with arbitrary foreign policies
and without requiring that the selected response transmitted a packet. -/
theorem sourceService_selected_continuation_silent
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (bound : (graph setup).EventId → Nat) (profile : BehavioralProfile setup.program)
    (owner : Player) (event : (graph setup).EventId) (turns : Nat) (slot : Fin (turns + 1))
    (middle : (application setup leaks).Execution)
    (selected : sourceServiceTurn setup leaks owner event (middle.recall owner)
      (middle.observe (application setup leaks) owner) = some slot.val)
    (response : (application setup leaks).Action) (horizon : Nat) :
    (application setup leaks).runUntilHorizon scheduler
        (Function.update players owner
          (sourceServiceTurnFamily setup leaks bound profile owner event turns slot))
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (middle.respond (application setup leaks) owner response) =
      (application setup leaks).runUntilHorizon scheduler
        (Function.update players owner (application setup leaks).silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (middle.respond (application setup leaks) owner response) := by
  let app := application setup leaks
  let start := middle.respond app owner response
  let first := Function.update players owner
    (sourceServiceTurnFamily setup leaks bound profile owner event turns slot)
  let invariant := fun current : app.Execution => start.recall owner <+: current.recall owner
  have preserved : app.PolicyInvariant first invariant := {
    respond := fun current actor action holds _ =>
      holds.trans (app.respond_recall_prefix current actor owner action)
    environment := fun current next command holds moved => by
      change start.recall owner <+: next.recall owner
      rw [app.environmentStep_recall current next command moved]
      exact holds }
  unfold ReactiveApplication.runUntilHorizon
  apply app.runUntil_congr_of_agree scheduler _ _ _ invariant
  · intro current holds _running command _ before moved actor _active
    by_cases foreign : actor ≠ owner
    · simp only [Function.update_of_ne foreign]
    · have same : actor = owner := not_ne_iff.mp foreign
      subst actor
      simp only [Function.update_self]
      apply family_silent_after_selected_input bound profile owner event turns slot middle selected
        response before
      rw [app.environmentStep_recall current before command moved]
      exact holds
  · intro current holds _running next reached
    obtain ⟨command, _, before, moved, cases⟩ := round_cases setup leaks reached
    have beforeHolds := preserved.environment current before command holds moved
    rcases cases with ⟨_, rfl⟩ | ⟨actor, _, action, chosen, rfl⟩
    · exact beforeHolds
    · exact preserved.respond before actor action beforeHolds chosen
  · rfl

end Vegas
