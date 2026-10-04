/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePastPrefix

/-! # Actual source prefixes at native owned information ancestors

An information history at an owned ready input has exactly the earlier source
ranks completed, by the graph's sequential dependency order. This fact needs
neither first-turn play nor clean histories. The retrospective decoder at every
later native descendant therefore reads that same before-response source prefix.
The chronological first-input passage may select such an ancestor without a
runtime snapshot or a stopping oracle.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Every actual history with this owned input has an active owner control,
the exact visible recall and view, and precisely the source prefix before its
ready event. The statement covers arbitrary raw legal menu histories. -/
theorem sourceServiceInformation_owned_prefix
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (menu : (application setup leaks).ResponseMenu)
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) (who : Player)
    (event : (graph setup).EventId)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (turn : view.application.publicView.ownTurn? who = some event)
    (before : (menu.information initial horizon scheduler).InformationHistory who
      (some (past, view))) :
    ∃ remaining execution,
      before.1.state = some ⟨remaining, some who, execution⟩ ∧
      execution.recall who = past ∧ execution.observe (application setup leaks) who = view ∧
      execution.application.config.cut.IsPrefix event.val ∧
      sourceServicePastPrefix? setup event.val execution.application.config =
        sourceServicePrefix? setup event.val execution.application.config := by
  let app := application setup leaks
  have infoEq : app.observe who before.1.state = some (past, view) := by
    rw [← menu.info initial horizon scheduler who before.1.trace]
    exact before.2
  obtain ⟨remaining, execution, current, recallEq, viewEq⟩ :
      ∃ remaining execution,
        before.1.state = some ⟨remaining, some who, execution⟩ ∧
        execution.recall who = past ∧ execution.observe app who = view := by
    cases stateEq : before.1.state with
    | none => simp only [stateEq, ReactiveApplication.observe] at infoEq; contradiction
    | some control =>
        by_cases actor : control.actor = some who
        · simp only [stateEq, ReactiveApplication.observe, actor, ↓reduceIte] at infoEq
          obtain ⟨recallEq, viewEq⟩ := Prod.mk.inj (Option.some.inj infoEq)
          exact ⟨control.remaining, control.execution, by cases control; cases actor; rfl,
            recallEq, viewEq⟩
        · simp only [stateEq, ReactiveApplication.observe, actor, ↓reduceIte] at infoEq
          contradiction
  have actualTurn : execution.application.publicView.ownTurn? who = some event := by
    change (execution.observe app who).application.publicView.ownTurn? who = some event
    rwa [viewEq]
  have ready := (execution.application.publicView_eventReady event).mp
    (execution.application.publicView.ownTurn?_spec who event actualTurn).1
  have ordered : execution.application.config.cut.IsPrefix event.val :=
    ⟨Nat.le_of_lt event.isLt, fun prior =>
      setup.eventGraph.sequentialize_mem_completed_iff_lt_of_ready
        execution.application.config.cut ready⟩
  exact ⟨remaining, execution, current, recallEq, viewEq, ordered,
    sourceServicePastPrefix?_eq_at_prefix setup event.val _ ordered⟩

/-- Every actual descendant reads the same source state and source action
history that preceded the owned ancestor response. No completion, policy,
likelihood, or fixed decision depth is required. -/
theorem sourceServiceInformation_ancestor_pastPrefix
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (menu : (application setup leaks).ResponseMenu)
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) (who : Player)
    (event : (graph setup).EventId)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (turn : view.application.publicView.ownTurn? who = some event)
    (before : (menu.information initial horizon scheduler).InformationHistory who
      (some (past, view)))
    (final : (menu.protocol initial horizon scheduler).History)
    (reached : (menu.protocol initial horizon scheduler).HistoryReaches before.1 final)
    (control : (application setup leaks).Control) (finalEq : final.state = some control) :
    ∃ remaining execution,
      before.1.state = some ⟨remaining, some who, execution⟩ ∧
      execution.recall who = past ∧ execution.observe (application setup leaks) who = view ∧
      execution.application.config.cut.IsPrefix event.val ∧
      sourceServicePastPrefix? setup event.val control.execution.application.config =
        sourceServicePrefix? setup event.val execution.application.config := by
  obtain ⟨remaining, execution, current, recallEq, viewEq, ordered, decoded⟩ :=
    sourceServiceInformation_owned_prefix setup leaks menu initial horizon scheduler who event
      past view turn before
  obtain ⟨fuel, path⟩ := reached
  have kept := sourceServicePastPrefix_reaches setup leaks initial horizon scheduler event.val
    (menu.reaches_raw initial horizon scheduler path) ⟨remaining, some who, execution⟩ control
    current finalEq (fun prior earlier => (ordered.2 prior).mpr earlier)
  exact ⟨remaining, execution, current, recallEq, viewEq, ordered, kept.2.trans decoded⟩

end Vegas
