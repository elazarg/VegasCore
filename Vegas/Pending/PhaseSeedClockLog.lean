/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedCalendar

/-! # Permanent tick closure in the actual all-event calendar

The driver's private bookkeeping is reconstructed from actual environment
recall. Nonactivation replies permanently close their physical coordinate at
that global clock; retirement never deletes an earlier closed coordinate.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem replayClosedFrom_append
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed)
    (closed : Finset (Nat × PhaseSeedAddress graph))
    (earlier left right : List (app).EnvironmentEntry) :
    replayClosedFrom runtime leaks priority rest closed earlier (left ++ right) =
      replayClosedFrom runtime leaks priority rest
        (replayClosedFrom runtime leaks priority rest closed earlier left)
          (earlier ++ left) right := by
  induction left generalizing closed earlier with
  | nil => simp only [List.nil_append, replayClosedFrom, List.append_nil]
  | cons entry later ih =>
      simp only [List.cons_append, replayClosedFrom, ih, List.append_assoc, List.nil_append]

theorem replayClosed_snoc
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (past : List (app).EnvironmentEntry)
    (entry : (app).EnvironmentEntry) :
    replayClosed runtime leaks priority rest (past ++ [entry]) =
      closeAfter runtime leaks (replayClosed runtime leaks priority rest past) entry.beforeView
        (selectOpen runtime leaks (replayClosed runtime leaks priority rest past) entry.beforeView
          (priority rest past entry.beforeView)) entry.command := by
  simp only [replayClosed, replayClosedFrom_append, List.nil_append, replayClosedFrom]

theorem replayClosedFrom_mono
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed)
    (closed : Finset (Nat × PhaseSeedAddress graph))
    (earlier later : List (app).EnvironmentEntry) :
    closed ⊆ replayClosedFrom runtime leaks priority rest closed earlier later := by
  induction later generalizing closed earlier with
  | nil => exact Finset.Subset.refl _
  | cons entry later ih =>
      exact (closeAfter_mono runtime leaks closed _ _ _).trans (ih _ _)

/-- Neither successful resolution nor a failed or rejected physical reply
removes the closed record of an earlier actual query. -/
theorem replayClosed_append_mono
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed)
    (past later : List (app).EnvironmentEntry) :
    replayClosed runtime leaks priority rest past ⊆
      replayClosed runtime leaks priority rest (past ++ later) := by
  unfold replayClosed
  rw [replayClosedFrom_append]
  exact replayClosedFrom_mono runtime leaks priority rest _ _ _

/-- The actual nonactivation command closes its selected physical address at
this tick, even when its application effect installs a new namespace. -/
theorem closed_after_nonactivation
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (past : List (app).EnvironmentEntry)
    (view : (app).EnvironmentView) (coordinate : PhaseSeedAddress graph) (command : (app).Command)
    (selected : selectOpen runtime leaks (replayClosed runtime leaks priority rest past) view
      (priority rest past view) = some coordinate)
    (idle : (command.actor? app).isNone = true) :
    (view.application.native.clock, coordinate) ∈
      replayClosed runtime leaks priority rest (past ++ [⟨view, command⟩]) := by
  rw [replayClosed_snoc, selected]
  simp only [closeAfter, idle, ite_true, Option.elim_some]
  exact Finset.mem_insert_self _ _

/-- At a fixed global clock a closed physical address cannot be selected again,
regardless of intervening callbacks, resets, or remainder priorities. -/
theorem not_selected_after_nonactivation
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed)
    (past later : List (app).EnvironmentEntry)
    (view nextView : (app).EnvironmentView) (coordinate : PhaseSeedAddress graph)
    (command : (app).Command)
    (selected : selectOpen runtime leaks (replayClosed runtime leaks priority rest past) view
      (priority rest past view) = some coordinate)
    (idle : (command.actor? app).isNone = true)
    (sameClock : nextView.application.native.clock = view.application.native.clock) :
    selectOpen runtime leaks
      (replayClosed runtime leaks priority rest (past ++ [⟨view, command⟩] ++ later)) nextView
      (priority rest (past ++ [⟨view, command⟩] ++ later) nextView) ≠
        some coordinate := by
  intro again
  have closed := replayClosed_append_mono runtime leaks priority rest
    (past ++ [⟨view, command⟩]) later
    (closed_after_nonactivation runtime leaks priority rest past view coordinate command
      selected idle)
  apply request_unclosed runtime leaks _ nextView _ coordinate again
  rwa [sameClock]

end Vegas.EventGraphRuntime.PhaseSeedCalendar
