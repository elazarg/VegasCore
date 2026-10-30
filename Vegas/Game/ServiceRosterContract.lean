/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ServiceRosterInvariant

/-! # Asynchronous guarantees from the public roster calendar

The calendar invariant bounds the age of every unfinished event and retains
responses made during obsolete blocks. Its history certificate supplies the
reaction, protected-inclusion and completion guarantees of the native service.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace RosterCalendarInvariant

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (rosters : (graph setup).EventId → List Player)
  (network : (runtime setup).NetworkPolicy leaks)
  (calendar : ∀ (control : (application setup (Vegas.runtime setup) leaks).Control),
    ((application setup (Vegas.runtime setup) leaks).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control) → RosterCalendarInvariant setup leaks rosters (some control))

include calendar

/-- Every ready owner is activated within its event's rank bound. -/
theorem opportunity (opportunities : ActorOpportunities setup rosters) :
    Opportunity (runtime setup) leaks (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) (fun event => event.val) := by
  intro control trace event owner entered owned readyView activated late
  dsimp only at late
  have ready := (State.publicView_eventReady _ event).mp readyView
  rcases calendar control trace with
    ⟨current, offset, entryClock, obsolete, phase⟩ | ⟨_, _, terminal⟩
  · by_cases prior : event.val < current.val
    · exact (ready.1 (phase.prior event prior)).elim
    by_cases future : current.val < event.val
    · have bound := phase.future event future entered activated
      omega
    have same : event = current := Fin.ext (by omega)
    subst current
    by_cases early : offset ≤ (rosters event).length
    · have bound := phase.entered entered activated
      have zero : offset - ((rosters event).length + 1) = 0 := by omega
      have now : control.execution.application.clock = entryClock := by
        rw [phase.clock, zero]
        simp
      omega
    · have covered : owner ∈ (rosters event).take offset := by
        rw [List.take_of_length_le (by omega)]
        exact opportunities event owner owned
      exact phase.opportunity owner owned covered entered ready activated
  · unfold EventOrder.Cut.Terminal at terminal
    exact (ready.1 (by rw [terminal]; exact Finset.mem_univ _)).elim

/-- A sole authored identifier for a ready event receives an inclusion receipt
before any subsequent clock advance, including after an early obsolete-block response. -/
theorem protectedInclusion :
    ProtectedInclusion (runtime setup) leaks (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) (fun _ => 0) := by
  intro control trace event owner owned earlier later entry message split emitted authored
    addressed seen sole unfinished late
  dsimp only at late
  rcases calendar control trace with
    ⟨current, offset, entryClock, obsolete, phase⟩ | ⟨_, _, terminal⟩
  · have member : entry ∈ control.execution.recall owner := by
      rw [split]
      simp
    obtain ⟨sent, currentOrObsolete⟩ := phase.responses owner entry member event seen unfinished
    by_cases old : obsolete = true
    · have now : control.execution.application.clock = entryClock := by
        rw [phase.clock]
        simp [old]
      omega
    have same : event = current := currentOrObsolete.resolve_right old
    subst current
    by_cases early : offset ≤ (rosters event).length
    · have zero : offset - ((rosters event).length + 1) = 0 := by omega
      have now : control.execution.application.clock = entryClock := by
        rw [phase.clock, zero]
        simp
      omega
    · exact phase.inclusion (by omega) unfinished owner owned earlier later entry message
        split emitted authored addressed sole
  · unfold EventOrder.Cut.Terminal at terminal
    exact (unfinished (by rw [terminal]; exact Finset.mem_univ _)).elim

/-- Exhausting the fixed command horizon leaves every graph event completed. -/
theorem completesPlay :
    CompletesPlay (runtime setup) leaks (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) := by
  intro control trace terminal
  obtain ⟨finished, _⟩ := terminal
  rcases calendar control trace with
    ⟨current, offset, entryClock, obsolete, phase⟩ | ⟨_, _, complete⟩
  · have total := phase.remaining
    have bound := rosterPlan_length_block setup rosters current
    have inside := phase.inside
    rw [phase.position, finished] at total
    omega
  · exact complete

end RosterCalendarInvariant

end Vegas
