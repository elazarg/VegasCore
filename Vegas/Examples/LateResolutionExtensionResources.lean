/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateResolutionFreeEquilibrium
import Interaction.ReactiveMenuRestriction

/-! # Actual retained information resources in larger response menus

The common decision depths follow from the initialized raw schedule and the
player's actual recall. Exact completed states are derived within the risk
menu's retained information histories, not assumed for a larger menu's new
off-path histories.
-/

noncomputable section

namespace Vegas.LateResolutionService

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory GameTheory.Math.Probability

theorem second_decision_information_state (bounds : MessageBounds nativeGraph)
    (disclose : Bool)
    (history : (nativeModel bounds).InformationHistory owner
      (some ((secondDecisionExecution disclose).recall owner,
        (secondDecisionExecution disclose).observe app owner))) :
    history.1.state = some ⟨4, some owner, secondDecisionExecution disclose⟩ := by
  obtain ⟨execution, current, _position, observed⟩ :=
    second_decision_information_resources bounds disclose history
  have active : (⟨4, some owner, execution⟩ : app.Control).actor = some owner := rfl
  rcases native_decision_history_cases bounds history.1 _ current active with
    first | waiting | ⟨other, completed⟩
  · rw [first] at current
    have same := Option.some.inj current
    have remaining := congrArg (fun control : app.Control => control.remaining) same
    change (7 : Nat) = 4 at remaining
    omega
  · rw [waiting] at current
    have same := Option.some.inj current
    have equal := congrArg (fun control : app.Control => control.execution) same
    change secondWaitExecution = execution at equal
    rw [← equal] at observed
    have submitted := congrArg (fun info : app.Info => info.map
      (fun input => input.1.map (fun entry => entry.action.transmission.isSome))) observed
    cases disclose <;> change some [false] = some [true] at submitted <;> cases submitted
  · rw [completed] at current
    have same := Option.some.inj current
    have equal := congrArg (fun control : app.Control => control.execution) same
    change secondDecisionExecution other = execution at equal
    rw [← equal] at observed
    have packets := congrArg (fun info : app.Info => info.map
      (fun input => input.1.map (fun entry =>
        entry.action.transmission.map (fun material => material.call.packet)))) observed
    cases other <;> cases disclose
    · exact completed
    · change some [some (Payload.withhold resolution : Payload nativeGraph)] =
        some [some (Payload.opening resolution firstCandidate ⟨BaseTy.bool, true⟩)] at packets
      cases packets
    · change some [some (Payload.opening resolution firstCandidate
        ⟨BaseTy.bool, true⟩ : Payload nativeGraph)] =
        some [some (Payload.withhold resolution)] at packets
      cases packets
    · exact completed

theorem menu_history_information_depth (menu : app.ResponseMenu)
    (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : (menu.information (initialLaw setup) horizon scheduler).infoOf owner
      history.trace = some (past, view)) :
    history.trace.length = if view.application.publicView.clock = 0 then 4 else 8 := by
  rcases history with ⟨state, trace⟩
  have information := (menu.info (initialLaw setup) horizon scheduler owner trace).symm.trans
    observed
  cases state with
  | none => simp [ReactiveApplication.observe] at information
  | some control =>
      change (if control.actor = some owner then
        some (control.execution.recall owner, control.execution.observe app owner) else none) = _
        at information
      split at information
      · rename_i active
        have same := Option.some.inj information
        have clock := congrArg (fun input : List app.PlayerEntry × app.PlayerView =>
          input.2.application.publicView.clock) same
        change control.execution.application.clock = view.application.publicView.clock at clock
        let rawTrace := menu.toRawTrace (initialLaw setup) horizon scheduler trace
        have phase := phase_history rawTrace
        have length := app.trace_length_of_control (initialLaw setup) horizon scheduler control
          rawTrace
        have rawLength : rawTrace.length = trace.length := by
          dsimp only [rawTrace]
          rw [menu.toRawTrace_length]
        rw [rawLength, Fin.sum_univ_one] at length
        rcases phase.activation (by rw [active]; rfl) with first | second
        · have clockZero := phase.clock
          rw [first] at clockZero
          change control.execution.application.clock = 0 at clockZero
          have publicZero : view.application.publicView.clock = 0 := clock.symm.trans clockZero
          rw [ite_eq_left publicZero]
          have count := phase.recallCount
          rw [first, active] at count
          rw [first, count] at length
          exact length
        · have clockOne := phase.clock
          rw [second] at clockOne
          change control.execution.application.clock = 1 at clockOne
          have publicOne : view.application.publicView.clock = 1 := clock.symm.trans clockOne
          rw [ite_eq_right (by omega)]
          have count := phase.recallCount
          rw [second, active] at count
          rw [second, count] at length
          exact length
      · cases information

def retainedNativeDepth (bounds : MessageBounds nativeGraph) (who : Player)
    (site : (nativeModel bounds).InformationSite who) : Nat :=
  if site.1.map (fun input => input.2.application.publicView.clock) = some 0 then 4 else 8

theorem retained_native_common_depth (bounds : MessageBounds nativeGraph)
    (menu : app.ResponseMenu) (included : (nativeMenu bounds).IncludedIn menu)
    (who : Player) (site : (nativeModel bounds).InformationSite who) :
    InformationModel.InformationSite.CommonDepth
      (menu.information (initialLaw setup) horizon scheduler)
      ((included.actionRestriction (initialLaw setup) horizon scheduler).site who site)
      (retainedNativeDepth bounds who site) := by
  have own : who = owner := Subsingleton.elim _ _
  subst who
  intro history
  have observed : (menu.information (initialLaw setup) horizon scheduler).infoOf owner
      history.1.trace = site.1 := history.2
  rcases native_decision_site_cases bounds site with early | late | ⟨disclose, completed⟩
  · have exactDepth := menu_history_information_depth menu history.1
      (firstExecution.recall owner) (firstExecution.observe app owner) (observed.trans early)
    change history.1.trace.length = 4 at exactDepth
    have clock : (firstExecution.observe app owner).application.publicView.clock = 0 := rfl
    simpa only [retainedNativeDepth, early, Option.map_some, clock, ↓reduceIte] using exactDepth
  · have exactDepth := menu_history_information_depth menu history.1
      (secondWaitExecution.recall owner) (secondWaitExecution.observe app owner)
      (observed.trans late)
    change history.1.trace.length = 8 at exactDepth
    have clock : (secondWaitExecution.observe app owner).application.publicView.clock = 1 := rfl
    simpa only [retainedNativeDepth, late, Option.map_some, clock, Option.some.injEq,
      show (1 : Nat) ≠ 0 by decide, ↓reduceIte] using exactDepth
  · have exactDepth := menu_history_information_depth menu history.1
      ((secondDecisionExecution disclose).recall owner)
      ((secondDecisionExecution disclose).observe app owner) (observed.trans completed)
    have clock :
        ((secondDecisionExecution disclose).observe app owner).application.publicView.clock =
          1 := by
      change (secondDecisionExecution disclose).application.clock = 1
      rw [second_decision_application]
    rw [clock, ite_eq_right (by decide)] at exactDepth
    simpa only [retainedNativeDepth, completed, Option.map_some, clock, Option.some.injEq,
      show (1 : Nat) ≠ 0 by decide, ↓reduceIte] using exactDepth

end Vegas.LateResolutionService
