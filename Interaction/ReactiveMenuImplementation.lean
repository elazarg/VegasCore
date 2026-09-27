/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveMenuContinuation
import Interaction.ReactiveRoundTrace
import Interaction.ReactiveImplementation

/-! # Retained histories of a private legal implementation

The implementation memory remains outside the game. Every supported physical
prefix has an actual legal menu trace. Opponent coverage is required only at
those traces, and follows from profile extension between nested menus.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu) (initial : FinDist app.State) (horizon : Nat)
  (scheduler : app.Scheduler)

theorem IncludedIn.decoded_admissible {smaller larger : app.ResponseMenu}
    (included : smaller.IncludedIn larger)
    (source : ∀ who, (smaller.information initial horizon scheduler).BehavioralPolicy who)
    (target : ∀ who, (larger.information initial horizon scheduler).BehavioralPolicy who)
    (agrees : (included.actionRestriction initial horizon scheduler).ExtendsProfile source target)
    (who : Principal) :
    smaller.Admissible initial horizon scheduler who
      (larger.decodeProfile initial horizon scheduler target who) := by
  intro control trace active response supported
  let history : (smaller.protocol initial horizon scheduler).History := ⟨some control, trace⟩
  have running : ¬ (smaller.protocol initial horizon scheduler).terminal history.state := by
    change ¬ (control.remaining = 0 ∧ control.actor = none)
    intro stopped
    rw [active] at stopped
    cases stopped.2
  have acts : (smaller.protocol initial horizon scheduler).active history.state who := active
  obtain ⟨site, observed⟩ :=
    (smaller.information initial horizon scheduler).exists_informationSite_of_active who
      history running acts
  have input : site.1 = some (control.execution.recall who, control.execution.observe app who) := by
    rw [observed]
    change (smaller.signals initial horizon scheduler).infoOf who history.trace = _
    rw [smaller.info]
    change (if control.actor = some who then _ else none) = _
    rw [ite_eq_left active]
  rw [included.decoded_at_site initial horizon scheduler source target agrees who site
    _ _ input] at supported
  exact smaller.decode_embedPolicy_covered initial horizon scheduler who (source who) _ _
    response supported

variable {Memory : Type} (implementation : app.Implementation Memory)
  (owner : Principal) (players : Principal → app.Policy)
  (opponents : ∀ who, who ≠ owner → menu.Admissible initial horizon scheduler who (players who))
  (covered : ∀ memory past view response,
    response ∈ (implementation.respond memory (past, view)).support →
      response.1 ∈ menu.actions owner past view)

include opponents covered

/-- A supported pending response preserves an actual retained trace, for every
private implementation state and every opponent response. -/
theorem trace_implementation_resume
    (remaining : Nat) (actor : Option Principal) (execution : app.Execution) (memory : Memory)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, actor, execution⟩))
    (next : app.Execution × Memory)
    (supported : next ∈ (implementation.resume owner players actor execution memory).support) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, next.1⟩)) := by
  cases actor with
  | none =>
      cases FinDist.mem_support_pure.mp supported
      exact ⟨trace⟩
  | some who =>
      by_cases same : who = owner
      · subst who
        simp only [Implementation.resume, ↓reduceIte, FinDist.support_map] at supported
        obtain ⟨response, chosen, rfl⟩ := supported
        exact menu.trace_respond initial horizon scheduler remaining execution owner response.1
          trace (covered memory _ _ response chosen)
      · simp only [Implementation.resume, same, ↓reduceIte, FinDist.support_map] at supported
        obtain ⟨middle, moved, rfl⟩ := supported
        obtain ⟨response, chosen, rfl⟩ := FinDist.support_map .. ▸ moved
        exact menu.trace_respond initial horizon scheduler remaining execution who response
          trace (opponents who same ⟨remaining, some who, execution⟩ trace rfl response chosen)

/-- One existing scheduler round expands to retained environment and response
transitions; no extra memory is inserted in the protocol history. -/
theorem trace_implementation_round
    (remaining : Nat) (execution : app.Execution) (memory : Memory)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (next : app.Execution × Memory)
    (supported : next ∈ (implementation.round owner players scheduler execution memory).support) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, next.1⟩)) := by
  obtain ⟨command, selected, dispatched⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨middle, moved, resumed⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ dispatched)
  obtain ⟨pending⟩ := menu.trace_environment initial horizon scheduler remaining execution middle
    command trace selected moved
  exact menu.trace_implementation_resume initial horizon scheduler implementation owner players
    opponents covered remaining (command.actor? app) middle memory pending next resumed

/-- Every supported prefix of the actual private implementation run remains
in the retained game against arbitrary extending target opponents. -/
theorem trace_implementation_run
    (remaining count : Nat) (execution : app.Execution) (memory : Memory)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + count, none, execution⟩))
    (next : app.Execution)
    (supported : next ∈
      (implementation.run owner players scheduler count execution memory).support) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace (some ⟨remaining, none, next⟩)) := by
  induction count generalizing execution memory with
  | zero =>
      rw [Implementation.run_zero] at supported
      cases FinDist.mem_support_pure.mp supported
      exact ⟨trace⟩
  | succ count ih =>
      rw [Implementation.run_succ] at supported
      obtain ⟨middle, moved, finished⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
      obtain ⟨middleTrace⟩ := menu.trace_implementation_round initial horizon scheduler
        implementation owner players opponents covered (remaining + count) execution memory
        trace middle moved
      exact ih middle.1 middle.2 middleTrace finished

/-- Retaining the private memory in the analysis preserves the same actual
menu history witness. The witness depends only on the execution projection. -/
theorem trace_implementation_runJoint
    (remaining count : Nat) (execution : app.Execution) (memory : Memory)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + count, none, execution⟩))
    (next : app.Execution × Memory)
    (supported : next ∈
      (implementation.runJoint owner players scheduler count execution memory).support) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, next.1⟩)) := by
  apply menu.trace_implementation_run initial horizon scheduler implementation owner players
    opponents covered remaining count execution memory trace next.1
  change next.1 ∈ ((implementation.runJoint owner players scheduler count execution memory).map
    Prod.fst).support
  rw [FinDist.support_map]
  exact ⟨next, supported, rfl⟩

end Interaction.ReactiveApplication.ResponseMenu
