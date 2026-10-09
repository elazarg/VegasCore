/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeLatePrefix
import Vegas.Examples.LateOpeningRuntimeServiceDecision
import Interaction.ReactiveSubmissionSerial
import Interaction.ReactiveAllocation

/-! # Evidence shared by actual native answer histories

The statements range over all legal raw histories, including malformed calls
and retries. The remembered silent observation excludes any earlier Bob
submission. Readiness and the public clock identify his answer-binding turn.
These facts classify parts of the native information fibers; they do not
assume or calculate an equilibrium posterior.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeFiberEvidence

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
open LateOpeningRuntimeLatePrefix

/-- A silent remembered observation leaves Bob's allocation counter at zero,
even if the other player has submitted arbitrary raw traffic. -/
theorem bob_silent_record_serial (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (bit : Bool) (label : Fin 3) (seen : Bool)
    (recalled : control.execution.recall bob = [bobObservationRecord bit label seen]) :
    control.execution.network.nextSerial bob = 0 := by
  have serial := app.serialRecall_history
    (LateOpeningRuntimeService.scheduler weight nonnegative) initial
      LateOpeningRuntimeService.horizon trace
  change control.execution.SerialRecall app at serial
  rw [serial bob, recalled]
  rfl

/-- In any actual history with that full remembered record, no Bob-authored
packet exists in pending, settled, leaked or recorded input traffic. -/
theorem bob_silent_record_no_packets (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (bit : Bool) (label : Fin 3) (seen : Bool)
    (recalled : control.execution.recall bob = [bobObservationRecord bit label seen]) :
    control.execution.network.Satisfies (fun message => message.sender ≠ bob) := by
  have zero := bob_silent_record_serial weight nonnegative control trace bit label seen recalled
  have allocated := app.serialsBeforeNext_history
    (LateOpeningRuntimeService.scheduler weight nonnegative) initial
      LateOpeningRuntimeService.horizon trace
  change control.execution.network.SerialsBeforeNext at allocated
  apply allocated.mono
  intro message earlier same
  change message.id.1 = bob at same
  rw [same, zero] at earlier
  exact Nat.not_lt_zero _ earlier

/-- Any actual ready answer-binding decision at clock three is the same
public callback, with exactly fourteen environment commands remaining. -/
theorem bob_binding_cursor (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (active : control.actor = some bob)
    (ready : control.execution.application.config.cut.Ready bobBindEvent)
    (clock : control.execution.application.clock = 3) :
    control.execution.environmentRecall.length = 12 ∧ control.remaining = 14 := by
  have located := active_cursor weight nonnegative control trace bob active
  have timed := clock_history weight nonnegative control trace
  have phase := completion_phase_history weight nonnegative control trace
  have position : control.execution.environmentRecall.length = 12 := by
    rcases located with ⟨impossible, _⟩ | ⟨_, positions | ⟨position, completed⟩⟩
    · exact ((by decide : bob ≠ alice) impossible).elim
    · simp only [Finset.mem_insert, Finset.mem_singleton] at positions
      rcases positions with position | position | position
      · rw [position, show LateOpeningRuntimeService.clockAt 5 = 1 by decide] at timed
        omega
      · exact position
      · exact (ready.1 (phase.afterBinding (by omega)).1).elim
    · apply (ready.1 ?_).elim
      exact (control.execution.application.config.history_exact bobBindEvent).mp completed
  have budget := command_budget weight nonnegative control trace
  exact ⟨position, by change control.remaining + _ = 26 at budget; omega⟩

/-- Membership in the actual bounded information fiber retains the complete
remembered observation, rather than merely a comparison game's label. -/
theorem bob_information_recall (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (bit : Bool) (label : Fin 3) (seen : Bool) (view : app.PlayerView)
    (same : (rawMenu.information initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).infoOf bob trace =
        some ([bobObservationRecord bit label seen], view)) :
    control.actor = some bob ∧
      control.execution.recall bob = [bobObservationRecord bit label seen] ∧
      control.execution.observe app bob = view := by
  change (rawMenu.signals initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).infoOf bob trace = _ at same
  rw [rawMenu.info] at same
  change (if control.actor = some bob then
    some (control.execution.recall bob, control.execution.observe app bob) else none) = _ at same
  by_cases active : control.actor = some bob
  · rw [ite_eq_left active] at same
    have equal := Option.some.inj same
    exact ⟨active, congrArg Prod.fst equal, congrArg Prod.snd equal⟩
  · rw [ite_eq_right active] at same
    cases same

theorem bob_information_no_packets (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (bit : Bool) (label : Fin 3) (seen : Bool) (view : app.PlayerView)
    (same : (rawMenu.information initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).infoOf bob trace =
        some ([bobObservationRecord bit label seen], view)) :
    control.execution.network.nextSerial bob = 0 ∧
      control.execution.network.Satisfies (fun message => message.sender ≠ bob) := by
  have recalled := (bob_information_recall weight nonnegative control trace
    bit label seen view same).2.1
  let raw := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  exact ⟨bob_silent_record_serial weight nonnegative control raw bit label seen recalled,
    bob_silent_record_no_packets weight nonnegative control raw bit label seen recalled⟩

end Vegas.Examples.LateOpeningRuntimeFiberEvidence
