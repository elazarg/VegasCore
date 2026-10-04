/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PrivateResolutionForkCompletionBounds
import Vegas.Game.SourceServiceAsyncTimeliness

/-! # Actual packet clocks and first receipts in the public fork

These resources hold on initialized raw histories, independently of player
policies. The first Alice envelope has a receipt after the first inclusion
command; the risky second response is recorded at clock one.
-/

noncomputable section

namespace Vegas.PrivateResolutionFork

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory.Protocol

structure PacketBounds (control : app.Control) : Prop where
  activeUnticked : ∀ who, control.actor = some who →
    lastTick control.execution.environmentRecall = false
  riskSecond : ∀ first entry,
    control.execution.environmentRecall.length = 6 →
    lastTick control.execution.environmentRecall = false →
    control.execution.recall alice = [first, entry] →
    entry.beforeView.application.publicView.clock = 1
  bobClock : ∀ entry ∈ control.execution.recall bob,
    entry.beforeView.application.publicView.clock = 3
  firstReceived : ∀ entry later message,
    4 ≤ control.execution.environmentRecall.length →
    control.execution.recall alice = entry :: later →
    entry.emitted = some message → message.sender = alice →
    message.payload.call.event? nativeGraph = some aliceResolution →
    ∃ accepted, (message.id, accepted) ∈ control.execution.receipts

def packetBoundsInvariant : app.ProtocolState → Prop
  | none => True
  | some control => PacketBounds control

private theorem PacketBounds.alice_prior (control : app.Control)
    (phase : PacketBounds control) (clock : ClockPhase control)
    (active : control.actor = some alice)
    (later : 4 ≤ control.execution.environmentRecall.length) :
    (control.execution.recall alice).length = 1 := by
  have unticked := phase.activeUnticked alice active
  have counted := clock.counted alice
  rw [active] at counted
  simp only [ite_true] at counted
  rcases clock.activation alice active with ⟨stage, _⟩ | ⟨stage, _⟩ |
      ⟨stage, _⟩ | ⟨_, impossible⟩
  · omega
  · simp [visitCount, stage, unticked] at counted
    omega
  · simp [visitCount, stage] at counted
    omega
  · cases impossible

private theorem packetBounds_respond (control : app.Control)
    (phase : PacketBounds control) (clock : ClockPhase control)
    (who : Player) (active : control.actor = some who) (response : app.Action) :
    PacketBounds { control with
      actor := none
      execution := control.execution.respond app who response } := by
  have recallEq := app.respond_environmentRecall control.execution who response
  have receiptEq := app.respond_receipts control.execution who response
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro observer impossible
    cases impossible
  · intro first entry stage risky split
    change (control.execution.respond app who response).recall alice = [first, entry] at split
    rw [recallEq] at stage risky
    by_cases same : who = alice
    · subst who
      obtain ⟨output, afterRecall, _⟩ :=
        respond_recall_self setup leaks control.execution alice response
      have counted := clock.counted alice
      rw [active] at counted
      simp [visitCount, stage] at counted
      have one : (control.execution.recall alice).length = 1 := by omega
      obtain ⟨prior, beforeRecall⟩ := List.length_eq_one_iff.mp one
      rw [afterRecall, beforeRecall] at split
      simp only [List.singleton_append, List.cons.injEq] at split
      cases split.2.1
      change control.execution.application.clock = 1
      rw [clock.clock]
      simp [stageClock, stage]
    · rw [app.respond_recall_other control.execution who alice (Ne.symm same) response] at split
      exact phase.riskSecond first entry stage risky split
  · intro entry member
    rcases app.respond_entry_origin control.execution who bob response entry member with
      prior | ⟨same, fresh⟩
    · exact phase.bobClock entry prior
    · rw [fresh]
      have owner : who = bob := same.symm
      rcases clock.activation who active with ⟨_, first⟩ | ⟨_, second⟩ |
          ⟨_, third⟩ | ⟨stage, _⟩
      · cases first.symm.trans owner
      · cases second.symm.trans owner
      · cases third.symm.trans owner
      · change control.execution.application.clock = 3
        rw [clock.clock]
        simp [stageClock, stage]
  · intro entry later message included split emitted authored addressed
    rw [recallEq] at included
    rw [receiptEq]
    by_cases same : who = alice
    · subst who
      change (control.execution.respond app alice response).recall alice = entry :: later at split
      obtain ⟨output, afterRecall, _⟩ :=
        respond_recall_self setup leaks control.execution alice response
      rw [afterRecall] at split
      rcases List.eq_nil_or_concat later with rfl | ⟨init, last, rfl⟩
      · have length := congrArg List.length split
        have one := PacketBounds.alice_prior control phase clock active included
        simp only [List.length_append, List.length_cons, List.length_nil] at length
        omega
      · simp only [List.concat_eq_append] at split
        have regroup : entry :: (init ++ [last]) = (entry :: init) ++ [last] := rfl
        rw [regroup] at split
        obtain ⟨beforeRecall, _⟩ := List.append_inj' split rfl
        exact phase.firstReceived entry init message included beforeRecall emitted authored
          addressed
    · change (control.execution.respond app who response).recall alice = entry :: later at split
      rw [app.respond_recall_other control.execution who alice (Ne.symm same) response] at split
      exact phase.firstReceived entry later message included split emitted authored addressed

private theorem packetBounds_environment (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (phase : PacketBounds control) (inactive : control.actor = none)
    (next : app.Execution) (command : app.Command)
    (selected : command ∈ (scheduler control.execution.environmentRecall
      (control.execution.observeEnvironment app)).support)
    (moved : next ∈ (control.execution.environmentStep app command).support)
    (remaining : Nat) :
    PacketBounds ⟨remaining, command.actor? app, next⟩ := by
  have appended := environmentStep_recall_append control.execution next command moved
  have recallEq := app.environmentStep_recall control.execution next command moved
  have receipts := app.environmentStep_receipts_prefix control.execution next command moved
  have length : next.environmentRecall.length = control.execution.environmentRecall.length + 1 := by
    rw [appended, List.length_append, List.length_singleton]
  have clock := clockPhase_history trace
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro who active
    change command.actor? app = some who at active
    rw [appended]
    cases command <;> simp_all [ReactiveApplication.Command.actor?, lastTick]
  · intro first entry stage risky split
    change next.recall alice = [first, entry] at split
    rw [recallEq] at split
    have priorStage : control.execution.environmentRecall.length = 5 := by
      rw [length] at stage
      omega
    have chosen := scheduler_support_other _ _ command (by omega) (by omega) selected
    rw [priorStage, stageCommand] at chosen
    have ticked : lastTick control.execution.environmentRecall = true := by
      cases priorTick : lastTick control.execution.environmentRecall
      · rw [priorTick] at chosen
        simp only [Bool.false_eq_true, ite_false] at chosen
        rw [appended, chosen] at risky
        simp [lastTick] at risky
      · rfl
    have counted := clock.counted alice
    rw [inactive] at counted
    simp only [reduceCtorEq, ite_false, Nat.add_zero] at counted
    simp [visitCount, priorStage, ticked] at counted
    have two := congrArg List.length split
    simp only [List.length_cons, List.length_nil] at two
    omega
  · intro entry member
    rw [recallEq] at member
    exact phase.bobClock entry member
  · intro entry later message included split emitted authored addressed
    change next.recall alice = entry :: later at split
    rw [recallEq] at split
    by_cases old : 4 ≤ control.execution.environmentRecall.length
    · obtain ⟨accepted, found⟩ :=
        phase.firstReceived entry later message old split emitted authored addressed
      exact ⟨accepted, receipts.subset found⟩
    have stage : control.execution.environmentRecall.length = 3 := by
      rw [length] at included
      omega
    obtain ⟨_, origins, recalled, retained, sound⟩ :=
      roster_trace_facts setup leaks horizon scheduler trace
    by_cases published : message.id ∈ control.execution.network.ledger.map Message.id
    · obtain ⟨accepted, found⟩ := receipt_of_published control.execution sound _ published
      exact ⟨accepted, receipts.subset found⟩
    have counted := clock.counted alice
    rw [inactive, split] at counted
    simp only [reduceCtorEq, ite_false, Nat.add_zero] at counted
    have empty : later = [] := by simpa [visitCount, stage] using counted
    subst later
    obtain ⟨pending, latestEq⟩ := reactiveLatest_sole (runtime setup) leaks control.execution
      origins recalled retained aliceResolution alice [] [] entry message split emitted
      authored addressed (by simp) published
    have chosen := scheduler_support_other _ _ command (by omega) (by omega) selected
    rw [stage, stageCommand, latestEq] at chosen
    rw [chosen] at moved
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
    cases (PMF.mem_support_pure_iff _ _).mp moved
    exact includePending_receipt_of_pending (runtime setup) leaks control.execution message pending

private theorem packetBounds_transition (before after : app.ProtocolState)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace before)
    (valid : packetBoundsInvariant before) (joint : Player → Option app.Action)
    (reached : after ∈
      (app.transition (initialLaw setup) horizon scheduler before joint).support) :
    packetBoundsInvariant after := by
  cases before with
  | none =>
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
      refine ⟨by simp, ?_, by simp [ReactiveApplication.Execution.initial], ?_⟩
      · intro first entry impossible
        cases impossible
      · intro entry later message impossible
        change 4 ≤ 0 at impossible
        omega
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          exact packetBounds_respond _ valid (clockPhase_history trace) who rfl _
      | none =>
          cases remaining with
          | zero =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact valid
          | succ remaining =>
              obtain ⟨command, selected, realized⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, moved, rfl⟩ := PMF.support_map .. ▸ realized
              exact packetBounds_environment _ trace valid rfl next command selected moved remaining

theorem packetBounds_history : ∀ {state}
    (_trace : (app.protocol (initialLaw setup) horizon scheduler).Trace state),
    packetBoundsInvariant state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      packetBounds_transition _ _ prior (packetBounds_history prior) joint reached

end Vegas.PrivateResolutionFork
