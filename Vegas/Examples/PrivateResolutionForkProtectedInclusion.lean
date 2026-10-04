/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PrivateResolutionForkPacketBounds
import Vegas.Examples.PrivateResolutionForkOpportunity

/-! # Protected sole-envelope inclusion in the public fork

Every actually protected owner envelope has a permanent receipt. The proof
distinguishes the public clean second activation from the risky second
activation and does not demand acceptance of the risky clock-one envelope.
-/

noncomputable section

namespace Vegas.PrivateResolutionFork

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory.Protocol

def inclusionEnd (event : nativeGraph.EventId) : Nat :=
  if event = aliceResolution then 7 else if event = bobResolution then 12 else 1

def ProtectedPacketClock (event : nativeGraph.EventId) (entry : app.PlayerEntry) : Prop :=
  event = aliceResolution → entry.beforeView.application.publicView.clock = 0

def receiptWindowInvariant : app.ProtocolState → Prop
  | none => True
  | some control => ∀ event owner, nativeGraph.actor? event = some owner →
      inclusionEnd event ≤ control.execution.environmentRecall.length →
      ∀ earlier later entry message,
      control.execution.recall owner = earlier ++ entry :: later →
      entry.emitted = some message → message.sender = owner →
      message.payload.call.event? nativeGraph = some event →
      ProtectedPacketClock event entry →
      (∀ other ∈ earlier ++ later, ¬ EmitsOtherFor (runtime setup) leaks other event message.id) →
      ∃ accepted, (message.id, accepted) ∈ control.execution.receipts

private theorem active_after_inclusion_impossible (control : app.Control)
    (clock : ClockPhase control) (who : Player) (active : control.actor = some who)
    (event : nativeGraph.EventId) (owned : nativeGraph.actor? event = some who)
    (included : inclusionEnd event ≤ control.execution.environmentRecall.length) : False := by
  have positions := clock.activation who active
  change Fin 4 at event
  fin_cases event
  · change none = some who at owned
    cases owned
  · change none = some who at owned
    cases owned
  · have same : who = alice := (Option.some.inj owned).symm
    subst who
    change 7 ≤ control.execution.environmentRecall.length at included
    rcases positions with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, impossible⟩
    all_goals first | cases impossible | omega
  · have same : who = bob := (Option.some.inj owned).symm
    subst who
    change 12 ≤ control.execution.environmentRecall.length at included
    rcases positions with ⟨_, impossible⟩ | ⟨_, impossible⟩ | ⟨_, impossible⟩ | ⟨_, _⟩
    all_goals first | cases impossible | omega

private theorem receiptWindow_respond (control : app.Control)
    (clock : ClockPhase control) (valid : receiptWindowInvariant (some control))
    (who : Player) (active : control.actor = some who) (response : app.Action) :
    receiptWindowInvariant (some { control with
      actor := none
      execution := control.execution.respond app who response }) := by
  intro event owner owned included earlier later entry message split emitted authored
    addressed clocked sole
  rw [app.respond_environmentRecall] at included
  rw [app.respond_receipts]
  by_cases same : who = owner
  · rw [← same] at owned split authored
    change (control.execution.respond app who response).recall who = earlier ++ entry :: later
      at split
    obtain ⟨output, afterRecall, _⟩ :=
      respond_recall_self setup leaks control.execution who response
    rw [afterRecall] at split
    rcases List.eq_nil_or_concat later with rfl | ⟨init, last, rfl⟩
    · exact (active_after_inclusion_impossible control clock who active event owned included).elim
    · simp only [List.concat_eq_append] at split sole
      have regroup : earlier ++ entry :: (init ++ [last]) =
          (earlier ++ entry :: init) ++ [last] := by simp
      rw [regroup] at split
      obtain ⟨beforeRecall, _⟩ := List.append_inj' split rfl
      exact valid event who owned included earlier init entry message beforeRecall emitted authored
        addressed clocked (by
          intro other member
          apply sole other
          simp only [List.mem_append] at member ⊢
          tauto)
  · change (control.execution.respond app who response).recall owner = earlier ++ entry :: later
      at split
    rw [app.respond_recall_other control.execution who owner (Ne.symm same) response] at split
    exact valid event owner owned included earlier later entry message split emitted authored
      addressed clocked sole

private theorem risky_zero_clock_first_receipt (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (inactive : control.actor = none) (stage : control.execution.environmentRecall.length = 6)
    (risky : lastTick control.execution.environmentRecall = false)
    (earlier later : List app.PlayerEntry) (entry : app.PlayerEntry)
    (message : Message Player (WitnessedPacket nativeGraph))
    (split : control.execution.recall alice = earlier ++ entry :: later)
    (emitted : entry.emitted = some message) (authored : message.sender = alice)
    (addressed : message.payload.call.event? nativeGraph = some aliceResolution)
    (sent : entry.beforeView.application.publicView.clock = 0) :
    ∃ accepted, (message.id, accepted) ∈ control.execution.receipts := by
  have clock := clockPhase_history trace
  have packets := packetBounds_history trace
  have counted : earlier.length + (later.length + 1) = 2 := by
    have current := clock.counted alice
    rw [inactive, split] at current
    simp only [reduceCtorEq, ite_false, Nat.add_zero] at current
    simpa [visitCount, stage] using current
  cases earlier with
  | nil =>
      exact packets.firstReceived entry later message (by omega) split emitted authored addressed
  | cons first before =>
      have emptyBefore : before = [] := List.length_eq_zero_iff.mp (by
        simp only [List.length_cons] at counted
        omega)
      have emptyLater : later = [] := List.length_eq_zero_iff.mp (by
        simp only [List.length_cons] at counted
        omega)
      subst before later
      have one := packets.riskSecond first entry stage risky split
      omega

private theorem receiptWindow_environment (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (valid : receiptWindowInvariant (some control)) (inactive : control.actor = none)
    (next : app.Execution) (command : app.Command)
    (selected : command ∈ (scheduler control.execution.environmentRecall
      (control.execution.observeEnvironment app)).support)
    (moved : next ∈ (control.execution.environmentStep app command).support)
    (remaining : Nat) :
    receiptWindowInvariant (some ⟨remaining, command.actor? app, next⟩) := by
  intro event owner owned included earlier later entry message split emitted authored
    addressed clocked sole
  change next.recall owner = earlier ++ entry :: later at split
  rw [app.environmentStep_recall control.execution next command moved] at split
  have receipts := app.environmentStep_receipts_prefix control.execution next command moved
  by_cases old : inclusionEnd event ≤ control.execution.environmentRecall.length
  · obtain ⟨accepted, found⟩ := valid event owner owned old earlier later entry message split
      emitted authored addressed clocked sole
    exact ⟨accepted, receipts.subset found⟩
  have appended := environmentStep_recall_append control.execution next command moved
  have fresh : control.execution.environmentRecall.length + 1 = inclusionEnd event := by
    rw [appended, List.length_append, List.length_singleton] at included
    omega
  by_cases risk : event = aliceResolution ∧
      lastTick control.execution.environmentRecall = false
  · rcases risk with ⟨rfl, risky⟩
    have same : owner = alice := (Option.some.inj owned).symm
    rw [same] at split authored
    have stage : control.execution.environmentRecall.length = 6 := by
      change control.execution.environmentRecall.length + 1 = 7 at fresh
      omega
    obtain ⟨accepted, found⟩ := risky_zero_clock_first_receipt control trace inactive stage risky
      earlier later entry message split emitted authored addressed (clocked rfl)
    exact ⟨accepted, receipts.subset found⟩
  obtain ⟨_, origins, recalled, retained, sound⟩ :=
    roster_trace_facts setup leaks horizon scheduler trace
  by_cases published : message.id ∈ control.execution.network.ledger.map Message.id
  · obtain ⟨accepted, found⟩ := receipt_of_published control.execution sound _ published
    exact ⟨accepted, receipts.subset found⟩
  obtain ⟨pending, latestEq⟩ := reactiveLatest_sole (runtime setup) leaks control.execution
    origins recalled retained event owner earlier later entry message split emitted authored
    addressed sole published
  have chosen : command = .include message.id := by
    change Fin 4 at event
    fin_cases event
    · change none = some owner at owned
      cases owned
    · change none = some owner at owned
      cases owned
    · have same : owner = alice := (Option.some.inj owned).symm
      have stage : control.execution.environmentRecall.length = 6 := by
        change control.execution.environmentRecall.length + 1 = 7 at fresh
        omega
      have clean : lastTick control.execution.environmentRecall = true := by
        exact Bool.eq_true_of_not_eq_false (fun ticked => risk ⟨rfl, ticked⟩)
      rw [scheduler_clean_second _ _ stage clean] at selected
      have actual := (PMF.mem_support_pure_iff _ _).mp selected
      rw [same] at latestEq
      exact actual.trans latestEq
    · have same : owner = bob := (Option.some.inj owned).symm
      have stage : control.execution.environmentRecall.length = 11 := by
        change control.execution.environmentRecall.length + 1 = 12 at fresh
        omega
      have actual := scheduler_support_other _ _ command (by omega) (by omega) selected
      rw [same] at latestEq
      rw [stage, stageCommand, latestEq] at actual
      exact actual
  rw [chosen] at moved
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
  cases (PMF.mem_support_pure_iff _ _).mp moved
  exact includePending_receipt_of_pending (runtime setup) leaks control.execution message pending

private theorem receiptWindow_transition (before after : app.ProtocolState)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace before)
    (valid : receiptWindowInvariant before) (joint : Player → Option app.Action)
    (reached : after ∈
      (app.transition (initialLaw setup) horizon scheduler before joint).support) :
    receiptWindowInvariant after := by
  cases before with
  | none =>
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
      intro event owner owned included
      have positive : 0 < inclusionEnd event := by
        unfold inclusionEnd
        split_ifs <;> omega
      change inclusionEnd event ≤ 0 at included
      omega
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          exact receiptWindow_respond _ (clockPhase_history trace) valid who rfl _
      | none =>
          cases remaining with
          | zero =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact valid
          | succ remaining =>
              obtain ⟨command, selected, realized⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, moved, rfl⟩ := PMF.support_map .. ▸ realized
              exact receiptWindow_environment _ trace valid rfl next command selected moved
                remaining

theorem receiptWindow_history : ∀ {state}
    (_trace : (app.protocol (initialLaw setup) horizon scheduler).Trace state),
    receiptWindowInvariant state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      receiptWindow_transition _ _ prior (receiptWindow_history prior) joint reached

theorem protectedInclusion :
    ProtectedInclusion (runtime setup) leaks (initialLaw setup) horizon scheduler bound := by
  intro control trace event owner owned earlier later entry message split emitted authored
    addressed ready sole unfinished due
  have clock := clockPhase_history trace
  have packets := packetBounds_history trace
  obtain ⟨rank, lower, _, ordered⟩ := (completionBounds_history trace).ordered
  have before : rank ≤ event.val := by
    have absent : ¬ event.val < rank := fun member => unfinished ((ordered.2 event).mpr member)
    omega
  have included : inclusionEnd event ≤ control.execution.environmentRecall.length := by
    rw [clock.clock] at due
    change Fin 4 at event
    fin_cases event
    · change none = some owner at owned
      cases owned
    · change none = some owner at owned
      cases owned
    · change 7 ≤ control.execution.environmentRecall.length
      change entry.beforeView.application.publicView.clock + 2 <
        stageClock control.execution.environmentRecall at due
      change rank ≤ 2 at before
      by_contra early
      dsimp only [stageClock] at due
      split_ifs at due <;> omega
    · have same : owner = bob := (Option.some.inj owned).symm
      have member : entry ∈ control.execution.recall bob := by
        rw [← same, split]
        simp
      rw [packets.bobClock entry member] at due
      change 12 ≤ control.execution.environmentRecall.length
      change 3 + 0 < stageClock control.execution.environmentRecall at due
      by_contra early
      dsimp only [stageClock] at due
      split_ifs at due <;> omega
  have clocked : ProtectedPacketClock event entry := by
    intro same
    subst event
    change rank ≤ 2 at before
    have maximum : control.execution.application.clock ≤ 3 := by
      rw [clock.clock]
      unfold lowerRank at lower
      dsimp only [stageClock]
      split_ifs at lower ⊢ <;> omega
    change entry.beforeView.application.publicView.clock + 2 <
      control.execution.application.clock at due
    omega
  exact receiptWindow_history trace event owner owned included earlier later entry message split
    emitted authored addressed clocked sole

/-- The fixed public-history scheduler meets every service clause at every
initialized raw protocol history, including malformed calls and retries. -/
theorem contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
    delay bound := ⟨opportunity, protectedInclusion, completesPlay⟩

end Vegas.PrivateResolutionFork
