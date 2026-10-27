/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.OddsEvensRecoveryClock
import Vegas.Pending.ExclusionActivationOrigin

/-! # Recorded owner opportunities on the actual forced-exit execution -/

noncomputable section

namespace Vegas.Examples.OddsEvensRecoveryService

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability

def ownerSlot (owner : OddsEvens.Player) : Nat := if owner then packetBudget + 1 else packetBudget

theorem ownerSlot_bounds (owner : OddsEvens.Player) : ownerSlot owner < width := by
  cases owner <;> decide

theorem owner_command (cycle : Nat) (owner : OddsEvens.Player) (view : app.EnvironmentView)
    (odd : cycle % 2 = 1) :
    command (cycle * width + ownerSlot owner) view = .activate owner := by
  cases owner with
  | false => exact even_activation cycle view odd
  | true => exact odd_activation cycle view odd

def RecordedOffers (execution : app.Execution) : Prop :=
  ∀ event owner entered cycle, compiled.actor? event = some owner →
    execution.application.native.activatedAt event = some entered →
    entered < cycle → cycle % 2 = 1 →
    cycle * width + ownerSlot owner < execution.environmentRecall.length →
    ∃ entry ∈ execution.environmentRecall, entry.command = .activate owner ∧
      entry.beforeView.application.1.activatedAt event = some entered ∧
      entry.beforeView.application.1.EventReady event ∧
      entry.beforeView.application.1.clock = cycle

private theorem cycle_le_before_offer (owner : OddsEvens.Player) (cycle cursor : Nat)
    (earlier : cycle * width + ownerSlot owner < cursor + 1) : cycle ≤ cursor / width := by
  have positive : 0 < width := by decide
  apply (Nat.le_div_iff_mul_le positive).mpr
  omega

theorem recorded_offers_invariant (inputs : compiled.Inputs) :
    app.ServiceInvariant scheduler (fun execution =>
      ClockAligned inputs 0 execution ∧ RecordedOffers execution) where
  respond execution who action valid := by
    refine ⟨(clock_aligned_invariant inputs 0).respond execution who action valid.1, ?_⟩
    intro event owner entered cycle acting activated older odd earlier
    rw [app.respond_environmentRecall] at earlier ⊢
    have beforeCycle : cycle ≤ execution.application.native.clock := by
      rw [valid.1.clock, Nat.zero_add]
      exact cycle_le_before_offer owner cycle execution.environmentRecall.length (by omega)
    have progress := Recovery.respond_progress runtime leaks inputs execution who action
      valid.1.valid.native
    have ready := ((progress.invariant.activated_iff event).mp (by
      rw [activated]; rfl)).1
    have origin := Recovery.respond_activationOrigin runtime leaks execution who action
      event entered activated ready.1
    rcases origin with retained | fresh
    · exact valid.2 event owner entered cycle acting retained older odd earlier
    · omega
  environment execution next selected valid supported moved := by
    refine ⟨(clock_aligned_invariant inputs 0).environment execution next selected valid.1
      supported moved, ?_⟩
    intro event owner entered cycle acting activated older odd earlier
    have recallEq := app.environmentStep_environmentRecall execution next selected moved
    have lengthEq : next.environmentRecall.length = execution.environmentRecall.length + 1 := by
      rw [recallEq, List.length_append, List.length_singleton]
    have beforeCycle : cycle ≤ execution.application.native.clock := by
      rw [valid.1.clock, Nat.zero_add]
      apply cycle_le_before_offer owner cycle execution.environmentRecall.length
      omega
    have progress := Recovery.environmentStep_progress runtime leaks inputs execution next selected
      valid.1.valid.native moved
    have ready := ((progress.invariant.activated_iff event).mp (by
      rw [activated]; rfl)).1
    have origin := Recovery.environmentStep_activationOrigin runtime leaks inputs execution next
      selected valid.1.valid.native moved event entered activated ready.1
    have prior : execution.application.native.activatedAt event = some entered := by
      rcases origin with retained | fresh
      · exact retained
      · omega
    by_cases old : cycle * width + ownerSlot owner < execution.environmentRecall.length
    · obtain ⟨entry, member, chosen, stamp, wasReady, clock⟩ :=
        valid.2 event owner entered cycle acting prior older odd old
      refine ⟨entry, ?_, chosen, stamp, wasReady, clock⟩
      rw [recallEq]
      exact List.mem_append_left _ member
    · have current : execution.environmentRecall.length = cycle * width + ownerSlot owner := by
        omega
      have chosen : selected = command execution.environmentRecall.length
          (execution.observeEnvironment app) := (PMF.mem_support_pure_iff _ _).mp supported
      rw [current, owner_command cycle owner _ odd] at chosen
      refine ⟨⟨execution.observeEnvironment app, selected⟩, ?_, chosen, prior, ?_, ?_⟩
      · rw [recallEq]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      · exact (execution.application.native.publicView_eventReady event).mpr
          ((valid.1.valid.native.activated_iff event).mp (by rw [prior]; rfl)).1
      · change execution.application.native.clock = cycle
        rw [valid.1.clock, current, Nat.zero_add]
        exact (cursor_arithmetic cycle (ownerSlot owner) (ownerSlot_bounds owner)).1

theorem opportunity :
    Recovery.Opportunity runtime leaks initial horizon scheduler (fun _ => 3) := by
  intro control trace event owner entered acting ready activated elapsed
  have invariant : app.ServiceInvariant scheduler (fun execution =>
      ∃ inputs, ClockAligned inputs 0 execution ∧ RecordedOffers execution) := {
    respond := by
      intro execution who action valid
      obtain ⟨inputs, valid⟩ := valid
      exact ⟨inputs, (recorded_offers_invariant inputs).respond execution who action valid⟩
    environment := by
      intro execution next selected valid supported moved
      obtain ⟨inputs, valid⟩ := valid
      exact ⟨inputs, (recorded_offers_invariant inputs).environment execution next selected
        valid supported moved⟩ }
  have state := invariant.history initial horizon (by
    intro state initialized
    rw [initial, PMF.support_map] at initialized
    obtain ⟨native, initialized, rfl⟩ := initialized
    rw [Vegas.initialLaw, serviceInitialLaw, PMF.support_map] at initialized
    obtain ⟨input, _, rfl⟩ := initialized
    refine ⟨fixture.eventInputs input, ?_, ?_⟩
    · exact ⟨RecoveryState.Invariant.initial _, by
        simp [ReactiveApplication.Execution.initial, State.initial]⟩
    · intro event owner entered cycle _ _ _ _ impossible
      change _ < 0 at impossible
      omega) trace
  obtain ⟨inputs, aligned, offers⟩ := state
  have divided : control.execution.application.native.clock =
      control.execution.environmentRecall.length / width := by
    simpa only [Nat.zero_add] using aligned.clock
  let cycle := if (entered + 1) % 2 = 1 then entered + 1 else entered + 2
  have odd : cycle % 2 = 1 := by dsimp [cycle]; split_ifs <;> omega
  have older : entered < cycle := by dsimp [cycle]; split_ifs <;> omega
  have beforeClock : cycle < control.execution.application.native.clock := by
    change entered + 3 < control.execution.application.native.clock at elapsed
    dsimp [cycle]
    split_ifs <;> omega
  have earlier : cycle * width + ownerSlot owner < control.execution.environmentRecall.length := by
    have slotBound := ownerSlot_bounds owner
    have mulBound := Nat.mul_le_mul_right width (Nat.succ_le_of_lt beforeClock)
    change (cycle + 1) * width ≤ control.execution.application.native.clock * width at mulBound
    have cursorBound := Nat.div_mul_le_self control.execution.environmentRecall.length width
    rw [← divided] at cursorBound
    have rightBound : cycle * width + ownerSlot owner < (cycle + 1) * width := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    omega
  obtain ⟨entry, member, chosen, stamp, wasReady, _⟩ :=
    offers event owner entered cycle acting activated older odd earlier
  refine ⟨RecoveryProjection.environmentEntry runtime leaks entry, ?_, ?_, stamp, wasReady⟩
  · exact List.mem_map.mpr ⟨entry, member, rfl⟩
  · change RecoveryProjection.command runtime leaks entry.command = .activate owner
    rw [chosen]
    rfl

end Vegas.Examples.OddsEvensRecoveryService
