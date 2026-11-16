module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.PeriodicServiceClock
public import Vegas.Pending.ReactiveServiceOpportunity

@[expose] public section

/-! # Owner opportunities in every raw periodic-service history -/

noncomputable section

namespace Vegas.EventGraphRuntime.PeriodicService

open EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

variable {graph : EventGraph Player L} {roster : Bool ≃ Player}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {inputLaw : PMF graph.Inputs}

local notation "app" => (reactiveApplication (timeouts graph)) leaks
local notation "deadlines" => timeouts graph
local notation "startLaw" => initial graph leaks inputLaw
local notation "schedule" => scheduler graph roster leaks
local notation "selectedCommand" => command graph roster leaks

def ownerSlot (owner : Player) : Nat := if roster.symm owner then packetBudget + 1 else
  packetBudget

omit [DecidableEq Player] in
theorem ownerSlot_bounds (owner : Player) : ownerSlot (roster := roster) owner < width := by
  unfold ownerSlot
  split_ifs <;> decide

theorem owner_command (cycle : Nat) (owner : Player) (view : (app).EnvironmentView)
    (odd : cycle % 2 = 1) :
    selectedCommand (cycle * width + ownerSlot (roster := roster) owner) view = .activate owner
      := by
  obtain ⟨bit, rfl⟩ := roster.surjective owner
  cases bit with
  | false => simpa only [ownerSlot, Equiv.symm_apply_apply, Bool.false_eq_true, ↓reduceIte]
      using first_activation cycle view odd
  | true => simpa only [ownerSlot, Equiv.symm_apply_apply, ↓reduceIte]
      using second_activation cycle view odd

def RecordedOffers (execution : (app).Execution) : Prop :=
  ∀ event owner entered cycle, graph.actor? event = some owner →
    execution.application.activatedAt event = some entered →
    entered < cycle → cycle % 2 = 1 →
    cycle * width + ownerSlot (roster := roster) owner < execution.environmentRecall.length →
    ∃ entry ∈ execution.environmentRecall, entry.command = .activate owner ∧
      entry.beforeView.application.activatedAt event = some entered ∧
      entry.beforeView.application.EventReady event ∧
      entry.beforeView.application.clock = cycle

omit [DecidableEq Player] in
private theorem cycle_le_before_offer (owner : Player) (cycle cursor : Nat)
    (earlier : cycle * width + ownerSlot (roster := roster) owner < cursor + 1) : cycle ≤ cursor
      / width := by
  have positive : 0 < width := by decide
  apply (Nat.le_div_iff_mul_le positive).mpr
  omega

theorem recorded_offers_invariant (inputs : graph.Inputs) :
    (app).ServiceInvariant schedule (fun execution =>
      ClockAligned inputs 0 execution ∧ RecordedOffers (roster := roster) execution) where
  respond execution who action valid := by
    refine ⟨(clock_aligned_invariant (roster := roster) inputs 0).respond execution who action
      valid.1, ?_⟩
    intro event owner entered cycle acting activated older odd earlier
    rw [(app).respond_environmentRecall] at earlier ⊢
    have beforeCycle : cycle ≤ execution.application.clock := by
      rw [valid.1.clock, Nat.zero_add]
      exact cycle_le_before_offer owner cycle execution.environmentRecall.length (by omega)
    have progress := reactive_respond_progress deadlines leaks inputs execution who action
      valid.1.valid
    have ready := ((progress.invariant.activated_iff event).mp (by
      rw [activated]; rfl)).1
    have origin := reactive_respond_activationOrigin deadlines leaks execution who action
      event entered activated ready.1
    rcases origin with retained | fresh
    · exact valid.2 event owner entered cycle acting retained older odd earlier
    · omega
  environment execution next selected valid supported moved := by
    refine ⟨(clock_aligned_invariant (roster := roster) inputs 0).environment execution next
      selected valid.1
      supported moved, ?_⟩
    intro event owner entered cycle acting activated older odd earlier
    have recallEq := (app).environmentStep_environmentRecall execution next selected moved
    have lengthEq : next.environmentRecall.length = execution.environmentRecall.length + 1 := by
      rw [recallEq, List.length_append, List.length_singleton]
    have beforeCycle : cycle ≤ execution.application.clock := by
      rw [valid.1.clock, Nat.zero_add]
      apply cycle_le_before_offer owner cycle execution.environmentRecall.length
      omega
    have progress := reactive_environment_progress deadlines leaks inputs execution next selected
      valid.1.valid moved
    have ready := ((progress.invariant.activated_iff event).mp (by
      rw [activated]; rfl)).1
    have origin := reactive_environmentStep_activationOrigin deadlines leaks execution next
      selected moved event entered activated ready.1
    have prior : execution.application.activatedAt event = some entered := by
      rcases origin with retained | fresh
      · exact retained
      · omega
    by_cases old : cycle * width + ownerSlot (roster := roster) owner <
      execution.environmentRecall.length
    · obtain ⟨entry, member, chosen, stamp, wasReady, clock⟩ :=
        valid.2 event owner entered cycle acting prior older odd old
      refine ⟨entry, ?_, chosen, stamp, wasReady, clock⟩
      rw [recallEq]
      exact List.mem_append_left _ member
    · have current : execution.environmentRecall.length = cycle * width + ownerSlot (roster :=
      roster) owner := by
        omega
      have chosen : selected = selectedCommand execution.environmentRecall.length
          (execution.observeEnvironment app) := (PMF.mem_support_pure_iff _ _).mp supported
      rw [current, owner_command cycle owner _ odd] at chosen
      refine ⟨⟨execution.observeEnvironment app, selected⟩, ?_, chosen, prior, ?_, ?_⟩
      · rw [recallEq]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      · exact (execution.application.publicView_eventReady event).mpr
          ((valid.1.valid.activated_iff event).mp (by rw [prior]; rfl)).1
      · change execution.application.clock = cycle
        rw [valid.1.clock, current, Nat.zero_add]
        exact (cursor_arithmetic cycle (ownerSlot (roster := roster) owner) (ownerSlot_bounds
          owner)).1

theorem opportunity :
    Opportunity deadlines leaks startLaw horizon schedule (fun _ => 3) := by
  intro control trace event owner entered acting ready activated elapsed
  have invariant : (app).ServiceInvariant schedule (fun execution =>
      ∃ inputs, ClockAligned inputs 0 execution ∧ RecordedOffers (roster := roster) execution) := {
    respond := by
      intro execution who action valid
      obtain ⟨inputs, valid⟩ := valid
      exact ⟨inputs, (recorded_offers_invariant (roster := roster) inputs).respond execution who
        action valid⟩
    environment := by
      intro execution next selected valid supported moved
      obtain ⟨inputs, valid⟩ := valid
      exact ⟨inputs, (recorded_offers_invariant (roster := roster) inputs).environment execution
        next selected
        valid supported moved⟩ }
  have state := invariant.history startLaw horizon (by
    intro state initialized
    rw [initial, PMF.support_map] at initialized
    obtain ⟨input, _, rfl⟩ := initialized
    refine ⟨input, ?_, ?_⟩
    · exact ⟨State.initial_invariant _, by
        simp [ReactiveApplication.Execution.initial, State.initial]⟩
    · intro event owner entered cycle _ _ _ _ impossible
      change _ < 0 at impossible
      omega) trace
  obtain ⟨inputs, aligned, offers⟩ := state
  have divided : control.execution.application.clock =
      control.execution.environmentRecall.length / width := by
    simpa only [Nat.zero_add] using aligned.clock
  let cycle := if (entered + 1) % 2 = 1 then entered + 1 else entered + 2
  have odd : cycle % 2 = 1 := by dsimp [cycle]; split_ifs <;> omega
  have older : entered < cycle := by dsimp [cycle]; split_ifs <;> omega
  have beforeClock : cycle < control.execution.application.clock := by
    change entered + 3 < control.execution.application.clock at elapsed
    dsimp [cycle]
    split_ifs <;> omega
  have earlier : cycle * width + ownerSlot (roster := roster) owner <
    control.execution.environmentRecall.length := by
    have slotBound := ownerSlot_bounds (roster := roster) owner
    have mulBound := Nat.mul_le_mul_right width (Nat.succ_le_of_lt beforeClock)
    change (cycle + 1) * width ≤ control.execution.application.clock * width at mulBound
    have cursorBound := Nat.div_mul_le_self control.execution.environmentRecall.length width
    rw [← divided] at cursorBound
    have rightBound : cycle * width + ownerSlot (roster := roster) owner < (cycle + 1) * width
      := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    omega
  obtain ⟨entry, member, chosen, stamp, wasReady, _⟩ :=
    offers event owner entered cycle acting activated older odd earlier
  exact ⟨entry, member, chosen, stamp, wasReady⟩



end Vegas.EventGraphRuntime.PeriodicService
