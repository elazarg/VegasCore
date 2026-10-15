/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedClockAccounting
import Vegas.Pending.PhaseSeedActivationMemory

/-! # Finite service receipts for actual all-event calendar rounds -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

inductive ServiceMark (graph : Vegas.EventGraph Player L) where
  | queried (activation : Bool) (tick : Nat) (coordinate : PhaseSeedAddress graph)
  | advanced (tick : Nat)
  | sampled (attempt : CommitAttemptId)

abbrev ServiceTicket (graph : Vegas.EventGraph Player L) :=
  (Bool × Nat × PhaseSeedAddress graph) ⊕ (Nat ⊕ CommitAttemptId)

namespace ServiceMark

def ticket : ServiceMark graph → ServiceTicket graph
  | .queried activation tick coordinate => .inl (activation, tick, coordinate)
  | .advanced tick => .inr (.inl tick)
  | .sampled attempt => .inr (.inr attempt)

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Receipt validity retains physical clocks, original activation anchors and
full callback provenance. It is a proof predicate, never scheduler memory. -/
def Valid
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed)
    (mark : ServiceMark graph) (execution : (app).Execution) : Prop :=
  match mark with
  | .queried false tick coordinate =>
      tick ≤ execution.application.current.native.clock ∧
        (tick, coordinate) ∈ replayClosed runtime leaks priority rest execution.environmentRecall
  | .queried true tick coordinate =>
      ∃ entered, ClosedCoordinateBound runtime tick entered coordinate.1 execution.application ∧
        ∃ owner entry, entry ∈ execution.environmentRecall ∧ entry.command = .activate owner ∧
          PhaseRuntimeState.requests entry.beforeView.application owner coordinate.1 ∧
          PhaseSeedScheduler.elapsed runtime leaks coordinate.1 entry.beforeView = tick - entered
  | .advanced tick => tick < execution.application.current.native.clock
  | .sampled attempt =>
      attempt.phase ≤ graph.order.eventCount ∧ attempt.generation ≤ Fintype.card Player ∧
        attempt.generation ≤ execution.application.attempt.generation ∧
        attempt.phase ≤ execution.application.attempt.phase ∧
        attempt ≠ execution.application.attempt

private theorem retired_of_progress (attempt before after : CommitAttemptId)
    (generation : attempt.generation ≤ before.generation)
    (phase : attempt.phase ≤ before.phase) (different : attempt ≠ before)
    (progress : before.generation ≤ after.generation ∧ before.phase ≤ after.phase) :
    attempt ≠ after := by
  intro same
  apply different
  have phaseEq : attempt.phase = before.phase := by
    have := congrArg CommitAttemptId.phase same
    omega
  have generationEq : attempt.generation = before.generation := by
    have := congrArg CommitAttemptId.generation same
    omega
  cases attempt
  cases before
  exact congrArg₂ CommitAttemptId.mk phaseEq generationEq

private theorem valid_mono
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed)
    (mark : ServiceMark graph) (before after : (app).Execution)
    (clock : before.application.current.native.clock ≤ after.application.current.native.clock)
    (namespaceProgress : before.application.attempt.generation ≤
      after.application.attempt.generation ∧
      before.application.attempt.phase ≤ after.application.attempt.phase)
    (closed : replayClosed runtime leaks priority rest before.environmentRecall ⊆
      replayClosed runtime leaks priority rest after.environmentRecall)
    (recorded : ∀ entry ∈ before.environmentRecall, entry ∈ after.environmentRecall)
    (bounds : ∀ tick entered coordinate,
      ClosedCoordinateBound runtime tick entered coordinate before.application →
        ClosedCoordinateBound runtime tick entered coordinate after.application)
    (valid : mark.Valid runtime leaks priority rest before) :
    mark.Valid runtime leaks priority rest after := by
  cases mark with
  | queried activation tick coordinate =>
      cases activation with
      | false => exact ⟨valid.1.trans clock, closed valid.2⟩
      | true =>
          obtain ⟨entered, bound, owner, entry, member, activated, request, elapsed⟩ := valid
          exact ⟨entered, bounds tick entered coordinate.1 bound, owner, entry,
            recorded entry member, activated, request, elapsed⟩
  | advanced tick => exact valid.trans_le clock
  | sampled attempt =>
      exact ⟨valid.1, valid.2.1, valid.2.2.1.trans namespaceProgress.1,
        valid.2.2.2.1.trans namespaceProgress.2,
        retired_of_progress attempt _ _ valid.2.2.1 valid.2.2.2.1 valid.2.2.2.2 namespaceProgress⟩

/-- Arbitrary player choices preserve every previously issued service receipt. -/
theorem valid_respond
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed)
    {inputs : graph.Inputs} (mark : ServiceMark graph)
    (execution : (app).Execution) (who : Player) (action : (app).Action)
    (invariant : execution.application.Invariant inputs) (ordered : execution.application.Ordered)
    (valid : mark.Valid runtime leaks priority rest execution) :
    mark.Valid runtime leaks priority rest (execution.respond app who action) := by
  apply valid_mono runtime leaks priority rest mark execution _
  · exact (respond_clock runtime leaks execution invariant who action).ge
  · exact (phaseApplication_namespace_progress runtime leaks).respond execution who action ordered
  · rw [(app).respond_environmentRecall]
  · intro entry member
    rwa [(app).respond_environmentRecall]
  · intro tick entered coordinate bound
    exact ClosedCoordinateBound.respond runtime leaks execution who action invariant ordered bound
  · exact valid

/-- Supported actual environment moves preserve all prior receipts, including
callbacks and closure records belonging to retired attempts. -/
theorem valid_environment
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed)
    {inputs : graph.Inputs} (mark : ServiceMark graph)
    (execution next : (app).Execution) (command : (app).Command)
    (invariant : execution.application.Invariant inputs) (ordered : execution.application.Ordered)
    (reached : next ∈ (execution.environmentStep app command).support)
    (valid : mark.Valid runtime leaks priority rest execution) :
    mark.Valid runtime leaks priority rest next := by
  apply valid_mono runtime leaks priority rest mark execution next
  · exact (phaseApplication_clock_monotone runtime leaks).environmentStep execution next command
      reached
  · exact (phaseApplication_namespace_progress runtime leaks).environmentStep execution next command
      reached ordered
  · rw [(app).environmentStep_environmentRecall execution next command reached]
    exact replayClosed_append_mono runtime leaks priority rest _ _
  · intro entry member
    rw [(app).environmentStep_environmentRecall execution next command reached]
    exact List.mem_append_left _ member
  · intro tick entered coordinate bound
    exact ClosedCoordinateBound.environmentStep runtime leaks execution next command invariant
      ordered reached bound
  · exact valid

open Classical in
/-- A fixed finite ticket reservoir covers clocks, both query replies per tick,
and every potential sample namespace. -/
def tickets : Finset (ServiceTicket graph) :=
  ((Finset.univ ×ˢ Finset.range (Fintype.card (ClockTicket runtime) + 1) ×ˢ Finset.univ).image
    Sum.inl) ∪
  ((Finset.range (Fintype.card (ClockTicket runtime))).image (Sum.inr ∘ Sum.inl)) ∪
  (((Finset.range (graph.order.eventCount + 1)) ×ˢ
    Finset.range (Fintype.card Player + 1)).image fun pair =>
      Sum.inr (Sum.inr (CommitAttemptId.mk pair.1 pair.2)))

/-- Actual clock accounting supplies every finite-carrier bound; no bound on
arbitrary hidden initial states or on a scheduler-provided trace is assumed. -/
theorem ticket_mem
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    {delay : graph.EventId → Nat}
    {seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay)}
    {inputs : graph.Inputs} {execution : (app).Execution}
    (accounting : ClockAccounting runtime leaks delay priority seeds inputs 0 execution)
    (mark : ServiceMark graph) (valid : mark.Valid runtime leaks priority seeds.1 execution) :
    mark.ticket ∈ tickets runtime := by
  classical
  have clock := ClockAccounting.clock_le runtime leaks delay priority seeds accounting
  simp only [Nat.zero_add] at clock
  cases mark with
  | queried activation tick coordinate =>
      have tickLe : tick ≤ execution.application.current.native.clock := by
        cases activation with
        | false => exact valid.1
        | true => obtain ⟨entered, bound, _⟩ := valid; exact bound.clock
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨(activation, tick, coordinate), ?_, rfl⟩
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and, and_true]
      omega
  | advanced tick =>
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨tick, Finset.mem_range.mpr (valid.trans_le clock), rfl⟩
  | sampled attempt =>
      have phaseBound := valid.1
      have generationBound := valid.2.1
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(attempt.phase, attempt.generation), ?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
          Finset.mem_range.mpr (by omega)⟩
      · rfl

theorem length_le_tickets
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    {delay : graph.EventId → Nat}
    {seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay)}
    {inputs : graph.Inputs} {execution : (app).Execution}
    (accounting : ClockAccounting runtime leaks delay priority seeds inputs 0 execution)
    (marks : List (ServiceMark graph)) (unique : (marks.map ticket).Nodup)
    (valid : ∀ mark ∈ marks, mark.Valid runtime leaks priority seeds.1 execution) :
    marks.length ≤ (tickets runtime).card := by
  classical
  have subset : (marks.map ticket).toFinset ⊆ tickets runtime := by
    intro selected member
    obtain ⟨mark, markMember, same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    rw [← same]
    exact ticket_mem runtime leaks priority accounting mark (valid mark markMember)
  have bounded := Finset.card_le_card subset
  simpa only [List.toFinset_card_of_nodup unique, List.length_map] using bounded

end ServiceMark
end Vegas.EventGraphRuntime.PhaseSeedCalendar
