/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCountServicePolicy

/-! # One original local tape for every counted binding occurrence -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode


/-- All binding occurrences use their original coordinate and ordinal tape.
Openings and malformed fallback inputs keep the same complete normalized
prescription. No table is refreshed when another event becomes ready. -/
def phaseCountServiceTapePolicy
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (app).PlayerEntry → (app).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent graph → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (horizon : Nat)
    (tapes : PhaseSeedAddress (serviceGraph setup mode) → Fin horizon → Bool × Bool)
    (who : Player) : (app).Policy :=
  let outside := phaseCountServicePolicy setup mode runtime leaks bounds values choose failure
    timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
    slotBounded rawWeight rawNonnegative rawBounded
  phasePolicyDispatch setup mode runtime leaks
    (fun owner _event _payload _binding => outside owner)
    (fun owner event payload binding past view =>
      if bounded : view.application.2.attempt.phase < (serviceGraph setup mode).order.eventCount ∧
          view.application.2.attempt.generation ≤ Fintype.card Player then
        PhaseCount.bindingServiceTapeMember runtime leaks bounds (outside owner) owner
          ⟨view.application.2.attempt, event⟩ payload
          (fun past view => (values owner event payload binding past view).map
            PublicationResult.success)
          (choose owner ⟨view.application.2.attempt, event⟩) failure timing firstNonnegative
          firstBounded timingNonnegative timingBounded slotWeight slotNonnegative slotBounded
          rawWeight rawNonnegative rawBounded horizon
          (tapes ⟨⟨view.application.2.attempt, event⟩, bounded⟩) past view
      else outside owner past view)
    who

/-- Every immutable tape member is supported by the same original counted
menu, including arbitrary old own histories and inputs outside the tape. -/
theorem phaseCountServiceTapePolicy_covered
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (app).PlayerEntry → (app).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent graph → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (horizon : Nat)
    (tapes : PhaseSeedAddress (serviceGraph setup mode) → Fin horizon → Bool × Bool)
    (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (response : (app).Action)
    (supported : response ∈ (phaseCountServiceTapePolicy setup mode runtime leaks bounds values
        choose failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon tapes who
      past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  apply phasePolicyDispatch_covered setup mode runtime leaks bounds _ _ _ _ who past view
    response supported
  · intro owner event payload binding before observed action offered
    exact phaseCountServicePolicy_covered setup mode runtime leaks bounds values choose failure
        timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded owner before observed action offered
  · intro owner event payload binding before observed action offered
    split at offered
    · exact PhaseCount.bindingServiceTapeMember_covered runtime leaks bounds
        (phaseCountServicePolicy setup mode runtime leaks bounds values choose failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded owner) owner
        (fun before observed action offered => phaseCountServicePolicy_covered setup mode runtime
            leaks bounds values choose failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded
          owner before observed action offered)
        _ payload _ _ failure timing firstNonnegative firstBounded timingNonnegative
        timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative
        rawBounded horizon _ before observed action offered
    · exact phaseCountServicePolicy_covered setup mode runtime leaks bounds values choose failure
        timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
        slotNonnegative slotBounded rawWeight rawNonnegative rawBounded owner before observed
        action offered

/-- A genuine request selects its original bounded tape address. The physical
generation budget supplies that address; it is not a strategy premise. -/
theorem phaseCountServiceTapePolicy_binding
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (app).PlayerEntry → (app).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent graph → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (horizon : Nat)
    (tapes : PhaseSeedAddress (serviceGraph setup mode) → Fin horizon → Bool × Bool)
    (execution : (app).Execution) {inputs} (valid : execution.application.Invariant inputs)
    (budget : execution.application.SeedBudget)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩) :
    phaseCountServiceTapePolicy setup mode runtime leaks bounds values choose failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon tapes who (execution.recall who)
        (execution.observe app who) =
      PhaseCount.bindingServiceTapeMember runtime leaks bounds (phaseCountServicePolicy setup mode
          runtime leaks bounds values choose failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded who) who
        ⟨execution.application.attempt, event⟩ payload
        (fun past view => (values who event payload binding past view).map
          PublicationResult.success)
        (choose who ⟨execution.application.attempt, event⟩) failure timing firstNonnegative
        firstBounded timingNonnegative timingBounded slotWeight slotNonnegative slotBounded
        rawWeight rawNonnegative rawBounded horizon (tapes (request.coordinate budget))
        (execution.recall who) (execution.observe app who) := by
  unfold phaseCountServiceTapePolicy
  rw [phasePolicyDispatch_binding setup mode runtime leaks _ _ execution valid who event payload
    binding request]
  have bounded : (execution.observe app who).application.2.attempt.phase <
        (serviceGraph setup mode).order.eventCount ∧
      (execution.observe app who).application.2.attempt.generation ≤ Fintype.card Player :=
    request.bounded budget
  simp only [dite_eq_left bounded]
  rfl

/-- At every genuine physical input, the complete table policy agrees with
its one-address splice. The outside continuation retains all other original
address tapes, including repeated events of the same owner. -/
theorem phaseCountServiceTapePolicy_local_member
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (app).PlayerEntry → (app).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent graph → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (horizon : Nat)
    (tapes : PhaseSeedAddress (serviceGraph setup mode) → Fin horizon → Bool × Bool)
    (coordinate : PhaseSeedAddress graph) (who : Player) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout coordinate.1.event = .binding who payload)
    (execution : (app).Execution) {inputs} (valid : execution.application.Invariant inputs)
    (budget : execution.application.SeedBudget) :
    phaseCountServiceTapePolicy setup mode runtime leaks bounds values choose failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon tapes who
        (execution.recall who) (execution.observe app who) =
      (PhaseCount.bindingServiceTapeMember runtime leaks bounds
      (phaseCountServiceTapePolicy setup mode runtime leaks bounds values choose failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon tapes who) who coordinate.1 payload
      (fun past view => (values who coordinate.1.event payload binding past view).map
        PublicationResult.success)
      (choose who coordinate.1) failure timing firstNonnegative firstBounded timingNonnegative
      timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
      horizon (tapes coordinate))
        (execution.recall who) (execution.observe app who) := by
  classical
  by_cases requested : PhaseRuntimeState.requests (execution.observe app who).application.2 who
      coordinate.1
  · have request := (PhaseRuntimeState.requests_publicView _ valid who coordinate.1).mp requested
    have coordinateEq : coordinate.1 =
        ⟨execution.application.attempt, coordinate.1.event⟩ := by
      exact congrArg (fun attempt => (⟨attempt, coordinate.1.event⟩ : CommitAttemptEvent graph))
        request.1
    have currentRequest : execution.application.SeedRequest who
        ⟨execution.application.attempt, coordinate.1.event⟩ := coordinateEq ▸ request
    have actual := phaseCountServiceTapePolicy_binding setup mode runtime leaks bounds values
        choose failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon tapes execution valid budget who
      coordinate.1.event payload binding currentRequest
    have addressEq : currentRequest.coordinate budget = coordinate := by
      apply Subtype.ext
      exact coordinateEq.symm
    rw [addressEq] at actual
    rw [actual]
    unfold PhaseCount.bindingServiceTapeMember
    simp only [← coordinateEq, requested, ↓reduceIte]
  · simp only [PhaseCount.bindingServiceTapeMember, requested, ↓reduceIte]

end Vegas
