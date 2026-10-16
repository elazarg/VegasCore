/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourcePolicy
import Vegas.Pending.PhaseBindingServiceEpisode

/-! # Normalized counted own-service prescriptions at all physical callbacks -/

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

/-- This normalized prescription uses the omission rate only at the first
binding callback. Its domain draw is independent of fresh-slot encoding and
the native SEND tier. Openings retain a positive WAIT tremble; the source
accepted-failure tremble is not a native encoder tier. -/
def phaseCountServicePolicy
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (app).PlayerEntry → (app).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent graph → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (who : Player) : (app).Policy :=
  phasePolicyDispatch setup mode runtime leaks
    (fun owner event payload binding past view =>
      mix rawWeight rawNonnegative rawBounded
        (PhaseCount.countedSendLaw runtime leaks bounds owner past view)
        (PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding
          (fun _ _ => mix timing timingNonnegative timingBounded
            (PMF.pure false) (PMF.pure true)) past view))
    (fun owner event payload binding past view =>
      PhaseCount.bindingServiceReference runtime leaks bounds owner
        ⟨view.application.2.attempt, event⟩ payload
        (fun past view => (values owner event payload binding past view).map
          PublicationResult.success)
        (choose owner ⟨view.application.2.attempt, event⟩)
        failure timing firstNonnegative firstBounded timingNonnegative timingBounded
        slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded past view)
    who

/-- Every branch is normalized and supported by the original counted menu,
including malformed inputs and inputs outside the selected phase. -/
theorem phaseCountServicePolicy_covered
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (app).PlayerEntry → (app).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent graph → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (response : (app).Action)
    (supported : response ∈ (phaseCountServicePolicy setup mode runtime leaks bounds values choose
      failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
        slotNonnegative slotBounded rawWeight rawNonnegative rawBounded who past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  apply phasePolicyDispatch_covered setup mode runtime leaks bounds _ _ _ _ who past view
    response supported
  · intro owner event payload binding before observed action offered
    rcases support_mix_subset _ _ _ _ _ offered with raw | opening
    · exact PhaseCount.countedSendLaw_covered runtime leaks bounds owner before observed action raw
    · exact PhaseCount.phaseOpeningPolicy_covered runtime leaks bounds owner event payload binding
        _ before observed action opening
  · intro owner event payload binding before observed action offered
    exact PhaseCount.bindingServiceReference_covered runtime leaks bounds owner
      ⟨observed.application.2.attempt, event⟩ payload _ _ failure timing firstNonnegative
      firstBounded timingNonnegative timingBounded slotWeight slotNonnegative slotBounded rawWeight
      rawNonnegative rawBounded before observed action offered

/-- A genuine binding request selects the normalized own-service law with
the actual full attempt address. The domain law is mapped only to success. -/
theorem phaseCountServicePolicy_binding
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (app).PlayerEntry → (app).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent graph → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (execution : (app).Execution) {inputs} (valid : execution.application.Invariant inputs)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩) :
    phaseCountServicePolicy setup mode runtime leaks bounds values choose failure timing
        firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
        slotBounded rawWeight rawNonnegative rawBounded who (execution.recall who)
        (execution.observe app who) =
      PhaseCount.bindingServiceReference runtime leaks bounds who
        ⟨execution.application.attempt, event⟩ payload
        (fun past view =>
          (values who event payload binding past view).map PublicationResult.success)
        (choose who ⟨execution.application.attempt, event⟩)
        failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
        slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
        (execution.recall who) (execution.observe app who) := by
  exact phasePolicyDispatch_binding setup mode runtime leaks _ _ execution valid who event payload
    binding request

/-- An original ordinal tape implements the actual dispatched binding law.
The outside policy remains the entire prescription, so earlier callbacks at
other events of this same owner are retained. The current tape coordinate is
unread after the entire own recall, rather than refreshed at this request. -/
theorem phaseCountServicePolicy_binding_tape_realization
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (app).PlayerEntry → (app).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent graph → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (execution : (app).Execution) {inputs} (valid : execution.application.Invariant inputs)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (horizon : Nat)
    (inside : (PhaseSeedScheduler.ownerWord runtime leaks
      ⟨execution.application.attempt, event⟩ who (execution.recall who)).length < horizon) :
    let prescribed := phaseCountServicePolicy setup mode runtime leaks bounds values choose
      failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
        slotNonnegative slotBounded rawWeight rawNonnegative rawBounded who
    let coordinate : CommitAttemptEvent graph := ⟨execution.application.attempt, event⟩
    let typed := fun past view =>
      (values who event payload binding past view).map PublicationResult.success
    let original := (independentProduct (fun index : Fin horizon =>
      PhaseCount.bindingServiceCoinLaw failure timing firstNonnegative firstBounded
        timingNonnegative timingBounded rawWeight rawNonnegative rawBounded index.val)).bind
          (fun tape => (PMF.pure ()).map (Prod.mk tape))
    let members := fun memory : (Fin horizon → Bool × Bool) × Unit =>
      PhaseCount.bindingServiceTapeMember runtime leaks bounds prescribed who coordinate payload
        typed (choose who coordinate) failure timing firstNonnegative firstBounded
        timingNonnegative timingBounded slotWeight slotNonnegative slotBounded rawWeight
        rawNonnegative rawBounded horizon memory.1
    ((app).policyMixture original members).policy (execution.recall who)
        (execution.observe app who) =
      prescribed (execution.recall who) (execution.observe app who) := by
  dsimp only
  have requested := (execution.application.requests_publicView valid who
    ⟨execution.application.attempt, event⟩).mpr request
  change PhaseRuntimeState.requests (execution.observe app who).application.2 who
    ⟨execution.application.attempt, event⟩ at requested
  obtain ⟨remainder, _posterior, realized⟩ := PhaseCount.bindingServiceTapeMember_realization
    (runtime := runtime) (leaks := leaks) (bounds := bounds) (owner := who)
    (coordinate := ⟨execution.application.attempt, event⟩) (payload := payload)
    (choose := choose who ⟨execution.application.attempt, event⟩)
    (failure := failure) (timing := timing) (firstNonnegative := firstNonnegative)
    (firstBounded := firstBounded) (timingNonnegative := timingNonnegative)
    (timingBounded := timingBounded) (slotWeight := slotWeight)
    (slotNonnegative := slotNonnegative) (slotBounded := slotBounded)
    (rawWeight := rawWeight) (rawNonnegative := rawNonnegative) (rawBounded := rawBounded)
    (horizon := horizon) (restLaw := PMF.pure ())
    (fun _ : Unit => phaseCountServicePolicy setup mode runtime leaks bounds values choose failure
      timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
      slotNonnegative slotBounded rawWeight rawNonnegative rawBounded who)
    (fun (_ : Unit) past view =>
      (values who event payload binding past view).map PublicationResult.success)
    (execution.recall who) (execution.observe app who) requested inside
  rw [PMF.bind_const] at realized
  exact realized.trans (phaseCountServicePolicy_binding setup mode runtime leaks bounds values
    choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
    slotNonnegative slotBounded rawWeight rawNonnegative rawBounded execution valid who event
    payload binding request).symm

/-- A genuine opening keeps both the normalized native SEND encoder and the
disclosure WAIT tremble, rather than replacing the entire opening law by TRUE. -/
theorem phaseCountServicePolicy_opening
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (app).PlayerEntry → (app).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent graph → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (execution : (app).Execution) {inputs} (valid : execution.application.Invariant inputs)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding who payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) =
      .resolve who payload binding checks)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩) :
    phaseCountServicePolicy setup mode runtime leaks bounds values choose failure timing
        firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
        slotBounded rawWeight rawNonnegative rawBounded who (execution.recall who)
        (execution.observe app who) =
      mix rawWeight rawNonnegative rawBounded
        (PhaseCount.countedSendLaw runtime leaks bounds who (execution.recall who)
          (execution.observe app who))
        (PhaseCount.phaseOpeningPolicy runtime leaks bounds who event payload binding
          (fun _ _ => mix timing timingNonnegative timingBounded
            (PMF.pure false) (PMF.pure true)) (execution.recall who)
              (execution.observe app who)) := by
  exact phasePolicyDispatch_opening setup mode runtime leaks _ _ execution valid who event payload
    binding checks outputEq codeEq request

/-- Actual counted history removes both source and slot guards. Consequently
the full dispatched prescription's SEND/WAIT law reads only the event's local
clock word and the fixed first-omission, timing and native-tier rates. -/
theorem phaseCountServicePolicy_transmission_of_history
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (app).PlayerEntry → (app).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent graph → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (plan : RuntimePhasePlan graph) (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (capacity : horizon ≤ bounds.candidateCount)
    (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (catalogue : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    (phaseCountServicePolicy setup mode runtime leaks bounds values choose failure timing
        firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
        slotBounded rawWeight rawNonnegative rawBounded who (control.execution.recall who)
        (control.execution.observe app who)).map (fun response => response.transmission.isSome) =
      PhaseCount.bindingServiceEmissionLaw
        (PhaseSeedScheduler.serviceClocks runtime leaks
          ⟨control.execution.application.attempt, event⟩ who (control.execution.recall who)
            (control.execution.observe app who))
        (choose who ⟨control.execution.application.attempt, event⟩)
        failure timing firstNonnegative firstBounded timingNonnegative timingBounded
          rawWeight rawNonnegative rawBounded := by
  obtain ⟨original, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ _ _ trace)
  rw [phaseCountServicePolicy_binding setup mode runtime leaks bounds values choose failure timing
    firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
    slotBounded rawWeight rawNonnegative rawBounded control.execution valid who event payload
    binding request]
  exact PhaseCount.bindingServiceReference_transmission_of_history runtime leaks bounds who event
    payload _ _ failure timing firstNonnegative firstBounded timingNonnegative timingBounded
    slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
    (PhaseCount.onePacketMenu runtime leaks bounds) plan inputs horizon scheduler capacity control
    trace active binding request unsent catalogue

end Vegas
