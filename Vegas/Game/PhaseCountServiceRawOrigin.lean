/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCountServicePhase

/-! # Original RAW labels at actual own-service SEND origins -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode

section RawOrigin

variable
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (phaseApplication runtime leaks).PlayerEntry → (phaseApplication runtime
      leaks).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent (serviceGraph setup mode) → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
  (horizon : Nat) (tapes : PhaseSeedAddress (serviceGraph setup mode) → Fin horizon → Bool × Bool)
  (plan : RuntimePhasePlan (serviceGraph setup mode)) (ordered : (serviceGraph setup
      mode).RevealRelaxedOrdered)
  (inputs : PMF (serviceGraph setup mode).Inputs)
  {LocalSeed RestSeed : Type}
  (seedLaw : PMF (RestSeed × (PhaseSeedAddress (serviceGraph setup mode) → LocalSeed)))
  (family : (RestSeed × (PhaseSeedAddress (serviceGraph setup mode) → LocalSeed)) →
      (phaseApplication runtime leaks).Scheduler)
  (calendar : PhaseService.PrivateActivationCalendar runtime leaks bounds plan inputs horizon
    seedLaw family)
  (privateSuccess : PhaseService.PrivateBindingSuccess runtime leaks bounds plan inputs horizon
    seedLaw family)
  (capacity : horizon ≤ bounds.candidateCount)
  (catalogue : ∀ owner event payload (_binding : (serviceGraph setup mode).outputLayout event =
      .binding owner payload),
    ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)

local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "Q" => phaseCountServiceTapePolicy setup mode runtime leaks bounds values choose
  failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
  slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes


/-- The actual initialized trace discharges the native invariant and ordinal budget. -/
theorem phaseCountServiceTapePolicy_local_member_at
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (owner : Player) (coordinate : PhaseSeedAddress graph) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout coordinate.1.event = .binding owner payload) :
    Q owner (control.execution.recall owner) (control.execution.observe app owner) =
      PhaseCount.bindingServiceTapeMember runtime leaks bounds (Q owner) owner coordinate.1 payload
        (fun past view => (values owner coordinate.1.event payload binding past view).map
          PublicationResult.success)
        (choose owner coordinate.1) failure timing firstNonnegative firstBounded timingNonnegative
        timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
        horizon (tapes coordinate) (control.execution.recall owner)
          (control.execution.observe app owner) := by
  have raw := (menu).toRawTrace initial horizon scheduler trace
  obtain ⟨input, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    raw
  have budget := (phaseApplication_seedBudget runtime leaks).history _ horizon scheduler
    (fun state member => by
      obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ member
      exact PhaseRuntimeState.initial_seedBudget plan draw) raw
  exact phaseCountServiceTapePolicy_local_member setup mode runtime leaks bounds values choose
    failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
    slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes coordinate owner
    payload binding control.execution valid budget

include ordered calendar capacity catalogue in
/-- Two genuine first SEND choices read the SAME original ordinal and RAW
flag, even if their hidden domain laws and absolute readiness clocks differ.
This uses the complete private calendar, not post-RAW success privacy. -/
theorem phaseCountServiceTapePolicy_first_send_raw_eq
    (firstSeeds secondSeeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (firstSupport : firstSeeds ∈ seedLaw.support) (secondSupport : secondSeeds ∈ seedLaw.support)
    (owner : Player) (coordinate : PhaseSeedAddress graph) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout coordinate.1.event = .binding owner payload)
    (first second : (app).Control)
    (firstTrace : ((menu).protocol initial horizon (family firstSeeds)).Trace (some first))
    (secondTrace : ((menu).protocol initial horizon (family secondSeeds)).Trace (some second))
    (firstActive : first.actor = some owner) (secondActive : second.actor = some owner)
    (firstRequest : first.execution.application.SeedRequest owner coordinate.1)
    (secondRequest : second.execution.application.SeedRequest owner coordinate.1)
    (sameSeed : firstSeeds.2 coordinate = secondSeeds.2 coordinate)
    (firstUnsent : ∀ message ∈ (app).outputs (first.execution.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate.1)
    (secondUnsent : ∀ message ∈ (app).outputs (second.execution.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate.1)
    (firstConsistent : (Q owner).Consistent (first.execution.recall owner))
    (secondConsistent : (Q owner).Consistent (second.execution.recall owner))
    (firstAction secondAction : (app).Action)
    (firstChosen : firstAction ∈ (Q owner (first.execution.recall owner)
      (first.execution.observe app owner)).support)
    (secondChosen : secondAction ∈ (Q owner (second.execution.recall owner)
      (second.execution.observe app owner)).support)
    (firstSends : firstAction.transmission.isSome = true)
    (secondSends : secondAction.transmission.isSome = true) :
    let firstIndex := PhaseCount.bindingServiceOrdinal_lt_horizon runtime leaks initial horizon
      (family firstSeeds) first ((menu).toRawTrace initial horizon (family firstSeeds) firstTrace)
        owner firstActive coordinate.1
    let secondIndex := PhaseCount.bindingServiceOrdinal_lt_horizon runtime leaks initial horizon
      (family secondSeeds) second
        ((menu).toRawTrace initial horizon (family secondSeeds) secondTrace)
        owner secondActive coordinate.1
    (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (first.execution.recall owner)).length =
      (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
        (second.execution.recall owner)).length ∧
    (tapes coordinate ⟨_, firstIndex⟩).1 = (tapes coordinate ⟨_, secondIndex⟩).1 := by
  intro firstIndex secondIndex
  have firstLocal := phaseCountServiceTapePolicy_local_consistent setup mode runtime leaks bounds
    values choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
    slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes plan
    inputs (family firstSeeds) first firstTrace coordinate owner payload binding firstConsistent
  have secondLocal := phaseCountServiceTapePolicy_local_consistent setup mode runtime leaks bounds
    values choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
    slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes plan
    inputs (family secondSeeds) second secondTrace coordinate owner payload binding
    secondConsistent
  rw [phaseCountServiceTapePolicy_local_member_at setup mode runtime leaks bounds values choose
    failure timing firstNonnegative
    firstBounded timingNonnegative timingBounded slotWeight slotNonnegative slotBounded rawWeight
    rawNonnegative rawBounded horizon tapes plan inputs (family firstSeeds) first firstTrace owner
    coordinate payload binding] at firstChosen
  rw [phaseCountServiceTapePolicy_local_member_at setup mode runtime leaks bounds values choose
    failure timing firstNonnegative
    firstBounded timingNonnegative timingBounded slotWeight slotNonnegative slotBounded rawWeight
    rawNonnegative rawBounded horizon tapes plan inputs (family secondSeeds) second secondTrace
    owner coordinate payload binding] at secondChosen
  have ordinal := PhaseCount.bindingServiceTapeMember_send_index_eq runtime leaks bounds plan
    ordered inputs horizon (Q owner) seedLaw family calendar firstSeeds secondSeeds firstSupport
    secondSupport owner coordinate payload _ _ (choose owner coordinate.1) failure timing
    firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
    slotBounded rawWeight rawNonnegative rawBounded capacity (tapes coordinate) first second
    firstTrace secondTrace firstActive secondActive binding firstRequest secondRequest sameSeed
    firstUnsent secondUnsent (catalogue owner coordinate.1.event payload binding) firstLocal
    secondLocal firstAction secondAction firstChosen secondChosen firstSends secondSends
  refine ⟨ordinal, ?_⟩
  have same : (⟨_, firstIndex⟩ : Fin horizon) = ⟨_, secondIndex⟩ := Fin.ext ordinal
  exact congrArg (fun index => (tapes coordinate index).1) same

end RawOrigin

end Vegas
