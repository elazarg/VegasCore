/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingServiceTapeHistory
import Vegas.Pending.PhasePrivateService
import Vegas.Pending.PhaseAttemptCheckpoint
import Vegas.Pending.PhaseBindingResponseWitness
import Interaction.ReactiveRecordedResponse

/-! # Actual earlier waits under one original counted service tape -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "menu" => onePacketMenu runtime leaks bounds

include ordered in
/-- Every earlier requested response in a genuinely unsent physical history is
WAIT. Its fixed local tape therefore prescribes WAIT at that exact original
ordinal. The proof recovers the actual callback and its supported response. -/
theorem bindingServiceTapeMember_recorded_wait
    (outside : (app).Policy)
    (owner : Player) (coordinate : CommitAttemptEvent graph) (payload : L.Ty)
    (values : List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (choose : List Nat → Bool) (failure timing : ℝ)
    (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
    (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (capacity : horizon ≤ bounds.candidateCount) (tape : Fin horizon → Bool × Bool)
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (output : graph.outputLayout coordinate.event = .binding owner payload)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall owner),
      event? message.payload ≠ some coordinate)
    (catalogue : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (consistent : (bindingServiceTapeMember runtime leaks bounds outside owner coordinate
      payload values
      choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
        slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
          horizon tape).Consistent
          (control.execution.recall owner))
    (earlier : List (app).PlayerEntry) (entry : (app).PlayerEntry)
    (later : List (app).PlayerEntry)
    (recalled : control.execution.recall owner = earlier ++ entry :: later)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate) :
    ∃ inside :
      (PhaseSeedScheduler.ownerWord runtime leaks coordinate owner earlier).length < horizon,
      bindingServiceCoinSends
        (PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner earlier entry.beforeView)
        choose (tape ⟨_, inside⟩) = false := by
  classical
  obtain ⟨before, prior, isPrefix, active, pastEq, viewed, offered⟩ :=
    (menu).recorded_response_at initial horizon scheduler control trace owner earlier entry later
      recalled
  have priorRaw := (menu).toRawTrace initial horizon scheduler prior
  have raw := (menu).toRawTrace initial horizon scheduler trace
  have priorActive : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨before.remaining, some owner, before.execution⟩) := by
    simpa only [← active] using prior
  obtain ⟨input, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    priorRaw
  have request : before.execution.application.SeedRequest owner coordinate := by
    rw [viewed] at requested
    exact (PhaseRuntimeState.requests_publicView _ valid owner coordinate).mp requested
  have coordinateEq : coordinate = ⟨before.execution.application.attempt, coordinate.event⟩ := by
    cases coordinate with
    | mk attempt event =>
        exact congrArg (fun tag : CommitAttemptId =>
          (⟨tag, event⟩ : CommitAttemptEvent graph)) request.1
  have priorUnsent : ∀ message ∈ (app).outputs (before.execution.recall owner),
      event? message.payload ≠ some coordinate := by
    intro message found
    apply unsent message
    rw [recalled, ReactiveApplication.outputs, List.filterMap_append]
    exact List.mem_append_left _ (pastEq ▸ found)
  have entryMember : entry ∈ control.execution.recall owner := by
    rw [recalled]
    exact List.mem_append_right _ List.mem_cons_self
  have silent : entry.action.transmission = none := by
    cases sent : entry.action.transmission with
    | none => rfl
    | some material =>
        have actionEq : entry.action = ⟨some material⟩ := by
          cases actionAt : entry.action with
          | mk transmission =>
              simpa only [actionAt] using congrArg ReactiveApplication.Action.mk sent
        rw [← pastEq, actionEq] at offered
        obtain ⟨serial, preparation, evidence, shape, _bounded, _fresh⟩ :=
          onePacket_binding_shape runtime leaks bounds plan ordered inputs horizon scheduler
            before.remaining owner before.execution priorActive coordinate.event payload output
              (coordinateEq ▸ request) material offered
        obtain ⟨message, emitted, _sender, packet⟩ := recalled_submission_emitted runtime leaks
          initial horizon scheduler raw owner entry entryMember material sent
        have actualTag := phase_recalled_emission_attempt runtime leaks initial horizon scheduler
          raw owner entry entryMember message emitted
        have tag : message.payload.attempt = coordinate.attempt := by
          rw [viewed] at actualTag
          exact actualTag.trans request.1.symm
        have impossible := unsent message (List.mem_filterMap.mpr ⟨entry, entryMember, emitted⟩)
        apply False.elim
        apply impossible
        simp only [event?, packet, shape, Payload.event?, Option.map_some, tag]
  have supported : entry.action ∈ (bindingServiceTapeMember runtime leaks bounds outside owner
    coordinate
      payload values choose failure timing firstNonnegative firstBounded timingNonnegative
        timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
          horizon tape earlier entry.beforeView).support := by
    have faithful := recalled ▸ consistent
    rw [← List.singleton_append, ← List.append_assoc] at faithful
    have sampled := (ReactiveApplication.Policy.consistent_snoc_iff _ earlier entry).mp
      (ReactiveApplication.Policy.Consistent.of_append faithful)
    exact sampled.2
  have law := bindingServiceTapeMember_transmission_of_history (outside := outside) runtime
    leaks bounds owner
    coordinate.event payload values choose failure timing firstNonnegative firstBounded
      timingNonnegative timingBounded slotWeight slotNonnegative slotBounded rawWeight
        rawNonnegative rawBounded plan inputs horizon scheduler capacity tape before prior active
          output (coordinateEq ▸ request) (coordinateEq ▸ priorUnsent) catalogue
  dsimp only at law
  simp only [← coordinateEq, pastEq, ← viewed] at law
  have inside : (PhaseSeedScheduler.ownerWord runtime leaks coordinate owner earlier).length <
      horizon := by
    rw [← pastEq]
    exact bindingServiceOrdinal_lt_horizon runtime leaks initial horizon scheduler before priorRaw
      owner active coordinate
  refine ⟨inside, ?_⟩
  have mapped : entry.action.transmission.isSome ∈ (PMF.pure
      (bindingServiceCoinSends
        (PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner earlier entry.beforeView)
          choose (tape ⟨_, inside⟩))).support := by
    rw [← law]
    exact (PMF.mem_support_map_iff ..).mpr ⟨entry.action, supported, rfl⟩
  have equality := (PMF.mem_support_pure_iff ..).mp mapped
  simpa only [silent, Option.isSome_none] using equality.symm


private theorem filter_index_split {α : Type} (selected : α → Bool) (past : List α)
    (index : Nat) (inside : index < (past.filter selected).length) :
    ∃ earlier entry later, past = earlier ++ entry :: later ∧ selected entry = true ∧
      (earlier.filter selected).length = index := by
  induction past generalizing index with
  | nil => simp only [List.filter_nil, List.length_nil, Nat.not_lt_zero] at inside
  | cons entry rest ih =>
      by_cases chosen : selected entry = true
      · rw [List.filter_cons_of_pos chosen, List.length_cons] at inside
        cases index with
        | zero => exact ⟨[], entry, rest, rfl, chosen, rfl⟩
        | succ index =>
            obtain ⟨earlier, found, later, split, requested, lengthEq⟩ := ih index (by omega)
            refine ⟨entry :: earlier, found, later, ?_, requested, ?_⟩
            · rw [split]; rfl
            · simp only [List.filter_cons_of_pos chosen, List.length_cons, lengthEq]
      · rw [List.filter_cons_of_neg chosen] at inside
        obtain ⟨earlier, found, later, split, requested, lengthEq⟩ := ih index inside
        refine ⟨entry :: earlier, found, later, ?_, requested, ?_⟩
        · rw [split]; rfl
        · simpa only [List.filter_cons_of_neg chosen] using lengthEq

include ordered in
/-- A callback that precedes another unsent episode's current ordinal must
still be a WAIT under their common original tape. The earlier occurrence in
the second history is recovered from actual recall, not supplied as a pairing. -/
theorem bindingServiceTapeMember_wait_before_unsent
    (outside : (app).Policy)
    {LocalSeed RestSeed : Type}
    (seedLaw : PMF (RestSeed × (PhaseSeedAddress graph → LocalSeed)))
    (family : (RestSeed × (PhaseSeedAddress graph → LocalSeed)) → (app).Scheduler)
    (calendar : PhaseService.PrivateActivationCalendar runtime leaks bounds plan inputs horizon
      seedLaw family)
    (firstSeeds secondSeeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (firstSupport : firstSeeds ∈ seedLaw.support) (secondSupport : secondSeeds ∈ seedLaw.support)
    (owner : Player) (coordinate : PhaseSeedAddress graph) (payload : L.Ty)
    (values : List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (choose : List Nat → Bool) (failure timing : ℝ)
    (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
    (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (capacity : horizon ≤ bounds.candidateCount) (tape : Fin horizon → Bool × Bool)
    (first second : (app).Control)
    (firstTrace : ((menu).protocol initial horizon (family firstSeeds)).Trace (some first))
    (secondTrace : ((menu).protocol initial horizon (family secondSeeds)).Trace (some second))
    (firstActive : first.actor = some owner)
    (output : graph.outputLayout coordinate.1.event = .binding owner payload)
    (firstRequest : first.execution.application.SeedRequest owner coordinate.1)
    (sameSeed : firstSeeds.2 coordinate = secondSeeds.2 coordinate)
    (firstUnsent : ∀ message ∈ (app).outputs (first.execution.recall owner),
      event? message.payload ≠ some coordinate.1)
    (secondUnsent : ∀ message ∈ (app).outputs (second.execution.recall owner),
      event? message.payload ≠ some coordinate.1)
    (catalogue : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (consistent : (bindingServiceTapeMember runtime leaks bounds outside owner coordinate.1
      payload values
      choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
        slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
          horizon tape).Consistent
          (second.execution.recall owner))
    (earlierIndex : (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (first.execution.recall owner)).length < (PhaseSeedScheduler.ownerWord runtime leaks
        coordinate.1 owner (second.execution.recall owner)).length) :
    ∃ inside : (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
        (first.execution.recall owner)).length < horizon,
      bindingServiceCoinSends (PhaseSeedScheduler.serviceClocks runtime leaks coordinate.1 owner
        (first.execution.recall owner) (first.execution.observe app owner)) choose
          (tape ⟨_, inside⟩) = false := by
  classical
  let selected := fun entry : (app).PlayerEntry =>
    decide (PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate.1)
  have filterLength : (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (second.execution.recall owner)).length =
        ((second.execution.recall owner).filter selected).length := by
    simp only [PhaseSeedScheduler.ownerWord, List.length_map, selected]
  obtain ⟨earlier, entry, later, recalled, requestedBool, lengthEq⟩ := filter_index_split selected
    (second.execution.recall owner) _ (filterLength ▸ earlierIndex)
  have requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate.1 :=
    of_decide_eq_true requestedBool
  obtain ⟨insideEarlier, waits⟩ := bindingServiceTapeMember_recorded_wait (outside := outside)
    runtime leaks bounds plan
    ordered inputs horizon (family secondSeeds) owner coordinate.1 payload values choose failure
      timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
        slotNonnegative slotBounded rawWeight rawNonnegative rawBounded capacity tape second
          secondTrace output secondUnsent catalogue consistent earlier entry later recalled
            requested
  obtain ⟨before, prior, _prefix, active, pastEq, viewed, _offered⟩ :=
    (menu).recorded_response_at initial horizon (family secondSeeds) second secondTrace owner
      earlier entry later recalled
  have raw := (menu).toRawTrace initial horizon (family secondSeeds) prior
  obtain ⟨input, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    (family secondSeeds) raw
  have request : before.execution.application.SeedRequest owner coordinate.1 := by
    rw [viewed] at requested
    exact (PhaseRuntimeState.requests_publicView _ valid owner coordinate.1).mp requested
  have priorUnsent : ∀ message ∈ (app).outputs (before.execution.recall owner),
      event? message.payload ≠ some coordinate.1 := by
    intro message found
    apply secondUnsent message
    rw [recalled, ReactiveApplication.outputs, List.filterMap_append]
    exact List.mem_append_left _ (pastEq ▸ found)
  have sameIndex : (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (first.execution.recall owner)).length =
        (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner earlier).length := by
    simpa only [PhaseSeedScheduler.ownerWord, List.length_map, selected] using lengthEq.symm
  have firstActiveTrace : ((menu).protocol initial horizon (family firstSeeds)).Trace
      (some ⟨first.remaining, some owner, first.execution⟩) := by
    simpa only [← firstActive] using firstTrace
  have beforeActiveTrace : ((menu).protocol initial horizon (family secondSeeds)).Trace
      (some ⟨before.remaining, some owner, before.execution⟩) := by
    simpa only [← active] using prior
  have sameClocks := PhaseService.PrivateActivationCalendar.unsentPrivacy runtime leaks bounds
    plan inputs horizon seedLaw family calendar firstSeeds firstSupport secondSeeds secondSupport
      first.remaining before.remaining owner first.execution before.execution firstActiveTrace
        beforeActiveTrace coordinate firstRequest request sameSeed (pastEq ▸ sameIndex)
          firstUnsent priorUnsent
  simp only [pastEq, ← viewed] at sameClocks
  have inside : (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (first.execution.recall owner)).length < horizon := sameIndex ▸ insideEarlier
  refine ⟨inside, ?_⟩
  have sameSlot : (⟨(PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (first.execution.recall owner)).length, inside⟩ : Fin horizon) = ⟨_, insideEarlier⟩ :=
    Fin.ext sameIndex
  rw [sameClocks, sameSlot]
  exact waits


/-- A supported actual SEND reads a true bit at its original unused ordinal.
This is a physical emission consequence of the normalized hidden encoders. -/
theorem bindingServiceTapeMember_send_decision
    (outside : (app).Policy)
    (owner : Player) (coordinate : CommitAttemptEvent graph) (payload : L.Ty)
    (values : List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (choose : List Nat → Bool) (failure timing : ℝ)
    (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
    (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (capacity : horizon ≤ bounds.candidateCount) (tape : Fin horizon → Bool × Bool)
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (active : control.actor = some owner)
    (output : graph.outputLayout coordinate.event = .binding owner payload)
    (request : control.execution.application.SeedRequest owner coordinate)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall owner),
      event? message.payload ≠ some coordinate)
    (catalogue : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (action : (app).Action)
    (supported : action ∈ (bindingServiceTapeMember runtime leaks bounds outside owner
      coordinate payload
      values choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
        slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tape
          (control.execution.recall owner) (control.execution.observe app owner)).support)
    (sends : action.transmission.isSome = true) :
    ∃ inside : (PhaseSeedScheduler.ownerWord runtime leaks coordinate owner
        (control.execution.recall owner)).length < horizon,
      bindingServiceCoinSends (PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner
        (control.execution.recall owner) (control.execution.observe app owner)) choose
          (tape ⟨_, inside⟩) = true := by
  have coordinateEq : coordinate = ⟨control.execution.application.attempt, coordinate.event⟩ := by
    cases coordinate with
    | mk attempt event =>
        exact congrArg (fun tag : CommitAttemptId =>
          (⟨tag, event⟩ : CommitAttemptEvent graph)) request.1
  have law := bindingServiceTapeMember_transmission_of_history (outside := outside) runtime
    leaks bounds owner
    coordinate.event payload values choose failure timing firstNonnegative firstBounded
      timingNonnegative timingBounded slotWeight slotNonnegative slotBounded rawWeight
        rawNonnegative rawBounded plan inputs horizon scheduler capacity tape control trace active
          output (coordinateEq ▸ request) (coordinateEq ▸ unsent) catalogue
  dsimp only at law
  simp only [← coordinateEq] at law
  have inside := bindingServiceOrdinal_lt_horizon runtime leaks initial horizon scheduler control
    ((menu).toRawTrace initial horizon scheduler trace) owner active coordinate
  refine ⟨inside, ?_⟩
  have mapped : action.transmission.isSome ∈ (PMF.pure
      (bindingServiceCoinSends (PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner
        (control.execution.recall owner) (control.execution.observe app owner)) choose
          (tape ⟨_, inside⟩))).support := by
    rw [← law]
    exact (PMF.mem_support_map_iff ..).mpr ⟨action, supported, rfl⟩
  simpa only [sends] using ((PMF.mem_support_pure_iff ..).mp mapped).symm


include ordered in
/-- Two actual first SEND callbacks under one original local tape have the
same ordinal. Arbitrary private source laws, encoders and foreign interleavings
may differ. A later unsent episode cannot skip an earlier tape SEND. -/
theorem bindingServiceTapeMember_send_index_eq
    (outside : (app).Policy)
    {LocalSeed RestSeed : Type}
    (seedLaw : PMF (RestSeed × (PhaseSeedAddress graph → LocalSeed)))
    (family : (RestSeed × (PhaseSeedAddress graph → LocalSeed)) → (app).Scheduler)
    (calendar : PhaseService.PrivateActivationCalendar runtime leaks bounds plan inputs horizon
      seedLaw family)
    (firstSeeds secondSeeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (firstSupport : firstSeeds ∈ seedLaw.support) (secondSupport : secondSeeds ∈ seedLaw.support)
    (owner : Player) (coordinate : PhaseSeedAddress graph) (payload : L.Ty)
    (firstValues secondValues : List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (choose : List Nat → Bool) (failure timing : ℝ)
    (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
    (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (capacity : horizon ≤ bounds.candidateCount) (tape : Fin horizon → Bool × Bool)
    (first second : (app).Control)
    (firstTrace : ((menu).protocol initial horizon (family firstSeeds)).Trace (some first))
    (secondTrace : ((menu).protocol initial horizon (family secondSeeds)).Trace (some second))
    (firstActive : first.actor = some owner) (secondActive : second.actor = some owner)
    (output : graph.outputLayout coordinate.1.event = .binding owner payload)
    (firstRequest : first.execution.application.SeedRequest owner coordinate.1)
    (secondRequest : second.execution.application.SeedRequest owner coordinate.1)
    (sameSeed : firstSeeds.2 coordinate = secondSeeds.2 coordinate)
    (firstUnsent : ∀ message ∈ (app).outputs (first.execution.recall owner),
      event? message.payload ≠ some coordinate.1)
    (secondUnsent : ∀ message ∈ (app).outputs (second.execution.recall owner),
      event? message.payload ≠ some coordinate.1)
    (catalogue : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (firstConsistent : (bindingServiceTapeMember runtime leaks bounds outside owner coordinate.1
      payload
      firstValues choose failure timing firstNonnegative firstBounded timingNonnegative
        timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
          horizon tape).Consistent (first.execution.recall owner))
    (secondConsistent : (bindingServiceTapeMember runtime leaks bounds outside owner
      coordinate.1 payload
      secondValues choose failure timing firstNonnegative firstBounded timingNonnegative
        timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
          horizon tape).Consistent (second.execution.recall owner))
    (firstAction secondAction : (app).Action)
    (firstChosen : firstAction ∈ (bindingServiceTapeMember runtime leaks bounds outside owner
      coordinate.1
      payload firstValues choose failure timing firstNonnegative firstBounded timingNonnegative
        timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
          horizon tape (first.execution.recall owner) (first.execution.observe app owner)).support)
    (secondChosen : secondAction ∈ (bindingServiceTapeMember runtime leaks bounds outside owner
      coordinate.1
      payload secondValues choose failure timing firstNonnegative firstBounded timingNonnegative
        timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
          horizon tape (second.execution.recall owner)
            (second.execution.observe app owner)).support)
    (firstSends : firstAction.transmission.isSome = true)
    (secondSends : secondAction.transmission.isSome = true) :
    (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (first.execution.recall owner)).length = (PhaseSeedScheduler.ownerWord runtime leaks
        coordinate.1 owner (second.execution.recall owner)).length := by
  obtain ⟨firstInside, firstTrue⟩ := bindingServiceTapeMember_send_decision (outside := outside)
    runtime leaks bounds
    plan inputs horizon (family firstSeeds) owner coordinate.1 payload firstValues choose failure
      timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
        slotNonnegative slotBounded rawWeight rawNonnegative rawBounded capacity tape first
          firstTrace firstActive output firstRequest firstUnsent catalogue firstAction firstChosen
            firstSends
  obtain ⟨secondInside, secondTrue⟩ := bindingServiceTapeMember_send_decision (outside :=
    outside) runtime leaks bounds
    plan inputs horizon (family secondSeeds) owner coordinate.1 payload secondValues choose failure
      timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
        slotNonnegative slotBounded rawWeight rawNonnegative rawBounded capacity tape second
          secondTrace secondActive output secondRequest secondUnsent catalogue secondAction
            secondChosen secondSends
  have notEarlier : ¬ (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (first.execution.recall owner)).length < (PhaseSeedScheduler.ownerWord runtime leaks
        coordinate.1 owner (second.execution.recall owner)).length := by
    intro smaller
    obtain ⟨_inside, waits⟩ := bindingServiceTapeMember_wait_before_unsent (outside := outside)
      runtime leaks bounds
      plan ordered inputs horizon seedLaw family calendar firstSeeds secondSeeds firstSupport
        secondSupport owner coordinate payload secondValues choose failure timing firstNonnegative
          firstBounded timingNonnegative timingBounded slotWeight slotNonnegative slotBounded
            rawWeight rawNonnegative rawBounded capacity tape first second firstTrace secondTrace
              firstActive output firstRequest sameSeed firstUnsent secondUnsent catalogue
                secondConsistent smaller
    rw [firstTrue] at waits
    cases waits
  have notLater : ¬ (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (second.execution.recall owner)).length < (PhaseSeedScheduler.ownerWord runtime leaks
        coordinate.1 owner (first.execution.recall owner)).length := by
    intro smaller
    obtain ⟨_inside, waits⟩ := bindingServiceTapeMember_wait_before_unsent (outside := outside)
      runtime leaks bounds
      plan ordered inputs horizon seedLaw family calendar secondSeeds firstSeeds secondSupport
        firstSupport owner coordinate payload firstValues choose failure timing firstNonnegative
          firstBounded timingNonnegative timingBounded slotWeight slotNonnegative slotBounded
            rawWeight rawNonnegative rawBounded capacity tape second first secondTrace firstTrace
              secondActive output secondRequest sameSeed.symm secondUnsent firstUnsent catalogue
                firstConsistent smaller
    rw [secondTrue] at waits
    cases waits
  omega


include ordered in
/-- A resolved episode with no packet exhausts the same potential calendar.
Thus no other episode with the same original seed and tape can send. The
missing later callbacks are ruled out by calendar exhaustion, not by an
assumed matching callback or an assumed independent success bit. -/
theorem bindingServiceTapeMember_silent_of_resolved_unsent
    (outside : (app).Policy)
    {LocalSeed RestSeed : Type}
    (seedLaw : PMF (RestSeed × (PhaseSeedAddress graph → LocalSeed)))
    (family : (RestSeed × (PhaseSeedAddress graph → LocalSeed)) → (app).Scheduler)
    (privateCalendar : PhaseService.PrivateActivationCalendar runtime leaks bounds plan inputs
      horizon seedLaw family)
    (firstSeeds secondSeeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (firstSupport : firstSeeds ∈ seedLaw.support) (secondSupport : secondSeeds ∈ seedLaw.support)
    (owner : Player) (coordinate : PhaseSeedAddress graph) (payload : L.Ty)
    (firstValues secondValues : List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (choose : List Nat → Bool) (failure timing : ℝ)
    (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
    (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (capacity : horizon ≤ bounds.candidateCount) (tape : Fin horizon → Bool × Bool)
    (first : (app).Control) (secondRemaining : Nat) (second : (app).Execution)
    (firstTrace : ((menu).protocol initial horizon (family firstSeeds)).Trace (some first))
    (secondTrace : ((menu).protocol initial horizon (family secondSeeds)).Trace
      (some ⟨secondRemaining, none, second⟩))
    (firstActive : first.actor = some owner)
    (output : graph.outputLayout coordinate.1.event = .binding owner payload)
    (firstRequest : first.execution.application.SeedRequest owner coordinate.1)
    (secondReady : ∃ (before : (app).Control)
      (beforeTrace : ((menu).protocol initial horizon (family secondSeeds)).Trace (some before)),
      GameTheory.Protocol.ExecutionProtocol.TracePrefix beforeTrace secondTrace ∧
        before.execution.application.SeedRequest owner coordinate.1)
    (secondResolved : coordinate.1.Resolved second.application)
    (sameSeed : firstSeeds.2 coordinate = secondSeeds.2 coordinate)
    (firstUnsent : ∀ message ∈ (app).outputs (first.execution.recall owner),
      event? message.payload ≠ some coordinate.1)
    (secondUnsent : ∀ message ∈ (app).outputs (second.recall owner),
      event? message.payload ≠ some coordinate.1)
    (catalogue : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (secondConsistent : (bindingServiceTapeMember runtime leaks bounds outside owner
      coordinate.1 payload
      secondValues choose failure timing firstNonnegative firstBounded timingNonnegative
        timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
          horizon tape).Consistent (second.recall owner))
    (action : (app).Action)
    (chosen : action ∈ (bindingServiceTapeMember runtime leaks bounds outside owner coordinate.1
      payload
      firstValues choose failure timing firstNonnegative firstBounded timingNonnegative
        timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
          horizon tape (first.execution.recall owner)
            (first.execution.observe app owner)).support) :
    action.transmission = none := by
  classical
  have noEmissions := PhaseService.bindingEmissionClocks_eq_nil_of_unsent runtime leaks bounds
    plan inputs horizon (family secondSeeds) secondRemaining second secondTrace coordinate.1 owner
      secondUnsent
  obtain ⟨calendar, callbacks, exhausted⟩ := privateCalendar
  have firstActiveTrace : ((menu).protocol initial horizon (family firstSeeds)).Trace
      (some ⟨first.remaining, some owner, first.execution⟩) := by
    simpa only [← firstActive] using firstTrace
  have initialPrefix := callbacks firstSeeds firstSupport first.remaining owner first.execution
    firstActiveTrace coordinate firstRequest firstUnsent
  have allClocks := exhausted secondSeeds secondSupport ⟨secondRemaining, none, second⟩
    secondTrace coordinate owner secondReady secondResolved noEmissions
  have earlierIndex : (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (first.execution.recall owner)).length < (PhaseSeedScheduler.ownerWord runtime leaks
        coordinate.1 owner (second.recall owner)).length := by
    have bound := initialPrefix.length_le
    rw [sameSeed, ← allClocks] at bound
    simpa only [PhaseSeedScheduler.serviceClocks, PhaseSeedScheduler.informationInput,
      List.length_append, List.length_map, List.length_singleton, Nat.add_one_le_iff] using bound
  cases sent : action.transmission with
  | none => rfl
  | some material =>
      have sends : action.transmission.isSome = true := by simp only [sent, Option.isSome_some]
      obtain ⟨_inside, positive⟩ := bindingServiceTapeMember_send_decision (outside := outside)
        runtime leaks bounds
        plan inputs horizon (family firstSeeds) owner coordinate.1 payload firstValues choose
          failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
            slotNonnegative slotBounded rawWeight rawNonnegative rawBounded capacity tape first
              firstTrace firstActive output firstRequest firstUnsent catalogue action chosen sends
      obtain ⟨_inside, waits⟩ := bindingServiceTapeMember_wait_before_unsent (outside :=
        outside) runtime leaks bounds
        plan ordered inputs horizon seedLaw family ⟨calendar, callbacks, exhausted⟩ firstSeeds
          secondSeeds firstSupport secondSupport owner coordinate payload secondValues choose
            failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
              slotNonnegative slotBounded rawWeight rawNonnegative rawBounded capacity tape first
                ⟨secondRemaining, none, second⟩ firstTrace secondTrace firstActive output
                  firstRequest sameSeed firstUnsent secondUnsent catalogue secondConsistent
                    earlierIndex
      rw [positive] at waits
      cases waits

end Vegas.EventGraphRuntime.PhaseCount
