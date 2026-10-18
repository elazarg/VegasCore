/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperFiber
import Vegas.Examples.CommitSeedSignallingOriginalReceipts
import Vegas.Pending.PhaseSeedEmissionUnique

/-! # A wrong-slot original Alice packet cannot be repaired by a clean continuation -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob)

/-- Only this owner's permission is used. Earlier and later foreign charged
packets do not enter the uniqueness argument for the owner's physical coordinate. -/
theorem own_permitted_original_emissions_one (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player) (clean : OwnPermitted owner execution) :
    (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
      execution.environmentRecall (execution.observeEnvironment app)).emissions.length ≤ 1 := by
  classical
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks rawMenu initial horizon
    (family seed) remaining execution trace
  have raw := rawMenu.toRawTrace initial horizon (family seed) trace
  let emissions := (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
    execution.environmentRecall (execution.observeEnvironment app)).emissions
  by_cases empty : emissions = []
  · rw [show (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
        execution.environmentRecall (execution.observeEnvironment app)).emissions = [] from empty]
    exact Nat.zero_le _
  · obtain ⟨selected, present⟩ := List.exists_mem_of_ne_nil _ empty
    have only (entry : Nat × Message Player (CommitAttemptPacket graph))
        (member : entry ∈ emissions) : entry.2 = selected.2 := by
      have first := PhaseSeedScheduler.localInput_emission_authentic runtime leaks execution
        (originalCoordinate owner) owner words clean.1.1 entry.1 entry.2 member
      have second := PhaseSeedScheduler.localInput_emission_authentic runtime leaks execution
        (originalCoordinate owner) owner words clean.1.1 selected.1 selected.2 present
      apply PhaseCount.Permits.eq_of_same_event
        ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 entry.2 first.1 first.2.1))
        ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 selected.2 second.1 second.2.1))
        first.1 second.1
      · intro left leftInput right rightInput same
        exact app.input_identifier_injective_history initial horizon (family seed)
          ⟨remaining, none, execution⟩ raw left right leftInput rightInput same
      · exact first.2.1.trans second.2.1.symm
      · simp only [PhaseCount.event?, first.2.2.2, second.2.2.2, Option.map_some,
          first.2.2.1, second.2.2.1]
    have unique := PhaseSeedScheduler.localInput_emissions_nodup runtime leaks execution
      (originalCoordinate owner) owner words clean.1
    change (emissions.map Prod.snd).Nodup at unique
    have mapped : emissions.map Prod.snd = List.replicate emissions.length selected.2 :=
      List.map_eq_replicate_iff.mpr only
    rw [mapped] at unique
    exact List.nodup_replicate.mp unique

private theorem singleton_emissions_same_time
    (emissions : List (Nat × Message Player (CommitAttemptPacket graph)))
    (one : emissions.length ≤ 1) (first second : Nat)
    (left right : Message Player (CommitAttemptPacket graph))
    (leftMember : (first, left) ∈ emissions) (rightMember : (second, right) ∈ emissions) :
    first = second := by
  cases emissions with
  | nil => exact (List.not_mem_nil leftMember).elim
  | cons head rest =>
      cases rest with
      | nil =>
          exact congrArg Prod.fst ((List.mem_singleton.mp leftMember).trans
            (List.mem_singleton.mp rightMember).symm)
      | cons next later =>
          simp only [List.length_cons] at one
          omega

/-- A real count-permitted packet sent by Alice at clock two cannot be
accepted with the late-three seed. All later foreign responses may be raw. -/
theorem alice_wrong_first_packet_unaccepted (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (bit : seedBits seed alice = true) (clean : OwnPermitted alice execution)
    (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall alice)
    (request : PhaseRuntimeState.requests entry.beforeView.application.2 alice
      (originalCoordinate alice))
    (clock : entry.beforeView.application.2.native.clock = 2)
    (message : Message Player (CommitAttemptPacket graph)) (emitted : entry.emitted = some message)
    (packet : PhaseSeedScheduler.ownPacket (originalCoordinate alice) alice message = true)
    (noEarly : ∀ snapshot, execution.environmentRecall[2]? = some snapshot →
      ∀ earlier ∈ snapshot.beforeView.network.inputs, earlier.sender ≠ alice) :
    ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate alice) alice execution := by
  classical
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks rawMenu initial horizon
    (family seed) remaining execution trace
  obtain ⟨before, prior, _kept, _acting, observed, _allowed, _later⟩ :=
    rawMenu.recorded_response_prefix initial horizon (family seed)
      ⟨remaining, none, execution⟩ trace alice entry recorded
  have valid := raw_native_valid (family seed) before
    (rawMenu.toRawTrace initial horizon (family seed) prior)
  have publicBefore : PhaseRuntimeState.requests before.execution.application.publicView alice
      (originalCoordinate alice) := by
    rw [observed] at request
    exact request
  have requested := (before.execution.application.requests_publicView valid alice
    (originalCoordinate alice)).mp publicBefore
  have timer := original_timer (family seed) before
    (rawMenu.toRawTrace initial horizon (family seed) prior) requested.1.symm aliceBinding
      (Or.inl rfl) requested.2.2.1.1
  have entryTimer : entry.beforeView.application.2.native.activatedAt aliceBinding = some 0 := by
    rw [observed]
    exact timer
  have first : (2, message) ∈
      (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate alice) alice
        execution.environmentRecall (execution.observeEnvironment app)).emissions := by
    rw [PhaseSeedScheduler.localInput_word, words alice (originalCoordinate alice)]
    apply List.mem_flatMap.mpr
    refine ⟨(2, [message]), ?_, ?_⟩
    · apply List.mem_map.mpr
      refine ⟨entry, List.mem_filter.mpr ⟨recorded, decide_eq_true request⟩, ?_⟩
      change (entry.beforeView.application.2.native.clock -
        (entry.beforeView.application.2.native.activatedAt aliceBinding).getD
          entry.beforeView.application.2.native.clock,
        entry.emitted.toList.filter (PhaseSeedScheduler.ownPacket
          (originalCoordinate alice) alice)) = (2, [message])
      rw [clock, entryTimer, Option.getD_some, Nat.sub_zero, emitted]
      simp only [Option.toList_some, List.filter_cons, packet, ite_true, List.filter_nil]
    · exact List.mem_map.mpr ⟨message, List.mem_singleton_self _, rfl⟩
  intro accepted
  obtain ⟨later, last⟩ := original_binding_accepted_late_of_empty_snapshot seed remaining execution
    trace alice noEarly accepted
  have seedBit : seed.2 (originalAddress alice) = true := bit
  rw [seedBit] at last
  have one := own_permitted_original_emissions_one seed remaining execution trace alice clean
  have impossible := singleton_emissions_same_time _ one 2 (lateClock alice true)
    message later first last
  change 2 = 3 at impossible
  omega

/-- At the actual final raw trace, a clean wrong-slot packet forces exclusion;
permanent original receipt provenance supplies the survivor implication. -/
theorem alice_wrong_first_packet_excluded (seed : Seeds) (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨0, none, execution⟩))
    (bit : seedBits seed alice = true) (clean : OwnPermitted alice execution)
    (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall alice)
    (request : PhaseRuntimeState.requests entry.beforeView.application.2 alice
      (originalCoordinate alice))
    (clock : entry.beforeView.application.2.native.clock = 2)
    (message : Message Player (CommitAttemptPacket graph)) (emitted : entry.emitted = some message)
    (packet : PhaseSeedScheduler.ownPacket (originalCoordinate alice) alice message = true)
    (noEarly : ∀ snapshot, execution.environmentRecall[2]? = some snapshot →
      ∀ earlier ∈ snapshot.beforeView.network.inputs, earlier.sender ≠ alice) :
    alice ∈ execution.application.current.excluded := by
  have unaccepted := alice_wrong_first_packet_unaccepted seed 0 execution trace bit clean entry
    recorded request clock message emitted packet noEarly
  by_contra survives
  have raw := rawMenu.toRawTrace initial horizon (family seed) trace
  have length := app.raw_trace_horizon initial horizon (family seed) raw
  change execution.environmentRecall.length + 0 = horizon at length
  have late : 22 ≤ execution.environmentRecall.length := by
    change execution.environmentRecall.length + 0 = 64 at length
    omega
  have closed := original_attempt_retired seed ⟨0, none, execution⟩ raw late
  have receipt := (survivor_original_receipt_or_open (family seed) ⟨0, none, execution⟩ raw
    alice survives).resolve_left closed
  exact unaccepted receipt

end Vegas.Examples.CommitSeedSignalling
