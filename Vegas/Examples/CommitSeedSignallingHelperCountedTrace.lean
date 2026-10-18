/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperPacketPermission
import Interaction.ReactiveAnchoredTrace
import Interaction.ReactiveRoundTrace

/-! # Counted representatives of the actual early helper information fiber -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup)

private theorem counted_trace_of_recorded_actions (current : app.Control)
    (trace : rawProtocol.Trace (some current))
    (permitted : ∀ owner earlier entry later,
      current.execution.recall owner = earlier ++ entry :: later →
      entry.action ∈ countedMenu.actions owner earlier entry.beforeView) :
    Nonempty (countedProtocol.Trace (some current)) := by
  classical
  let silent : Player → app.Policy := fun _ _ _ => PMF.pure ⟨none⟩
  let players := ReactiveApplication.anchoredPolicy current.execution silent
  have covered (owner : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
      (action : app.Action) (selected : action ∈ (players owner past view).support) :
      action ∈ countedMenu.actions owner past view := by
    change action ∈
      (ReactiveApplication.anchoredPolicy current.execution silent owner past view).support
      at selected
    unfold ReactiveApplication.anchoredPolicy at selected
    cases found : (current.execution.recall owner)[past.length]? with
    | none =>
        rw [found] at selected
        cases (PMF.mem_support_pure_iff _ _).mp selected
        exact PhaseCount.silence_onePacket runtime leaks bounds owner past view
    | some entry =>
        rw [found] at selected
        dsimp only at selected
        by_cases matched : past ++ [entry] <+: current.execution.recall owner ∧
            entry.beforeView = view
        · rw [ite_eq_left matched, PMF.mem_support_pure_iff] at selected
          subst action
          obtain ⟨later, joined⟩ := matched.1
          have recalled : current.execution.recall owner = past ++ entry :: later := by
            simpa only [List.append_assoc, List.singleton_append] using joined.symm
          rw [← matched.2]
          exact permitted owner past entry later recalled
        · rw [ite_eq_right matched] at selected
          cases (PMF.mem_support_pure_iff _ _).mp selected
          exact PhaseCount.silence_onePacket runtime leaks bounds owner past view
  have actual := ReactiveApplication.anchored_of_trace initial horizon scheduler current.execution
    silent (rawMenu.toRawTrace initial horizon scheduler trace) current rfl
      (fun _ => List.prefix_refl _)
  rcases current with ⟨remaining, actor, execution⟩
  obtain ⟨bounded, actual⟩ := actual
  cases actor with
  | none =>
      obtain ⟨counted⟩ := countedMenu.trace_roundsFrom initial horizon scheduler players covered
        (horizon - remaining) (by omega) execution actual
      have countEq : horizon - (horizon - remaining) = remaining := Nat.sub_sub_self bounded
      rw [countEq] at counted
      exact ⟨counted⟩
  | some owner =>
      obtain ⟨strict, before, reached, command, selected, acting, moved⟩ := actual
      change remaining < horizon at strict
      obtain ⟨prior⟩ := countedMenu.trace_roundsFrom initial horizon scheduler players covered
        (horizon - remaining - 1) (by omega) before reached
      have countEq : horizon - (horizon - remaining - 1) = remaining + 1 := by omega
      rw [countEq] at prior
      obtain ⟨after⟩ := countedMenu.trace_environment initial horizon scheduler remaining before
        execution command prior selected moved
      rw [acting] at after
      exact ⟨after⟩

private theorem original_early_clock_index (seed : Seeds) (current : app.Control)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt)
    (clock : current.execution.application.current.native.clock ≤ 3) :
    current.execution.environmentRecall.length ≤ 12 := by
  have indexed := original_clock_index seed current
    (rawMenu.toRawTrace initial horizon (family seed) trace) original
  rw [indexed] at clock
  by_contra late
  obtain ⟨extra, length⟩ : ∃ extra, current.execution.environmentRecall.length = extra + 13 :=
    ⟨current.execution.environmentRecall.length - 13, by omega⟩
  rw [length] at clock
  norm_num [originalClock, originalClockFrom, originalTick] at clock
  omega

private theorem bob_early_recall_prior_empty (seed : Seeds) (current : app.Control)
    (trace : rawProtocol.Trace (some current))
    (fixed : (rawMenu.protocol initial horizon (family seed)).Trace (some current))
    (request : current.execution.application.SeedRequest alice (originalCoordinate alice))
    (early : current.execution.environmentRecall.length ≤ 12)
    (earlier : List app.PlayerEntry) (entry : app.PlayerEntry) (later : List app.PlayerEntry)
    (recalled : current.execution.recall bob = earlier ++ entry :: later) : earlier = [] := by
  have recorded : entry ∈ current.execution.recall bob := by
    rw [recalled]
    exact List.mem_append_right _ (List.mem_cons_self)
  obtain ⟨original, zero⟩ := bob_record_before_late_origin seed current fixed request early entry
    recorded
  obtain ⟨before, prior, _kept, active, pastEq, viewed, _allowed⟩ :=
    rawMenu.recorded_response_at initial horizon scheduler current trace bob earlier entry later
      recalled
  rw [viewed] at original zero
  obtain (⟨impossible, _⟩ | ⟨_owner, first, state⟩) := original_zero_clock_decision before bob
    (rawMenu.toRawTrace initial horizon scheduler prior) active original zero
  · exact ((by decide : bob ≠ alice) impossible).elim
  · have empty : before.execution.recall bob = [] := by
      rw [state]
      exact bobFirst_recall first
    exact pastEq.symm.trans empty

private theorem bob_early_recall_singleton (seed : Seeds) (current : app.Control)
    (trace : rawProtocol.Trace (some current))
    (fixed : (rawMenu.protocol initial horizon (family seed)).Trace (some current))
    (request : current.execution.application.SeedRequest alice (originalCoordinate alice))
    (early : current.execution.environmentRecall.length ≤ 12)
    (entry : app.PlayerEntry) (recorded : entry ∈ current.execution.recall bob) :
    current.execution.recall bob = [entry] := by
  cases recalled : current.execution.recall bob with
  | nil => rw [recalled] at recorded; exact (List.not_mem_nil recorded).elim
  | cons head rest =>
      cases rest with
      | nil =>
          rw [recalled] at recorded
          exact congrArg (fun value : app.PlayerEntry => [value])
            (List.mem_singleton.mp recorded).symm
      | cons second rest =>
          have empty := bob_early_recall_prior_empty seed current trace fixed request early [head]
            second rest (by simpa only [List.singleton_append] using recalled)
          cases empty

/-- Every actual raw realization of an early helper input has a counted
prehistory at the identical physical control. The signed helper is retained
among authored inputs, whether its observation is current or recalled. -/
theorem raw_helper_input_counted_trace (sourceSeed targetSeed : Seeds)
    (source target : app.Control)
    (sourceTrace : countedProtocol.Trace (some source))
    (sourceFixed : (rawMenu.protocol initial horizon (family sourceSeed)).Trace (some source))
    (targetTrace : rawProtocol.Trace (some target))
    (targetFixed : (rawMenu.protocol initial horizon (family targetSeed)).Trace (some target))
    (request : source.execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : source.execution.application.current.native.clock ≤ 3)
    (recalled : target.execution.recall alice = source.execution.recall alice)
    (observed : target.execution.observe app alice = source.execution.observe app alice)
    (message : Message Player (CommitAttemptPacket graph)) (sender : message.sender = bob)
    (sourceInput : message ∈ source.execution.network.inputs)
    (targetInput : message ∈ target.execution.network.inputs) :
    Nonempty (countedProtocol.Trace (some target)) := by
  have sourceRaw := countedMenu.toRawTrace initial horizon scheduler sourceTrace
  have targetRaw := rawMenu.toRawTrace initial horizon scheduler targetTrace
  have sourceValid := raw_native_valid scheduler source sourceRaw
  have targetValid := raw_native_valid scheduler target targetRaw
  have sourcePublic := (source.execution.application.requests_publicView sourceValid alice
    (originalCoordinate alice)).mpr request
  have targetPublic : PhaseRuntimeState.requests target.execution.application.publicView alice
      (originalCoordinate alice) := by
    change PhaseRuntimeState.requests (target.execution.observe app alice).application.2 alice _
    rw [observed]
    exact sourcePublic
  have targetRequest := (target.execution.application.requests_publicView targetValid alice
    (originalCoordinate alice)).mp targetPublic
  have targetClock : target.execution.application.current.native.clock ≤ 3 := by
    have same := congrArg (fun view : app.PlayerView => view.application.2.native.clock) observed
    change target.execution.application.current.native.clock =
      source.execution.application.current.native.clock at same
    rwa [same]
  have sourceEarly := original_early_clock_index sourceSeed source sourceFixed request.1.symm clock
  have targetEarly := original_early_clock_index targetSeed target targetFixed
    targetRequest.1.symm targetClock
  have permitted := (observed_helper_packet_permission sourceSeed source sourceTrace sourceFixed
    request sourceEarly message sourceInput sender).2
  obtain ⟨entry, recorded, emitted, original, zero⟩ := bob_packet_before_late_origin targetSeed
    target targetFixed targetRequest targetEarly message targetInput sender
  obtain ⟨_first, viewed, allowed, _aliceRecorded⟩ := bob_original_record_counted_of_helper target
    targetTrace entry recorded original zero message emitted permitted
  have singleton := bob_early_recall_singleton targetSeed target targetTrace targetFixed
    targetRequest targetEarly entry recorded
  have bobAllowed : entry.action ∈ countedMenu.actions bob [] entry.beforeView := by
    rw [viewed]
    exact allowed
  apply counted_trace_of_recorded_actions target targetTrace
  intro owner earlier chosen later splitRecall
  fin_cases owner
  · have sourceRecall : source.execution.recall alice = earlier ++ chosen :: later := by
      rw [← recalled]
      exact splitRecall
    obtain ⟨_before, _prior, _kept, _active, _past, viewed, allowed⟩ :=
      countedMenu.recorded_response_at initial horizon scheduler source sourceTrace alice earlier
        chosen later sourceRecall
    rwa [← viewed] at allowed
  · change target.execution.recall bob = earlier ++ chosen :: later at splitRecall
    rw [singleton] at splitRecall
    cases earlier with
    | nil =>
        simp only [List.nil_append] at splitRecall
        have same : chosen = entry := (List.cons.inj splitRecall).1.symm
        subst chosen
        exact bobAllowed
    | cons first earlier =>
        have lengths := congrArg List.length splitRecall
        simp only [List.length_cons, List.length_nil, List.length_append] at lengths
        omega

end Vegas.Examples.CommitSeedSignalling
