/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCountServiceTableRun
import Interaction.ReactiveRecovery
import Interaction.ReactiveLocalContinuation
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryAtom

/-! # Actual entry posteriors support their original complete service members -/

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
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds

variable
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent (serviceGraph setup mode) → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
  (horizon : Nat)

local notation "Q" => phaseCountServiceTapePolicy setup mode runtime leaks bounds values choose
  failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
  slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
local notation "P" => phaseCountServicePolicy setup mode runtime leaks bounds values choose
  failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
  slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
local notation "original" => independentProduct (fun _address : PhaseSeedAddress graph =>
  independentProduct (fun index : Fin horizon => PhaseCount.bindingServiceCoinLaw failure timing
    firstNonnegative firstBounded timingNonnegative timingBounded rawWeight rawNonnegative
      rawBounded (Fin.val index)))

/-- Selecting each address from its actual owner's original table changes
none of that owner's complete policy. Unused coordinates remain original tags;
the derived table is only a deterministic readout of the per-owner vector. -/
theorem phaseCountServiceTapePolicy_owned_table
    (tables : Player → PhaseSeedAddress graph → Fin horizon → Bool × Bool) (who : Player) :
    let owned := fun (address : PhaseSeedAddress graph) =>
      match (serviceGraph setup mode).actor? address.val.event with
      | none => fun _ : Fin horizon => (false, false)
      | some owner => tables owner address
    Q (tables who) who = Q owned who := by
  classical
  intro owned
  funext past view
  unfold phaseCountServiceTapePolicy
  obtain common | ⟨event, payload, binding, selectedBranch⟩ :=
    phasePolicyDispatch_indexed_cases setup mode runtime leaks
      (fun owner _event _payload _binding => P owner)
      (fun (table : PhaseSeedAddress graph → Fin horizon → Bool × Bool)
          owner event payload binding before view =>
        if bounded : view.application.2.attempt.phase < (serviceGraph setup mode).order.eventCount ∧
            view.application.2.attempt.generation ≤ Fintype.card Player then
          PhaseCount.bindingServiceTapeMember runtime leaks bounds (P owner) owner
            ⟨view.application.2.attempt, event⟩ payload
            (fun before view => (values owner event payload binding before view).map
              PublicationResult.success)
            (choose owner ⟨view.application.2.attempt, event⟩) failure timing firstNonnegative
            firstBounded timingNonnegative timingBounded slotWeight slotNonnegative slotBounded
            rawWeight rawNonnegative rawBounded horizon
            (table ⟨⟨view.application.2.attempt, event⟩, bounded⟩) before view
        else P owner before view)
      who past view
  · obtain ⟨law, same⟩ := common
    exact (same (tables who)).trans (same owned).symm
  · rw [selectedBranch (tables who), selectedBranch owned]
    split
    · rename_i bounded
      have lookup : owned ⟨⟨view.application.2.attempt, event⟩, bounded⟩ =
          tables who ⟨⟨view.application.2.attempt, event⟩, bounded⟩ := by
        dsimp only [owned]
        rw [(serviceGraph setup mode).actor?_of_outputLayout_binding binding]
      rw [lookup]
    · rfl

variable (plan : RuntimePhasePlan (serviceGraph setup mode))
  (inputs : PMF (serviceGraph setup mode).Inputs)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds)
  (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds)
  (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler

/-- Supported initialized member play supplies complete own-recall
consistency through the original finite stopped runner. No member-consistency
premise or fresh table draw is used at the resulting entry. -/
theorem phaseCountServiceTapePolicy_table_member_consistent
    (tables : Player → PhaseSeedAddress graph → Fin horizon → Bool × Bool)
    (stopped : (E).History → Prop) (final : (E).History)
    (supported : final ∈ ((N).runBehavioralUntil
      ((menu).bounded initial horizon scheduler).wellFoundedHistories
      (fun who => (menu).restrictPolicy initial horizon scheduler who (Q (tables who) who))
        stopped (E).initHistory).support) :
    ∀ who, (Q (tables who) who).Consistent ((app).recallAt who final.state) := by
  classical
  let players := fun who => Q (tables who) who
  let profile := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
  let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
  have kept := (N).runBehavioralUntil_support_prefix certificate profile stopped (E).initHistory
    final supported
  have first := (N).runBehavioralUntil_support_first certificate profile stopped (E).initHistory
    final supported
  have halted := (N).mem_support_runBehavioralUntil certificate profile stopped (E).initHistory
    final supported
  have atom := (N).runBehavioralUntil_apply_of_first_hit certificate profile stopped
    (E).initHistory final kept halted first
  have finite : final ∈
      ((N).runBehavioralFrom profile final.trace.length (E).initHistory).support := by
    have positive := pmf_toReal_pos_iff.mpr supported
    rw [atom] at positive
    exact pmf_toReal_pos_iff.mp positive
  have projected : final.state ∈ (((N).runBehavioralFrom profile final.trace.length
      (E).initHistory).map History.state).support :=
    (PMF.mem_support_map_iff ..).mpr ⟨final, finite, rfl⟩
  rw [(menu).run_map_controlSteps] at projected
  have decoded : (menu).decodeProfile initial horizon scheduler profile = players := by
    funext who
    exact (menu).decode_restrictPolicy_of_covered initial horizon scheduler who (players who)
      (fun past view action member => phaseCountServiceTapePolicy_covered setup mode runtime leaks
        bounds values choose failure timing firstNonnegative firstBounded timingNonnegative
        timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
        horizon (tables who) who past view action member)
  rw [decoded] at projected
  have canonical : final.state ∈ ((InformationModel.runSingleMoverBehavioralFrom
      ((app).information initial horizon scheduler) ((app).singleMover initial horizon scheduler)
        (fun who => (app).encodePolicy (players who)) final.trace.length
          ((app).protocol initial horizon scheduler).initHistory).map History.state).support := by
    rw [(app).run_map_state]
    exact projected
  have invariant := ((app).consistentRecall_policyInvariant players).canonical_run initial horizon
    scheduler (fun state _member who => .nil) final.trace.length final.state canonical
  cases current : final.state with
  | none => intro who; exact .nil
  | some control =>
      rw [current] at invariant
      exact invariant

/-- A table tag in the genuine initialized entry posterior supports the
actual entire old recall. This follows from the original tagged run identity,
rather than positing support of a refreshed member at entry. -/
theorem phaseCountServiceTapePolicy_table_entry_consistent
    (stopped : (E).History → Prop) (entry : (E).History)
    (entrySupported : entry ∈ ((N).runBehavioralUntil
      ((menu).bounded initial horizon scheduler).wellFoundedHistories
        (fun who => (menu).restrictPolicy initial horizon scheduler who (P who)) stopped
          (E).initHistory).support)
    (tables : Player → PhaseSeedAddress graph → Fin horizon → Bool × Bool)
    (tablesSupported : tables ∈ (independentProduct (fun who =>
      ((app).policyMixture original (fun table => Q table who)).posterior
        ((app).recallAt who entry.state))).support) :
    ∀ who, (Q (tables who) who).Consistent ((app).recallAt who entry.state) := by
  have joint := phaseCountServiceTapePolicy_table_initial_joint setup mode runtime leaks bounds
    values choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
    slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon plan inputs
    scheduler ((menu).bounded initial horizon scheduler).wellFoundedHistories stopped
  have tagged : (entry, tables) ∈ (((N).runBehavioralUntil
      ((menu).bounded initial horizon scheduler).wellFoundedHistories
        (fun who => (menu).restrictPolicy initial horizon scheduler who (P who)) stopped
          (E).initHistory).bind fun final => (independentProduct (fun who =>
            ((app).policyMixture original (fun table => Q table who)).posterior
              ((app).recallAt who final.state))).map (Prod.mk final)).support :=
    (PMF.mem_support_bind_iff ..).mpr ⟨entry, entrySupported,
      (PMF.mem_support_map_iff ..).mpr ⟨tables, tablesSupported, rfl⟩⟩
  rw [← joint, PMF.mem_support_bind_iff] at tagged
  obtain ⟨saved, _original, tagged⟩ := tagged
  obtain ⟨final, member, equal⟩ := (PMF.mem_support_map_iff ..).mp tagged
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  exact phaseCountServiceTapePolicy_table_member_consistent setup mode runtime leaks bounds values
    choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
    slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon plan inputs scheduler
    saved stopped final member

end Vegas
