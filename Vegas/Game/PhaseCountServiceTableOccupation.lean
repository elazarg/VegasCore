/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCountServiceTableRun
import Interaction.ReactiveProfileMixture
import Interaction.ReactiveResponseConditioning
import Interaction.ReactiveControlOccupation
import Interaction.ReactiveRoundTrace

/-! # Original primitive tags and complete timing tables at native command inputs -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player Tag : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode

variable
  (values : Tag → ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
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
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (tagLaw : PMF Tag) (input : Tag → (serviceGraph setup mode).Inputs)
  (scheduler : Tag → (phaseApplication runtime leaks).Scheduler)

local notation "original" => independentProduct (fun _address : PhaseSeedAddress graph =>
  independentProduct (fun index : Fin horizon => PhaseCount.bindingServiceCoinLaw failure timing
    firstNonnegative firstBounded timingNonnegative timingBounded rawWeight rawNonnegative
      rawBounded (Fin.val index)))
local notation "members" => fun (tag : Tag) (owner : Player)
  (table : PhaseSeedAddress graph → Fin horizon → Bool × Bool) =>
    phaseCountServiceTapePolicy setup mode runtime leaks bounds (values tag) choose failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon table owner
local notation "players" => fun (tag : Tag) (owner : Player) =>
  ReactiveApplication.Implementation.policy
    (ReactiveApplication.policyMixture (phaseApplication runtime leaks) original
      (members tag owner))
local notation "factors" => fun (tag : Tag)
  (state : ReactiveApplication.ProtocolState (phaseApplication runtime leaks)) (owner : Player) =>
  ReactiveApplication.Implementation.posterior
    (ReactiveApplication.policyMixture (phaseApplication runtime leaks) original
      (members tag owner))
      (ReactiveApplication.recallAt (phaseApplication runtime leaks) owner state)

/-- An actual before-response command retains every original table jointly
with its full native control. Only the genuine whole-own-recall posteriors
appear on the right; the physical initial state and scheduler are unchanged. -/
theorem phaseCountServiceTapePolicy_command_tables_joint
    (tag : Tag) (remaining count : Nat) :
    (independentProduct (fun _owner : Player => original)).bind (fun tables =>
      ((app).commandControlLaw (scheduler tag) (fun owner => members tag owner (tables owner))
        (PMF.pure (PhaseRuntimeState.initial plan (input tag))) remaining count).map
          (fun state => (state, tables))) =
      ((app).commandControlLaw (scheduler tag) (players tag)
        (PMF.pure (PhaseRuntimeState.initial plan (input tag))) remaining count).bind
          fun state => (independentProduct (factors tag state)).map (Prod.mk state) := by
  let start := ReactiveApplication.Execution.initial (app) (PhaseRuntimeState.initial plan
    (input tag))
  let continuation := fun pair : (app).Execution ×
      (Player → PhaseSeedAddress graph → Fin horizon → Bool × Bool) =>
    (scheduler tag pair.1.environmentRecall (pair.1.observeEnvironment (app))).bind fun command =>
      (pair.1.environmentStep (app) command).map fun active =>
        (some (⟨remaining, command.actor? (app), active⟩ : (app).Control), pair.2)
  have rounds := (app).runRounds_policyMixtures_posterior_joint (scheduler tag)
    (fun _owner => original) (members tag) count start
  have moved := congrArg (fun distribution => distribution.bind continuation) rounds
  simp only [continuation, PMF.bind_bind, PMF.bind_map, Function.comp_def] at moved
  simp only [ReactiveApplication.commandControlLaw, PMF.pure_bind, PMF.map_bind,
    PMF.bind_bind, PMF.map_comp, Function.comp_def]
  refine moved.trans ?_
  apply bind_congr_on_support
  intro before _supported
  rw [PMF.bind_comm]
  apply bind_congr_on_support
  intro command _chosen
  have disintegrated := ReactiveApplication.environmentStep_disintegrate_profile
    (fun owner => (app).policyMixture original (members tag owner)) before command
    (fun active tables => PMF.pure
      (some (⟨remaining, command.actor? (app), active⟩ : (app).Control), tables))
  simpa only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def,
    ReactiveApplication.recallAt, Option.elim_some] using disintegrated

variable [NeZero horizon]

/-- The original primitive tag and every complete private timing table are
sampled once before initialized play. The native command index and full
before-response control remain in the same immutable tagged law. -/
def phaseCountServiceTableOccupation :
    PMF ((((Fin horizon × Tag) × (app).ProtocolState)) ×
      (Player → PhaseSeedAddress graph → Fin horizon → Bool × Bool)) :=
  (PMF.uniformOfFintype (Fin horizon)).bind fun time => tagLaw.bind fun tag =>
    (independentProduct (fun _owner : Player => original)).bind fun tables =>
      ((app).commandControlLaw (scheduler tag) (fun owner => members tag owner (tables owner))
        (PMF.pure (PhaseRuntimeState.initial plan (input tag)))
          (horizon - time.val - 1) time.val).map
            (fun state => (((time, tag), state), tables))

/-- Original source-plan, setup and scheduler tags may have arbitrary joint
law. Sampling their original command index and all per-owner timing tables
once gives this exact native occupation joint, with every tag retained. -/
theorem phaseCountServiceTapePolicy_occupation_tables_joint :
    let law := (PMF.uniformOfFintype (Fin horizon)).bind fun time => tagLaw.bind fun tag =>
      ((app).commandControlLaw (scheduler tag) (players tag)
        (PMF.pure (PhaseRuntimeState.initial plan (input tag))) (horizon - time.val - 1)
          time.val).map (fun state => ((time, tag), state))
    phaseCountServiceTableOccupation setup mode runtime leaks bounds values choose failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon plan tagLaw input scheduler =
        law.bind (fun branch =>
      (independentProduct (factors branch.1.2 branch.2)).map (Prod.mk branch)) := by
  intro law
  simp only [phaseCountServiceTableOccupation, law, PMF.bind_bind, PMF.bind_map]
  apply bind_congr_on_support
  intro time _timeSupported
  apply bind_congr_on_support
  intro tag _tagSupported
  have joint := phaseCountServiceTapePolicy_command_tables_joint setup mode runtime leaks bounds
    values choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
    slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon plan input
    scheduler tag (horizon - time.val - 1) time.val
  have tagged := congrArg (PMF.map fun pair => (((time, tag), pair.1), pair.2)) joint
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using tagged

/-- A positive original native input fiber supplies its bounded full address
and unused ordinal from an actual initialized counted history. Both are read
from the same observable input, independently of the retained primitive tag. -/
theorem phaseCountServiceTapePolicy_native_coordinate
    (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (coordinate : CommitAttemptEvent graph)
    (request : PhaseRuntimeState.requests view.application.2 who coordinate)
    (present : some (past, view) ∈
      ((phaseCountServiceTableOccupation setup mode runtime leaks bounds values choose failure
        timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
        slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon plan tagLaw input
        scheduler).map (fun pair => (app).observe who pair.1.2)).support) :
    (coordinate.attempt.phase < (serviceGraph setup mode).order.eventCount ∧
      coordinate.attempt.generation ≤ Fintype.card Player) ∧
      (PhaseSeedScheduler.ownerWord runtime leaks coordinate who past).length < horizon := by
  classical
  obtain ⟨outcome, supported, observed⟩ := (PMF.mem_support_map_iff ..).mp present
  simp only [phaseCountServiceTableOccupation, PMF.support_bind, Set.mem_iUnion,
    PMF.support_map] at supported
  obtain ⟨time, _timeSupported, tag, _tagSupported, tables, _tableSupported, state, commanded,
    equation⟩ := supported
  cases equation
  simp only [ReactiveApplication.commandControlLaw, PMF.pure_bind, PMF.support_bind,
    Set.mem_iUnion, PMF.support_map] at commanded
  obtain ⟨before, rounds, command, selected, mapped⟩ := commanded
  obtain ⟨after, moved, equation⟩ := mapped
  cases equation
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let inputs := PMF.pure (input tag)
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let localPlayers := fun owner => members tag owner (tables owner)
  have covered : ∀ owner before observed action,
      action ∈ (localPlayers owner before observed).support →
        action ∈ menu.actions owner before observed := by
    intro owner before observed action offered
    exact phaseCountServiceTapePolicy_covered setup mode runtime leaks bounds (values tag) choose
      failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
      slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon (tables owner) owner
      before observed action offered
  have actual : PhaseRuntimeState.initial plan (input tag) ∈ initial.support :=
    (PMF.mem_support_map_iff ..).mpr
      ⟨input tag, (PMF.mem_support_pure_iff ..).mpr rfl, rfl⟩
  obtain ⟨initialTrace⟩ := menu.trace_initial initial horizon (scheduler tag) _ actual
  obtain ⟨beforeTrace⟩ := menu.trace_runRounds initial horizon (scheduler tag) localPlayers covered
    (horizon - time.val) time.val _ before
      (by simpa only [Nat.sub_add_cancel time.isLt.le] using initialTrace) rounds
  have beforeTrace' : (menu.protocol initial horizon (scheduler tag)).Trace
      (some ⟨(horizon - time.val - 1) + 1, none, before⟩) := by
    have remainingEq : (horizon - time.val - 1) + 1 = horizon - time.val := by omega
    simpa only [remainingEq] using beforeTrace
  obtain ⟨pending⟩ := menu.trace_environment initial horizon (scheduler tag)
    (horizon - time.val - 1) before after command beforeTrace' selected moved
  have raw := menu.toRawTrace initial horizon (scheduler tag) pending
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    (scheduler tag) raw
  have budget := (phaseApplication_seedBudget runtime leaks).history initial horizon
    (scheduler tag) (fun state member => by
      obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ member
      exact PhaseRuntimeState.initial_seedBudget plan draw) raw
  change (if command.actor? app = some who then
    some (after.recall who, after.observe app who) else none) = some (past, view) at observed
  split_ifs at observed with active
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj observed)
    have actualRequest := (after.application.requests_publicView valid who coordinate).mp request
    refine ⟨actualRequest.bounded budget, ?_⟩
    exact PhaseCount.bindingServiceOrdinal_lt_horizon runtime leaks initial horizon
      (scheduler tag) _ raw who active coordinate

end Vegas
