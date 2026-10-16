/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueStoppedMemory
import Vegas.Pending.PhaseAttemptEntryStopping
import GameTheoryExtensions.Analysis.Protocol.StoppedComposition

/-! # Original memory at the first actual full attempt entry -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (runtimePlan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)) horizon
      scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)) horizon
      scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "initial" => PMF.map (PhaseRuntimeState.initial runtimePlan)
  (PMF.map encodeInputs setup.initialLaw)
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent => PhasePublicExclusion setup mode runtime leaks
  (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent => PhaseUnprotected runtime leaks bound
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound

local instance phaseRecoveryValueEntryPoolFintype : Fintype Pool := Fintype.ofFinite _

open Classical in
/-- First reaching an exact attempt keeps the ORIGINAL global source-policy
and separate full owner-plan tags, updated by the genuine complete old recall.
Skipped namespaces, terminal histories and first exclusions retain their mass. -/
theorem phaseTimingPlanPolicy_value_attempt_entry_joint
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (weights : (p : Pool) → PMF (Parts p))
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories)
    (target : CommitAttemptId) :
    let priors := fun who => (independentProduct weights).bind fun plan =>
      (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).map (Prod.mk plan)
    let members := fun who memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    let profile := (N).agentBehavior (N).playedInformation fallback (fun agent =>
      (weights (pool agent)).bind (phaseTimingComponent setup mode runtime leaks bounds initial
        horizon scheduler bound wellFormed assessment noise noiseNonnegative noiseBounded
          slotWeight slotNonnegative slotBounded agent))
    let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
      phaseAttemptEntryStop runtime leaks target history.state
    let posteriors := fun history : ((menu).protocol initial horizon scheduler).History =>
      independentProduct (fun who => ((app).policyMixture (priors who) (members who)).posterior
        ((app).recallAt who history.state))
    (independentProduct priors).bind (fun memories =>
      ((N).runBehavioralUntil certificate (fun who => (menu).restrictPolicy initial horizon
        scheduler who (members who (memories who))) stopped
          ((menu).protocol initial horizon scheduler).initHistory).map
            (fun final => (final, memories))) =
      ((N).runBehavioralUntil certificate profile stopped
        ((menu).protocol initial horizon scheduler).initHistory).bind
          (fun final => (posteriors final).map (Prod.mk final)) ∧
    ∀ entry ∈ ((N).runBehavioralUntil certificate profile stopped
        ((menu).protocol initial horizon scheduler).initHistory).support,
      ∀ control, entry.state = some control → control.execution.application.attempt = target →
        control.actor = none ∧ ∀ who, ∀ record ∈ control.execution.recall who,
          record.beforeView.application.2.attempt ≠ target := by
  intro priors members profile stopped posteriors
  let extra := fun history : ((menu).protocol initial horizon scheduler).History =>
    match history.state with
    | none => False
    | some current => current.execution.application.attempt = target
  have joint := phaseTimingPlanPolicy_value_initial_memory_joint setup mode runtime leaks bounds
    runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed finite weights
      noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded certificate extra
  have stopEq : (fun history : ((menu).protocol initial horizon scheduler).History =>
      extra history ∨ match history.state with
        | none => False
        | some current => current.execution.application.current.excluded ≠ ∅) = stopped := by
    funext history
    cases state : history.state <;>
      simp only [extra, stopped, phaseAttemptEntryStop, state, false_or, or_comm]
  dsimp only at joint
  erw [stopEq] at joint
  refine ⟨joint, ?_⟩
  have initialized : ∀ state : (app).State, state ∈ (initial).support → state.Ordered := by
    intro state member
    obtain ⟨input, _supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp member
    exact PhaseRuntimeState.initial_ordered runtimePlan input
  exact phase_attempt_first_visit_fresh runtime leaks (menu) initial initialized horizon scheduler
    certificate profile target

open Classical in
/-- Original immutable members continue from the actual first-entry law
with their genuine recall-updated memories. No fresh prior or entry independence
is introduced when seeking a later full-history event in that exact attempt. -/
theorem phaseTimingPlanPolicy_value_attempt_entry_continuation
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (weights : (p : Pool) → PMF (Parts p))
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories)
    (target : CommitAttemptId)
    (wanted : ((menu).protocol initial horizon scheduler).History → Prop) :
    let priors := fun who => (independentProduct weights).bind fun plan =>
      (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).map (Prod.mk plan)
    let members := fun who memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    let profile := (N).agentBehavior (N).playedInformation fallback (fun agent =>
      (weights (pool agent)).bind (phaseTimingComponent setup mode runtime leaks bounds initial
        horizon scheduler bound wellFormed assessment noise noiseNonnegative noiseBounded
          slotWeight slotNonnegative slotBounded agent))
    let entryStop := fun history : ((menu).protocol initial horizon scheduler).History =>
      phaseAttemptEntryStop runtime leaks target history.state
    let laterStop := fun history : ((menu).protocol initial horizon scheduler).History =>
      match history.state with
        | none => False
        | some current => current.execution.application.current.excluded ≠ ∅ ∨
            (current.execution.application.attempt = target ∧ wanted history)
    let posteriors := fun history : ((menu).protocol initial horizon scheduler).History =>
      independentProduct (fun who => ((app).policyMixture (priors who) (members who)).posterior
        ((app).recallAt who history.state))
    (independentProduct priors).bind (fun memories =>
      ((N).runBehavioralUntil certificate (fun who => (menu).restrictPolicy initial horizon
        scheduler who (members who (memories who))) laterStop
          ((menu).protocol initial horizon scheduler).initHistory).map
            (fun final => (final, memories))) =
      ((N).runBehavioralUntil certificate profile entryStop
        ((menu).protocol initial horizon scheduler).initHistory).bind
          (fun entry => (posteriors entry).bind fun memories =>
            ((N).runBehavioralUntil certificate (fun who => (menu).restrictPolicy initial horizon
              scheduler who (members who (memories who))) laterStop entry).map
                (fun final => (final, memories))) := by
  intro priors members profile entryStop laterStop posteriors
  let E := (menu).protocol initial horizon scheduler
  let Memory := (who : Player) → ((p : Pool) → Parts p) ×
    (setup.informationModel (CommitmentInterface.forfeiture setup.program)).Policy who
  let continuation := fun row : E.History × Memory =>
    ((N).runBehavioralUntil certificate (fun who => (menu).restrictPolicy initial horizon
      scheduler who (members who (row.2 who))) laterStop row.1).map
        (fun final => (final, row.2))
  have nested : ∀ history, laterStop history → entryStop history := by
    intro history
    cases state : history.state with
    | none =>
        simpa only [laterStop, entryStop, phaseAttemptEntryStop, state] using id (α := False)
    | some control =>
        simp only [laterStop, entryStop, phaseAttemptEntryStop, state]
        exact fun halt => halt.imp_right And.left
  have entryJoint := (phaseTimingPlanPolicy_value_attempt_entry_joint setup mode runtime leaks
    bounds runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed finite
      weights noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
        certificate target).1
  have joined := congrArg (fun law => law.bind continuation) entryJoint
  change ((independentProduct priors).bind (fun memories =>
      ((N).runBehavioralUntil certificate (fun who => (menu).restrictPolicy initial horizon
        scheduler who (members who (memories who))) entryStop E.initHistory).map
          (fun final => (final, memories)))).bind continuation = _ at joined
  have split (memories : Memory) := (N).runBehavioralUntil_eq_bind_runBehavioralUntil certificate
    (fun who => (menu).restrictPolicy initial horizon scheduler who (members who (memories who)))
      entryStop laterStop nested E.initHistory
  calc
    _ = ((independentProduct priors).bind (fun memories =>
        ((N).runBehavioralUntil certificate (fun who => (menu).restrictPolicy initial horizon
          scheduler who (members who (memories who))) entryStop E.initHistory).map
            (fun final => (final, memories)))).bind continuation := by
      simp only [PMF.bind_bind, PMF.bind_map]
      apply congrArg (PMF.bind _)
      funext memories
      rw [split, PMF.map_bind]
      rfl
    _ = _ := joined.trans (by simp only [PMF.bind_bind, PMF.bind_map]; rfl)

end Vegas
