/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordPlanCoupling
import Vegas.Game.PhaseCommitWordCanonicalOption
import Vegas.Game.PhaseCommitWordPhysicalCoupling

/-! # Actual finite timing-plan word responses under evolving physical memory -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.InformationModel
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) horizon
      scheduler).History]
  [∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) horizon
        scheduler).InfoState who)]

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler

local notation "Pool" => FreeKeyedPool
  (fun agent : (N).InformationAgent (N).playedInformation =>
    PhasePublicExclusion setup mode runtime leaks (Subtype.val (Sigma.snd agent)))
  (fun agent => PhaseUnprotected runtime leaks bound (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
  (fun agent => phaseTimingKey runtime leaks (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

include maximal

/-- One actual finite timing plan couples both complete-word members at two
genuine clear callbacks. Played pools, operational key, source omission draw,
canonical fallback serial and physical successor memory are all derived. -/
theorem phase_timing_plan_word_physical_coupling
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice)
    (n : Nat) (fallback : (who : Player) → (N).Policy who)
    (parts : (p : Pool) → Parts p)
    (owner : Player) {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (firstWord secondWord : DecisionView owner Δ)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (left right : (app).Control)
    (leftTrace : (E).Trace (some left)) (rightTrace : (E).Trace (some right))
    (firstActive : left.actor = some owner) (secondActive : right.actor = some owner)
    (memory : BindingShadow (graph)) (owned : memory.OwnBindings owner)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (application : left.execution.application = memory.phased owner right.execution.application)
    (network : left.execution.network = right.execution.network)
    (receipts : left.execution.receipts = right.execution.receipts)
    (service : left.execution.environmentRecall = right.execution.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.execution.recall who = right.execution.recall who)
    (past : (left.execution.recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
      (right.execution.recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)))
    (clear : right.execution.application.current.excluded = ∅)
    (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding owner payload)
    (request : right.execution.application.SeedRequest owner
      ⟨right.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (right.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨right.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (capacity : horizon ≤ bounds.candidateCount)
    (inside : low ≤ event.val ∧ event.val < low + block.length)
    (address : right.execution.application.attempt = ⟨low, generation⟩) :
    ∃ paired : PMF ((app).Execution × (app).Execution),
      paired.map Prod.fst =
        (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed (approximation.sequence n) block low generation slotWeight
            slotNonnegative slotBounded parts owner firstWord (left.execution.recall owner)
              (left.execution.observe app owner)).map (left.execution.respond app owner) ∧
      paired.map Prod.snd =
        (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed (approximation.sequence n) block low generation slotWeight
            slotNonnegative slotBounded parts owner secondWord (right.execution.recall owner)
              (right.execution.observe app owner)).map (right.execution.respond app owner) ∧
      ∀ pair ∈ paired.support, ∃ nextMemory : BindingShadow graph,
        nextMemory.OwnBindings owner ∧
        (∀ slot, nextMemory.candidates slot ≠ some .fresh) ∧
        pair.1.application = nextMemory.phased owner pair.2.application ∧
        pair.1.network = pair.2.network ∧ pair.1.receipts = pair.2.receipts ∧
        pair.1.environmentRecall = pair.2.environmentRecall ∧
        (∀ who, who ≠ owner → pair.1.recall who = pair.2.recall who) ∧
        (pair.1.recall owner).map (fun entry =>
            (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
          (pair.2.recall owner).map (fun entry =>
            (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) := by
  have planCases := phaseTimingWordPlanPolicy_paired_binding setup mode runtime leaks bounds
    initial horizon scheduler bound fallback wellFormed (approximation.sequence n) block low
      generation slotWeight slotNonnegative slotBounded parts owner left right leftTrace rightTrace
        firstActive secondActive memory owned valid application network receipts past clear event
          payload binding request
  have timing (option : LateOption bounds.candidateCount) :=
    phase_commit_timing_word_physical_coupling setup mode runtime leaks bounds plan horizon
                scheduler
      finite wellFormed target approximation maximal owner block low generation firstWord secondWord
        n left right leftTrace rightTrace memory owned valid application network receipts service
          recalled past clear event payload binding request unsent values capacity secondActive
                inside
            address option slotWeight slotNonnegative slotBounded
  rcases planCases with ⟨firstCanonical, secondCanonical⟩ | ⟨option, firstTiming, secondTiming⟩
  · let inputs := setup.initialLaw.map (fun draw => encodeInputs draw)
    have countedLeft : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some left) := by
      dsimp only [inputs]
      rw [PMF.map_comp]
      exact leftTrace
    have countedRight : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some right) := by
      dsimp only [inputs]
      rw [PMF.map_comp]
      exact rightTrace
    have rawLeft := (menu).toRawTrace _ horizon scheduler countedLeft
    have rawRight := (menu).toRawTrace _ horizon scheduler countedRight
    have firstCount := PhaseCount.countRecall_history runtime leaks rawLeft
    have secondCount := PhaseCount.countRecall_history runtime leaks rawRight
    have outputs : (app).outputs (left.execution.recall owner) =
        (app).outputs (right.execution.recall owner) := by
      rw [← firstCount.1 owner, ← secondCount.1 owner, network]
    have firstRequest : left.execution.application.SeedRequest owner
        ⟨left.execution.application.attempt, event⟩ := by rw [application]; exact request
    have firstUnsent : ∀ message ∈ (app).outputs (left.execution.recall owner),
        PhaseCount.event? message.payload ≠ some ⟨left.execution.application.attempt, event⟩ := by
      rw [outputs, application]
      exact unsent
    have firstAddress : left.execution.application.attempt = ⟨low, generation⟩ := by
      rw [application]
      exact address
    obtain ⟨firstSerial, firstSerialEq, firstOption⟩ := phaseCommitWordPolicy_canonical_option
      setup mode runtime leaks bounds wellFormed (approximation.sequence n) block low generation
        slotWeight slotNonnegative slotBounded plan inputs horizon scheduler capacity left
          countedLeft owner firstActive event payload binding firstRequest firstUnsent values inside
            firstAddress
    obtain ⟨secondSerial, secondSerialEq, secondOption⟩ := phaseCommitWordPolicy_canonical_option
      setup mode runtime leaks bounds wellFormed (approximation.sequence n) block low generation
        slotWeight slotNonnegative slotBounded plan inputs horizon scheduler capacity right
          countedRight owner secondActive event payload binding request unsent values inside address
    have sameAllocator : reactiveFreshSlot (left.execution.observe app owner).application.1 =
        reactiveFreshSlot (right.execution.observe app owner).application.1 := by
      apply reactiveFreshSlot_congr
      intro serial
      change left.execution.application.current.native.candidates.lookup
        (owner, .prepared serial) = .fresh ↔
          right.execution.application.current.native.candidates.lookup (owner, .prepared serial) =
            .fresh
      rw [application]
      simp only [BindingShadow.phased, BindingShadow.recovery, BindingShadow.native,
        CommitmentCandidates.lookup, ite_true]
      exact memory.candidate_fresh_iff valid (.prepared serial) _
    have serialEq : firstSerial = secondSerial := by
      apply Fin.ext
      rw [sameAllocator] at firstSerialEq
      exact firstSerialEq.symm.trans secondSerialEq
    subst secondSerial
    obtain ⟨paired, firstLaw, secondLaw, related⟩ := timing (some firstSerial)
    refine ⟨paired, ?_, ?_, related⟩
    · rw [firstCanonical firstWord, firstOption firstWord]
      exact firstLaw
    · rw [secondCanonical secondWord, secondOption secondWord]
      exact secondLaw
  · obtain ⟨paired, firstLaw, secondLaw, related⟩ := timing option
    refine ⟨paired, ?_, ?_, related⟩
    · rw [firstTiming firstWord]
      exact firstLaw
    · rw [secondTiming secondWord]
      exact secondLaw

end Vegas
