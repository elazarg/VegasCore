/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingPlanControlCoupling
import GameTheory.Math.Probability.ConditionalObservation
import Interaction.ReactiveLocalContinuation

/-! # Actual history-step coupling of original finite timing-plan members -/

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

/-- The paired physical step lifts to BOTH original behavioral history laws
using their actual state fibers, preserving complete preexisting entry histories. -/
theorem phase_timing_plan_history_word_coupling
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice)
    (n : Nat) (fallback : (who : Player) → (N).Policy who)
    (parts : (p : Pool) → Parts p)
    (opponents : (who : Player) → (N).BehavioralPolicy who) (owner : Player)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (firstWord secondWord : DecisionView owner Δ)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (left right : (app).Control)
    (firstHistory secondHistory : (E).History)
    (firstCurrent : firstHistory.state = some left)
    (secondCurrent : secondHistory.state = some right)
    (sameRemaining : left.remaining = right.remaining) (sameActor : left.actor = right.actor)
    (running : ¬(left.remaining = 0 ∧ left.actor = none))
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
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : right.execution.application.phases = phase :: remaining)
    (committing : phase.kind = .commitment)
    (lower : phase.low = low) (upper : phase.high = low + block.length)
    (values : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (capacity : horizon ≤ bounds.candidateCount)
    (address : right.execution.application.attempt = ⟨low, generation⟩) :
    let firstProfile := GameTheory.Profile.update (sig := (N).behavioralSignature) opponents owner
      ((menu).restrictPolicy initial horizon scheduler owner
        (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed (approximation.sequence n) block low generation slotWeight
            slotNonnegative slotBounded parts owner firstWord))
    let secondProfile := GameTheory.Profile.update (sig := (N).behavioralSignature) opponents owner
      ((menu).restrictPolicy initial horizon scheduler owner
        (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed (approximation.sequence n) block low generation slotWeight
            slotNonnegative slotBounded parts owner secondWord))
    ∃ paired : PMF ((E).History × (E).History),
      paired.map Prod.fst = (N).runBehavioralFrom firstProfile 1 firstHistory ∧
      paired.map Prod.snd = (N).runBehavioralFrom secondProfile 1 secondHistory ∧
      ∀ pair ∈ paired.support, ∃ count actor first second,
        pair.1.state = some ⟨count, actor, first⟩ ∧
        pair.2.state = some ⟨count, actor, second⟩ ∧
        ((first.application.current.excluded ≠ ∅ ∧ second.application.current.excluded ≠ ∅) ∨
          ∃ nextMemory : BindingShadow graph,
            nextMemory.OwnBindings owner ∧
            (∀ slot, nextMemory.candidates slot ≠ some .fresh) ∧
            first.application = nextMemory.phased owner second.application ∧
            first.network = second.network ∧ first.receipts = second.receipts ∧
            first.environmentRecall = second.environmentRecall ∧
            (∀ who, who ≠ owner → first.recall who = second.recall who) ∧
            (first.recall owner).map (fun entry =>
                (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
              (second.recall owner).map (fun entry =>
                (phaseOperationalView runtime leaks entry.beforeView, entry.emitted))) := by
  classical
  intro firstProfile secondProfile
  let rawWord (word : DecisionView owner Δ) := phaseTimingWordPlanPolicy setup mode runtime leaks
    bounds initial horizon scheduler bound fallback wellFormed (approximation.sequence n) block
      low generation slotWeight slotNonnegative slotBounded parts owner word
  have covered (word : DecisionView owner Δ) (past : List (app).PlayerEntry)
      (view : (app).PlayerView) (response : (app).Action)
      (supported : response ∈ (rawWord word past view).support) :
      response ∈ (menu).actions owner past view :=
    (menu).decode_embedPolicy_covered initial horizon scheduler owner _ past view response supported
  have decodedWord (word : DecisionView owner Δ) :=
    (menu).decode_restrictPolicy_of_covered initial horizon scheduler owner (rawWord word)
      (covered word)
  have firstDecode : (menu).decodeProfile initial horizon scheduler firstProfile =
      Function.update ((menu).decodeProfile initial horizon scheduler opponents) owner
        (rawWord firstWord) := by
    rw [ReactiveApplication.ResponseMenu.decodeProfile_update]
    rw [decodedWord firstWord]
  have secondDecode : (menu).decodeProfile initial horizon scheduler secondProfile =
      Function.update ((menu).decodeProfile initial horizon scheduler opponents) owner
        (rawWord secondWord) := by
    rw [ReactiveApplication.ResponseMenu.decodeProfile_update]
    rw [decodedWord secondWord]
  have leftTrace : (E).Trace (some left) := firstCurrent ▸ firstHistory.trace
  have rightTrace : (E).Trace (some right) := secondCurrent ▸ secondHistory.trace
  obtain ⟨stateJoint, firstStateLaw, secondStateLaw, related⟩ :=
    phase_timing_plan_control_word_coupling setup mode runtime leaks bounds plan maximal horizon
      scheduler bound finite wellFormed target approximation n fallback parts
        ((menu).decodeProfile initial horizon scheduler opponents) owner block low generation
          firstWord secondWord slotWeight slotNonnegative slotBounded left right leftTrace
            rightTrace sameRemaining sameActor running memory owned valid application network
              receipts service recalled past clear phase remaining installed committing lower upper
                values capacity address
  let firstRun := (N).runBehavioralFrom firstProfile 1 firstHistory
  let secondRun := (N).runBehavioralFrom secondProfile 1 secondHistory
  have firstMarginal : stateJoint.map Prod.fst = firstRun.map History.state := by
    rw [(menu).run_map_controlSteps]
    simp only [Function.iterate_one, PMF.pure_bind, firstCurrent, firstDecode]
    exact firstStateLaw
  have secondMarginal : stateJoint.map Prod.snd = secondRun.map History.state := by
    rw [(menu).run_map_controlSteps]
    simp only [Function.iterate_one, PMF.pure_bind, secondCurrent, secondDecode]
    exact secondStateLaw
  let paired := stateJoint.bind fun states => bindPairLaw
    (fiberPosterior firstRun History.state states.1)
      (fun _ => fiberPosterior secondRun History.state states.2)
  refine ⟨paired, ?_, ?_, ?_⟩
  · simp only [paired, PMF.map_bind, bindPairLaw_map_fst]
    change stateJoint.bind ((fiberPosterior firstRun History.state) ∘ Prod.fst) = firstRun
    rw [← PMF.bind_map, firstMarginal]
    exact fiberPosterior_reconstruct firstRun History.state
  · simp only [paired, PMF.map_bind, bindPairLaw_map_snd, PMF.bind_const]
    change stateJoint.bind ((fiberPosterior secondRun History.state) ∘ Prod.snd) = secondRun
    rw [← PMF.bind_map, secondMarginal]
    exact fiberPosterior_reconstruct secondRun History.state
  · intro pair supported
    obtain ⟨states, stateSupport, conditional⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
    obtain ⟨first, firstSupport, mappedSupport⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ conditional)
    obtain ⟨second, actualSecondSupport, same⟩ :=
      (PMF.mem_support_map_iff _ _ _).mp mappedSupport
    cases same
    have firstPresent : states.1 ∈ (firstRun.map History.state).support := by
      rw [← firstMarginal]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨states, stateSupport, rfl⟩
    have secondPresent : states.2 ∈ (secondRun.map History.state).support := by
      rw [← secondMarginal]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨states, stateSupport, rfl⟩
    have firstState := (mem_support_fiberPosterior firstPresent firstSupport).1
    have secondState := (mem_support_fiberPosterior secondPresent actualSecondSupport).1
    obtain ⟨count, actor, firstExecution, secondExecution, pairEq, actual⟩ :=
      related states stateSupport
    rw [pairEq] at firstState secondState
    exact ⟨count, actor, firstExecution, secondExecution, firstState, secondState, actual⟩

end Vegas
