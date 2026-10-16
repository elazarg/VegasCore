/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingPlanPhysicalCoupling
import Vegas.Pending.PhaseBindingMemoryCallback

/-! # Complete actual callbacks of a finite timing plan in a commitment block -/

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

/-- Every actual owner callback in the addressed commitment block couples under
one original timing plan, including sent and absent-request silent callbacks. -/
theorem phase_timing_plan_word_callback_coupling
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
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : right.execution.application.phases = phase :: remaining)
    (committing : phase.kind = .commitment)
    (lower : phase.low = low) (upper : phase.high = low + block.length)
    (values : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (capacity : horizon ≤ bounds.candidateCount)
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
  let inputs := setup.initialLaw.map (fun draw => encodeInputs draw)
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
  have activeLeft : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some ⟨left.remaining, some owner, left.execution⟩) := by
    cases left with
    | mk count actor execution =>
        dsimp only at firstActive
        subst actor
        exact countedLeft
  have activeRight : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some ⟨right.remaining, some owner, right.execution⟩) := by
    cases right with
    | mk count actor execution =>
        dsimp only at secondActive
        subst actor
        exact countedRight
  have cases := BindingShadow.callback_binding_or_silent runtime leaks bounds plan
    (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler left.remaining
      right.remaining owner left.execution right.execution activeLeft activeRight memory
        application network clear phase remaining installed committing
  rcases cases with ⟨leftSilent, rightSilent⟩ |
      ⟨event, payload, binding, eventLower, eventUpper, request, unsent⟩
  · let firstPolicy := phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon
      scheduler bound fallback wellFormed (approximation.sequence n) block low generation slotWeight
        slotNonnegative slotBounded parts owner firstWord
    let secondPolicy := phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon
      scheduler bound fallback wellFormed (approximation.sequence n) block low generation slotWeight
        slotNonnegative slotBounded parts owner secondWord
    have covered (word : DecisionView owner Δ) (past : List (app).PlayerEntry)
        (view : (app).PlayerView) (response : (app).Action)
        (supported : response ∈ (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial
          horizon scheduler bound fallback wellFormed (approximation.sequence n) block low
            generation slotWeight slotNonnegative slotBounded parts owner word past view).support) :
        response ∈ PhaseCount.onePacketActions runtime leaks bounds owner past view := by
      exact (menu).decode_embedPolicy_covered initial horizon scheduler owner _ past view response
        supported
    have firstPure : firstPolicy (left.execution.recall owner)
        (left.execution.observe app owner) = PMF.pure ⟨none⟩ := by
      apply pmf_eq_pure_of_support_subset_singleton
      intro response supported
      have member := covered firstWord _ _ response supported
      rw [leftSilent] at member
      exact Finset.mem_singleton.mp member
    have secondPure : secondPolicy (right.execution.recall owner)
        (right.execution.observe app owner) = PMF.pure ⟨none⟩ := by
      apply pmf_eq_pure_of_support_subset_singleton
      intro response supported
      have member := covered secondWord _ _ response supported
      rw [rightSilent] at member
      exact Finset.mem_singleton.mp member
    let first := left.execution.respond app owner ⟨none⟩
    let second := right.execution.respond app owner ⟨none⟩
    refine ⟨PMF.pure (first, second), ?_, ?_, ?_⟩
    · change (PMF.pure (first, second)).map Prod.fst =
        (firstPolicy (left.execution.recall owner) (left.execution.observe app owner)).map _
      rw [firstPure, PMF.pure_map, PMF.pure_map]
    · change (PMF.pure (first, second)).map Prod.snd =
        (secondPolicy (right.execution.recall owner) (right.execution.observe app owner)).map _
      rw [secondPure, PMF.pure_map, PMF.pure_map]
    · intro pair supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      refine ⟨memory, owned, valid, application, network, receipts, service, ?_, ?_⟩
      · intro who different
        exact ((app).respond_recall_other left.execution owner who different ⟨none⟩).trans
          ((recalled who different).trans
            ((app).respond_recall_other right.execution owner who different ⟨none⟩).symm)
      · exact phaseOperationalRecall_response runtime leaks left.execution right.execution owner
          ⟨none⟩ ⟨none⟩ network past
          (phaseOperationalView_memory runtime leaks memory owner owned valid left.execution
            right.execution application network receipts) network
  · apply phase_timing_plan_word_physical_coupling setup mode runtime leaks bounds plan maximal
      horizon scheduler bound finite wellFormed target approximation n fallback parts owner block
        low generation firstWord secondWord slotWeight slotNonnegative slotBounded left right
          leftTrace rightTrace firstActive secondActive memory owned valid application network
            receipts service recalled past clear event payload binding request unsent
              (values payload) capacity _ address
    exact ⟨lower ▸ eventLower, upper ▸ eventUpper⟩

end Vegas
