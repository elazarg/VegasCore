/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingPlanCallbackCoupling
import Vegas.Pending.PhaseBindingForeignResponseMemory

/-! # Actual callback laws for an arbitrary selected actor under hidden word changes -/

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

/-- The selected actor uses its same full private input when foreign, while the
hidden owner uses the actual finite-plan word coupling at every callback. -/
theorem phase_timing_plan_actor_word_coupling
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice)
    (n : Nat) (fallback : (who : Player) → (N).Policy who)
    (parts : (p : Pool) → Parts p)
    (opponents : Player → (app).Policy) (owner actor : Player)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (firstWord secondWord : DecisionView owner Δ)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (left right : (app).Control)
    (leftTrace : (E).Trace (some left)) (rightTrace : (E).Trace (some right))
    (firstActive : left.actor = some actor) (secondActive : right.actor = some actor)
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
        ((Function.update opponents owner (phaseTimingWordPlanPolicy setup mode runtime leaks bounds
          initial horizon scheduler bound fallback wellFormed (approximation.sequence n) block low
            generation slotWeight slotNonnegative slotBounded parts owner firstWord)) actor
              (left.execution.recall actor) (left.execution.observe app actor)).map
                (left.execution.respond app actor) ∧
      paired.map Prod.snd =
        ((Function.update opponents owner (phaseTimingWordPlanPolicy setup mode runtime leaks bounds
          initial horizon scheduler bound fallback wellFormed (approximation.sequence n) block low
            generation slotWeight slotNonnegative slotBounded parts owner secondWord)) actor
              (right.execution.recall actor) (right.execution.observe app actor)).map
                (right.execution.respond app actor) ∧
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
  classical
  by_cases same : actor = owner
  · subst actor
    simpa only [Function.update_self] using phase_timing_plan_word_callback_coupling setup mode
      runtime leaks bounds plan maximal horizon scheduler bound finite wellFormed target
        approximation n fallback parts owner block low generation firstWord secondWord slotWeight
          slotNonnegative slotBounded left right leftTrace rightTrace firstActive secondActive
            memory owned valid application network receipts service recalled past clear phase
              remaining installed committing lower upper values capacity address
  · have observed : left.execution.observe app actor = right.execution.observe app actor := by
      change (⟨left.execution.network.observe actor, left.execution.application.playerView actor,
        left.execution.receipts⟩ : (app).PlayerView) = ⟨_, _, _⟩
      rw [network, receipts, application,
        BindingShadow.phased_playerView_other owned _ actor same]
      rfl
    let paired := (opponents actor (right.execution.recall actor)
      (right.execution.observe app actor)).map fun response =>
        (left.execution.respond app actor response, right.execution.respond app actor response)
    refine ⟨paired, ?_, ?_, ?_⟩
    · simp only [paired, PMF.map_comp, Function.comp_def, Function.update_of_ne same]
      rw [recalled actor same, observed]
    · simp only [paired, PMF.map_comp, Function.comp_def, Function.update_of_ne same]
    · intro pair supported
      obtain ⟨response, _chosen, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      obtain ⟨state, net, receipt, log, recallEq, firstPast, secondPast⟩ :=
        BindingShadow.respond_foreign_memory runtime leaks memory owner actor same owned
          left.execution right.execution application network receipts service recalled response
      refine ⟨memory, owned, valid, state, net, receipt, log, recallEq, ?_⟩
      rw [firstPast, secondPast]
      exact past

end Vegas
