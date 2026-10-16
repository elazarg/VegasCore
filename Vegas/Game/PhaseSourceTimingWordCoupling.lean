/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordCoupling
import Vegas.Game.PhaseBindingWordOmission

/-! # Original source draws in actual timing-word physical coupling -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- The physical kernel uses each callback's ORIGINAL source omission law.
Their equality is derived from actual source playedness and compiler position;
no common-draw, response-law or successor-memory premise is supplied. -/
theorem phase_source_timing_word_response_physical_coupling
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (n : Nat) (left right : (app).Control)
    (leftTrace : (E).Trace (some left)) (rightTrace : (E).Trace (some right))
    (owner : Player) (memory : BindingShadow graph) (owned : memory.OwnBindings owner)
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
    (serial : Nat)
    (eligible : serial ∈ PhaseCount.phaseBindingSlots runtime leaks bounds owner event payload
      (right.execution.recall owner) (right.execution.observe app owner))
    (option : LateOption bounds.candidateCount) (slotWeight : ℝ)
    (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (firstResult secondResult : PublicationResult (L.Val payload)) :
    let firstMissing := ((approximation.sequence n).strategy owner
      (setup.commitRecoveryClearInformation wellFormed owner
        (phaseSourceView? setup mode runtime leaks owner event
          (left.execution.observe app owner)))).map (fun choice => CommitRecoveryMove.missed
            choice.1)
    let secondMissing := ((approximation.sequence n).strategy owner
      (setup.commitRecoveryClearInformation wellFormed owner
        (phaseSourceView? setup mode runtime leaks owner event
          (right.execution.observe app owner)))).map (fun choice => CommitRecoveryMove.missed
            choice.1)
    ∃ paired : PMF ((app).Execution × (app).Execution),
      paired.map Prod.fst =
        (phaseBindingTimingWordResponse setup mode runtime leaks bounds owner event payload
          firstMissing
          option slotWeight slotNonnegative slotBounded firstResult (left.execution.recall owner)
            (left.execution.observe app owner)).map (left.execution.respond app owner) ∧
      paired.map Prod.snd =
        (phaseBindingTimingWordResponse setup mode runtime leaks bounds owner event payload
          secondMissing
          option slotWeight slotNonnegative slotBounded secondResult
            (right.execution.recall owner) (right.execution.observe app owner)).map
              (right.execution.respond app owner) ∧
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
  intro firstMissing secondMissing
  have firstClear : left.execution.application.current.excluded = ∅ := by
    rw [application]
    exact clear
  have firstReady : left.execution.application.current.native.config.cut.Ready event := by
    rw [application]
    exact request.2.2.1
  have sameMissing : firstMissing = secondMissing :=
    phaseBindingWord_missing_eq_of_histories setup mode runtime leaks bounds plan horizon scheduler
      finite wellFormed target approximation maximal n owner event payload binding left right
        leftTrace rightTrace firstClear clear firstReady request.2.2.1
  let inputs := setup.initialLaw.map (fun draw => encodeInputs draw)
  have countedLeft : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some left) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact leftTrace
  have countedRight : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some right) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact rightTrace
  obtain ⟨paired, firstLaw, secondLaw, related⟩ :=
    phaseBindingTimingWordResponse_physical_coupling setup mode runtime leaks bounds
      (PhaseCount.onePacketMenu runtime leaks bounds) plan inputs horizon scheduler left right
        countedLeft countedRight owner memory owned valid application network receipts service
          recalled past clear event payload binding request unsent values serial eligible
            firstMissing option
            slotWeight slotNonnegative slotBounded firstResult secondResult
  refine ⟨paired, firstLaw, ?_, related⟩
  rw [sameMissing] at secondLaw
  exact secondLaw

end Vegas
