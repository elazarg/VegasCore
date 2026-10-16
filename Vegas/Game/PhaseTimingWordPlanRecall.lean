/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordPlan
import Vegas.Game.PhaseCommitWordResponseRecall

/-! # Accepted source-word meaning under the actual varying finite timing plan -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (runtimePlan : RuntimePhasePlan (serviceGraph setup mode))
  (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial runtimePlan)
variable [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler).InfoState who)]

variable {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
  (fallback : (who : Player) →
    ((PhaseCount.onePacketMenu runtime leaks bounds).information
      (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler).Policy who)
  (wellFormed : setup.WellFormed)
  (source : setup.commitRecoveryModel.BehavioralAssessment)
  (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (timingPlan : (p : FreeKeyedPool
    (fun agent : InformationModel.InformationAgent
        ((PhaseCount.onePacketMenu runtime leaks bounds).information
          (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler)
        (InformationModel.playedInformation
          ((PhaseCount.onePacketMenu runtime leaks bounds).information
            (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler)) =>
      PhasePublicExclusion setup mode runtime leaks (Subtype.val (Sigma.snd agent)))
    (fun agent => PhaseUnprotected runtime leaks bound (Sigma.fst agent)
      (Subtype.val (Sigma.snd agent)))
    (fun agent => phaseTimingKey runtime leaks (Sigma.fst agent)
      (Subtype.val (Sigma.snd agent)))) →
    PhaseTimingPart setup mode runtime leaks bounds
      (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler bound p)
  (who : Player) (word : DecisionView who Δ)

local notation "family" => phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial
  horizon scheduler bound fallback wellFormed source block low generation slotWeight
    slotNonnegative slotBounded timingPlan who

/-- Under one original finite plan, every surviving addressed binding has the
exact original source-word meaning. The actual part may differ at every past
key, and WAIT creates no source-result record. Raw noise is not in this family. -/
theorem phaseTimingWordPlanRecall_accepted
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (inside : low ≤ event.val ∧ event.val < low + block.length)
    (address : control.execution.application.attempt = ⟨low, generation⟩)
    (candidate : Handle (serviceGraph setup mode))
    (accepted : control.execution.application.current.native.accepted (.inr event) = some candidate)
    (consistent : (family word).Consistent (control.execution.recall who)) :
    let result := (phaseRecoveryBindingData setup mode event who payload binding
      (CommitRecoveryMove.lift (block.wordAction who (event.val - low) word))).1
    ∃ (entry : (app).PlayerEntry) (serial : Nat),
      entry ∈ control.execution.recall who ∧
      entry.beforeView.application.2.attempt = ⟨low, generation⟩ ∧
      entry.action = phaseBindingResponse runtime leaks who event payload result serial ∧
      candidate = (who, .prepared serial) ∧
      control.execution.application.current.native.bindingResult candidate payload = result ∧
      phaseBindingAction? setup.program mode runtime leaks entry.action =
        decodeEventAction setup.program event
          (cast (congrArg EventField.Action binding.symm) result) := by
  apply phaseCommitWordRecall_accepted_of_response setup mode runtime leaks bounds block low
    generation who word runtimePlan inputs horizon scheduler (family word) ?_ ?_ trace
      clear event payload binding inside address candidate accepted consistent
  · intro past view response supported
    unfold phaseTimingWordPlanPolicy at supported
    exact (menu).decode_embedPolicy_covered initial horizon scheduler who _ past view response
      supported
  · intro remaining execution prior beforeClear selected value shape request addressed tag response
      sampled nonsilent
    have raw := (menu).toRawTrace initial horizon scheduler prior
    obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history runtime leaks runtimePlan inputs horizon
      scheduler raw
    obtain canonical | ⟨option, timed⟩ := phaseTimingWordPlanPolicy_of_clear_actor setup mode
      runtime leaks bounds initial horizon scheduler bound fallback wellFormed source block low
        generation slotWeight slotNonnegative slotBounded timingPlan who
          ⟨remaining, some who, execution⟩ prior rfl beforeClear
    · rw [canonical word] at sampled
      rw [phaseCommitWordPolicy_binding setup mode runtime leaks bounds wellFormed source block
        low generation slotWeight slotNonnegative slotBounded who word execution valid selected
          value shape request addressed tag] at sampled
      unfold PhaseCount.phaseBindingWordPolicy at sampled
      split at sampled
      · exact PhaseCount.phaseBindingWordResponse_nonsilent runtime leaks bounds who selected value
          _ _ slotWeight slotNonnegative slotBounded _ _ _ response sampled nonsilent
      · exact (nonsilent ((PMF.mem_support_pure_iff ..).mp sampled)).elim
    · rw [timed word] at sampled
      rw [phaseCommitTimingWordPolicy_binding setup mode runtime leaks bounds wellFormed source
        block low generation slotWeight slotNonnegative slotBounded option who word execution
          valid selected value shape request addressed tag] at sampled
      exact phaseBindingTimingWordResponse_nonsilent setup mode runtime leaks bounds who selected
        value _ option slotWeight slotNonnegative slotBounded _ _ _ response sampled nonsilent

end Vegas
