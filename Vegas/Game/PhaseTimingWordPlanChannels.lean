/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordPlan
import Vegas.Game.PhaseTimingWordPlanRecall

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
      (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler bound p) (who : Player)

local notation "family" => phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial
  horizon scheduler bound fallback wellFormed source block low generation slotWeight
    slotNonnegative slotBounded timingPlan who

/-- Every actual varying-plan input is word-independent or reads exactly one
addressed source result through a concrete legal channel. Its silence atom
is independent of that result, and any transmission names that same result. -/
theorem phaseTimingWordPlanPolicy_channels
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    (∃ law, ∀ word, family word past view = law) ∨
      ∃ event payload, ∃ binding :
        (serviceGraph setup mode).outputLayout event = .binding who payload,
        (low ≤ event.val ∧ event.val < low + block.length) ∧
        view.application.2.attempt = ⟨low, generation⟩ ∧
        ∃ kernel : PublicationResult (L.Val payload) → PMF (app).Action,
          (∀ first second, kernel first ⟨none⟩ = kernel second ⟨none⟩) ∧
          (∀ result response, response ∈ (kernel result).support → response ≠ ⟨none⟩ →
            ∃ serial, response = phaseBindingResponse runtime leaks who event payload result
              serial) ∧
          ∀ word, family word past view = kernel
            (phaseRecoveryBindingData setup mode event who payload binding
              (CommitRecoveryMove.lift (block.wordAction who (event.val - low) word))).1 := by
  classical
  obtain ⟨law, constant⟩ | canonical | ⟨option, timed⟩ := phaseTimingWordPlanPolicy_cases setup mode
    runtime leaks bounds initial horizon scheduler bound fallback wellFormed source block low
      generation slotWeight slotNonnegative slotBounded timingPlan who past view
  · exact Or.inl ⟨law, constant⟩
  · obtain ⟨law, constant⟩ | ⟨event, payload, binding, inside, address, channels⟩ :=
      phaseCommitWordPolicy_cases setup mode runtime leaks bounds wellFormed source block low
        generation slotWeight slotNonnegative slotBounded who past view
    · exact Or.inl ⟨law, fun word => (canonical word).trans (constant word)⟩
    · let missing := (source.strategy who (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event view))).map
          (fun choice => CommitRecoveryMove.missed choice.1)
      let serial := (reactiveFreshSlot view.application.1).getD 0
      by_cases allowed : ∀ result, phaseBindingResponse runtime leaks who event payload result
          serial ∈ PhaseCount.onePacketActions runtime leaks bounds who past view
      · let kernel := fun result => PhaseCount.phaseBindingWordResponse runtime leaks bounds who
          event payload missing serial slotWeight slotNonnegative slotBounded result past view
        refine Or.inr ⟨event, payload, binding, inside, address, kernel, ?_, ?_, ?_⟩
        · intro first second
          exact PhaseCount.phaseBindingWordResponse_silence_congr runtime leaks bounds who event
            payload missing serial slotWeight slotNonnegative slotBounded first second past view
        · intro result response supported nonsilent
          exact PhaseCount.phaseBindingWordResponse_nonsilent runtime leaks bounds who event
            payload missing serial slotWeight slotNonnegative slotBounded result past view response
              supported nonsilent
        · intro word
          rw [canonical word, channels word]
          unfold PhaseCount.phaseBindingWordPolicy
          rw [ite_eq_left allowed]
      · refine Or.inl ⟨PMF.pure ⟨none⟩, ?_⟩
        intro word
        rw [canonical word, channels word]
        unfold PhaseCount.phaseBindingWordPolicy
        rw [ite_eq_right allowed]
  · obtain ⟨law, constant⟩ | ⟨event, payload, binding, inside, address, channels⟩ :=
      phaseCommitTimingWordPolicy_cases setup mode runtime leaks bounds wellFormed source block low
        generation slotWeight slotNonnegative slotBounded option who past view
    · exact Or.inl ⟨law, fun word => (timed word).trans (constant word)⟩
    · let missing := (source.strategy who (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event view))).map
          (fun choice => CommitRecoveryMove.missed choice.1)
      let kernel := fun result => phaseBindingTimingWordResponse setup mode runtime leaks bounds
        who event payload missing option slotWeight slotNonnegative slotBounded result past view
      refine Or.inr ⟨event, payload, binding, inside, address, kernel, ?_, ?_, ?_⟩
      · intro first second
        exact phaseBindingTimingWordResponse_silence_congr setup mode runtime leaks bounds who
          event payload missing option slotWeight slotNonnegative slotBounded first second past view
      · intro result response supported nonsilent
        exact phaseBindingTimingWordResponse_nonsilent setup mode runtime leaks bounds who event
          payload missing option slotWeight slotNonnegative slotBounded result past view response
            supported nonsilent
      · intro word
        exact (timed word).trans (channels word)

end Vegas
