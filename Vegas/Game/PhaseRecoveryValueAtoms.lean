/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryValueConditioning
import Vegas.Game.PhaseTimingWordResponse
import Vegas.Game.PhaseBindingCounterpart

/-! # Actual silent response atoms of immutable ordinary source policies -/

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

/-- Each immutable ordinary policy uses the existing physical word encoder,
with the original fresh omission law and independent slot tier. This follows
by conditioning the actual resampled source policy, not a supplied prediction. -/
theorem phaseRecoveryValueTimingPolicy_word_response (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (who : Player)
    (member : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (option : LateOption bounds.candidateCount)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (present : false ∈ ((assessment.strategy who
      (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event view))).map
          (fun choice => CommitRecoveryMove.missed choice.1)).support) :
    let changed := setup.commitRecoveryValueAssessment wellFormed assessment who member
    mix slotWeight slotNonnegative slotBounded
        (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed changed who event
          payload binding past view)
        (phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed changed who event
          payload binding option past view) =
      phaseBindingTimingWordResponse setup mode runtime leaks bounds who event payload
        ((assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
          (phaseSourceView? setup mode runtime leaks who event view))).map
            (fun choice => CommitRecoveryMove.missed choice.1)) option slotWeight slotNonnegative
              slotBounded
        (phaseRecoveryBindingData setup mode event who payload binding
          (CommitRecoveryMove.lift
            (member (phaseSourceView? setup mode runtime leaks who event view)).val)).1
        past view := by
  intro changed
  let observed := phaseSourceView? setup mode runtime leaks who event view
  have nonmissing := setup.commitRecoveryValueAssessment_nonmissing wellFormed assessment who
    member observed present
  have predicts : (PMF.pure (member observed).val).map id =
      (setup.commitRecoveryNonmissingProfile changed.strategy who
        (setup.commitRecoveryClearInformation wellFormed who observed)).map
          (fun choice => CommitRecoveryMove.underlying choice.1) := by
    rw [PMF.map_id, nonmissing, PMF.pure_map]
    exact congrArg PMF.pure (CommitRecoveryMove.underlying_lift (member observed).val).symm
  have law := phaseBindingTimingWordResponse_law setup mode runtime leaks bounds wellFormed
    changed who event payload binding past view slotWeight slotNonnegative slotBounded
      (PMF.pure (member observed).val) id predicts option
  have missing : (changed.strategy who
      (setup.commitRecoveryClearInformation wellFormed who observed)).map
        (fun choice => CommitRecoveryMove.missed choice.1) =
      (assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who observed)).map
        (fun choice => CommitRecoveryMove.missed choice.1) := by
    simp only [changed, SourceProgram.Setup.commitRecoveryValueAssessment,
      InformationModel.BehavioralAssessment.ofStrategy, Function.update_self]
    exact setup.commitRecoveryValuePolicy_clear_missing wellFormed assessment.strategy who member
      observed
  dsimp only [observed] at missing
  simpa only [PMF.pure_bind, id_eq, missing] using law

/-- A silent callback has the SAME original source/slot atom for every
immutable source-value policy. An arbitrary fixed timing WAIT or guarded serial
is retained, and no RAW menu or unrelated history is equated. -/
theorem phaseRecoveryValueTimingPolicy_silence_congr (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (who : Player)
    (first second : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (option : LateOption bounds.candidateCount)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (present : false ∈ ((assessment.strategy who
      (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event view))).map
          (fun choice => CommitRecoveryMove.missed choice.1)).support) :
    (mix slotWeight slotNonnegative slotBounded
      (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who first) who event payload
          binding past view)
      (phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who first) who event payload
          binding option past view)) ⟨none⟩ =
    (mix slotWeight slotNonnegative slotBounded
      (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who second) who event payload
          binding past view)
      (phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who second) who event payload
          binding option past view)) ⟨none⟩ := by
  rw [phaseRecoveryValueTimingPolicy_word_response setup mode runtime leaks bounds wellFormed
    assessment who first event payload binding past view option slotWeight slotNonnegative
      slotBounded present,
    phaseRecoveryValueTimingPolicy_word_response setup mode runtime leaks bounds wellFormed
      assessment who second event payload binding past view option slotWeight slotNonnegative
        slotBounded present]
  exact phaseBindingTimingWordResponse_silence_congr setup mode runtime leaks bounds who event
    payload _ option slotWeight slotNonnegative slotBounded _ _ past view

/-- Actual initialized clear binding histories supply the positive original
nonmissing event internally. Every immutable source member therefore gives
the same silent atom at that callback, for any timing option and slot weight. -/
theorem phaseRecoveryValueTimingPolicy_silence_of_history
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (ready : control.execution.application.current.native.config.cut.Ready event)
    (clear : control.execution.application.current.excluded = ∅)
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (option : LateOption bounds.candidateCount)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1) :
    let response := fun member : (setup.informationModel
        (CommitmentInterface.forfeiture setup.program)).Policy who =>
      mix slotWeight slotNonnegative slotBounded
        (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed
          (setup.commitRecoveryValueAssessment wellFormed assessment who member) who event payload
            binding (control.execution.recall who)
              (control.execution.observe (phaseApplication runtime leaks) who))
        (phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed
          (setup.commitRecoveryValueAssessment wellFormed assessment who member) who event payload
            binding option (control.execution.recall who)
              (control.execution.observe (phaseApplication runtime leaks) who))
    ∀ first second, response first ⟨none⟩ = response second ⟨none⟩ := by
  intro response first second
  obtain ⟨source, sourceTrace, sourceClear, _generation, actor, same⟩ :=
    phase_ready_binding_sourceView setup mode runtime leaks plan maximal horizon scheduler trace
      who event payload binding ready clear
  have running : ¬ setup.commitRecoveryProtocol.terminal (some source) := by
    intro stopped
    have impossible := ProtocolState.terminal_actor_none who setup.program source.point stopped
    rw [ProtocolState.actor_observe_eq, actor] at impossible
    cases impossible
  have present := setup.commitRecovery_nonmissing_present assessment mixed ⟨some source,
    sourceTrace⟩ running who
  rw [setup.commitRecoveryClearInformation_observed wellFormed who sourceTrace sourceClear]
    at present
  change phaseSourceView? setup mode runtime leaks who event
      (control.execution.observe (phaseApplication runtime leaks) who) =
    setup.commitRecoveryPrivate who (some source) at same
  rw [← same] at present
  exact phaseRecoveryValueTimingPolicy_silence_congr setup mode runtime leaks bounds wellFormed
    assessment who first second event payload binding (control.execution.recall who)
      (control.execution.observe (phaseApplication runtime leaks) who) option slotWeight
        slotNonnegative slotBounded present

end Vegas
