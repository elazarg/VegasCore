/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryTimingComponent
import Vegas.Game.PhaseSourcePerturbation

/-! # Finite phased timing components with independent source and raw tiers -/

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

/-- Waiting is silence at the callback, without restricting future callbacks.
A send option uses its guarded serial at bindings and canonical TRUE at openings. -/
def phaseSourceTimingPolicy (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (option : LateOption bounds.candidateCount) (who : Player) :
    (phaseApplication runtime leaks).Policy :=
  match option with
  | none => fun _ _ => PMF.pure ⟨none⟩
  | some serial => phasePolicyDispatch setup mode runtime leaks bounds
      (fun owner event payload binding => phaseRecoveryTimingPolicy setup mode runtime leaks
        bounds wellFormed assessment owner event payload binding (some serial)) who

theorem phaseSourceTimingPolicy_covered (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (option : LateOption bounds.candidateCount) (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (phaseSourceTimingPolicy setup mode runtime leaks bounds wellFormed
      assessment option who past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  cases option with
  | none =>
      cases (PMF.mem_support_pure_iff ..).mp supported
      exact PhaseCount.silence_onePacket runtime leaks bounds who past view
  | some serial =>
      exact phasePolicyDispatch_covered setup mode runtime leaks bounds
        (fun owner event payload binding => phaseRecoveryTimingPolicy setup mode runtime leaks
          bounds wellFormed assessment owner event payload binding (some serial))
        (fun owner event payload binding past view response supported =>
          phaseRecoveryTimingPolicy_covered setup mode runtime leaks bounds wellFormed assessment
            owner event payload binding (some serial) past view response supported)
        who past view response supported

/-- Actual binding requests use the unchanged source draw followed by the
selected timing encoder, including the WAIT option. -/
theorem phaseSourceTimingPolicy_binding (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (option : LateOption bounds.candidateCount)
    (execution : (phaseApplication runtime leaks).Execution) {inputs}
    (valid : execution.application.Invariant inputs) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩) :
    phaseSourceTimingPolicy setup mode runtime leaks bounds wellFormed assessment option who
        (execution.recall who) (execution.observe (phaseApplication runtime leaks) who) =
      phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed assessment who event
        payload binding option (execution.recall who)
          (execution.observe (phaseApplication runtime leaks) who) := by
  cases option with
  | none =>
      exact (phaseRecoveryTimingPolicy_wait setup mode runtime leaks bounds wellFormed assessment
        who event payload binding _ _).symm
  | some serial =>
      exact phasePolicyDispatch_binding setup mode runtime leaks bounds _ execution valid who
        event payload binding request

/-- The globally covered component has an exact representation in the actual
finite phased menu, including inputs that never occur in an initialized play. -/
def phaseSourceTimingStrategy (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (option : LateOption bounds.candidateCount) (who : Player) :
    ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
      scheduler).BehavioralPolicy who :=
  (PhaseCount.onePacketMenu runtime leaks bounds).restrictPolicy initial horizon scheduler who
    (phaseSourceTimingPolicy setup mode runtime leaks bounds wellFormed assessment option who)

theorem phaseSourceTimingStrategy_map_val (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (option : LateOption bounds.candidateCount) (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    ((phaseSourceTimingStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler option who) (some (past, view))).map Subtype.val =
      (phaseSourceTimingPolicy setup mode runtime leaks bounds wellFormed assessment option who
        past view).map some := by
  exact (PhaseCount.onePacketMenu runtime leaks bounds).restrictPolicy_map_val initial horizon
    scheduler who _ past view (fun response supported => phaseSourceTimingPolicy_covered setup
      mode runtime leaks bounds wellFormed assessment option who past view response supported)

variable (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- An independent raw tier covers every finite choice. The slot tier still
copies the original result/missing law before encoding; its rate is independent
of the raw-noise rate and of the selected operational option. -/
def phaseSourceTimingComponent (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (input : (phaseApplication runtime leaks).Info)
    (option : LateOption bounds.candidateCount) : PMF ((N).Choice who input) :=
  mix noise noiseNonnegative noiseBounded
    ((menu).uniformPolicy initial horizon scheduler who input)
    (mix slotWeight slotNonnegative slotBounded
      (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler who input)
      (phaseSourceTimingStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler option who input))

theorem phaseSourceTimingComponent_fullSupport (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (positive : 0 < noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (input : (phaseApplication runtime leaks).Info)
    (option : LateOption bounds.candidateCount) :
    FullSupport (phaseSourceTimingComponent setup mode runtime leaks bounds initial horizon
      scheduler wellFormed assessment noise positive.le noiseBounded slotWeight slotNonnegative
        slotBounded who input option) := by
  intro choice
  let := Fintype.ofFinite ((N).Choice who input)
  exact mem_support_mix_left _ _ _ positive (PMF.mem_support_uniformOfFintype choice)

/-- The selected operational law retains its original mass separately from
both the value-preserving slot tier and the raw menu perturbation. -/
theorem phaseSourceTimingComponent_ge_option (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (input : (phaseApplication runtime leaks).Info)
    (option : LateOption bounds.candidateCount) (choice : (N).Choice who input) :
    (1 - noise) * (1 - slotWeight) *
        ((phaseSourceTimingStrategy setup mode runtime leaks bounds wellFormed assessment initial
          horizon scheduler option who input) choice).toReal ≤
      (phaseSourceTimingComponent setup mode runtime leaks bounds initial horizon scheduler
        wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
          slotBounded who input option choice).toReal := by
  unfold phaseSourceTimingComponent
  rw [mix_apply_toReal, mix_apply_toReal]
  have uniform := ENNReal.toReal_nonneg (a :=
    ((menu).uniformPolicy initial horizon scheduler who input) choice)
  have slots := ENNReal.toReal_nonneg (a :=
    (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial horizon
      scheduler who input) choice)
  have first := mul_nonneg noiseNonnegative uniform
  have second := mul_nonneg (sub_nonneg.mpr noiseBounded) (mul_nonneg slotNonnegative slots)
  nlinarith

end Vegas
