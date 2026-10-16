/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseBindingNonmissingLaw

/-! # Complete raw binding laws from omission flags and latent typed results

The original source omission marginal is sampled without conditioning it
away. Conditional on transmitting, the typed result selects the existing
canonical or independent fresh-slot response kernel.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

/-- Binding an actual input law through a pointwise mixture distributes over that mixture. -/
theorem bind_mix_kernel {A B : Type} (law : PMF A)
    (first second : A → PMF B) (weight : ℝ) (nonnegative : 0 ≤ weight) (bounded : weight ≤ 1) :
    law.bind (fun point => mix weight nonnegative bounded (first point) (second point)) =
      mix weight nonnegative bounded (law.bind first) (law.bind second) := by
  ext result
  rw [PMF.bind_apply, mix_apply, PMF.bind_apply, PMF.bind_apply]
  calc
    _ = ∑' point, (ENNReal.ofReal weight * (law point * first point result) +
        ENNReal.ofReal (1 - weight) * (law point * second point result)) := by
      apply tsum_congr
      intro point
      rw [mix_apply]
      ring
    _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]

private theorem bool_flag_factor {A B : Type} (source : PMF A) (flag : A → Bool)
    (silence : B) (send : A → PMF B) :
    (source.bind fun point => if flag point then PMF.pure silence else send point) =
      (source.map flag).bind (fun missing => if missing then PMF.pure silence else
        (fiberPosterior source flag false).bind send) := by
  conv_lhs => rw [← fiberPosterior_reconstruct source flag]
  rw [PMF.bind_bind]
  apply bind_congr_on_support _
  intro missing present
  cases missing with
  | true =>
      change (fiberPosterior source flag true).bind _ = PMF.pure silence
      calc
        _ = (fiberPosterior source flag true).bind (fun _ => PMF.pure silence) := by
          apply bind_congr_on_support _
          intro point supported
          rw [(mem_support_fiberPosterior present supported).1]
          rfl
        _ = _ := PMF.bind_const _ _
  | false =>
      apply bind_congr_on_support _
      intro point supported
      rw [(mem_support_fiberPosterior present supported).1]
      rfl

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

/-- The whole raw canonical/slot binding law factors through the original
omission flag and a nonmissing typed-result draw. Failed accepted bindings
remain in the latter law. No raw uniform-noise tier is removed by this identity. -/
theorem phaseRecoveryBindingResponse_factor (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (serial : Nat) (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1) :
    let source := assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
      (phaseSourceView? setup mode runtime leaks who event view))
    let data := fun choice => phaseRecoveryBindingData setup mode event who payload binding choice.1
    let results := ((setup.commitRecoveryNonmissingProfile assessment.strategy who
      (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event view))).map data).map Prod.fst
    mix slotWeight slotNonnegative slotBounded
        (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed assessment who event
          payload binding past view)
        (phaseRecoveryBindingLaw setup mode runtime leaks wellFormed assessment who event payload
          binding serial (phaseSourceView? setup mode runtime leaks who event view)) =
      (source.map (fun choice => CommitRecoveryMove.missed choice.1)).bind fun missing =>
        if missing then PMF.pure ⟨none⟩ else results.bind fun result =>
          mix slotWeight slotNonnegative slotBounded
            (PhaseCount.phaseBindingSlotPolicy runtime leaks bounds who event payload
              (fun _ _ => PMF.pure result) past view)
            (PMF.pure (phaseBindingResponse runtime leaks who event payload result serial)) := by
  intro source data results
  let send := fun result => mix slotWeight slotNonnegative slotBounded
    (PhaseCount.phaseBindingSlotPolicy runtime leaks bounds who event payload
      (fun _ _ => PMF.pure result) past view)
    (PMF.pure (phaseBindingResponse runtime leaks who event payload result serial))
  have joint : mix slotWeight slotNonnegative slotBounded
      (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed assessment who event
        payload binding past view)
      (phaseRecoveryBindingLaw setup mode runtime leaks wellFormed assessment who event payload
        binding serial (phaseSourceView? setup mode runtime leaks who event view)) =
      source.bind (fun choice => if CommitRecoveryMove.missed choice.1 then PMF.pure ⟨none⟩
        else send (data choice).1) := by
    unfold phaseRecoverySlotPolicy phaseRecoveryBindingLaw
    rw [← PMF.bind_pure_comp, ← bind_mix_kernel source]
    apply congrArg (PMF.bind source)
    funext choice
    have missing := phaseRecoveryBindingData_missing setup mode who event payload binding choice.1
    change (data choice).2 = CommitRecoveryMove.missed choice.1 at missing
    unfold phaseRecoveryBindingResponse
    change mix slotWeight slotNonnegative slotBounded
      (if (data choice).2 then PMF.pure ⟨none⟩ else
        PhaseCount.phaseBindingSlotPolicy runtime leaks bounds who event payload
          (fun _ _ => PMF.pure (data choice).1) past view)
      (PMF.pure (if (data choice).2 then ⟨none⟩ else
        phaseBindingResponse runtime leaks who event payload (data choice).1 serial)) = _
    rw [missing]
    cases missing : CommitRecoveryMove.missed choice.1 <;> simp only [Bool.false_eq_true,
      ↓reduceIte, mix_self, send]
  rw [joint, bool_flag_factor source (fun choice => CommitRecoveryMove.missed choice.1)]
  apply congrArg (PMF.bind (source.map (fun choice => CommitRecoveryMove.missed choice.1)))
  funext missing
  cases missing with
  | true => rfl
  | false =>
      change (setup.commitRecoveryNonmissingProfile assessment.strategy who
        (setup.commitRecoveryClearInformation wellFormed who
          (phaseSourceView? setup mode runtime leaks who event view))).bind _ = results.bind send
      dsimp only [results]
      rw [PMF.bind_map, PMF.bind_map]
      rfl

end Vegas
