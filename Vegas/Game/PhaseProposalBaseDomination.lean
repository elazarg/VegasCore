/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalUnflagged

/-! # Retained mass after removing prospective response flags -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Probability that none of the three BASE perturbations is selected at the
current callback. Ordinary source randomness is not a perturbation flag. -/
def PhaseProposalRates.baseKeep (rates : PhaseProposalRates) : ℝ :=
  (1 - rates.waiting.val) * ((1 - rates.slots.val) * (1 - rates.badPreparation.val))

theorem PhaseProposalRates.baseKeep_nonnegative (rates : PhaseProposalRates) :
    0 ≤ rates.baseKeep :=
  mul_nonneg (sub_nonneg.mpr rates.waiting.property.2)
    (mul_nonneg (sub_nonneg.mpr rates.slots.property.2)
      (sub_nonneg.mpr rates.badPreparation.property.2))

theorem PhaseProposalRates.baseKeep_le_waiting (rates : PhaseProposalRates) :
    rates.baseKeep ≤ 1 - rates.waiting.val := by
  apply mul_le_of_le_one_right (sub_nonneg.mpr rates.waiting.property.2)
  exact (mul_le_of_le_one_left (sub_nonneg.mpr rates.badPreparation.property.2)
    (by linarith [rates.slots.property.1])).trans
      (by linarith [rates.badPreparation.property.1])

theorem PhaseProposalRates.baseKeep_le_one (rates : PhaseProposalRates) :
    rates.baseKeep ≤ 1 :=
  rates.baseKeep_le_waiting.trans (by linarith [rates.waiting.property.1])

private theorem mix_retains_right {α : Type*} (weight : Set.Icc (0 : ℝ) 1)
    (extra retained : PMF α) (value : α) :
    (1 - weight.val) * (retained value).toReal ≤
      (mix weight.val weight.property.1 weight.property.2 extra retained value).toReal := by
  rw [mix_apply_toReal]
  exact le_add_of_nonneg_left (mul_nonneg weight.property.1 ENNReal.toReal_nonneg)

private theorem map_retains_mass {α β : Type*} (source target : PMF α)
    (factor : ℝ) (lower : ∀ value, factor * (source value).toReal ≤ (target value).toReal)
    (encode : α → β) (value : β) :
    factor * ((source.map encode) value).toReal ≤ ((target.map encode) value).toReal := by
  simpa only [pmf_bind_pure_eq_map] using
    prob_bind_ge_mul source target factor lower (fun item => PMF.pure (encode item)) value

variable (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks

/-- A missing query forces the SAME failure law on both sides. At a present
query only the independent current bad-preparation atom is removed. This
pointwise statement does not condition on qualification or on future success. -/
theorem phaseProposalBindingResults_retained
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player) (event : (serviceGraph setup mode).EventId)
    (payload : L.Ty) (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (result : PublicationResult (L.Val payload)) :
    (1 - rates.badPreparation.val) *
        (phaseProposalBindingResults setup mode runtime leaks plan values PhaseProposalRates.zero
          who event payload binding past view result).toReal ≤
      (phaseProposalBindingResults setup mode runtime leaks plan values rates who event payload
        binding past view result).toReal := by
  unfold phaseProposalBindingResults
  split
  · exact mul_le_of_le_one_left ENNReal.toReal_nonneg
      (by linarith [rates.badPreparation.property.1])
  · simpa only [PhaseProposalRates.zero, mix_zero] using
      mix_retains_right rates.badPreparation (PMF.pure .failure) _ result

private theorem binding_policy_retained
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (source target : List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (factor : ℝ) (bounded : factor ≤ 1)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (lower : ∀ result, factor * (source past view result).toReal ≤
      (target past view result).toReal) (response : (app).Action) :
    factor * (PhaseCount.phaseBindingPolicy runtime leaks bounds who event payload source
      past view response).toReal ≤
      (PhaseCount.phaseBindingPolicy runtime leaks bounds who event payload target
        past view response).toReal := by
  classical
  unfold PhaseCount.phaseBindingPolicy
  split
  · exact mul_le_of_le_one_left ENNReal.toReal_nonneg bounded
  · split
    · exact map_retains_mass _ _ factor lower _ response
    · exact mul_le_of_le_one_left ENNReal.toReal_nonneg bounded

/-- On every literal input, retain the ordinary source draw and the actual
canonical allocator. Freshness/menu guards are identical on both sides; an
already spent or unavailable event is not rehabilitated. -/
theorem phaseProposalBindingEncoder_retained
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player) (event : (serviceGraph setup mode).EventId)
    (payload : L.Ty) (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (response : (app).Action) :
    ((1 - rates.slots.val) * (1 - rates.badPreparation.val)) *
        (PhaseCount.bindingResultEncoder runtime leaks bounds who event payload
          (phaseProposalBindingResults setup mode runtime leaks plan values PhaseProposalRates.zero
            who event payload binding) 0 le_rfl zero_le_one past view response).toReal ≤
      (PhaseCount.bindingResultEncoder runtime leaks bounds who event payload
        (phaseProposalBindingResults setup mode runtime leaks plan values rates who event payload
          binding) rates.slots.val rates.slots.property.1 rates.slots.property.2
        past view response).toReal := by
  have lower := binding_policy_retained setup mode runtime leaks bounds who event payload
    (phaseProposalBindingResults setup mode runtime leaks plan values PhaseProposalRates.zero
      who event payload binding)
    (phaseProposalBindingResults setup mode runtime leaks plan values rates who event payload
      binding) (1 - rates.badPreparation.val)
    (by linarith [rates.badPreparation.property.1]) past view
    (phaseProposalBindingResults_retained setup mode runtime leaks plan values rates who event
      payload binding past view) response
  unfold PhaseCount.bindingResultEncoder
  rw [mix_zero]
  have retained := mix_retains_right rates.slots
    (PhaseCount.phaseBindingSlotPolicy runtime leaks bounds who event payload
      (phaseProposalBindingResults setup mode runtime leaks plan values rates who event payload
        binding) past view)
    (PhaseCount.phaseBindingPolicy runtime leaks bounds who event payload
      (phaseProposalBindingResults setup mode runtime leaks plan values rates who event payload
        binding) past view) response
  calc
    _ = (1 - rates.slots.val) * ((1 - rates.badPreparation.val) * _) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left lower (sub_nonneg.mpr rates.slots.property.2)
    _ ≤ _ := retained

/-- The current voluntary WAIT, slot and bad-preparation branches together
lose at most their product complement. Existing forced WAITs are unchanged. -/
theorem phaseProposalBindingResponse_retained
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player) (event : (serviceGraph setup mode).EventId)
    (payload : L.Ty) (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (response : (app).Action) :
    rates.baseKeep *
        (PhaseCount.bindingResultEncoder runtime leaks bounds who event payload
          (phaseProposalBindingResults setup mode runtime leaks plan values PhaseProposalRates.zero
            who event payload binding) 0 le_rfl zero_le_one past view response).toReal ≤
      (mix rates.waiting.val rates.waiting.property.1 rates.waiting.property.2
        (PMF.pure ⟨none⟩) (PhaseCount.bindingResultEncoder runtime leaks bounds who event payload
          (phaseProposalBindingResults setup mode runtime leaks plan values rates who event payload
            binding) rates.slots.val rates.slots.property.1 rates.slots.property.2
          past view) response).toReal := by
  have lower := phaseProposalBindingEncoder_retained setup mode runtime leaks bounds plan values
    rates who event payload binding past view response
  have retained := mix_retains_right rates.waiting (PMF.pure ⟨none⟩)
    (PhaseCount.bindingResultEncoder runtime leaks bounds who event payload
      (phaseProposalBindingResults setup mode runtime leaks plan values rates who event payload
        binding) rates.slots.val rates.slots.property.1 rates.slots.property.2 past view) response
  calc
    _ = (1 - rates.waiting.val) *
        (((1 - rates.slots.val) * (1 - rates.badPreparation.val)) * _) := by
      unfold PhaseProposalRates.baseKeep
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left lower (sub_nonneg.mpr rates.waiting.property.2)
    _ ≤ _ := retained

/-- Publication comparison retains the current successful stored value and
accepted handle. The component's forced-silence guards are not removed. -/
theorem phaseProposalOpeningResponse_retained
    (rates : PhaseProposalRates) (who : Player) (event : (serviceGraph setup mode).EventId)
    (payload : L.Ty) (binding : FieldRef (serviceGraph setup mode).layout (.binding who payload))
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (response : (app).Action) :
    rates.baseKeep *
        (PhaseCount.phaseOpeningPolicy runtime leaks bounds who event payload binding
          (fun _ _ => PMF.pure true) past view response).toReal ≤
      (PhaseCount.phaseOpeningPolicy runtime leaks bounds who event payload binding
        (fun _ _ => mix rates.waiting.val rates.waiting.property.1 rates.waiting.property.2
          (PMF.pure false) (PMF.pure true)) past view response).toReal := by
  classical
  unfold PhaseCount.phaseOpeningPolicy
  split
  · dsimp only
    split
    · rename_i value candidate _stored _accepted _allowed
      have lower := map_retains_mass (PMF.pure true)
        (mix rates.waiting.val rates.waiting.property.1 rates.waiting.property.2
          (PMF.pure false) (PMF.pure true)) (1 - rates.waiting.val)
        (mix_retains_right rates.waiting (PMF.pure false) (PMF.pure true))
        (fun disclose => if disclose then
          PhaseCount.phaseOpeningResponse runtime leaks event candidate ⟨payload, value⟩
          else ⟨none⟩) response
      exact (mul_le_mul_of_nonneg_right rates.baseKeep_le_waiting
        ENNReal.toReal_nonneg).trans lower
    · exact mul_le_of_le_one_left ENNReal.toReal_nonneg rates.baseKeep_le_one
  · exact mul_le_of_le_one_left ENNReal.toReal_nonneg rates.baseKeep_le_one

/-- The actual BASE law retains a fixed fraction of its unflagged law at every
literal physical input, including dirty and known-debt inputs. This comparison
does not alter any past response, pending message, stored meaning or clock. -/
theorem phaseProposalBasePolicy_retained
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView) (response : (app).Action) :
    rates.baseKeep *
        (phaseProposalBasePolicy setup mode runtime leaks bounds plan values PhaseProposalRates.zero
          who past view response).toReal ≤
      (phaseProposalBasePolicy setup mode runtime leaks bounds plan values rates who past view
        response).toReal := by
  unfold phaseProposalBasePolicy
  apply phasePolicyDispatch_probability_domination setup mode runtime leaks _ _ _ _
    rates.baseKeep rates.baseKeep_le_one who past view
  · intro owner event payload binding action
    simpa only [PhaseProposalRates.zero, mix_zero] using
      phaseProposalOpeningResponse_retained setup mode runtime leaks bounds rates owner event
        payload binding past view action
  · intro owner event payload binding action
    simpa only [PhaseProposalRates.zero, mix_zero] using
      phaseProposalBindingResponse_retained setup mode runtime leaks bounds plan values rates owner
        event payload binding past view action

end Vegas
