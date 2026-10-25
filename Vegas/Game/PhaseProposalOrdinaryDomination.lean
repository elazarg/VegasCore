/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalBaseDomination
import Vegas.Game.ProposalRecoveryPools

/-! # Ordinary response mass fixed before private preparation noise

The comparison keeps the actual timing, physical-slot and alias kernels. Its
ordinary table is fixed before optimizing source weights, and only the private
bad-preparation component is removed. The comparison law uses BASE classes
directly, since a zero bad rate must not activate support totalization.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Preserve timing, slot exploration and aliases while removing only private
unusable preparation. This is not the all-flags-removed continuation law. -/
def PhaseProposalRates.ordinary (rates : PhaseProposalRates) : PhaseProposalRates :=
  { rates with badPreparation := ⟨0, le_rfl, zero_le_one⟩ }

variable (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
/-- The source constructor's literal pooled table dominates its fixed
ordinary reference. The floor is chosen before pool weights are optimized. -/
theorem phaseProposalPooledDomain_ordinary_domination
    [Fintype setup.proposalRecoveryProtocol.History]
    (finite : setup.program.FiniteBindingTypes) (floor : ℝ)
    (nonnegative : 0 ≤ floor) (bounded : floor ≤ 1)
    (pins : (pool : setup.ProposalRecoveryValuePool) →
      Option (PMF (setup.ProposalRecoveryPoolPart pool)))
    (weights : (pool : setup.ProposalRecoveryValuePool) →
      PMF (setup.ProposalRecoveryPoolPart pool))
    (who : Player) (key : setup.ProposalRecoveryComponent who)
    (value : setup.CommitRecoveryValueChoice who key.1) :
    floor * (setup.commitRecoveryValueReference finite who key.1 value).toReal ≤
      (setup.proposalRecoveryPooledDomainLaw finite floor nonnegative bounded pins weights
        who key value).toReal := by
  unfold Setup.proposalRecoveryPooledDomainLaw
  rw [mix_apply_toReal]
  exact le_add_of_nonneg_right
    (mul_nonneg (sub_nonneg.mpr bounded) ENNReal.toReal_nonneg)

/-- A lower bound on ordinary source draws is not multiplied by the private
bad atom. Missing-query forced failure is compared literally on both sides. -/
theorem phaseProposalBindingResults_ordinary_domination
    (source target : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (floor : ℝ) (nonnegative : 0 ≤ floor) (bounded : floor ≤ 1)
    (domain : ∀ who key value, floor * (source who key value).toReal ≤
      (target who key value).toReal)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (result : PublicationResult (L.Val payload)) :
    ((1 - rates.badPreparation.val) * floor) *
        (phaseProposalBindingResults setup mode runtime leaks plan source rates.ordinary who event
          payload binding past view result).toReal ≤
      (phaseProposalBindingResults setup mode runtime leaks plan target rates who event payload
        binding past view result).toReal := by
  have factorBound : (1 - rates.badPreparation.val) * floor ≤ 1 :=
    (mul_le_of_le_one_left nonnegative (by linarith [rates.badPreparation.property.1])).trans
      bounded
  unfold phaseProposalBindingResults
  split
  · exact mul_le_of_le_one_left ENNReal.toReal_nonneg factorBound
  · rename_i key present
    simp only [PhaseProposalRates.ordinary, mix_zero]
    have lower := map_prob_domination (source who key) (target who key) floor (domain who key)
      (fun value => PublicationResult.success
        (phaseRecoveryDomainValue setup mode event who payload binding value.val.val)) result
    rw [mix_apply_toReal]
    have weighted := mul_le_mul_of_nonneg_left lower
      (sub_nonneg.mpr rates.badPreparation.property.2)
    have extra : 0 ≤ rates.badPreparation.val * ((PMF.pure
        (PublicationResult.failure : PublicationResult (L.Val payload))) result).toReal :=
      mul_nonneg rates.badPreparation.property.1 ENNReal.toReal_nonneg
    nlinarith

private theorem ordinary_encoder_lower
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (source target : List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (rates : PhaseProposalRates) (factor : ℝ) (bounded : factor ≤ 1)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (lower : ∀ result, factor * (source past view result).toReal ≤
      (target past view result).toReal) (response : (app).Action) :
    factor * (PhaseCount.bindingResultEncoder runtime leaks bounds who event payload source
        rates.slots.val rates.slots.property.1 rates.slots.property.2 past view response).toReal ≤
      (PhaseCount.bindingResultEncoder runtime leaks bounds who event payload target
        rates.slots.val rates.slots.property.1 rates.slots.property.2 past view
        response).toReal := by
  classical
  have allocator : ∀ value, factor * (PhaseCount.phaseBindingPolicy runtime leaks bounds who event
      payload source past view value).toReal ≤
      (PhaseCount.phaseBindingPolicy runtime leaks bounds who event payload target
        past view value).toReal := by
    intro value
    unfold PhaseCount.phaseBindingPolicy
    split
    · exact mul_le_of_le_one_left ENNReal.toReal_nonneg bounded
    · split
      · exact map_prob_domination _ _ factor lower _ value
      · exact mul_le_of_le_one_left ENNReal.toReal_nonneg bounded
  have slots : ∀ value, factor * (PhaseCount.phaseBindingSlotPolicy runtime leaks bounds who event
      payload source past view value).toReal ≤
      (PhaseCount.phaseBindingSlotPolicy runtime leaks bounds who event payload target
        past view value).toReal := by
    intro value
    unfold PhaseCount.phaseBindingSlotPolicy
    split
    · simpa only [one_mul] using bind_supported_domination _ _ _ _ 1 factor zero_le_one
        (fun _ => by simp only [one_mul]; exact le_rfl)
        (fun serial _ chosen => map_prob_domination _ _ factor lower _ chosen) value
    · exact mul_le_of_le_one_left ENNReal.toReal_nonneg bounded
  exact mix_prob_domination rates.slots _ _ _ _ factor slots allocator response

/-- The actual BASE response law dominates an ordinary-only comparison on
every literal native input. Timing and slot parameters remain unchanged, so
the comparison supplies floors for every eligible slot, not only the allocator. -/
theorem phaseProposalBasePolicy_ordinary_domination
    (source target : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (floor : ℝ) (nonnegative : 0 ≤ floor) (bounded : floor ≤ 1)
    (domain : ∀ who key value, floor * (source who key value).toReal ≤
      (target who key value).toReal)
    (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (response : (app).Action) :
    ((1 - rates.badPreparation.val) * floor) *
        (phaseProposalBasePolicy setup mode runtime leaks bounds plan source rates.ordinary who
          past view response).toReal ≤
      (phaseProposalBasePolicy setup mode runtime leaks bounds plan target rates who
        past view response).toReal := by
  let factor := (1 - rates.badPreparation.val) * floor
  have factorBound : factor ≤ 1 :=
    (mul_le_of_le_one_left nonnegative (by linarith [rates.badPreparation.property.1])).trans
      bounded
  unfold phaseProposalBasePolicy
  apply phasePolicyDispatch_probability_domination setup mode runtime leaks _ _ _ _
    factor factorBound who past view
  · intro owner event payload binding action
    exact mul_le_of_le_one_left ENNReal.toReal_nonneg factorBound
  · intro owner event payload binding action
    apply mix_prob_domination rates.waiting _ _ _ _ factor
    · exact fun _ => mul_le_of_le_one_left ENNReal.toReal_nonneg factorBound
    · intro chosen
      exact ordinary_encoder_lower setup mode runtime leaks bounds owner event payload _ _ rates
        factor factorBound past view
        (phaseProposalBindingResults_ordinary_domination setup mode runtime leaks plan source
          target rates floor nonnegative bounded domain owner event payload binding past view)
        chosen

/-- Split the ordinary-only BASE classes in their actual raw preimages. This
comparison deliberately bypasses the full-support reference's totalization. -/
def phaseProposalOrdinaryResponses
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView) : PMF (PhaseProposal.Response runtime leaks bounds who past view) :=
  PhaseProposal.splitResponseLaw runtime leaks bounds who past view
    (phaseProposalBaseClasses setup mode runtime leaks bounds plan values rates.ordinary who
      past view) rates.aliases.val rates.aliases.property.1 rates.aliases.property.2

/-- Ordinary-only response sampling still uses each actual counted preimage;
absence of a bad atom does not totalize or enlarge a menu. -/
def phaseProposalOrdinaryPolicy
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player) : (app).Policy := fun past view =>
  (phaseProposalOrdinaryResponses setup mode runtime leaks bounds plan values rates who past
    view).map Subtype.val

theorem phaseProposalOrdinaryPolicy_covered
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView) (response : (app).Action)
    (supported : response ∈ (phaseProposalOrdinaryPolicy setup mode runtime leaks bounds plan
      values rates who past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  obtain ⟨chosen, _selected, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact chosen.property

/-- Positive alias noise supports every literal preimage of a supported
ordinary class, even though other classes can have zero ordinary mass. -/
theorem phaseProposalOrdinaryResponses_mem_of_class
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (aliases : 0 < rates.aliases.val) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (response : PhaseProposal.Response runtime leaks bounds who past view)
    (selected : PhaseProposal.projectResponse runtime leaks bounds who past view response ∈
      (phaseProposalBaseClasses setup mode runtime leaks bounds plan values rates.ordinary who
        past view).support) :
    response ∈ (phaseProposalOrdinaryResponses setup mode runtime leaks bounds plan values rates
      who past view).support := by
  apply (PMF.mem_support_bind_iff _ _ _).mpr
  refine ⟨PhaseProposal.projectResponse runtime leaks bounds who past view response, selected, ?_⟩
  apply mem_support_mix_left _ _ _ aliases
  exact (PMF.fiberUniform_supported _ _ _ _ response).mpr rfl

/-- Genuine support removal plus exact actual preimage splitting turns the
ordinary table floor into a raw response floor. No conditional reach enters. -/
theorem phaseProposalReferenceResponses_ordinary_domination
    (source target : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (floor : ℝ) (nonnegative : 0 ≤ floor) (bounded : floor ≤ 1)
    (domain : ∀ who key value, floor * (source who key value).toReal ≤
      (target who key value).toReal)
    (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (full : FullSupport
      (phaseProposalBaseClasses setup mode runtime leaks bounds plan target rates who past view))
    (response : PhaseProposal.Response runtime leaks bounds who past view) :
    ((1 - rates.badPreparation.val) * floor) *
        (phaseProposalOrdinaryResponses setup mode runtime leaks bounds plan source rates who past
          view response).toReal ≤
      (phaseProposalReferenceResponses setup mode runtime leaks bounds plan target rates who past
        view response).toReal := by
  have attached (chosen : PhaseProposal.Response runtime leaks bounds who past view) :
      ((1 - rates.badPreparation.val) * floor) *
          (phaseProposalBaseResponses setup mode runtime leaks bounds plan source rates.ordinary
            who past view chosen).toReal ≤
        (phaseProposalBaseResponses setup mode runtime leaks bounds plan target rates who past
          view chosen).toReal := by
    have lower := phaseProposalBasePolicy_ordinary_domination setup mode runtime leaks bounds plan
      source target rates floor nonnegative bounded domain who past view chosen.val
    rw [← phaseProposalBaseResponses_map_val setup mode runtime leaks bounds plan source
      rates.ordinary who past view,
      ← phaseProposalBaseResponses_map_val setup mode runtime leaks bounds plan target rates
        who past view] at lower
    simpa only [pmf_map_apply_of_injective _ Subtype.val_injective] using lower
  have classes (chosen : PhaseProposal.ResponseClass runtime leaks bounds who past view) :
      ((1 - rates.badPreparation.val) * floor) *
          (phaseProposalBaseClasses setup mode runtime leaks bounds plan source rates.ordinary who
            past view chosen).toReal ≤
        (phaseProposalBaseClasses setup mode runtime leaks bounds plan target rates who past
          view chosen).toReal := by
    simpa only [phaseProposalBaseClasses, pmf_bind_pure_eq_map] using
      prob_bind_ge_mul _ _ ((1 - rates.badPreparation.val) * floor) attached
        (fun raw => PMF.pure
          (PhaseProposal.projectResponse runtime leaks bounds who past view raw))
        chosen
  unfold phaseProposalOrdinaryResponses phaseProposalReferenceResponses
  rw [phaseProposalReferenceClasses_eq setup mode runtime leaks bounds plan target rates who past
    view full]
  exact prob_bind_ge_mul _ _ ((1 - rates.badPreparation.val) * floor) classes
    (PMF.splitKernel (PhaseProposal.projectResponse runtime leaks bounds who past view)
      (PhaseProposal.canonicalResponse runtime leaks bounds who past view)
      (PhaseProposal.project_canonicalResponse runtime leaks bounds who past view)
      rates.aliases.val rates.aliases.property.1 rates.aliases.property.2) response

end Vegas
