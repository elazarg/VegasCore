/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalBaseDomination

/-! # Prospective reference-response error without qualification conditioning -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Retain the current ordinary draw and the canonical representative, removing
only four prospective perturbation flags. -/
def PhaseProposalRates.keep (rates : PhaseProposalRates) : ℝ :=
  rates.baseKeep * (1 - rates.aliases.val)

/-- A union bound for newly selected flags; flags already present in the
literal execution are outside this quantity. -/
def PhaseProposalRates.flagBound (rates : PhaseProposalRates) : ℝ :=
  rates.waiting.val + rates.badPreparation.val + rates.slots.val + rates.aliases.val

theorem PhaseProposalRates.keep_nonnegative (rates : PhaseProposalRates) :
    0 ≤ rates.keep :=
  mul_nonneg rates.baseKeep_nonnegative (sub_nonneg.mpr rates.aliases.property.2)

theorem PhaseProposalRates.keep_le_one (rates : PhaseProposalRates) : rates.keep ≤ 1 :=
  (mul_le_of_le_one_right rates.baseKeep_nonnegative
    (by linarith [rates.aliases.property.1])).trans rates.baseKeep_le_one

theorem PhaseProposalRates.keep_lt_one (rates : PhaseProposalRates)
    (waiting : 0 < rates.waiting.val) : rates.keep < 1 := by
  have below : rates.keep ≤ rates.baseKeep :=
    mul_le_of_le_one_right rates.baseKeep_nonnegative
      (by linarith [rates.aliases.property.1])
  exact (below.trans rates.baseKeep_le_waiting).trans_lt (by linarith)

private theorem product_missing_le (first second : ℝ) (firstBound : first ≤ 1)
    (secondBound : second ≤ 1) : 1 - first * second ≤ (1 - first) + (1 - second) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr firstBound) (sub_nonneg.mpr secondBound)]

theorem PhaseProposalRates.missing_keep_le (rates : PhaseProposalRates) :
    1 - rates.keep ≤ rates.flagBound := by
  have bs := product_missing_le (1 - rates.slots.val) (1 - rates.badPreparation.val)
    (by linarith [rates.slots.property.1])
    (by linarith [rates.badPreparation.property.1])
  have bsBound : (1 - rates.slots.val) * (1 - rates.badPreparation.val) ≤ 1 :=
    (mul_le_of_le_one_left (sub_nonneg.mpr rates.badPreparation.property.2)
      (by linarith [rates.slots.property.1])).trans
        (by linarith [rates.badPreparation.property.1])
  have wbs := product_missing_le (1 - rates.waiting.val)
    ((1 - rates.slots.val) * (1 - rates.badPreparation.val))
    (by linarith [rates.waiting.property.1]) bsBound
  have all := product_missing_le rates.baseKeep (1 - rates.aliases.val)
    rates.baseKeep_le_one (by linarith [rates.aliases.property.1])
  unfold PhaseProposalRates.keep PhaseProposalRates.flagBound PhaseProposalRates.baseKeep
  unfold PhaseProposalRates.baseKeep at all
  linarith

variable (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks

/-- The BASE response subtype uses the same menu at both rates. Its attached
membership proofs do not introduce a likelihood factor. -/
theorem phaseProposalBaseResponses_retained
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView)
    (response : PhaseProposal.Response runtime leaks bounds who past view) :
    rates.baseKeep *
        (phaseProposalBaseResponses setup mode runtime leaks bounds plan values
          PhaseProposalRates.zero who past view response).toReal ≤
      (phaseProposalBaseResponses setup mode runtime leaks bounds plan values rates who past view
        response).toReal := by
  have lower := phaseProposalBasePolicy_retained setup mode runtime leaks bounds plan values rates
    who past view response.val
  rw [← phaseProposalBaseResponses_map_val setup mode runtime leaks bounds plan values
    PhaseProposalRates.zero who past view,
    ← phaseProposalBaseResponses_map_val setup mode runtime leaks bounds plan values rates
      who past view] at lower
  simpa only [pmf_map_apply_of_injective _ Subtype.val_injective] using lower

/-- Summation over actual packet/preparation classes preserves BASE retained
mass. No equality of foreign private catalogues or literal own records is used. -/
theorem phaseProposalBaseClasses_retained
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView)
    (chosen : PhaseProposal.ResponseClass runtime leaks bounds who past view) :
    rates.baseKeep *
        (phaseProposalBaseClasses setup mode runtime leaks bounds plan values
          PhaseProposalRates.zero who past view chosen).toReal ≤
      (phaseProposalBaseClasses setup mode runtime leaks bounds plan values rates who past view
        chosen).toReal := by
  simpa only [phaseProposalBaseClasses, pmf_bind_pure_eq_map] using
    prob_bind_ge_mul _ _ rates.baseKeep
      (phaseProposalBaseResponses_retained setup mode runtime leaks bounds plan values rates
        who past view)
      (fun response => PMF.pure
        (PhaseProposal.projectResponse runtime leaks bounds who past view response)) chosen

/-- Once the genuine-menu support adapter removes the totalization branch,
the actual reference contains the unflagged law with a uniform retained mass.
This is a local adapter: the support premise is discharged from counted shapes
and the genuine query before any execution or incentive theorem uses it. -/
theorem phaseProposalReferenceResponses_retained
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView)
    (full : FullSupport
      (phaseProposalBaseClasses setup mode runtime leaks bounds plan values rates who past view))
    (response : PhaseProposal.Response runtime leaks bounds who past view) :
    rates.keep *
        (phaseProposalUnflaggedResponses setup mode runtime leaks bounds plan values who past view
          response).toReal ≤
      (phaseProposalReferenceResponses setup mode runtime leaks bounds plan values rates who
        past view response).toReal := by
  classical
  unfold phaseProposalReferenceResponses
  rw [phaseProposalReferenceClasses_eq setup mode runtime leaks bounds plan values rates who
    past view full]
  unfold PhaseProposal.splitResponseLaw phaseProposalUnflaggedResponses
  rw [← PMF.bind_pure_comp]
  apply bind_supported_domination _ _ _ _ rates.baseKeep (1 - rates.aliases.val)
    rates.baseKeep_nonnegative
    (phaseProposalBaseClasses_retained setup mode runtime leaks bounds plan values rates
      who past view)
  intro chosen _supported value
  unfold PMF.splitKernel
  rw [mix_apply_toReal]
  exact le_add_of_nonneg_left (mul_nonneg rates.aliases.property.1 ENNReal.toReal_nonneg)

/-- Full native response laws, including their actual raw aliases, differ by
at most the prospective flag sum at this unchanged input. No future receipt,
qualification event or no-fault event is conditioned on. -/
theorem phaseProposalReferencePolicy_unflagged_close
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView)
    (full : FullSupport
      (phaseProposalBaseClasses setup mode runtime leaks bounds plan values rates who past view)) :
    PMF.WithinTV rates.flagBound
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who past view)
      (phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates who
        past view) := by
  apply PMF.WithinTV.mono rates.missing_keep_le
  exact (PMF.WithinTV.of_domination _ _ rates.keep rates.keep_le_one
    (phaseProposalReferenceResponses_retained setup mode runtime leaks bounds plan values rates
      who past view full)).map Subtype.val

/-- Forgetting subtype witnesses also preserves the retained mass pointwise.
This supplies the actual raw response kernel used in scheduler rounds. -/
theorem phaseProposalReferencePolicy_retained
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView)
    (full : FullSupport
      (phaseProposalBaseClasses setup mode runtime leaks bounds plan values rates who past view))
    (response : (app).Action) :
    rates.keep *
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who past view
          response).toReal ≤
      (phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates who
        past view response).toReal := by
  simpa only [phaseProposalUnflaggedPolicy, phaseProposalReferencePolicy,
    pmf_bind_pure_eq_map] using
    prob_bind_ge_mul _ _ rates.keep
      (phaseProposalReferenceResponses_retained setup mode runtime leaks bounds plan values rates
        who past view full) (fun response => PMF.pure response.val) response

/-- An exact actual-policy realization of the clean prospective branch. A
fresh current Bernoulli flag has probability `1-keep`; before that flag the
ordinary draw and actual unflagged response law are unchanged. The residual
is covered by the same menu, so this does not introduce a fictitious action.
The genuine support adapter is discharged before this local lemma is used. -/
theorem phaseProposalReferencePolicy_decompose
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (waiting : 0 < rates.waiting.val)
    (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (full : FullSupport
      (phaseProposalBaseClasses setup mode runtime leaks bounds plan values rates who past view)) :
    ∃ residual : PMF (app).Action,
      mix rates.keep rates.keep_nonnegative (rates.keep_lt_one waiting).le
          (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who past view)
          residual =
        phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates who
          past view ∧
      ∀ response ∈ residual.support,
        response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  obtain ⟨residual, same⟩ := exists_mix_eq_of_le
    (phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates who past view)
    (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who past view)
    rates.keep rates.keep_nonnegative (rates.keep_lt_one waiting)
    (phaseProposalReferencePolicy_retained setup mode runtime leaks bounds plan values rates who
      past view full)
  refine ⟨residual, same, ?_⟩
  intro response supported
  apply phaseProposalReferencePolicy_covered setup mode runtime leaks bounds plan values rates who
    past view response
  rw [← same]
  exact mem_support_mix_right _ _ _ (rates.keep_lt_one waiting) supported

end Vegas
