/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.DisclosureAssessment
import GameTheoryExtensions.Math.Probability.ObservationRetraction

/-! # Source assessment comparisons after an owner-visible response

Condition the actual normalized source prefix on a response determined by the
owner's source observation. Distinct observations and erased private disclosure
intentions can produce that response. Both continuation laws are represented by
one finite mixture of deviations in the original source assessment. The
conditioning law is constructed from the source execution; no posterior
equality or normalized sequential equilibrium is assumed.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (admission : CommitmentInterface setup.program)
  [∀ who (site : (setup.informationModel admission).InformationSite who),
    Fintype ((setup.informationModel admission).InformationHistory who site.1)]

/-- A positive physical-response projection may merge normalized views as
well as private original intentions. It still selects a common mixture of
actual original source comparisons, retaining both terminal laws exactly. -/
theorem normalized_disclosure_response_comparison
    (assessment : (setup.informationModel admission).BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (setup.informationModel admission) assessment (setup.decision_antichain admission))
    (count : Nat) :
    let profile := setup.decodeBehavioralProfile admission assessment.strategy
    let normalized := normalizeDisclosureProfile setup.program []
      (Revelations.initial setup.context) profile
    let prefixLaw := (setup.initialLaw.map setup.initialConfig).bind fun config =>
      (fun distribution => distribution.bind (ProtocolState.behavioralStateStep setup.program
        normalized))^[count] (FinDist.pure (ProtocolState.entry setup.program config))
    ∀ who (alternative : BehavioralPolicy who setup.program),
      alternative.Admitted setup.program admission →
      ∀ {Response : Type} (respond : SourceProgram.ProtocolView who setup.program → Response)
        (response : Response),
      response ∈ (prefixLaw.map (respond ∘ ProtocolState.observe who setup.program)).support →
      (∀ view ∈ (prefixLaw.map (ProtocolState.observe who setup.program)).support,
        respond view = response → SourceProgram.ProtocolView.actor who setup.program view =
          some who) →
      ∃ mixture : FinDist ((setup.informationModel admission).AssessmentDeviation who),
        (((prefixLaw.condOnFibre (respond ∘ ProtocolState.observe who setup.program) response).bind
          (ProtocolState.continuationLaw setup.program normalized)).map some) =
          mixture.bind (fun deviation => ((setup.informationModel admission).assessmentComparison
            (fun final => setup.protocolReadout final.state) (instructionCount setup.program + 1)
              assessment who deviation).prescribed) ∧
        (((prefixLaw.condOnFibre (respond ∘ ProtocolState.observe who setup.program) response).bind
          (ProtocolState.continuationLaw setup.program
            (Function.update normalized who alternative))).map some) =
          mixture.bind (fun deviation => ((setup.informationModel admission).assessmentComparison
            (fun final => setup.protocolReadout final.state) (instructionCount setup.program + 1)
              assessment who deviation).alternative) := by
  classical
  dsimp only
  intro who alternative admitted Response respond response present active
  let profile := setup.decodeBehavioralProfile admission assessment.strategy
  let normalized := normalizeDisclosureProfile setup.program []
    (Revelations.initial setup.context) profile
  let prefixLaw := (setup.initialLaw.map setup.initialConfig).bind fun config =>
    (fun distribution => distribution.bind (ProtocolState.behavioralStateStep setup.program
      normalized))^[count] (FinDist.pure (ProtocolState.entry setup.program config))
  let observe := ProtocolState.observe who setup.program
  let conditioned := prefixLaw.condOnFibre (respond ∘ observe) response
  let views := conditioned.map observe
  obtain ⟨witness, supported, responded⟩ := FinDist.support_map .. ▸ present
  have meets : ∃ state ∈ (respond ∘ observe) ⁻¹' {response}, state ∈ prefixLaw.support :=
    ⟨witness, responded, supported⟩
  have viewSupport (view) (member : view ∈ views.support) :
      view ∈ (prefixLaw.map observe).support ∧ respond view = response := by
    obtain ⟨state, stateSupported, stateView⟩ := FinDist.support_map .. ▸ member
    change state ∈ (prefixLaw.condOnFibre (respond ∘ observe) response).support at stateSupported
    rw [FinDist.condOnFibre, dite_eq_left meets] at stateSupported
    obtain ⟨stateResponse, statePresent⟩ := FinDist.support_condOn _ _ _ stateSupported
    refine ⟨FinDist.support_map .. ▸ ⟨state, statePresent, stateView⟩, ?_⟩
    change respond (observe state) = response at stateResponse
    rwa [stateView] at stateResponse
  have comparisons (view) (member : view ∈ views.support) :=
    setup.normalized_disclosure_assessment_comparison admission assessment mixed bayes count
      who alternative admitted view (viewSupport view member).1
        (active view (viewSupport view member).1 (viewSupport view member).2)
  let mixture := views.bindOnSupport fun view member => (comparisons view member).choose
  have conditionedLaw : conditioned = views.bind (prefixLaw.condOnFibre observe) := by
    conv_lhs => rw [conditioned.eq_bind_condOnFibre observe]
    apply FinDist.bind_congr
    intro view member
    exact FinDist.conditional_fiber_after_projection prefixLaw observe respond response view member
  refine ⟨mixture, ?_, ?_⟩
  · change (conditioned.bind (ProtocolState.continuationLaw setup.program normalized)).map some = _
    rw [conditionedLaw, FinDist.bind_bind, FinDist.map_bind]
    symm
    change (views.bindOnSupport _).bind _ = _
    rw [FinDist.bind_bindOnSupport]
    apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
    intro view member
    exact (comparisons view member).choose_spec.1.symm
  · change (conditioned.bind (ProtocolState.continuationLaw setup.program
      (Function.update normalized who alternative))).map some = _
    rw [conditionedLaw, FinDist.bind_bind, FinDist.map_bind]
    symm
    change (views.bindOnSupport _).bind _ = _
    rw [FinDist.bind_bindOnSupport]
    apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
    intro view member
    exact (comparisons view member).choose_spec.2.symm

end Vegas.SourceProgram.Setup
