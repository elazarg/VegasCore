/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateResolutionNativeContinuation
import Interaction.ReactiveMenuPolicy
import Interaction.ReactiveFiniteAssessment
import GameTheoryExtensions.Protocol.ContinuationHorizon
import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion

/-! # Native continuation regret at the actual late information fiber

Every history at this information site has the same audited waiting value and
the same legal explicit-FALSE alternative. Thus the comparison holds for any
assessment belief, including beliefs justified by fully mixed native play.
It does not rule out rational completion with a different policy at this site.
-/

noncomputable section

namespace Vegas.LateResolutionService

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory GameTheory.Math.Probability

theorem late_history_info (bounds : MessageBounds nativeGraph)
    (witness : app.Execution)
    (trace : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, witness⟩))
    (history : (nativeModel bounds).InformationHistory owner (lateSite bounds witness trace).1)
    (execution : app.Execution) (current : history.1.state = some ⟨4, some owner, execution⟩) :
    some (execution.recall owner, execution.observe app owner) =
      (lateSite bounds witness trace).1 := by
  have observed := ((nativeMenu bounds).info (initialLaw setup) horizon scheduler owner
    history.1.trace).symm.trans history.2
  rw [current] at observed
  simpa only [ReactiveApplication.observe, ↓reduceIte] using observed

section Values

variable (bounds : MessageBounds nativeGraph) (witness : app.Execution)
  (trace : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).Trace
    (some ⟨4, some owner, witness⟩))
  (ready : witness.application.config.cut.Ready resolution)
  (entered : witness.application.activatedAt resolution = some 0)
  (clock : witness.application.clock = 1) (empty : witness.network = .empty)
  (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
  (deposit : ℝ) (assessment : (nativeModel bounds).BehavioralAssessment)

include ready entered clock empty

theorem late_context_wait_value
    (waits : (assessment.strategy owner (lateSite bounds witness trace).1).map Subtype.val =
      PMF.pure (some ⟨none⟩)) :
    (assessment.truncatedContinuationContext (lateSite bounds witness trace)
      (fun final => auditedUtility sample deposit final.state owner) 21).value
        (assessment.strategy owner) = -deposit := by
  rw [InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
    Profile.update_eq_self, expect_bind_of_finite]
  calc
    _ = expect (assessment.belief owner (lateSite bounds witness trace))
        (fun _ => -deposit) := by
      apply expect_congr_on_support
      intro history _
      obtain ⟨execution, current, position, actualClock, actualReady, actualEntered, actualEmpty⟩ :=
        late_information_resources bounds witness trace ready entered clock empty history
      rw [late_native_response_value (nativeMenu bounds) assessment.strategy history.1
        execution current
        position ⟨none⟩ (by
          rw [late_history_info bounds witness trace history execution current]
          exact waits) (fun state => auditedUtility sample deposit state owner)]
      exact late_silence_value execution position actualReady actualEntered actualClock actualEmpty
        sample deposit
    _ = _ := expect_constant _ _

theorem late_context_false_value (candidate : Handle nativeGraph)
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (alternative : (nativeModel bounds).BehavioralPolicy owner)
    (chooses : (alternative (lateSite bounds witness trace).1).map Subtype.val =
      PMF.pure (some (lateResponse candidate false))) :
    (assessment.truncatedContinuationContext (lateSite bounds witness trace)
      (fun final => auditedUtility sample deposit final.state owner) 21).value alternative = 0 := by
  rw [InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
    expect_bind_of_finite]
  calc
    _ = expect (assessment.belief owner (lateSite bounds witness trace)) (fun _ => (0 : ℝ)) := by
      apply expect_congr_on_support
      intro history _
      obtain ⟨execution, current, position, actualClock, actualReady, actualEntered, actualEmpty⟩ :=
        late_information_resources bounds witness trace ready entered clock empty history
      rw [late_native_response_value (nativeMenu bounds) _ history.1 execution current position
        (lateResponse candidate false) (by
          rw [late_history_info bounds witness trace history execution current,
            Profile.update_same]
          exact chooses) (fun state => auditedUtility sample deposit state owner)]
      exact late_continuation_value execution candidate
        ((nativeMenu bounds).toRawTrace (initialLaw setup) horizon scheduler
          (current ▸ history.1.trace)) position actualReady actualEntered actualClock actualEmpty
          sample authentic deposit false
    _ = _ := expect_constant _ _

theorem late_wait_not_locally_optimal
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (positive : 0 < deposit)
    (waits : (assessment.strategy owner (lateSite bounds witness trace).1).map Subtype.val =
      PMF.pure (some ⟨none⟩)) :
    ¬ (assessment.truncatedContinuationContext (lateSite bounds witness trace)
      (fun final => auditedUtility sample deposit final.state owner) 21).IsLocallyOptimal
        Set.univ (assessment.strategy owner) := by
  classical
  let candidate : Handle nativeGraph := ⟨owner, .prepared 0⟩
  let choice : (nativeModel bounds).Choice owner (lateSite bounds witness trace).1 :=
    ⟨some (lateResponse candidate false), lateResponse candidate false,
      late_withhold_available bounds witness trace ready entered clock empty candidate, rfl⟩
  let alternative := (assessment.strategy owner).withLaw (lateSite bounds witness trace).1
    (PMF.pure choice)
  have chooses : (alternative (lateSite bounds witness trace).1).map Subtype.val =
      PMF.pure (some (lateResponse candidate false)) := by
    simp only [alternative, InformationModel.BehavioralPolicy.withLaw_self, PMF.pure_map]
    rfl
  intro optimal
  have inequality := (Context.isLocallyOptimal_iff_of_integrable
    (payoffIntegrable_of_finite _ _) (fun _ _ => payoffIntegrable_of_finite _ _)).mp
      optimal alternative (Set.mem_univ _)
  rw [late_context_wait_value bounds witness trace ready entered clock empty sample deposit
    assessment waits,
    late_context_false_value bounds witness trace ready entered clock empty sample deposit
      assessment candidate authentic alternative chooses] at inequality
  linarith

end Values

/-- The finite-menu representation of the actual turn policy, with no claimed
equilibrium property at inputs where it prescribes waiting. -/
def nativeTurnProfile (bounds : MessageBounds nativeGraph) (turns : Nat)
    (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program) :
    ∀ who, (nativeModel bounds).BehavioralPolicy who := fun who =>
  (nativeMenu bounds).restrictPolicy (initialLaw setup) horizon scheduler who
    (sourceServiceTurnPolicy setup leaks bound turns timing profile who)

theorem late_nativeTurnProfile_waits (bounds : MessageBounds nativeGraph)
    (witness : app.Execution) (ready : witness.application.config.cut.Ready resolution)
    (entered : witness.application.activatedAt resolution = some 0)
    (clock : witness.application.clock = 1) (turns : Nat)
    (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program) :
    ((nativeTurnProfile bounds turns timing profile owner)
      (some (witness.recall owner, witness.observe app owner))).map Subtype.val =
        PMF.pure (some ⟨none⟩) := by
  have silent := late_turnPolicy_silent witness ready entered clock turns timing profile
  have covered : ∀ response ∈ (sourceServiceTurnPolicy setup leaks bound turns timing profile
      owner (witness.recall owner) (witness.observe app owner)).support,
      response ∈ (nativeMenu bounds).actions owner (witness.recall owner)
        (witness.observe app owner) := by
    rw [silent]
    intro response supported
    have same := (PMF.mem_support_pure_iff _ _).mp supported
    subst response
    exact silence_risk bounds owner _ _
  change (((nativeMenu bounds).restrictPolicy (initialLaw setup) horizon scheduler owner
    (sourceServiceTurnPolicy setup leaks bound turns timing profile owner))
      (some (witness.recall owner, witness.observe app owner))).map Subtype.val = _
  rw [(nativeMenu bounds).restrictPolicy_map_val (initialLaw setup) horizon scheduler owner
    _ _ _ covered, silent, PMF.pure_map]

theorem nativeTurnProfile_not_sequentially_rational
    (bounds : MessageBounds nativeGraph)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) (positive : 0 < deposit) (turns : Nat)
    (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (assessment : (nativeModel bounds).BehavioralAssessment)
    (strategy : assessment.strategy = nativeTurnProfile bounds turns timing profile) :
    ¬ assessment.IsSequentiallyRationalFor (fun who site =>
      assessment.truncatedContinuationContext site
        (fun final => auditedUtility sample deposit final.state who) 21) := by
  obtain ⟨before, witness, _, _, _, ⟨trace⟩, _, clock, ready, entered, empty⟩ :=
    exists_late_risk_turn bounds
  have waits : (assessment.strategy owner (lateSite bounds witness trace).1).map Subtype.val =
      PMF.pure (some ⟨none⟩) := by
    rw [strategy]
    exact late_nativeTurnProfile_waits bounds witness ready entered clock turns timing profile
  intro rational
  exact late_wait_not_locally_optimal bounds witness trace ready entered clock empty sample
    deposit assessment authentic positive waits (rational owner (lateSite bounds witness trace))

theorem nativeCertificate (bounds : MessageBounds nativeGraph) :
    ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).WellFoundedHistories :=
  ((nativeMenu bounds).bounded (initialLaw setup) horizon scheduler).wellFoundedHistories

/-- No choice of native beliefs can make this prescribed waiting policy a
sequential equilibrium. A different completion at late inputs remains possible. -/
theorem nativeTurnProfile_not_sequential_equilibrium
    (bounds : MessageBounds nativeGraph)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) (positive : 0 < deposit) (turns : Nat)
    (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (assessment : (nativeModel bounds).BehavioralAssessment)
    (strategy : assessment.strategy = nativeTurnProfile bounds turns timing profile) :
    ¬ assessment.IsSequentialEquilibrium
      ((nativeMenu bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler)
      (nativeCertificate bounds)
      (fun who final => auditedUtility sample deposit final.state who) := by
  intro equilibrium
  have bounded :
      ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).BoundedHorizon 21 := by
    exact (nativeMenu bounds).bounded (initialLaw setup) horizon scheduler
  have rational := ((assessment.isSequentialEquilibrium_iff_truncated_of_bounded
    (nativeModel bounds)
    ((nativeMenu bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler)
    (nativeCertificate bounds) bounded
    (fun who final => auditedUtility sample deposit final.state who)).mp equilibrium).1
  exact nativeTurnProfile_not_sequentially_rational bounds sample authentic deposit positive
    turns timing profile assessment strategy rational

/-- Consistent native beliefs exist for the restricted policy, but they cannot
repair its strict waiting regret at the actual late information site. -/
theorem exists_consistent_native_turn_obstruction
    (bounds : MessageBounds nativeGraph)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) (positive : 0 < deposit) (turns : Nat)
    (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program) :
    ∃ assessment : (nativeModel bounds).BehavioralAssessment,
      assessment.strategy = nativeTurnProfile bounds turns timing profile ∧
      assessment.IsSequentiallyConsistent
        ((nativeMenu bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler) ∧
      ¬ assessment.IsSequentialEquilibrium
        ((nativeMenu bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler)
        (nativeCertificate bounds)
        (fun who final => auditedUtility sample deposit final.state who) := by
  obtain ⟨assessment, strategy, consistent⟩ :=
    InformationModel.BehavioralAssessment.exists_consistent_completion
      ((nativeMenu bounds).uniformAssessment (initialLaw setup) horizon scheduler)
      ((nativeMenu bounds).uniform_fullyMixed (initialLaw setup) horizon scheduler)
      ((nativeMenu bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler)
      (nativeTurnProfile bounds turns timing profile)
  exact ⟨assessment, strategy, consistent,
    nativeTurnProfile_not_sequential_equilibrium bounds sample authentic deposit positive
      turns timing profile assessment strategy⟩

end Vegas.LateResolutionService
