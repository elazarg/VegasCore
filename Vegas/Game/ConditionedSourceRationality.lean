module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ConditionedSourceContinuation
public import Vegas.Game.ConditionedSourceEquilibrium

@[expose] public section

/-! # Sequential equilibrium within an observed initial component -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Finite Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  {Signal : Type*} (signal : State L setup.context → Signal) (value : Signal)
  (supported : value ∈ (setup.initialLaw.map signal).support)
  (inside : ∀ who (site : (setup.conditionInitial signal value).intendedModel.InformationSite who)
    (history : setup.intendedModel.InformationHistory who site.1),
    setup.initialComponent signal value history.1.state)

omit [Finite Player] in
private theorem conditionInitial_policy_surjective (who : Player) :
    Function.Surjective (setup.conditionInitial_policy signal value who) := by
  intro alternative
  refine ⟨fun view => (alternative view).map
    (setup.conditionInitial_choiceEquiv signal value who view), ?_⟩
  funext view
  simp [conditionInitial_policy, PMF.map_comp, PMF.map_id]

private theorem conditionInitial_context_outcome (A : setup.intendedModel.BehavioralAssessment)
    (who : Player) (site : (setup.conditionInitial signal value).intendedModel.InformationSite who)
    (payoff : setup.intendedProtocol.History → ℝ) (fuel : Nat)
    (alternative : setup.intendedModel.BehavioralPolicy who) :
    let embed := setup.conditionInitial_history signal value supported
    let restricted := setup.conditionInitial_assessment signal value supported inside A
    (((restricted.truncatedContinuationContext site (payoff ∘ embed) fuel).outcome
      (setup.conditionInitial_policy signal value who alternative)).map embed) =
      (A.truncatedContinuationContext (setup.conditionInitial_informationSite signal value
        supported site) payoff fuel).outcome alternative := by
  classical
  let restricted := setup.conditionInitial_assessment signal value supported inside A
  let updated := Profile.update (sig := setup.intendedModel.behavioralSignature)
    A.strategy who alternative
  have profiles : Profile.update (sig := (setup.conditionInitial signal value).intendedModel
      |>.behavioralSignature) restricted.strategy who
        (setup.conditionInitial_policy signal value who alternative) =
      fun i => setup.conditionInitial_policy signal value i (updated i) := by
    funext i
    by_cases eq : i = who
    · subst i
      simp only [updated, Profile.update_same]
    · simp only [updated, Profile.update_of_ne _ _ eq]
      rfl
  change PMF.map _ ((restricted.belief who site).bind fun h =>
    (setup.conditionInitial signal value).intendedModel.runBehavioralFrom _ fuel h.1) =
    (A.belief who _).bind fun h => setup.intendedModel.runBehavioralFrom updated fuel h.1
  rw [profiles, PMF.map_bind, ← setup.conditionInitial_assessment_belief_map
    signal value supported inside A who site, PMF.bind_map]
  apply bind_congr_on_support
  intro history _
  apply setup.conditionInitial_runBehavioralFrom
  intro root
  have active := InformationModel.InformationSite.active
    (M := (setup.conditionInitial signal value).intendedModel) site history
  rw [root] at active
  exact active

/-- If every decision view in a supported component identifies it, restriction of
any intended sequential equilibrium is an intended sequential equilibrium there. -/
theorem conditionInitial_intendedSequentialEquilibrium
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (A : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium parameter utility A) :
    (setup.conditionInitial signal value).IntendedSequentialEquilibrium parameter utility
      (setup.conditionInitial_assessment signal value supported inside A) := by
  classical
  let restricted := setup.conditionInitial_assessment signal value supported inside A
  let embed := setup.conditionInitial_history signal value supported
  let payoff := fun who (h : setup.intendedProtocol.History) =>
    (setup.protocolReadout h.state).elim 0
      (fun terminal => utility (setup.parameterOutcome parameter terminal) who)
  refine ⟨?_, setup.conditionInitial_assessment_consistent signal value supported inside A
    equilibrium.2⟩
  apply (restricted.isSequentiallyRational_iff_truncated_of_bounded _
    (setup.conditionInitial signal value).intended_bounded (fun who => payoff who ∘ embed)).mpr
  intro who site
  let original := A.truncatedContinuationContext
    (setup.conditionInitial_informationSite signal value supported site) (payoff who)
    (instructionCount setup.program + 1)
  let conditional := restricted.truncatedContinuationContext site (payoff who ∘ embed)
    (instructionCount setup.program + 1)
  let restrict := setup.conditionInitial_policy signal value who
  have optimal := (A.isSequentiallyRational_iff_truncated_of_bounded _
    setup.intended_bounded payoff).mp equilibrium.1 who
      (setup.conditionInitial_informationSite signal value supported site)
  have outcomes (a) : ((conditional.outcome (restrict a)).map embed) = original.outcome a :=
    setup.conditionInitial_context_outcome signal value supported inside A who site _ _ a
  have admissible (a) : conditional.HasValueAt (restrict a) ↔ original.HasValueAt a := by
    change HasExpectation _ (payoff who ∘ embed) ↔ HasExpectation _ (payoff who)
    rw [← hasExpectation_map_iff, outcomes]
  have values (a) : conditional.extendedValue (restrict a) = original.extendedValue a := by
    change extendedExpect _ (payoff who ∘ embed) = extendedExpect _ (payoff who)
    rw [← extendedExpect_map, outcomes]
  refine ⟨(admissible _).mpr optimal.1, ?_, ?_⟩
  · intro alternative _
    obtain ⟨a, rfl⟩ := setup.conditionInitial_policy_surjective signal value who alternative
    exact (admissible _).mpr (optimal.2.1 a (Set.mem_univ _))
  · intro alternative _
    obtain ⟨a, rfl⟩ := setup.conditionInitial_policy_surjective signal value who alternative
    exact (values a).trans_le ((optimal.2.2 a (Set.mem_univ _)).trans_eq (values _).symm)

end Vegas.SourceProgram.Setup
