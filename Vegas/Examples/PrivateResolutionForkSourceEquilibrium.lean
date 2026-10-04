/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PrivateResolutionForkSourceConsistency
import Vegas.Examples.PrivateResolutionForkLowFalseUtility
import Vegas.Game.SourceLocalContinuation
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Source incentives for the private-type resolution fork

The original source strategy discloses at both types. Bob chooses LOW after
TRUE and HIGH after FALSE. The utility uses the immutable initial parameter
and the public outcome, including the FALSE reward of one for LOW type.
Native scheduling and native sequential equilibrium are not asserted here.
-/

noncomputable section

namespace Vegas.PrivateResolutionFork

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

def sourcePayoff (who : Player) (history : sourceArena.History) : ℝ :=
  (setup.protocolReadout history.state).elim 0 (fun source => lowFalseSourceUtility source who)

theorem source_done_payoff (high disclose guess : Bool) (who : Player) :
    (setup.protocolReadout (SourcePosition.done high disclose guess).state).elim 0
      (fun source => lowFalseSourceUtility source who) =
      if who = alice then
        (if high then (if disclose then 2 else 0)
        else if disclose then (if guess then 2 else 1 / 2)
        else if guess then 0 else 1)
      else if guess = high then 1 else 0 :=
  lowFalse_source_utility high disclose guess who

theorem sourceCertificate : sourceArena.WellFoundedHistories :=
  sourceArena.wellFoundedHistories_of_fintype

def sourceAliceInput (high : Bool) : setup.ProtocolView alice :=
  setup.protocolObserve alice (SourcePosition.ready high).state

theorem source_alice_inputs_eq_iff (first second : Bool) :
    sourceAliceInput first = sourceAliceInput second ↔ first = second := by
  constructor
  · intro same
    change (some (.inr (.inr (.inl ((sourceReady first).view alice)))) :
        setup.ProtocolView alice) =
      some (.inr (.inr (.inl ((sourceReady second).view alice)))) at same
    have views := Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Option.some.inj same)))
    have parameter := congrArg
      (fun view => view.1.cells.get (.there (.there (.there (.there .here))))) views
    change (some first : Option Bool) = some second at parameter
    exact Option.some.inj parameter
  · rintro rfl
    rfl

theorem source_alice_site_type (site : sourceModel.InformationSite alice) :
    ∃ high, ∀ history : sourceModel.InformationHistory alice site.1,
      history.1.state = (SourcePosition.ready high).state := by
  obtain ⟨witness, _, _⟩ := site.2
  obtain ⟨high, same⟩ := source_alice_active_state site witness
  refine ⟨high, ?_⟩
  intro history
  obtain ⟨other, actual⟩ := source_alice_active_state site history
  have observed : sourceAliceInput other = sourceAliceInput high := by
    calc
      _ = sourceModel.infoOf alice history.1.trace := by
        rw [source_history_observe, actual]
        rfl
      _ = site.1 := history.2
      _ = sourceModel.infoOf alice witness.1.trace := witness.2.symm
      _ = _ := by rw [source_history_observe, same]; rfl
  have equal := (source_alice_inputs_eq_iff other high).mp observed
  exact equal ▸ actual

def sourceChoiceDisclosure (who : Player) (info : sourceModel.InfoState who)
    (law : PMF (sourceModel.Choice who info)) : PMF Bool :=
  law.map (fun choice => OwnAction.disclosure choice.1)

/-- One actual source transition at Alice's ready state reads only her
genuine local choice. The complete protocol state and action memory remain. -/
theorem source_ready_step
    (profile : Profile sourceModel.behavioralSignature) (high : Bool) :
    setup.behavioralStateStep sourceAdmission profile (SourcePosition.ready high).state =
      (sourceChoiceDisclosure alice (sourceAliceInput high)
        (profile alice (sourceAliceInput high))).map
          (fun disclose => (SourcePosition.guessed high disclose).state) := by
  classical
  unfold Setup.behavioralStateStep
  rw [ite_eq_right (by exact not_false)]
  have step (choices : ∀ who, sourceModel.Choice who
      (setup.protocolObserve who (SourcePosition.ready high).state)) :
      setup.protocolStep (SourcePosition.ready high).state (fun who => (choices who).1) =
        PMF.pure (SourcePosition.guessed high
          (OwnAction.disclosure (choices alice).1)).state := by
    simp [Setup.protocolStep, SourcePosition.state, setup, program,
      ProtocolState.step, ProtocolState.entry, sourceAliceDone, PMF.pure_map]
  simp_rw [step]
  change ((independentProduct fun who => profile who
    (setup.protocolObserve who (SourcePosition.ready high).state)).bind fun choices =>
      PMF.pure (SourcePosition.guessed high
        (OwnAction.disclosure (choices alice).1)).state) = _
  change ((independentProduct fun who => profile who
    (setup.protocolObserve who (SourcePosition.ready high).state)).map
      ((fun choice => (SourcePosition.guessed high (OwnAction.disclosure choice.1)).state) ∘
        fun choices => choices alice)) = _
  rw [← PMF.map_comp, independentProduct_map_eval]
  simp only [sourceChoiceDisclosure, sourceAliceInput, PMF.map_comp, Function.comp_def]

/-- Bob's last actual source transition preserves Alice's publication and
reads only his genuine local choice. -/
theorem source_guessed_step
    (profile : Profile sourceModel.behavioralSignature) (high disclose : Bool) :
    setup.behavioralStateStep sourceAdmission profile (SourcePosition.guessed high disclose).state =
      (sourceChoiceDisclosure bob (sourceBobInput disclose)
        (profile bob (sourceBobInput disclose))).map
          (fun guess => (SourcePosition.done high disclose guess).state) := by
  classical
  unfold Setup.behavioralStateStep
  rw [ite_eq_right (by exact not_false)]
  have step (choices : ∀ who, sourceModel.Choice who
      (setup.protocolObserve who (SourcePosition.guessed high disclose).state)) :
      setup.protocolStep (SourcePosition.guessed high disclose).state
          (fun who => (choices who).1) =
        PMF.pure (SourcePosition.done high disclose
          (OwnAction.disclosure (choices bob).1)).state := by
    simp [Setup.protocolStep, SourcePosition.state, setup, program,
      ProtocolState.step, ProtocolState.entry, sourceDone, PMF.pure_map]
  simp_rw [step]
  change ((independentProduct fun who => profile who
    (setup.protocolObserve who (SourcePosition.guessed high disclose).state)).bind fun choices =>
      PMF.pure (SourcePosition.done high disclose
        (OwnAction.disclosure (choices bob).1)).state) = _
  change ((independentProduct fun who => profile who
    (setup.protocolObserve who (SourcePosition.guessed high disclose).state)).map
      ((fun choice => (SourcePosition.done high disclose (OwnAction.disclosure choice.1)).state) ∘
        fun choices => choices bob)) = _
  rw [← PMF.map_comp, independentProduct_map_eval, source_bob_input]
  simp only [sourceChoiceDisclosure, PMF.map_comp, Function.comp_def]

theorem source_equilibrium_alice_choice (high : Bool) :
    sourceChoiceDisclosure alice (sourceAliceInput high)
      (sourceEquilibriumProfile alice (sourceAliceInput high)) = PMF.pure true := by
  unfold sourceChoiceDisclosure
  rw [show (fun choice : sourceModel.Choice alice (sourceAliceInput high) =>
    OwnAction.disclosure choice.1) = OwnAction.disclosure ∘ Subtype.val from rfl]
  rw [← PMF.map_comp]
  change ((sourceProfile (fun _ => PMF.pure true) (fun disclose => PMF.pure (!disclose)) alice
    (setup.protocolObserve alice (SourcePosition.ready high).state)).map Subtype.val).map
      OwnAction.disclosure = _
  rw [source_alice_profile_map, PMF.map_comp]
  simp only [Function.comp_def, OwnAction.disclosure, PMF.pure_map]

theorem source_equilibrium_bob_choice (disclose : Bool) :
    sourceChoiceDisclosure bob (sourceBobInput disclose)
      (sourceEquilibriumProfile bob (sourceBobInput disclose)) = PMF.pure (!disclose) := by
  unfold sourceChoiceDisclosure
  rw [show (fun choice : sourceModel.Choice bob (sourceBobInput disclose) =>
    OwnAction.disclosure choice.1) = OwnAction.disclosure ∘ Subtype.val from rfl]
  rw [← PMF.map_comp]
  change ((sourceProfile (fun _ => PMF.pure true) (fun disclose => PMF.pure (!disclose)) bob
    (setup.protocolObserve bob (SourcePosition.guessed true disclose).state)).map Subtype.val).map
      OwnAction.disclosure = _
  rw [source_bob_profile_map, PMF.map_comp]
  simp only [Function.comp_def, OwnAction.disclosure, PMF.pure_map]

theorem source_alice_continuation_state (alternative : sourceModel.BehavioralPolicy alice)
    (history : sourceArena.History) (high : Bool)
    (state : history.state = (SourcePosition.ready high).state) :
    (sourceModel.runBehavioralFrom
      (Profile.update sourceEquilibriumProfile alice alternative) 2 history).map History.state =
      (sourceChoiceDisclosure alice (sourceAliceInput high)
        (alternative (sourceAliceInput high))).map
          (fun disclose => (SourcePosition.done high disclose (!disclose)).state) := by
  rw [Setup.runBehavioralFrom_state]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, PMF.pure_bind]
  rw [state, source_ready_step]
  simp only [Profile.update_same, PMF.bind_map]
  calc
    _ = (sourceChoiceDisclosure alice (sourceAliceInput high)
        (alternative (sourceAliceInput high))).bind (fun disclose =>
          PMF.pure (SourcePosition.done high disclose (!disclose)).state) := by
      apply bind_congr_on_support _
      intro disclose _
      dsimp only [Function.comp_def]
      rw [source_guessed_step]
      simp only [sourceChoiceDisclosure, Profile.update_of_ne sourceEquilibriumProfile alternative
        (by decide : bob ≠ alice)]
      change (sourceChoiceDisclosure bob (sourceBobInput disclose)
        (sourceEquilibriumProfile bob (sourceBobInput disclose))).map _ = _
      rw [source_equilibrium_bob_choice, PMF.pure_map]
    _ = _ := rfl

theorem source_bob_continuation_state (alternative : sourceModel.BehavioralPolicy bob)
    (history : sourceArena.History) (high disclose : Bool)
    (state : history.state = (SourcePosition.guessed high disclose).state) :
    (sourceModel.runBehavioralFrom
      (Profile.update sourceEquilibriumProfile bob alternative) 1 history).map History.state =
      (sourceChoiceDisclosure bob (sourceBobInput disclose)
        (alternative (sourceBobInput disclose))).map
          (fun guess => (SourcePosition.done high disclose guess).state) := by
  rw [Setup.runBehavioralFrom_state]
  simp only [Function.iterate_one, PMF.pure_bind]
  rw [state, source_guessed_step]
  simp only [Profile.update_same]

theorem source_alice_continuation_value (alternative : sourceModel.BehavioralPolicy alice)
    (history : sourceArena.History) (high : Bool)
    (state : history.state = (SourcePosition.ready high).state) :
    expect (sourceModel.runBehavioralFrom
      (Profile.update sourceEquilibriumProfile alice alternative) 2 history)
      (sourcePayoff alice) =
      expect (sourceChoiceDisclosure alice (sourceAliceInput high)
        (alternative (sourceAliceInput high)))
          (fun disclose => if disclose then (if high then 2 else 1 / 2) else 0) := by
  let readout (state : setup.ProtocolState) : ℝ :=
    (setup.protocolReadout state).elim 0 (fun source => lowFalseSourceUtility source alice)
  calc
    _ = expect ((sourceModel.runBehavioralFrom
        (Profile.update sourceEquilibriumProfile alice alternative) 2 history).map History.state)
        readout := (expect_map _ _ _).symm
    _ = _ := by
      rw [source_alice_continuation_state alternative history high state, expect_map]
      apply expect_congr_on_support
      intro disclose _
      change (setup.protocolReadout (SourcePosition.done high disclose (!disclose)).state).elim
        0 (fun source => lowFalseSourceUtility source alice) = _
      rw [source_done_payoff]
      cases high <;> cases disclose <;> norm_num

theorem source_bob_continuation_value (alternative : sourceModel.BehavioralPolicy bob)
    (history : sourceArena.History) (high disclose : Bool)
    (state : history.state = (SourcePosition.guessed high disclose).state) :
    expect (sourceModel.runBehavioralFrom
      (Profile.update sourceEquilibriumProfile bob alternative) 1 history)
      (sourcePayoff bob) =
      expect (sourceChoiceDisclosure bob (sourceBobInput disclose)
        (alternative (sourceBobInput disclose)))
          (fun guess => if guess = high then 1 else 0) := by
  let readout (state : setup.ProtocolState) : ℝ :=
    (setup.protocolReadout state).elim 0 (fun source => lowFalseSourceUtility source bob)
  calc
    _ = expect ((sourceModel.runBehavioralFrom
        (Profile.update sourceEquilibriumProfile bob alternative) 1 history).map History.state)
        readout := (expect_map _ _ _).symm
    _ = _ := by
      rw [source_bob_continuation_state alternative history high disclose state, expect_map]
      apply expect_congr_on_support
      intro guess _
      change (setup.protocolReadout (SourcePosition.done high disclose guess).state).elim
        0 (fun source => lowFalseSourceUtility source bob) = _
      rw [source_done_payoff]
      simp only [show bob ≠ alice by decide, ite_false]

theorem source_bob_site_state (site : sourceModel.InformationSite bob) (disclose : Bool)
    (observed : site.1 = sourceBobInput disclose)
    (history : sourceModel.InformationHistory bob site.1) :
    ∃ high, history.1.state = (SourcePosition.guessed high disclose).state := by
  obtain ⟨high, actual, state⟩ := source_bob_active_state site history
  have input : setup.protocolObserve bob (SourcePosition.guessed high actual).state =
      sourceBobInput disclose := by
    calc
      _ = setup.protocolObserve bob history.1.state := by rw [state]
      _ = sourceModel.infoOf bob history.1.trace := (source_history_observe bob history.1).symm
      _ = sourceBobInput disclose := history.2.trans observed
  have equal := (source_bob_input_eq_iff high actual disclose).mp input
  exact ⟨high, equal ▸ state⟩

theorem source_bob_belief_reward (assessment : sourceModel.BehavioralAssessment)
    (site : sourceModel.InformationSite bob) (disclose : Bool)
    (observed : site.1 = sourceBobInput disclose) (guess : Bool) :
    expect (assessment.belief bob site)
      (fun history => if sourceBobType history.1.state = some guess then (1 : ℝ) else 0) =
      if guess then
        ((assessment.belief bob site).toOuterMeasure
          {history | sourceBobType history.1.state = some true}).toReal
      else 1 - ((assessment.belief bob site).toOuterMeasure
          {history | sourceBobType history.1.state = some true}).toReal := by
  classical
  have indicator : expect (assessment.belief bob site)
      (fun history => if sourceBobType history.1.state = some true then (1 : ℝ) else 0) =
      ((assessment.belief bob site).toOuterMeasure
        {history | sourceBobType history.1.state = some true}).toReal := by
    calc
      _ = expect (assessment.belief bob site) (fun history =>
          @ite ℝ (sourceBobType history.1.state = some true) (Classical.propDecidable _) 1 0) := by
        apply expect_congr_on_support
        intro history _
        split_ifs <;> rfl
      _ = _ := expect_indicator _ _
  cases guess with
  | true => exact indicator
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      calc
        _ = expect (assessment.belief bob site)
            (fun history =>
              1 - (if sourceBobType history.1.state = some true then (1 : ℝ) else 0)) := by
          apply expect_congr_on_support
          intro history _
          obtain ⟨high, state⟩ := source_bob_site_state site disclose observed history
          rw [state, source_bob_type]
          cases high <;> norm_num
        _ = _ := by
          rw [expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
            expect_constant, indicator]

theorem source_alice_rational (assessment : sourceModel.BehavioralAssessment)
    (strategy : assessment.strategy = sourceEquilibriumProfile)
    (site : sourceModel.InformationSite alice) :
    (assessment.truncatedContinuationContext site (sourcePayoff alice) 5).IsLocallyOptimal
      Set.univ (assessment.strategy alice) := by
  have context := assessment.truncatedContinuationContext_remaining sourceModel 5
    (setup.protocol_bounded sourceAdmission) alice site 3 (source_alice_depth site)
    (sourcePayoff alice)
  change assessment.truncatedContinuationContext site (sourcePayoff alice) 2 = _ at context
  rw [← context]
  obtain ⟨high, fixed⟩ := source_alice_site_type site
  refine (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _)
    (fun _ _ => payoffIntegrable_of_finite _ _)).mpr fun alternative _ => ?_
  have baseline : (assessment.truncatedContinuationContext site (sourcePayoff alice) 2).value
      (assessment.strategy alice) = if high then 2 else 1 / 2 := by
    rw [InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
      strategy, expect_bind_of_finite]
    calc
      _ = expect (assessment.belief alice site) (fun _ => if high then (2 : ℝ) else 1 / 2) := by
        apply expect_congr_on_support
        intro history _
        rw [source_alice_continuation_value _ history.1 high (fixed history),
          source_equilibrium_alice_choice, expect_pure]
        rfl
      _ = _ := expect_constant _ _
  rw [baseline]
  rw [InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
    strategy, expect_bind_of_finite]
  apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
  intro history _
  rw [source_alice_continuation_value _ history.1 high (fixed history)]
  apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
  intro disclose _
  cases disclose <;> cases high <;> norm_num

theorem source_bob_context_value (assessment : sourceModel.BehavioralAssessment)
    (strategy : assessment.strategy = sourceEquilibriumProfile)
    (site : sourceModel.InformationSite bob) (disclose : Bool)
    (observed : site.1 = sourceBobInput disclose)
    (alternative : sourceModel.BehavioralPolicy bob) :
    (assessment.truncatedContinuationContext site (sourcePayoff bob) 1).value alternative =
      expect (sourceChoiceDisclosure bob (sourceBobInput disclose)
        (alternative (sourceBobInput disclose))) (fun guess =>
        if guess then ((assessment.belief bob site).toOuterMeasure
          {history | sourceBobType history.1.state = some true}).toReal
        else 1 - ((assessment.belief bob site).toOuterMeasure
          {history | sourceBobType history.1.state = some true}).toReal) := by
  rw [InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
    strategy, expect_bind_of_finite]
  calc
    _ = expect (assessment.belief bob site) (fun history =>
        expect (sourceChoiceDisclosure bob (sourceBobInput disclose)
          (alternative (sourceBobInput disclose))) (fun guess =>
            if sourceBobType history.1.state = some guess then (1 : ℝ) else 0)) := by
      apply expect_congr_on_support
      intro history _
      obtain ⟨high, state⟩ := source_bob_site_state site disclose observed history
      rw [source_bob_continuation_value alternative history.1 high disclose state]
      apply expect_congr_on_support
      intro guess _
      rw [state, source_bob_type]
      simp only [Option.some.injEq, eq_comm]
    _ = _ := by
      rw [expect_comm_of_support_finite _ _ (Set.toFinite _) (Set.toFinite _)]
      apply expect_congr_on_support
      intro guess _
      exact source_bob_belief_reward assessment site disclose observed guess

theorem source_bob_rational (assessment : sourceModel.BehavioralAssessment)
    (strategy : assessment.strategy = sourceEquilibriumProfile)
    (beliefs : ∀ (site : sourceModel.InformationSite bob) (disclose : Bool),
      site.1 = sourceBobInput disclose →
      ((assessment.belief bob site).toOuterMeasure
        {history | sourceBobType history.1.state = some true}).toReal =
          if disclose then (1 / 4 : ℝ) else 1)
    (site : sourceModel.InformationSite bob) :
    (assessment.truncatedContinuationContext site (sourcePayoff bob) 5).IsLocallyOptimal
      Set.univ (assessment.strategy bob) := by
  have context := assessment.truncatedContinuationContext_remaining sourceModel 5
    (setup.protocol_bounded sourceAdmission) bob site 4 (source_bob_depth site)
    (sourcePayoff bob)
  change assessment.truncatedContinuationContext site (sourcePayoff bob) 1 = _ at context
  rw [← context]
  obtain ⟨disclose, observed⟩ := source_bob_site_input site
  refine (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _)
    (fun _ _ => payoffIntegrable_of_finite _ _)).mpr fun alternative _ => ?_
  rw [source_bob_context_value assessment strategy site disclose observed alternative,
    source_bob_context_value assessment strategy site disclose observed (assessment.strategy bob),
    strategy, source_equilibrium_bob_choice, expect_pure, beliefs site disclose observed]
  apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
  intro guess _
  cases disclose <;> cases guess <;> norm_num

/-- The strongest declared public utility has a genuine source sequential
equilibrium, with beliefs certified by one actual fully mixed source sequence.
No native equilibrium or runtime fork is inferred from this source result. -/
theorem exists_source_equilibrium :
    ∃ assessment : sourceModel.BehavioralAssessment,
      assessment.strategy = sourceEquilibriumProfile ∧
      assessment.IsSequentialEquilibrium (setup.decision_antichain sourceAdmission)
        sourceCertificate sourcePayoff := by
  obtain ⟨assessment, strategy, consistent, beliefs⟩ := exists_consistent_source_assessment
  refine ⟨assessment, strategy, ?_⟩
  apply (assessment.isSequentialEquilibrium_iff_truncated_of_bounded sourceModel
    (setup.decision_antichain sourceAdmission) sourceCertificate
    (setup.protocol_bounded sourceAdmission) sourcePayoff).mpr
  refine ⟨?_, consistent⟩
  intro who site
  fin_cases who
  · exact source_alice_rational assessment strategy site
  · exact source_bob_rational assessment strategy beliefs site

end Vegas.PrivateResolutionFork
