module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.PrescribedProfile
public import Vegas.EventGraph.PrefixNash
public import Vegas.Game.GraphPayoff
public import Vegas.Game.IntendedNash
public import Vegas.Game.IntendedSourceProfile
public import Vegas.Source.ValueBindingAdmission

@[expose] public section

/-! # Source Nash preservation with independent commitments and reveals

Prescribed clients use source-prefix observations and submit at every binding.
The dependency hypothesis permits independent bindings and independent reveals
to run concurrently. Deviations retain their actual chronological observations.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open Vegas.EventGraph GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem submitted_compile_oblivious (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies) (source : BehavioralProfile setup.program)
    (disclosing : ∀ who, Disclosing setup.program (source who)) :
    (setup.dataflowGraph.withDependencies deps).ObliviousAtPublications
      ((setup.dataflowGraph.withDependencies deps).submitProfile
        (compileEventProfile setup.program source)) := by
  let graph := setup.dataflowGraph.withDependencies deps
  let submitted : graph.BehavioralProfile :=
    graph.submitProfile (compileEventProfile setup.program source)
  have opens (who : Player) (event : graph.EventId) (actor : graph.actor? event = some who)
      (publication : (graph.outputLayout event).IsPublication)
      (observation : graph.PlayerObservation who) (active : who ∉ observation.defaulted) :
      submitted who event actor observation active =
        PMF.pure (EventField.openAction _ publication) := by
    change (compileEventPolicy setup.program who (source who) event actor observation active).map
      (EventField.submitAction _) = _
    rw [compileEventPolicy_publication setup.program who (source who)
      (disclosing who) event actor publication,
      PMF.pure_map]
    congr 1
    exact EventField.submitAction_eq_self _ _
      (EventField.submitted_of_publication _ publication _)
  intro who event actor publication left right leftActive rightActive
  exact (opens who event actor publication left leftActive).trans
    (opens who event actor publication right rightActive).symm

/-- Prescribed clients of a submitting, disclosing source equilibrium retain its Nash error
under every public scheduler of a reveal-relaxed dependency choice. -/
theorem isεNash_compilePrescribedProfile (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies)
    (relaxed : (setup.dataflowGraph.withDependencies deps).RevealRelaxedOrdered)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excluded : Player → ℝ) (low : ∀ outcome who, excluded who ≤ utility outcome who)
    (source : BehavioralProfile setup.program) (submits : ∀ who, SourceProgram.SubmitsBindings
      setup.program (source who))
    (disclosing : ∀ who, Disclosing setup.program (source who))
    (ε : ℝ)
    (equilibrium : IsεNash (setup.parameterGameForm parameter)
      (exclusionUtility setup.program excluded utility) ε source)
    (scheduler : (setup.dataflowGraph.withDependencies deps).PublicScheduler) :
    IsεNash ((setup.dataflowGraph.withDependencies deps).gameForm (setup.graphInputs deps)
      scheduler)
      (fun outcome who => setup.graphPayoff deps parameter utility excluded who outcome.1) ε
      (compilePrescribedProfile setup.program deps source) := by
  let graph := setup.dataflowGraph.withDependencies deps
  let compiled : graph.BehavioralProfile := compileEventProfile setup.program source
  let submitted : graph.BehavioralProfile := graph.submitProfile compiled
  let payoff := exclusionUtility setup.program excluded utility
  have actions : graph.FiniteActions := toInformationGraph_finiteActions setup.program finite
  have oblivious : graph.ObliviousAtPublications submitted :=
    submitted_compile_oblivious setup deps source
      disclosing
  have decisive (who : Player) :
      graph.OpensDecisively who (graph.prefixPolicy who (submitted who)) := by
    exact compilePrescribedProfile_opensDecisively setup.program deps source
      disclosing who
  have graphNash := (setup.parameterEventGame_approximate_nash_iff parameter finite
    setup.informationGraph.canonicalScheduler payoff ε source).mpr equilibrium
  rw [IsεNash, isNash_iff] at graphNash
  have canonicalBound (who : Player) (policy : graph.BehavioralPolicy who) :
      expect (setup.canonicalEventGame.play (Profile.update
        (sig := setup.informationGraph.gameSignature) compiled who policy))
        (fun outcome => payoff (setup.eventParameterOutcome parameter outcome) who) ≤
      expect (setup.canonicalEventGame.play compiled)
        (fun outcome => payoff (setup.eventParameterOutcome parameter outcome) who) + ε := by
    have preference := graphNash who policy
    rwa [euPreferenceWithin_iff _ _ _ _ _
      (payoffIntegrable_of_finite_support _ _ (setup.eventGame_play_support_finite finite _ _))
      (payoffIntegrable_of_finite_support _ _ (setup.eventGame_play_support_finite finite _ _))]
      at preference
  have repair : (setup.graphInputs deps).bind (graph.runPolicies graph.canonicalScheduler
      submitted) = (setup.graphInputs deps).bind (graph.runPolicies graph.canonicalScheduler
      compiled) := by
    apply bind_congr_on_support _
    intro initial _
    exact runPolicies_canonical_submit_compile setup.program deps source submits initial
  have repairUpdate (who : Player) (policy : graph.BehavioralPolicy who) :
      (setup.graphInputs deps).bind (graph.runPolicies graph.canonicalScheduler
        (Profile.update (sig := graph.gameSignature) submitted who policy)) =
      (setup.graphInputs deps).bind (graph.runPolicies graph.canonicalScheduler
        (Profile.update (sig := graph.gameSignature) compiled who policy)) := by
    apply bind_congr_on_support _
    intro initial _
    exact runPolicies_canonical_submit_compile_update setup.program deps source who
      (fun owner _ => submits owner) policy initial
  change IsεNash (graph.gameForm (setup.graphInputs deps) scheduler)
    (fun outcome who => setup.graphPayoff deps parameter utility excluded who outcome.1) ε
    (graph.prefixProfile submitted)
  apply relaxed.isεNash_prefixProfile actions submitted (submitsBindings_submitProfile _ _)
    oblivious decisive
    (fun who => setup.graphPayoff deps parameter utility excluded who)
    (fun who => setup.graphPayoff_factors deps parameter utility excluded who) excluded
    (fun who => setup.le_graphPayoff deps parameter utility excluded who (fun outcome => low
      outcome who))
    (fun who => setup.graphPayoff_of_defaulted deps parameter utility excluded who)
    (setup.graphInputs deps) (setup.graphInputs_support_finite deps) ε
  intro who policy _submits _oblivious
  rw [repairUpdate, repair,
    setup.expect_graphPayoff_canonical deps parameter utility excluded who,
    setup.expect_graphPayoff_canonical deps parameter utility excluded who]
  exact canonicalBound who policy

/-- Submitting, disclosing source policies retain the joint full-configuration and fixed-exit
payoff law under every public scheduler, without equilibrium or finiteness premises. -/
private theorem compilePrescribedProfile_run_law (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies)
    (relaxed : (setup.dataflowGraph.withDependencies deps).RevealRelaxedOrdered)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excluded : Player → ℝ) (source : BehavioralProfile setup.program)
    (submits : ∀ who, SourceProgram.SubmitsBindings setup.program (source who))
    (disclosing : ∀ who, Disclosing setup.program (source who))
    (scheduler : (setup.dataflowGraph.withDependencies deps).PublicScheduler) :
    ((setup.graphInputs deps).bind ((setup.dataflowGraph.withDependencies deps).runPolicies
        scheduler (compilePrescribedProfile setup.program deps source))).map
        (setup.graphObservation deps parameter utility excluded) =
      (setup.run source).map fun terminal =>
        (some terminal, fun who => exclusionUtility setup.program excluded utility
          (setup.parameterOutcome parameter terminal) who) := by
  let graph := setup.dataflowGraph.withDependencies deps
  let compiled : graph.BehavioralProfile := compileEventProfile setup.program source
  let submitted : graph.BehavioralProfile := graph.submitProfile compiled
  have oblivious : graph.ObliviousAtPublications submitted :=
    submitted_compile_oblivious setup deps source
      disclosing
  have law := relaxed.runPolicies_prefixProfile_map_eq_canonical submitted oblivious scheduler
    (setup.graphInputs deps) (setup.graphObservation deps parameter utility excluded)
    (setup.graphObservation_factors deps parameter utility excluded)
  have canonical : (setup.graphInputs deps).bind
      (graph.runPolicies graph.canonicalScheduler (graph.prefixProfile submitted)) =
      (setup.graphInputs deps).bind (graph.runPolicies graph.canonicalScheduler compiled) := by
    apply bind_congr_on_support _
    intro initial _
    exact (runPolicies_canonical_prefixProfile submitted (submitsBindings_submitProfile _ _)
      initial).trans (runPolicies_canonical_submit_compile setup.program deps source submits
        initial)
  rw [canonical] at law
  change ((setup.graphInputs deps).bind (graph.runPolicies scheduler
    (graph.prefixProfile submitted))).map _ = _
  refine law.trans ((setup.canonical_graphObservation_law deps parameter utility excluded
    compiled).trans ?_)
  have sourceLaw := canonical_setup_law setup source
  have mapped := congrArg (PMF.map fun terminal : Config Player L setup.program.terminalCtx =>
    (some terminal, fun who => exclusionUtility setup.program excluded utility
      (setup.parameterOutcome parameter terminal) who)) sourceLaw
  rw [PMF.map_comp] at mapped
  exact mapped

/-- Submitting, disclosing source policies preserve the complete source-configuration and
fixed-exit payoff law in the graph game, under every permitted scheduler. -/
theorem compilePrescribedProfile_law (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies)
    (relaxed : (setup.dataflowGraph.withDependencies deps).RevealRelaxedOrdered)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excluded : Player → ℝ) (source : BehavioralProfile setup.program)
    (submits : ∀ who, SourceProgram.SubmitsBindings setup.program (source who))
    (disclosing : ∀ who, Disclosing setup.program (source who))
    (scheduler : (setup.dataflowGraph.withDependencies deps).PublicScheduler) :
    (((setup.dataflowGraph.withDependencies deps).gameForm (setup.graphInputs deps) scheduler).play
        (compilePrescribedProfile setup.program deps source)).map
        (fun outcome => (some (setup.graphReadout deps outcome), fun who =>
          setup.graphPayoff deps parameter utility excluded who outcome.1)) =
      (setup.run source).map fun terminal =>
        (some terminal, fun who => exclusionUtility setup.program excluded utility
          (setup.parameterOutcome parameter terminal) who) := by
  let graph := setup.dataflowGraph.withDependencies deps
  have observed : (fun outcome : graph.gameSignature.Outcome =>
      (some (setup.graphReadout deps outcome), fun who =>
        setup.graphPayoff deps parameter utility excluded who outcome.1)) =
      setup.graphObservation deps parameter utility excluded ∘ Subtype.val := by
    funext outcome
    simp only [Function.comp_apply, graphObservation, dite_eq_left outcome.2, graphReadout]
  rw [observed, ← PMF.map_comp, gameForm_play_map_val]
  exact setup.compilePrescribedProfile_run_law deps relaxed parameter utility excluded source
    submits disclosing scheduler

/-- Every disclosing intended extension has prescribed clients with the same Nash error
for every dependency choice retaining the reveal-relaxed information barriers. -/
theorem isεNash_compileIntendedExtension (setup : Setup (Player := Player) (L := L))
    [Finite Player] (deps : setup.dataflowGraph.Dependencies)
    (relaxed : (setup.dataflowGraph.withDependencies deps).RevealRelaxedOrdered)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excluded : Player → ℝ) (low : ∀ outcome who, excluded who ≤ utility outcome who)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    (disclosing : ∀ who, Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who)) (ε : ℝ)
    (equilibrium : IsεNash (setup.intendedModel.toBehavioralGameForm
        (instructionCount setup.program + 1))
      (fun final who => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)) ε intended)
    (scheduler : (setup.dataflowGraph.withDependencies deps).PublicScheduler) :
    IsεNash ((setup.dataflowGraph.withDependencies deps).gameForm (setup.graphInputs deps)
      scheduler)
      (fun outcome who => setup.graphPayoff deps parameter utility excluded who outcome.1) ε
      (compilePrescribedProfile setup.program deps
        (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target)) := by
  let admission := CommitmentInterface.forfeiture setup.program
  let repaired := setup.submittedSourceProfile target
  let source := setup.decodeBehavioralProfile admission repaired
  have extension := setup.submittedSourceProfile_extends intended target agrees
  have protocolNash := (setup.intended_isεNash_preserved admission finite wellFormed parameter
    utility excluded (fun _ _ _ who => low _ who) intended repaired extension ε equilibrium).1
  have sourceNash := (setup.parameterProtocol_isεNash_iff admission
    (fun _ policy => policy.admitted_forfeiture setup.program) parameter
    (exclusionUtility setup.program excluded utility) ε repaired).mp protocolNash
  have clientsEq : compilePrescribedProfile setup.program deps source =
      compilePrescribedProfile setup.program deps
        (setup.decodeBehavioralProfile admission target) := by
    dsimp only [source, repaired, admission]
    rw [setup.decodeBehavioralProfile_submittedSourceProfile,
      compilePrescribedProfile_submitBindings]
  have result := setup.isεNash_compilePrescribedProfile deps relaxed finite parameter utility
    excluded low source (setup.submittedSourceProfile_submits target)
    (fun who => setup.submittedSourceProfile_disclosing target who (disclosing who))
    ε sourceNash scheduler
  rw [clientsEq] at result
  exact result

/-- Every disclosing intended extension retains the full configuration and payoff law.
No equilibrium, finite binding-type, finite initial-support or payoff-bound premise is needed. -/
theorem compileIntendedExtension_law (setup : Setup (Player := Player) (L := L))
    [Finite Player] (deps : setup.dataflowGraph.Dependencies)
    (relaxed : (setup.dataflowGraph.withDependencies deps).RevealRelaxedOrdered)
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excluded : Player → ℝ) (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    (disclosing : ∀ who, Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    (scheduler : (setup.dataflowGraph.withDependencies deps).PublicScheduler) :
    (((setup.dataflowGraph.withDependencies deps).gameForm (setup.graphInputs deps) scheduler).play
        (compilePrescribedProfile setup.program deps (setup.decodeBehavioralProfile
          (CommitmentInterface.forfeiture setup.program) target))).map
        (fun outcome => (some (setup.graphReadout deps outcome), fun who =>
          setup.graphPayoff deps parameter utility excluded who outcome.1)) =
      (setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
        (fun final => (setup.protocolReadout final.state, fun who =>
          (setup.protocolReadout final.state).elim 0
            (fun terminal => utility (setup.parameterOutcome parameter terminal) who))) := by
  let admission := CommitmentInterface.forfeiture setup.program
  let repaired := setup.submittedSourceProfile target
  let source := setup.decodeBehavioralProfile admission repaired
  let exclusion := exclusionUtility setup.program excluded utility
  have clientsEq : compilePrescribedProfile setup.program deps source =
      compilePrescribedProfile setup.program deps
        (setup.decodeBehavioralProfile admission target) := by
    dsimp only [source, repaired, admission]
    rw [setup.decodeBehavioralProfile_submittedSourceProfile,
      compilePrescribedProfile_submitBindings]
  have sourceLaw := setup.compilePrescribedProfile_law deps relaxed parameter utility excluded
    source (setup.submittedSourceProfile_submits target)
    (fun who => setup.submittedSourceProfile_disclosing target who (disclosing who)) scheduler
  rw [clientsEq] at sourceLaw
  refine sourceLaw.trans ?_
  have protocolLaw := (setup.protocol_readout_law admission).1 repaired
  have viaSome : (setup.run source).map (fun terminal => (some terminal, fun who =>
      exclusion (setup.parameterOutcome parameter terminal) who)) =
      ((setup.run source).map some).map (fun readout => (readout, fun who =>
        readout.elim 0 (fun terminal => exclusion (setup.parameterOutcome parameter terminal)
          who))) := by
    rw [PMF.map_comp]
    rfl
  rw [viaSome, ← protocolLaw, PMF.map_comp]
  have restrictionLaw := (setup.intendedRestriction admission).initialized_law intended repaired
    (setup.submittedSourceProfile_extends intended target agrees) (instructionCount setup.program +
      1)
  rw [← restrictionLaw, PMF.map_comp]
  apply map_congr_on_support _
  intro final _
  refine Prod.ext rfl (funext fun who => ?_)
  change (setup.protocolReadout final.state).elim 0
    (fun terminal => exclusion (setup.parameterOutcome parameter terminal) who) = _
  cases read : setup.protocolReadout final.state with
  | none => rfl
  | some terminal =>
    simp only [Option.elim_some]
    apply exclusionUtility_of_not_defaulted
    exact setup.not_defaulted_of_intendedState
      (setup.intendedState_trace wellFormed final.trace) who read

/-- Every disclosing intended extension produces neither public defaults nor failed reveals. -/
theorem compileIntendedExtension_clean (setup : Setup (Player := Player) (L := L))
    [Finite Player] (deps : setup.dataflowGraph.Dependencies)
    (relaxed : (setup.dataflowGraph.withDependencies deps).RevealRelaxedOrdered)
    (wellFormed : setup.WellFormed)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    (disclosing : ∀ who, Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    (scheduler : (setup.dataflowGraph.withDependencies deps).PublicScheduler)
    (outcome : (setup.dataflowGraph.withDependencies deps).gameSignature.Outcome)
    (supported : outcome ∈ (((setup.dataflowGraph.withDependencies deps).gameForm
      (setup.graphInputs deps) scheduler).play (compilePrescribedProfile setup.program deps
        (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
          target))).support) :
    (setup.graphReadout deps outcome).defaulted = ∅ ∧
      ∀ who, failedReveals setup.program who (publicOutcome setup.program
        (setup.graphReadout deps outcome)) = 0 := by
  have law := setup.compileIntendedExtension_law deps relaxed wellFormed (fun _ => ())
    (fun _ _ => (0 : ℝ)) (fun _ => 0) intended target agrees disclosing scheduler
  have readoutLaw := congrArg (PMF.map Prod.fst) law
  simp only [PMF.map_comp, Function.comp_def] at readoutLaw
  have observed : some (setup.graphReadout deps outcome) ∈
      ((setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
        (fun final => setup.protocolReadout final.state)).support := by
    rw [← readoutLaw, PMF.support_map]
    exact ⟨outcome, supported, rfl⟩
  obtain ⟨final, _, read⟩ := (PMF.mem_support_map_iff _ _ _).mp observed
  have known := setup.intendedState_trace wellFormed final.trace
  exact ⟨Finset.eq_empty_iff_forall_notMem.mpr (fun who =>
    setup.not_defaulted_of_intendedState known who read),
    fun who => setup.failedReveals_eq_zero_of_intendedState known who read⟩

end Vegas.SourceProgram.Setup
