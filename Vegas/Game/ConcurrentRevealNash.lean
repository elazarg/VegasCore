module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.PublicationPolicy
public import Vegas.EventGraph.ConcurrentRevealNash
public import Vegas.EventGraph.SequentialNormalization
public import Vegas.Compile.ConcurrentRevealGraph
public import Vegas.Game.GraphPayoff
public import Vegas.Game.IntendedNash
public import Vegas.Source.Utility
public import Vegas.Source.ValueBindingAdmission

@[expose] public section

/-! # Intended-game Nash equilibria under every schedule of concurrent reveals

Relax the reveal dependencies of the compiled graph, so that independent
reveals may complete in any order a public scheduler chooses. A player's payoff
reads the outcome with default entries in instruction order, and is the
excluded payoff once the player has defaulted. The compiled clients of a source
profile that discloses at every reveal and extends an `ε`-Nash equilibrium of
the intended game, normalized to ignore completion order, are an `ε`-Nash
equilibrium under every public scheduler.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open Vegas.EventGraph GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Under canonical scheduling, normalization changes no play of the compiled game. -/
theorem canonicalEventGame_play_normalizeProfile (setup : Setup (Player := Player) (L := L))
    (profile : setup.informationGraph.BehavioralProfile) :
    setup.canonicalEventGame.play (setup.informationGraph.normalizeProfile profile) =
      setup.canonicalEventGame.play profile := by
  change (setup.graphInputs setup.revealDependencies).bind (setup.informationGraph.terminalOutcomes
      _ _) =
    (setup.graphInputs setup.revealDependencies).bind (setup.informationGraph.terminalOutcomes _ _)
  congr 1
  funext initial
  apply pmf_map_injective (f := Subtype.val) Subtype.val_injective
  rw [EventGraph.terminalOutcomes_map_val, EventGraph.terminalOutcomes_map_val]
  exact runPolicies_canonical_normalizeProfile setup.informationGraph_total profile initial

/-- **Intended-game Nash under every schedule of concurrent reveals.** For a
well-formed setup with finite commitment payload types and an excluded payoff
below every utility, let a source profile disclose at every reveal and extend
an `ε`-Nash equilibrium of the intended game under the forfeiture interface.
On the compiled graph with independent reveals concurrent, its compiled
clients, normalized to ignore completion order, are an `ε`-Nash equilibrium
under every public scheduler, for the exclusion utility of the outcome read in
instruction order. -/
theorem concurrentReveal_intended_isεNash (setup : Setup (Player := Player) (L := L))
    [Finite Player] (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (low : ∀ outcome who, excludedPayoff who ≤ utility outcome who)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target) (ε : ℝ)
    (equilibrium : IsεNash (setup.intendedModel.toBehavioralGameForm
        (instructionCount setup.program + 1))
      (fun final who => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)) ε intended)
    (disclosing : ∀ who, Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    (scheduler : setup.revealRelaxedGraph.PublicScheduler) :
    IsεNash (setup.revealRelaxedGraph.gameForm (setup.graphInputs setup.revealDependencies)
        scheduler)
      (fun outcome who => setup.graphPayoff setup.revealDependencies parameter utility
          excludedPayoff who outcome.1) ε
      (setup.revealRelaxedGraph.normalizeProfile (compileEventProfile setup.program
        (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
          target))) := by
  let admission := CommitmentInterface.forfeiture setup.program
  let source := setup.decodeBehavioralProfile admission target
  let compiled : setup.informationGraph.BehavioralProfile := compileEventProfile setup.program
    source
  let exclusion := exclusionUtility setup.program excludedPayoff utility
  have actions := toInformationGraph_finiteActions setup.program finite
  -- The source chain: intended Nash, protocol Nash, source Nash, compiled canonical Nash.
  have protocolNash := (setup.intended_isεNash_preserved admission finite wellFormed parameter
    utility excludedPayoff (fun _ _ _ who => low _ who) intended target agrees ε equilibrium).1
  have sourceNash := (setup.parameterProtocol_isεNash_iff admission
    (fun _ policy => policy.admitted_forfeiture setup.program) parameter exclusion ε target).mp
      protocolNash
  have graphNash := (setup.parameterEventGame_approximate_nash_iff parameter finite
    setup.informationGraph.canonicalScheduler exclusion ε source).mpr sourceNash
  rw [IsεNash, isNash_iff] at graphNash
  have canonicalBound (who : Player) (policy : setup.informationGraph.BehavioralPolicy who) :
      expect (setup.canonicalEventGame.play
          (Profile.update (sig := setup.informationGraph.gameSignature) compiled who policy))
          (fun outcome => exclusion (setup.eventParameterOutcome parameter outcome) who) ≤
        expect (setup.canonicalEventGame.play compiled)
          (fun outcome => exclusion (setup.eventParameterOutcome parameter outcome) who) + ε := by
    have preference := graphNash who policy
    rwa [euPreferenceWithin_iff _ _ _ _ _
      (payoffIntegrable_of_finite_support _ _ (setup.eventGame_play_support_finite finite _ _))
      (payoffIntegrable_of_finite_support _ _ (setup.eventGame_play_support_finite finite _ _))]
      at preference
  -- The compiled clients open decisively and ignore observations at publications.
  have opens (who : Player) (event : setup.revealRelaxedGraph.EventId)
      (actor : setup.revealRelaxedGraph.actor? event = some who)
      (publication : (setup.revealRelaxedGraph.outputLayout event).IsPublication)
      (observation : setup.revealRelaxedGraph.PlayerObservation who)
      (active : who ∉ observation.defaulted) :
      compiled who event actor observation active =
        PMF.pure (EventField.openAction _ publication) :=
    compileEventPolicy_publication setup.program who (source who) (disclosing who) event actor
      publication observation active
  have oblivious : setup.revealRelaxedGraph.ObliviousAtPublications compiled :=
    fun who event actor publication left right leftActive rightActive => by
      rw [opens who event actor publication left leftActive,
        opens who event actor publication right rightActive]
  have canonicalConcurrent (who : Player) (profile : setup.informationGraph.BehavioralProfile) :
      expect ((setup.graphInputs setup.revealDependencies).bind
          (setup.revealRelaxedGraph.runPolicies
          setup.revealRelaxedGraph.canonicalScheduler
            (setup.revealRelaxedGraph.normalizeProfile profile)))
          (setup.graphPayoff setup.revealDependencies parameter utility excludedPayoff who) =
        expect (setup.canonicalEventGame.play profile)
          (fun outcome => exclusion (setup.eventParameterOutcome parameter outcome) who) :=
    (setup.expect_graphPayoff_canonical setup.revealDependencies parameter utility
        excludedPayoff who
      (setup.informationGraph.normalizeProfile profile)).trans
        (congrArg (fun law => expect law (fun outcome =>
          exclusion (setup.eventParameterOutcome parameter outcome) who))
          (setup.canonicalEventGame_play_normalizeProfile profile))
  have only : setup.revealRelaxedGraph.RevealsOnlyConcurrent :=
    setup.informationGraph.relaxReveals_revealsOnlyConcurrent setup.informationGraph_total
  exact only.isεNash_normalizeProfile actions compiled oblivious
    (fun who => opensDecisively_of_opens who _ fun _ event actor publication active =>
      opens who event actor publication _ _)
    (fun who => setup.graphPayoff setup.revealDependencies parameter utility excludedPayoff who)
    (fun who => setup.graphPayoff_factors setup.revealDependencies parameter utility excludedPayoff
        who)
    excludedPayoff
    (fun who => setup.le_graphPayoff setup.revealDependencies parameter utility excludedPayoff who
      (fun outcome => low outcome who))
    (fun who => setup.graphPayoff_of_defaulted setup.revealDependencies parameter utility
        excludedPayoff who)
    (setup.graphInputs setup.revealDependencies) (setup.graphInputs_support_finite
        setup.revealDependencies) ε
    (fun who policy => by
      rw [canonicalConcurrent who, canonicalConcurrent who]
      exact canonicalBound who policy)
    scheduler

/-- **Intended law under every schedule of concurrent reveals.** Under the
hypotheses of `concurrentReveal_intended_isεNash`, the order-blind compiled
clients have, under every public scheduler, the intended joint law of terminal
configuration, read in instruction order, and payoff vector. -/
theorem concurrentReveal_intended_law (setup : Setup (Player := Player) (L := L))
    [Finite Player] (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (low : ∀ outcome who, excludedPayoff who ≤ utility outcome who)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target) (ε : ℝ)
    (equilibrium : IsεNash (setup.intendedModel.toBehavioralGameForm
        (instructionCount setup.program + 1))
      (fun final who => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)) ε intended)
    (disclosing : ∀ who, Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    (scheduler : setup.revealRelaxedGraph.PublicScheduler) :
    ((setup.revealRelaxedGraph.gameForm (setup.graphInputs setup.revealDependencies) scheduler).play
        (setup.revealRelaxedGraph.normalizeProfile (compileEventProfile setup.program
          (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
            target)))).map (fun outcome => (some (setup.graphReadout setup.revealDependencies
                outcome),
          fun who => setup.graphPayoff setup.revealDependencies parameter utility excludedPayoff
              who outcome.1)) =
      (setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
        (fun final => (setup.protocolReadout final.state, fun who =>
          (setup.protocolReadout final.state).elim 0
            (fun state => utility (setup.parameterOutcome parameter state) who))) := by
  let admission := CommitmentInterface.forfeiture setup.program
  let source := setup.decodeBehavioralProfile admission target
  let compiled : setup.informationGraph.BehavioralProfile := compileEventProfile setup.program
    source
  let exclusion := exclusionUtility setup.program excludedPayoff utility
  have preserved := setup.intended_isεNash_preserved admission finite wellFormed parameter
    utility excludedPayoff (fun _ _ _ who => low _ who) intended target agrees ε equilibrium
  have opens (who : Player) (event : setup.revealRelaxedGraph.EventId)
      (actor : setup.revealRelaxedGraph.actor? event = some who)
      (publication : (setup.revealRelaxedGraph.outputLayout event).IsPublication)
      (observation : setup.revealRelaxedGraph.PlayerObservation who)
      (active : who ∉ observation.defaulted) :
      compiled who event actor observation active =
        PMF.pure (EventField.openAction _ publication) :=
    compileEventPolicy_publication setup.program who (source who) (disclosing who) event actor
      publication observation active
  have oblivious : setup.revealRelaxedGraph.ObliviousAtPublications compiled :=
    fun who event actor publication left right leftActive rightActive => by
      rw [opens who event actor publication left leftActive,
        opens who event actor publication right rightActive]
  have only : setup.revealRelaxedGraph.RevealsOnlyConcurrent :=
    setup.informationGraph.relaxReveals_revealsOnlyConcurrent setup.informationGraph_total
  -- Play to runs.
  have mapped : ((setup.revealRelaxedGraph.gameForm (setup.graphInputs setup.revealDependencies)
      scheduler).play
      (setup.revealRelaxedGraph.normalizeProfile compiled)).map Subtype.val =
        (setup.graphInputs setup.revealDependencies).bind (setup.revealRelaxedGraph.runPolicies
            scheduler
          (setup.revealRelaxedGraph.normalizeProfile compiled)) := by
    change ((setup.graphInputs setup.revealDependencies).bind _).map Subtype.val = _
    rw [PMF.map_bind]
    simp only [EventGraph.terminalOutcomes_map_val]
  have observed : (fun outcome : setup.revealRelaxedGraph.gameSignature.Outcome =>
      (some (setup.graphReadout setup.revealDependencies outcome),
        fun who => setup.graphPayoff setup.revealDependencies parameter utility excludedPayoff who
            outcome.1)) =
      setup.graphObservation setup.revealDependencies parameter utility excludedPayoff ∘
          Subtype.val := by
    funext outcome
    simp only [Function.comp_apply, graphObservation, dite_eq_left outcome.2,
      graphReadout]
  change PMF.map _ ((setup.revealRelaxedGraph.gameForm (setup.graphInputs setup.revealDependencies)
      scheduler).play
    (setup.revealRelaxedGraph.normalizeProfile compiled)) = _
  rw [observed, ← PMF.map_comp, mapped,
    only.runPolicies_map_eq_canonical compiled oblivious scheduler (setup.graphInputs
        setup.revealDependencies) _
      (setup.graphObservation_factors setup.revealDependencies parameter utility excludedPayoff)]
  have canonicalLaw :
      ((setup.graphInputs setup.revealDependencies).bind
        (setup.revealRelaxedGraph.runPolicies setup.revealRelaxedGraph.canonicalScheduler
          (setup.revealRelaxedGraph.normalizeProfile compiled))).map
            (setup.graphObservation setup.revealDependencies parameter utility excludedPayoff) =
        (setup.canonicalEventGame.play compiled).map (fun outcome =>
          (some (terminalConfig setup.program outcome), fun who =>
            exclusionUtility setup.program excludedPayoff utility
              (setup.eventParameterOutcome parameter outcome) who)) :=
    (setup.canonical_graphObservation_law setup.revealDependencies parameter utility excludedPayoff
      (setup.informationGraph.normalizeProfile compiled)).trans
        (congrArg (fun law => law.map (fun outcome =>
          (some (terminalConfig setup.program outcome), fun who =>
            exclusionUtility setup.program excludedPayoff utility
              (setup.eventParameterOutcome parameter outcome) who)))
          (setup.canonicalEventGame_play_normalizeProfile compiled))
  rw [canonicalLaw]
  -- The compiled canonical law is the source law.
  have sourceLaw := canonical_setup_law setup source
  have throughSource : (setup.canonicalEventGame.play compiled).map (fun outcome =>
      (some (terminalConfig setup.program outcome), fun who =>
        exclusion (setup.eventParameterOutcome parameter outcome) who)) =
      (setup.run source).map (fun terminal => (some terminal, fun who =>
        exclusion (setup.parameterOutcome parameter terminal) who)) := by
    rw [← sourceLaw, PMF.map_comp]
    rfl
  rw [throughSource]
  -- The source law is the protocol readout law.
  have protocolLaw := (setup.protocol_readout_law admission).1 target
  have viaSome : (setup.run source).map (fun terminal => (some terminal, fun who =>
      exclusion (setup.parameterOutcome parameter terminal) who)) =
      ((setup.run source).map some).map (fun readout => (readout, fun who =>
        readout.elim 0 (fun terminal => exclusion (setup.parameterOutcome parameter terminal)
          who))) := by
    rw [PMF.map_comp]
    rfl
  rw [viaSome, ← protocolLaw, PMF.map_comp]
  exact preserved.2.2

end Vegas.SourceProgram.Setup
