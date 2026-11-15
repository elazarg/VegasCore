module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourcePrefixNash
public import Vegas.Game.GraphForfeit
public import GameTheoryExtensions.Analysis.UtilityComparison

@[expose] public section

/-! # Intended Nash preservation with concurrent commitments and forfeiture

The fixed-exit comparison applies to every valid dependency choice retaining
the reveal-relaxed barriers. Intended play has its full source configuration
and utility law; arbitrary deviations remain available in the graph game.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open Vegas.EventGraph GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Intended Nash error, the complete configuration/payoff law and absence of
defaults and failed reveals are preserved under every permitted graph scheduler. -/
theorem compileIntendedExtension_forfeit (setup : Setup (Player := Player) (L := L))
    [Finite Player] (deps : setup.dataflowGraph.Dependencies)
    (relaxed : (setup.dataflowGraph.withDependencies deps).RevealRelaxedOrdered)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
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
        (fun terminal => utility (setup.parameterOutcome parameter terminal) who)) ε intended)
    (scheduler : (setup.dataflowGraph.withDependencies deps).PublicScheduler) :
    IsεNash ((setup.dataflowGraph.withDependencies deps).gameForm (setup.graphInputs deps)
      scheduler)
        (setup.graphForfeitPayoff deps parameter utility forfeit) ε
        (compilePrescribedProfile setup.program deps (setup.decodeBehavioralProfile
          (CommitmentInterface.forfeiture setup.program) target)) ∧
      (∀ outcome ∈ (((setup.dataflowGraph.withDependencies deps).gameForm (setup.graphInputs deps)
          scheduler).play (compilePrescribedProfile setup.program deps
            (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
              target))).support,
        (setup.graphReadout deps outcome).defaulted = ∅ ∧
          ∀ who, failedReveals setup.program who
            (publicOutcome setup.program (setup.graphReadout deps outcome)) = 0) ∧
      (((setup.dataflowGraph.withDependencies deps).gameForm (setup.graphInputs deps)
        scheduler).play (compilePrescribedProfile setup.program deps
          (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
            target))).map (fun outcome =>
            (some (setup.graphReadout deps outcome),
              setup.graphForfeitPayoff deps parameter utility forfeit outcome)) =
        (setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
          (fun final => (setup.protocolReadout final.state, fun who =>
            (setup.protocolReadout final.state).elim 0
              (fun terminal => utility (setup.parameterOutcome parameter terminal) who))) := by
  let graph := setup.dataflowGraph.withDependencies deps
  let game := graph.gameForm (setup.graphInputs deps) scheduler
  let clients := compilePrescribedProfile setup.program deps (setup.decodeBehavioralProfile
    (CommitmentInterface.forfeiture setup.program) target)
  let excluded := leastUtility utility
  let upper : graph.gameSignature.Outcome → Player → ℝ := fun outcome who =>
    setup.graphPayoff deps parameter utility excluded who outcome.1
  have nash := setup.isεNash_compileIntendedExtension deps relaxed finite wellFormed parameter
    utility excluded (fun outcome who => leastUtility_le utility range who outcome)
    intended target agrees disclosing ε equilibrium scheduler
  have clean := setup.compileIntendedExtension_clean deps relaxed wellFormed intended target agrees
    disclosing scheduler
  have same (outcome : graph.gameSignature.Outcome) (supported : outcome ∈ (game.play
    clients).support)
      (who : Player) : setup.graphForfeitPayoff deps parameter utility forfeit outcome who =
      upper outcome who := by
    have safe := clean outcome supported
    exact setup.graphForfeitPayoff_eq_graphPayoff_of_clean deps parameter utility forfeit excluded
      outcome who (by rw [safe.1]; exact Finset.notMem_empty _) (safe.2 who)
  refine ⟨?_, clean, ?_⟩
  · apply nash.of_utility_le_on_support
    · intro who outcome supported
      exact same outcome supported who
    · intro who replacement outcome supported
      obtain ⟨initial, reached⟩ := setup.graph_play_reachable deps scheduler
        (Profile.update (sig := graph.gameSignature) clients who replacement) outcome supported
      exact setup.graphForfeitPayoff_le deps parameter utility range outcome reached who
    · intro who replacement
      apply UtilityIntegrable.hasExpectation
      apply payoffIntegrable_of_finite_support
      exact graph.gameForm_play_support_finite (setup.graphInputs deps)
        (setup.graphInputs_support_finite deps) scheduler
        (Profile.update (sig := game.sig) clients who replacement)
        ((toInformationGraph_finiteActions setup.program finite).profileFiniteSupport _)
  · have law := setup.compileIntendedExtension_law deps relaxed wellFormed parameter utility
      excluded intended target agrees disclosing scheduler
    refine Eq.trans ?_ law
    apply map_congr_on_support _
    intro outcome supported
    exact Prod.ext rfl (funext fun who => same outcome supported who)

end Vegas.SourceProgram.Setup
