module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import GameTheoryExtensions.Analysis.UtilityComparison
public import Vegas.Game.ConcurrentRevealNash
public import Vegas.Game.GraphForfeit

@[expose] public section

/-! # Intended-game Nash under concurrent reveals with the forfeit pass

Under every public scheduler of the compiled graph with independent reveals
concurrent, a defaulted player has failed a reveal, so with a forfeit at least
the payoff range its forfeited utility is at most the least utility. The
forfeited utility is therefore below the exclusion utility with that exit
payoff, and equals it on intended play, so the exclusion-utility equilibrium
is an equilibrium of the forfeited utility, with the same intended law.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open Vegas.EventGraph GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- **Intended-game Nash under every schedule of concurrent reveals, with the
forfeit pass.** For a well-formed setup with finite commitment payload types, a
forfeit no smaller than the payoff range, and a source profile that discloses
at every reveal and extends an `ε`-Nash equilibrium of the intended game, the
order-blind compiled clients are an `ε`-Nash equilibrium for the forfeited
utility under every public scheduler, with the intended joint law of terminal
configuration and payoff vector, and no public default or failed reveal. -/
theorem concurrentReveal_intended_forfeit (setup : Setup (Player := Player) (L := L))
    [Finite Player] (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
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
        (setup.graphForfeitPayoff setup.revealDependencies parameter utility forfeit) ε
        (setup.revealRelaxedGraph.normalizeProfile (compileEventProfile setup.program
          (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
            target))) ∧
      (∀ outcome ∈ ((setup.revealRelaxedGraph.gameForm (setup.graphInputs setup.revealDependencies)
          scheduler).play
          (setup.revealRelaxedGraph.normalizeProfile (compileEventProfile setup.program
            (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
              target)))).support,
        (setup.graphReadout setup.revealDependencies outcome).defaulted = ∅ ∧
          ∀ who, failedReveals setup.program who
            (publicOutcome setup.program (setup.graphReadout setup.revealDependencies outcome)) =
                0) ∧
      ((setup.revealRelaxedGraph.gameForm (setup.graphInputs setup.revealDependencies)
          scheduler).play
          (setup.revealRelaxedGraph.normalizeProfile (compileEventProfile setup.program
            (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
              target)))).map (fun outcome => (some (setup.graphReadout setup.revealDependencies
                  outcome),
            setup.graphForfeitPayoff setup.revealDependencies parameter utility forfeit outcome)) =
        (setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
          (fun final => (setup.protocolReadout final.state, fun who =>
            (setup.protocolReadout final.state).elim 0
              (fun state => utility (setup.parameterOutcome parameter state) who))) := by
  let honest := setup.revealRelaxedGraph.normalizeProfile (compileEventProfile setup.program
    (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target))
  let game := setup.revealRelaxedGraph.gameForm (setup.graphInputs setup.revealDependencies)
      scheduler
  let exitPayoff := leastUtility utility
  let exclusion : setup.revealRelaxedGraph.gameSignature.Outcome → Player → ℝ :=
    fun outcome who =>
    setup.graphPayoff setup.revealDependencies parameter utility exitPayoff who outcome.1
  have nashExclusion := setup.concurrentReveal_intended_isεNash finite wellFormed parameter
    utility exitPayoff (fun outcome who => leastUtility_le utility range who outcome) intended
    target agrees ε equilibrium disclosing scheduler
  have lawExclusion := setup.concurrentReveal_intended_law finite wellFormed parameter utility
    exitPayoff (fun outcome who => leastUtility_le utility range who outcome) intended target
    agrees ε equilibrium disclosing scheduler
  have clean : ∀ outcome ∈ (game.play honest).support,
      (setup.graphReadout setup.revealDependencies outcome).defaulted = ∅ ∧
        ∀ who, failedReveals setup.program who
          (publicOutcome setup.program (setup.graphReadout setup.revealDependencies outcome)) = 0
              := by
    intro outcome supported
    have pair : (some (setup.graphReadout setup.revealDependencies outcome), exclusion outcome) ∈
        ((setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
          (fun final => (setup.protocolReadout final.state, fun who =>
            (setup.protocolReadout final.state).elim 0
              (fun state => utility (setup.parameterOutcome parameter state) who)))).support := by
      rw [← lawExclusion, PMF.support_map]
      exact ⟨outcome, supported, rfl⟩
    obtain ⟨final, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp pair
    have read := congrArg Prod.fst same
    have intendedState := setup.intendedState_trace wellFormed final.trace
    exact ⟨Finset.eq_empty_iff_forall_notMem.mpr fun who =>
      setup.not_defaulted_of_intendedState intendedState who read,
      fun who => setup.failedReveals_eq_zero_of_intendedState intendedState who read⟩
  have honestEq : ∀ outcome ∈ (game.play honest).support,
      setup.graphForfeitPayoff setup.revealDependencies parameter utility forfeit outcome =
          exclusion outcome := by
    intro outcome supported
    funext who
    apply setup.graphForfeitPayoff_eq_graphPayoff_of_clean setup.revealDependencies
      parameter utility forfeit exitPayoff outcome who
    · rw [(clean outcome supported).1]
      exact Finset.notMem_empty who
    · exact (clean outcome supported).2 who
  refine ⟨?_, clean, ?_⟩
  · apply nashExclusion.of_utility_le_on_support
    · intro who outcome supported
      exact congrFun (honestEq outcome supported) who
    · intro who deviation outcome supported
      obtain ⟨inputs, reach⟩ := setup.graph_play_reachable setup.revealDependencies scheduler
        (Profile.update (sig := game.sig) honest who deviation) outcome supported
      exact setup.graphForfeitPayoff_le setup.revealDependencies parameter utility range outcome
        reach who
    · intro who deviation
      apply UtilityIntegrable.hasExpectation
      apply payoffIntegrable_of_finite_support
      exact setup.revealRelaxedGraph.gameForm_play_support_finite _
        (setup.graphInputs_support_finite setup.revealDependencies) scheduler
        (Profile.update (sig := game.sig) honest who deviation)
        ((toInformationGraph_finiteActions setup.program finite).profileFiniteSupport _)
  · rw [← lawExclusion]
    apply map_congr_on_support _
    intro outcome supported
    rw [honestEq outcome supported]

end Vegas.SourceProgram.Setup
