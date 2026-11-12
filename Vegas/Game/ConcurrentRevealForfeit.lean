module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ConcurrentRevealNash
public import Vegas.Compile.BindingReveal
public import Vegas.Compile.RevealFailureReadout

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

/-- The forfeited utility of a concurrent outcome, read in instruction order. -/
def concurrentForfeitPayoff (setup : Setup (Player := Player) (L := L)) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (outcome : setup.concurrentRevealGraph.gameSignature.Outcome) (who : Player) : ℝ :=
  forfeitUtility setup.program forfeit utility
    (setup.eventParameterOutcome parameter
      ⟨setup.rankedConfig outcome.1 outcome.2, setup.rankedConfig_terminal outcome.1 outcome.2⟩)
    who

/-- A defaulted player of a reachable concurrent terminal configuration has
failed a reveal in the source-order readout. -/
theorem failedReveals_pos_of_concurrent_defaulted (setup : Setup (Player := Player) (L := L))
    {inputs : setup.concurrentRevealGraph.Inputs} {config : setup.concurrentRevealGraph.Config}
    (reach : Config.Reachable inputs config) (terminal : config.cut.Terminal) {who : Player}
    (defaulted : who ∈ config.defaulted) :
    1 ≤ failedReveals setup.program who (publicOutcome setup.program
      (terminalConfig setup.program
        ⟨setup.rankedConfig config terminal, setup.rankedConfig_terminal config terminal⟩)) := by
  obtain ⟨reveal, actor, publication, failed⟩ := failed_publication_of_defaulted
    (graph := setup.concurrentRevealGraph) (toEventGraph_bindingsRevealed setup.program) reach
    terminal defaulted
  exact failedReveals_pos_of_failed_output setup.program _ reveal who publication
    ((eventOwner?_eq_actor setup.program reveal).trans actor) failed

/-- The least utility of a player, an exit payoff no greater than any utility. -/
def leastUtility {Outcome : Type} (utility : Outcome → Player → ℝ) (who : Player) : ℝ :=
  ⨅ outcome, utility outcome who

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem leastUtility_le {Outcome : Type} (utility : Outcome → Player → ℝ) {forfeit : ℝ}
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit) (who : Player)
    (outcome : Outcome) : leastUtility utility who ≤ utility outcome who := by
  apply ciInf_le
  refine ⟨utility outcome who - forfeit, ?_⟩
  rintro _ ⟨other, rfl⟩
  have := range outcome other who
  linarith

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem sub_forfeit_le_leastUtility {Outcome : Type} (utility : Outcome → Player → ℝ)
    {forfeit : ℝ} (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (who : Player) (outcome : Outcome) :
    utility outcome who - forfeit ≤ leastUtility utility who := by
  have : Nonempty Outcome := ⟨outcome⟩
  apply le_ciInf
  intro other
  have := range outcome other who
  linarith

/-- On a reachable concurrent terminal configuration, the forfeited utility is
at most the exclusion utility with the least utility as exit payoff. -/
theorem concurrentForfeitPayoff_le (setup : Setup (Player := Player) (L := L))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) {forfeit : ℝ}
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    {inputs : setup.concurrentRevealGraph.Inputs}
    (outcome : setup.concurrentRevealGraph.gameSignature.Outcome)
    (reach : Config.Reachable inputs outcome.1) (who : Player) :
    setup.concurrentForfeitPayoff parameter utility forfeit outcome who ≤
      setup.concurrentPayoff parameter utility (leastUtility utility) who outcome.1 := by
  have nonnegative : 0 ≤ forfeit := by
    have := range (setup.eventParameterOutcome parameter
      ⟨setup.rankedConfig outcome.1 outcome.2, setup.rankedConfig_terminal _ _⟩)
      (setup.eventParameterOutcome parameter
      ⟨setup.rankedConfig outcome.1 outcome.2, setup.rankedConfig_terminal _ _⟩) who
    linarith
  unfold concurrentForfeitPayoff concurrentPayoff forfeitUtility
  rw [dite_eq_left outcome.2]
  unfold exclusionUtility
  by_cases defaulted : who ∈ outcome.1.defaulted
  · have failed := setup.failedReveals_pos_of_concurrent_defaulted reach outcome.2 defaulted
    have shown : who ∈ (setup.eventParameterOutcome parameter
        ⟨setup.rankedConfig outcome.1 outcome.2,
          setup.rankedConfig_terminal outcome.1 outcome.2⟩).2.defaulted := by
      change who ∈ (setup.rankedConfig outcome.1 outcome.2).defaulted
      rw [defaulted_rankedConfig]
      exact defaulted
    rw [ite_eq_left shown]
    have least := sub_forfeit_le_leastUtility utility range who
      (setup.eventParameterOutcome parameter
        ⟨setup.rankedConfig outcome.1 outcome.2, setup.rankedConfig_terminal _ _⟩)
    have count : (1 : ℝ) ≤ (failedReveals setup.program who (publicOutcome setup.program
      (terminalConfig setup.program ⟨setup.rankedConfig outcome.1 outcome.2,
        setup.rankedConfig_terminal _ _⟩)) : ℝ) := by exact_mod_cast failed
    change _ - forfeit * (failedReveals setup.program who (publicOutcome setup.program
      (terminalConfig setup.program ⟨setup.rankedConfig outcome.1 outcome.2,
        setup.rankedConfig_terminal _ _⟩)) : ℝ) ≤ _
    nlinarith
  · have hidden : who ∉ (setup.eventParameterOutcome parameter
        ⟨setup.rankedConfig outcome.1 outcome.2,
          setup.rankedConfig_terminal outcome.1 outcome.2⟩).2.defaulted := by
      change who ∉ (setup.rankedConfig outcome.1 outcome.2).defaulted
      rw [defaulted_rankedConfig]
      exact defaulted
    rw [ite_eq_right hidden]
    have : (0 : ℝ) ≤ forfeit * (failedReveals setup.program who
        (setup.eventParameterOutcome parameter ⟨setup.rankedConfig outcome.1 outcome.2,
          setup.rankedConfig_terminal _ _⟩).2 : ℝ) :=
      mul_nonneg nonnegative (Nat.cast_nonneg _)
    linarith

/-- A supported concurrent outcome is reachable from its initial inputs. -/
theorem concurrent_play_reachable (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.concurrentRevealGraph.PublicScheduler)
    (profile : setup.concurrentRevealGraph.BehavioralProfile)
    (outcome : setup.concurrentRevealGraph.gameSignature.Outcome)
    (supported : outcome ∈ ((setup.concurrentRevealGraph.gameForm setup.concurrentInputs
      scheduler).play profile).support) :
    ∃ inputs, Config.Reachable inputs outcome.1 := by
  change outcome ∈ (setup.concurrentInputs.bind _).support at supported
  rw [PMF.support_bind] at supported
  simp only [Set.mem_iUnion] at supported
  obtain ⟨initial, _, member⟩ := supported
  have inRun : outcome.1 ∈ (setup.concurrentRevealGraph.runPolicies scheduler profile
      initial).support := by
    rw [← setup.concurrentRevealGraph.terminalOutcomes_map_val, PMF.support_map]
    exact ⟨outcome, member, rfl⟩
  exact ⟨initial, setup.concurrentRevealGraph.run_reachable initial _ outcome.1 inRun⟩

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
    (scheduler : setup.concurrentRevealGraph.PublicScheduler) :
    IsεNash (setup.concurrentRevealGraph.gameForm setup.concurrentInputs scheduler)
        (setup.concurrentForfeitPayoff parameter utility forfeit) ε
        (setup.concurrentRevealGraph.normalizeProfile (compileEventProfile setup.program
          (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
            target))) ∧
      (∀ outcome ∈ ((setup.concurrentRevealGraph.gameForm setup.concurrentInputs scheduler).play
          (setup.concurrentRevealGraph.normalizeProfile (compileEventProfile setup.program
            (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
              target)))).support,
        (setup.concurrentReadout outcome).defaulted = ∅ ∧
          ∀ who, failedReveals setup.program who
            (publicOutcome setup.program (setup.concurrentReadout outcome)) = 0) ∧
      ((setup.concurrentRevealGraph.gameForm setup.concurrentInputs scheduler).play
          (setup.concurrentRevealGraph.normalizeProfile (compileEventProfile setup.program
            (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
              target)))).map (fun outcome => (some (setup.concurrentReadout outcome),
            setup.concurrentForfeitPayoff parameter utility forfeit outcome)) =
        (setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
          (fun final => (setup.protocolReadout final.state, fun who =>
            (setup.protocolReadout final.state).elim 0
              (fun state => utility (setup.parameterOutcome parameter state) who))) := by
  let honest := setup.concurrentRevealGraph.normalizeProfile (compileEventProfile setup.program
    (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target))
  let game := setup.concurrentRevealGraph.gameForm setup.concurrentInputs scheduler
  let exitPayoff := leastUtility utility
  let exclusion : setup.concurrentRevealGraph.gameSignature.Outcome → Player → ℝ :=
    fun outcome who =>
    setup.concurrentPayoff parameter utility exitPayoff who outcome.1
  have nashExclusion := setup.concurrentReveal_intended_isεNash finite wellFormed parameter
    utility exitPayoff (fun outcome who => leastUtility_le utility range who outcome) intended
    target agrees ε equilibrium disclosing scheduler
  have lawExclusion := setup.concurrentReveal_intended_law finite wellFormed parameter utility
    exitPayoff (fun outcome who => leastUtility_le utility range who outcome) intended target
    agrees ε equilibrium disclosing scheduler
  have clean : ∀ outcome ∈ (game.play honest).support,
      (setup.concurrentReadout outcome).defaulted = ∅ ∧
        ∀ who, failedReveals setup.program who
          (publicOutcome setup.program (setup.concurrentReadout outcome)) = 0 := by
    intro outcome supported
    have pair : (some (setup.concurrentReadout outcome), exclusion outcome) ∈
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
  -- On honest play the two utilities agree.
  have honestEq : ∀ outcome ∈ (game.play honest).support,
      setup.concurrentForfeitPayoff parameter utility forfeit outcome = exclusion outcome := by
    intro outcome supported
    have pair : (some (setup.concurrentReadout outcome), exclusion outcome) ∈
        ((setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
          (fun final => (setup.protocolReadout final.state, fun who =>
            (setup.protocolReadout final.state).elim 0
              (fun state => utility (setup.parameterOutcome parameter state) who)))).support := by
      rw [← lawExclusion, PMF.support_map]
      exact ⟨outcome, supported, rfl⟩
    rw [PMF.support_map] at pair
    obtain ⟨final, _, same⟩ := pair
    have read : setup.protocolReadout final.state = some (setup.concurrentReadout outcome) :=
      congrArg Prod.fst same
    have payoffs : exclusion outcome = fun who => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who) :=
      (congrArg Prod.snd same).symm
    funext who
    have clean := setup.failedReveals_eq_zero_of_intendedState
      (setup.intendedState_trace wellFormed final.trace) who read
    rw [congrFun payoffs who]
    simp only [read, Option.elim_some]
    unfold concurrentForfeitPayoff forfeitUtility
    change _ - forfeit * (failedReveals setup.program who
      (publicOutcome setup.program (setup.concurrentReadout outcome)) : ℝ) = _
    rw [clean]
    simp only [Nat.cast_zero, mul_zero, sub_zero]
    rfl
  refine ⟨?_, clean, ?_⟩
  · rw [IsεNash, isNash_iff] at nashExclusion ⊢
    intro who deviation
    have support (chosen : Profile game.sig) : (game.play chosen).support.Finite :=
      setup.concurrentRevealGraph.gameForm_play_support_finite _
        setup.concurrentInputs_support_finite scheduler chosen
        ((toEventGraph_finiteActions setup.program finite).profileFiniteSupport chosen)
    let deviating := Profile.update (sig := game.sig) honest who deviation
    have forfeitHonest : UtilityIntegrable (setup.concurrentForfeitPayoff parameter utility
        forfeit) who (game.play honest) := payoffIntegrable_of_finite_support _ _ (support _)
    have forfeitDeviation : UtilityIntegrable (setup.concurrentForfeitPayoff parameter utility
        forfeit) who (game.play deviating) := payoffIntegrable_of_finite_support _ _ (support _)
    have exclusionHonest : UtilityIntegrable exclusion who (game.play honest) :=
      payoffIntegrable_of_finite_support _ _ (support _)
    have exclusionDeviation : UtilityIntegrable exclusion who (game.play deviating) :=
      payoffIntegrable_of_finite_support _ _ (support _)
    obtain ⟨_, _, preference⟩ := nashExclusion who deviation
    have real : expectedUtility exclusion who (game.play deviating) ≤
        expectedUtility exclusion who (game.play honest) + ε := by
      have lifted : ((expectedUtility exclusion who (game.play deviating) : ℝ) : EReal) ≤
          ((expectedUtility exclusion who (game.play honest) : ℝ) : EReal) + (ε : EReal) := by
        rw [← extendedExpectedUtility_eq exclusionHonest,
          ← extendedExpectedUtility_eq exclusionDeviation]
        exact preference
      exact_mod_cast lifted
    refine ⟨forfeitHonest.hasExpectation, forfeitDeviation.hasExpectation, ?_⟩
    rw [extendedExpectedUtility_eq forfeitHonest, extendedExpectedUtility_eq forfeitDeviation]
    refine EReal.coe_le_coe_iff.mpr ?_ |>.trans_eq (EReal.coe_add _ _)
    have below : expectedUtility (setup.concurrentForfeitPayoff parameter utility forfeit) who
        (game.play deviating) ≤ expectedUtility exclusion who (game.play deviating) := by
      unfold expectedUtility
      apply expect_mono _ forfeitDeviation exclusionDeviation
      intro outcome supported
      obtain ⟨inputs, reach⟩ := setup.concurrent_play_reachable scheduler deviating outcome
        supported
      exact setup.concurrentForfeitPayoff_le parameter utility range outcome reach who
    have same : expectedUtility (setup.concurrentForfeitPayoff parameter utility forfeit) who
        (game.play honest) = expectedUtility exclusion who (game.play honest) := by
      unfold expectedUtility
      apply expect_congr_on_support
      intro outcome supported
      rw [honestEq outcome supported]
    rw [same]
    exact below.trans real
  · rw [← lawExclusion]
    apply map_congr_on_support _
    intro outcome supported
    rw [honestEq outcome supported]

end Vegas.SourceProgram.Setup
