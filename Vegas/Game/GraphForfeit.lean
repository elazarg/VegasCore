module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.GraphPayoff
public import Vegas.Compile.BindingReveal
public import Vegas.Compile.RevealFailureReadout

@[expose] public section

/-! # Forfeiture payoffs for compiled graphs

Every defaulted player in a reachable terminal configuration has failed a reveal.
When the forfeiture covers the utility spread, forfeited utility is bounded by
fixed-exit utility with the least utility as its exit value. These statements
apply to every valid dependency choice on the compiled event code.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open Vegas.EventGraph GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The forfeited utility of a graph outcome, read in instruction order. -/
def graphForfeitPayoff (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (outcome : (setup.dataflowGraph.withDependencies deps).gameSignature.Outcome)
    (who : Player) : ℝ :=
  forfeitUtility setup.program forfeit utility
    (setup.eventParameterOutcome parameter
      ⟨rankedConfig (graph := (setup.dataflowGraph.withDependencies deps)) outcome.1 outcome.2,
          rankedConfig_terminal (graph := (setup.dataflowGraph.withDependencies deps))
            outcome.1 outcome.2⟩)
    who

/-- A player with no default or failed reveal in the source readout has the
same forfeited utility and fixed-exit utility, for any exit payoff. -/
theorem graphForfeitPayoff_eq_graphPayoff_of_clean
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (excludedPayoff : Player → ℝ)
    (outcome : (setup.dataflowGraph.withDependencies deps).gameSignature.Outcome) (who : Player)
    (active : who ∉ (setup.graphReadout deps outcome).defaulted)
    (clean : failedReveals setup.program who
      (publicOutcome setup.program (setup.graphReadout deps outcome)) = 0) :
    setup.graphForfeitPayoff deps parameter utility forfeit outcome who =
      setup.graphPayoff deps parameter utility excludedPayoff who outcome.1 := by
  unfold graphForfeitPayoff graphPayoff
  rw [dite_eq_left outcome.2]
  change forfeitUtility setup.program forfeit utility
      (setup.parameterOutcome parameter (setup.graphReadout deps outcome)) who =
    exclusionUtility setup.program excludedPayoff utility
      (setup.parameterOutcome parameter (setup.graphReadout deps outcome)) who
  rw [exclusionUtility_of_not_defaulted setup.program excludedPayoff utility
    (outcome := setup.parameterOutcome parameter (setup.graphReadout deps outcome)) active]
  change utility _ who - forfeit * (failedReveals setup.program who
    (publicOutcome setup.program (setup.graphReadout deps outcome)) : ℝ) = utility _ who
  rw [clean]
  simp only [Nat.cast_zero, mul_zero, sub_zero]

/-- A defaulted player of a reachable graph terminal configuration has
failed a reveal in the source-order readout. -/
theorem failedReveals_pos_of_graph_defaulted (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies)
    {inputs : (setup.dataflowGraph.withDependencies deps).Inputs}
    {config : (setup.dataflowGraph.withDependencies deps).Config}
    (reach : Config.Reachable inputs config) (terminal : config.cut.Terminal) {who : Player}
    (defaulted : who ∈ config.defaulted) :
    1 ≤ failedReveals setup.program who (publicOutcome setup.program
      (terminalConfig setup.program
        ⟨rankedConfig (graph := (setup.dataflowGraph.withDependencies deps)) config terminal,
          rankedConfig_terminal
            (graph := (setup.dataflowGraph.withDependencies deps)) config terminal⟩)) := by
  obtain ⟨reveal, actor, publication, failed⟩ := failed_publication_of_defaulted
    (graph := (setup.dataflowGraph.withDependencies deps))
    (toInformationGraph_bindingsRevealed setup.program) reach terminal defaulted
  exact failedReveals_pos_of_failed_output setup.program _ reveal who publication
    ((eventOwner?_eq_actor setup.program reveal).trans actor) failed

/-- The infimum utility, used as an exit payoff under the utility-spread bound. -/
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

/-- On a reachable graph terminal configuration, the forfeited utility is
at most the exclusion utility with the least utility as exit payoff. -/
theorem graphForfeitPayoff_le (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) {forfeit : ℝ}
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    {inputs : (setup.dataflowGraph.withDependencies deps).Inputs}
    (outcome : (setup.dataflowGraph.withDependencies deps).gameSignature.Outcome)
    (reach : Config.Reachable inputs outcome.1) (who : Player) :
    setup.graphForfeitPayoff deps parameter utility forfeit outcome who ≤
      setup.graphPayoff deps parameter utility (leastUtility utility) who outcome.1 := by
  have nonnegative : 0 ≤ forfeit := by
    have := range (setup.eventParameterOutcome parameter
      ⟨rankedConfig (graph := (setup.dataflowGraph.withDependencies deps)) outcome.1 outcome.2,
          rankedConfig_terminal (graph := (setup.dataflowGraph.withDependencies deps)) _ _⟩)
      (setup.eventParameterOutcome parameter
      ⟨rankedConfig (graph := (setup.dataflowGraph.withDependencies deps)) outcome.1 outcome.2,
          rankedConfig_terminal (graph := (setup.dataflowGraph.withDependencies deps)) _ _⟩) who
    linarith
  unfold graphForfeitPayoff graphPayoff forfeitUtility
  rw [dite_eq_left outcome.2]
  unfold exclusionUtility
  by_cases defaulted : who ∈ outcome.1.defaulted
  · have failed := setup.failedReveals_pos_of_graph_defaulted deps reach outcome.2 defaulted
    have shown : who ∈ (setup.eventParameterOutcome parameter
        ⟨rankedConfig (graph := (setup.dataflowGraph.withDependencies deps)) outcome.1 outcome.2,
          rankedConfig_terminal (graph := (setup.dataflowGraph.withDependencies deps)) outcome.1
              outcome.2⟩).2.defaulted := by
      change who ∈ (rankedConfig (graph := (setup.dataflowGraph.withDependencies deps))
        outcome.1 outcome.2).defaulted
      rw [defaulted_rankedConfig]
      exact defaulted
    rw [ite_eq_left shown]
    have least := sub_forfeit_le_leastUtility utility range who
      (setup.eventParameterOutcome parameter
        ⟨rankedConfig (graph := (setup.dataflowGraph.withDependencies deps)) outcome.1 outcome.2,
            rankedConfig_terminal (graph := (setup.dataflowGraph.withDependencies deps)) _ _⟩)
    have count : (1 : ℝ) ≤ (failedReveals setup.program who (publicOutcome setup.program
      (terminalConfig setup.program
        ⟨rankedConfig (graph := (setup.dataflowGraph.withDependencies deps)) outcome.1 outcome.2,
          rankedConfig_terminal
            (graph := (setup.dataflowGraph.withDependencies deps)) _ _⟩)) : ℝ) := by
      exact_mod_cast failed
    change _ - forfeit * (failedReveals setup.program who (publicOutcome setup.program
      (terminalConfig setup.program
        ⟨rankedConfig (graph := (setup.dataflowGraph.withDependencies deps)) outcome.1 outcome.2,
          rankedConfig_terminal
            (graph := (setup.dataflowGraph.withDependencies deps)) _ _⟩)) : ℝ) ≤ _
    nlinarith
  · have hidden : who ∉ (setup.eventParameterOutcome parameter
        ⟨rankedConfig (graph := (setup.dataflowGraph.withDependencies deps)) outcome.1 outcome.2,
          rankedConfig_terminal (graph := (setup.dataflowGraph.withDependencies deps)) outcome.1
              outcome.2⟩).2.defaulted := by
      change who ∉ (rankedConfig (graph := (setup.dataflowGraph.withDependencies deps))
        outcome.1 outcome.2).defaulted
      rw [defaulted_rankedConfig]
      exact defaulted
    rw [ite_eq_right hidden]
    have : (0 : ℝ) ≤ forfeit * (failedReveals setup.program who
        (setup.eventParameterOutcome parameter
          ⟨rankedConfig (graph := (setup.dataflowGraph.withDependencies deps)) outcome.1 outcome.2,
            rankedConfig_terminal
              (graph := (setup.dataflowGraph.withDependencies deps)) _ _⟩).2 : ℝ) :=
      mul_nonneg nonnegative (Nat.cast_nonneg _)
    linarith

/-- A supported graph outcome is reachable from its initial inputs. -/
theorem graph_play_reachable (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies)
    (scheduler : (setup.dataflowGraph.withDependencies deps).PublicScheduler)
    (profile : (setup.dataflowGraph.withDependencies deps).BehavioralProfile)
    (outcome : (setup.dataflowGraph.withDependencies deps).gameSignature.Outcome)
    (supported : outcome ∈ (((setup.dataflowGraph.withDependencies deps).gameForm
      (setup.graphInputs deps) scheduler).play profile).support) :
    ∃ inputs, Config.Reachable inputs outcome.1 := by
  change outcome ∈ ((setup.graphInputs deps).bind _).support at supported
  rw [PMF.support_bind] at supported
  simp only [Set.mem_iUnion] at supported
  obtain ⟨initial, _, member⟩ := supported
  have inRun : outcome.1 ∈ ((setup.dataflowGraph.withDependencies deps).runPolicies
      scheduler profile initial).support := by
    rw [← (setup.dataflowGraph.withDependencies deps).terminalOutcomes_map_val, PMF.support_map]
    exact ⟨outcome, member, rfl⟩
  exact ⟨initial,
    (setup.dataflowGraph.withDependencies deps).run_reachable initial _ outcome.1 inRun⟩

end Vegas.SourceProgram.Setup
