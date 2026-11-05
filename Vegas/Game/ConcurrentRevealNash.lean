/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.ConcurrentRevealGraph
import Vegas.Game.ProgramPaymentNash
import Vegas.Game.IntendedNash
import Vegas.Source.Utility

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

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The forfeiture interface admits every source policy. -/
theorem BehavioralPolicy.admitted_forfeiture {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (policy : BehavioralPolicy who program) →
      policy.Admitted program (CommitmentInterface.forfeiture program)
  | _, _, .ret _, _ => trivial
  | _, _, .sample _ _ _ next, policy => admitted_forfeiture next policy
  | _, _, .commit _ _ _ _ next, policy => by
      refine ⟨fun _ _ _ choice _ => ?_, admitted_forfeiture next policy.2⟩
      rcases choice with _ | _ | _
      · trivial
      · rfl
      · trivial
  | _, _, .reveal _ _ _ _ _ _ next, policy => admitted_forfeiture next policy.2

end Vegas.SourceProgram

namespace Vegas.SourceProgram.Setup

open Vegas.EventGraph GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A player's payoff on the concurrent graph: the exclusion utility of the
outcome read with default entries in instruction order, or the excluded payoff
before the run ends. -/
def concurrentPayoff (setup : Setup (Player := Player) (L := L)) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) (config : setup.concurrentRevealGraph.Config) :
    ℝ :=
  if terminal : config.cut.Terminal then
    exclusionUtility setup.program excludedPayoff utility
      (setup.eventParameterOutcome parameter
        ⟨setup.rankedConfig config terminal, setup.rankedConfig_terminal config terminal⟩) who
  else excludedPayoff who

omit [DecidableEq Player] in
private theorem config_eq_of_data_eq {graph : Vegas.EventGraph Player L}
    {left right : graph.Config} (inputs : left.inputs = right.inputs)
    (cut : left.cut = right.cut) (outputs : left.outputs = right.outputs)
    (history : left.history = right.history) : left = right := by
  cases left
  cases right
  simp_all

/-- The source-order recasting depends only on the order-free final state. -/
theorem rankedConfig_congr (setup : Setup (Player := Player) (L := L))
    {left right : setup.concurrentRevealGraph.Config} (same : runKey left = runKey right)
    (leftTerminal : left.cut.Terminal) (rightTerminal : right.cut.Terminal) :
    setup.rankedConfig left leftTerminal = setup.rankedConfig right rightTerminal := by
  have store : left.store = right.store := congrArg (fun key => key.2.1) same
  have records : completionOf left = completionOf right := congrArg (fun key => key.2.2) same
  apply config_eq_of_data_eq
  · funext input
    exact Option.some.inj (congrFun store (.inl input))
  · rfl
  · funext event
    exact congrFun store (.inr event)
  · change (List.finRange _).filterMap (completionOf left) =
      (List.finRange _).filterMap (completionOf right)
    rw [records]

theorem concurrentPayoff_factors (setup : Setup (Player := Player) (L := L)) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) (left right : setup.concurrentRevealGraph.Config)
    (same : runKey left = runKey right) :
    setup.concurrentPayoff parameter utility excludedPayoff who left =
      setup.concurrentPayoff parameter utility excludedPayoff who right := by
  have cut : left.cut = right.cut := congrArg Prod.fst same
  unfold concurrentPayoff
  by_cases terminal : left.cut.Terminal
  · have rightTerminal : right.cut.Terminal := cut ▸ terminal
    rw [dite_eq_left terminal, dite_eq_left rightTerminal]
    have outcome : (⟨setup.rankedConfig left terminal, setup.rankedConfig_terminal left terminal⟩ :
          {config : setup.eventGraph.Config // config.cut.Terminal}) =
        ⟨setup.rankedConfig right rightTerminal,
          setup.rankedConfig_terminal right rightTerminal⟩ :=
      Subtype.ext (setup.rankedConfig_congr same terminal rightTerminal)
    rw [outcome]
  · have rightTerminal : ¬ right.cut.Terminal := cut ▸ terminal
    rw [dite_eq_right terminal, dite_eq_right rightTerminal]

theorem concurrentPayoff_of_defaulted (setup : Setup (Player := Player) (L := L))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) (config : setup.concurrentRevealGraph.Config)
    (defaulted : who ∈ config.defaulted) :
    setup.concurrentPayoff parameter utility excludedPayoff who config = excludedPayoff who := by
  unfold concurrentPayoff
  by_cases terminal : config.cut.Terminal
  · rw [dite_eq_left terminal]
    apply exclusionUtility_of_defaulted
    change who ∈ (setup.rankedConfig config terminal).defaulted
    rw [defaulted_rankedConfig]
    exact defaulted
  · rw [dite_eq_right terminal]

theorem le_concurrentPayoff (setup : Setup (Player := Player) (L := L)) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player)
    (low : ∀ outcome, excludedPayoff who ≤ utility outcome who)
    (config : setup.concurrentRevealGraph.Config) :
    excludedPayoff who ≤ setup.concurrentPayoff parameter utility excludedPayoff who config := by
  unfold concurrentPayoff exclusionUtility
  split
  · split
    · exact le_rfl
    · exact low _
  · exact le_rfl

/-- The initial law of the concurrent graph: the setup draw, encoded as inputs. -/
abbrev concurrentInputs (setup : Setup (Player := Player) (L := L)) :
    PMF setup.concurrentRevealGraph.Inputs :=
  setup.initialLaw.map fun initial => setup.eventInputs initial

theorem concurrentInputs_support_finite (setup : Setup (Player := Player) (L := L))
    [setup.FiniteInitialLaw] : setup.concurrentInputs.support.Finite := by
  rw [PMF.support_map]
  exact setup.initialLaw_support_finite.image _

theorem concurrentRun_support_finite (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (profile : setup.concurrentRevealGraph.BehavioralProfile)
    (scheduler : setup.concurrentRevealGraph.PublicScheduler) :
    (setup.concurrentInputs.bind
      (setup.concurrentRevealGraph.runPolicies scheduler profile)).support.Finite := by
  rw [PMF.support_bind]
  exact setup.concurrentInputs_support_finite.biUnion fun initial _ =>
    setup.concurrentRevealGraph.runPolicies_support_finite scheduler profile
      ((toEventGraph_finiteActions setup.program finite).profileFiniteSupport profile) initial

/-- **Canonical identity.** Under canonical scheduling the concurrent graph's
expected payoff is the compiled canonical game's expected exclusion utility. -/
theorem expect_concurrentPayoff_canonical (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) (profile : setup.eventGraph.BehavioralProfile) :
    expect (setup.concurrentInputs.bind (setup.concurrentRevealGraph.runPolicies
        setup.concurrentRevealGraph.canonicalScheduler profile))
        (setup.concurrentPayoff parameter utility excludedPayoff who) =
      expect (setup.canonicalEventGame.play profile) fun outcome =>
        exclusionUtility setup.program excludedPayoff utility
          (setup.eventParameterOutcome parameter outcome) who := by
  have actions := toEventGraph_finiteActions setup.program finite
  let readout : setup.eventGraph.Config → ℝ := fun config =>
    if terminal : config.cut.Terminal then
      exclusionUtility setup.program excludedPayoff utility
        (setup.eventParameterOutcome parameter ⟨config, terminal⟩) who
    else 0
  have play : setup.canonicalEventGame.play profile = setup.concurrentInputs.bind
      (setup.eventGraph.terminalOutcomes setup.eventGraph.canonicalScheduler profile) := rfl
  rw [play, expect_bind_tower _ _ _ (payoffIntegrable_of_finite_support _ _
      (setup.concurrentRun_support_finite finite profile _)),
    expect_bind_tower _ _ _ (payoffIntegrable_of_finite_support _ _ (by
      rw [PMF.support_bind]
      exact setup.concurrentInputs_support_finite.biUnion fun initial _ => by
        have run := setup.eventGraph.runPolicies_support_finite
          setup.eventGraph.canonicalScheduler profile (actions.profileFiniteSupport profile)
          initial
        rw [← setup.eventGraph.terminalOutcomes_map_val, PMF.support_map] at run
        exact run.of_finite_image Subtype.val_injective.injOn))]
  apply expect_congr_on_support
  intro initial _
  have law := setup.concurrentRevealGraph.canonical_fromSequential_config_law profile initial
  rw [← law, expect_map]
  have outcomes : expect (setup.eventGraph.terminalOutcomes setup.eventGraph.canonicalScheduler
      profile initial) (fun outcome => exclusionUtility setup.program excludedPayoff utility
        (setup.eventParameterOutcome parameter outcome) who) =
      expect (setup.eventGraph.runPolicies setup.eventGraph.canonicalScheduler profile initial)
        readout := by
    rw [← setup.eventGraph.terminalOutcomes_map_val, expect_map]
    apply expect_congr_on_support
    intro outcome _
    simp only [Function.comp_apply, readout, dite_eq_left outcome.2]
  refine Eq.trans ?_ outcomes.symm
  change expect (setup.eventGraph.runPolicies setup.eventGraph.canonicalScheduler profile initial)
      (setup.concurrentPayoff parameter utility excludedPayoff who ∘
        setup.concurrentRevealGraph.fromSequentialConfig) = _
  apply expect_congr_on_support
  intro config member
  have reach := setup.eventGraph.run_reachable initial _ config member
  have terminal := setup.eventGraph.runPolicies_terminal _ profile initial config member
  have viewTerminal : (setup.concurrentRevealGraph.fromSequentialConfig config).cut.Terminal :=
    terminal
  simp only [Function.comp_apply, concurrentPayoff, readout, dite_eq_left viewTerminal,
    dite_eq_left terminal]
  have recast := setup.rankedConfig_fromSequentialConfig reach viewTerminal
  have outcome : (⟨setup.rankedConfig (setup.concurrentRevealGraph.fromSequentialConfig config)
        viewTerminal, setup.rankedConfig_terminal _ viewTerminal⟩ :
          {config : setup.eventGraph.Config // config.cut.Terminal}) = ⟨config, terminal⟩ :=
    Subtype.ext recast
  rw [outcome]

end Vegas.SourceProgram.Setup
