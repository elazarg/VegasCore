module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.RevealDeviation
public import GameTheory.Math.Probability.ExpectationBind

@[expose] public section

/-! # Withholding buys nothing against an exclusion payoff

Fix a player and a payoff of final configurations that is never below an
excluded value and equals it whenever the player has defaulted. Suppose that
at every one of the player's publications an honest kernel plays one action
and every other action makes the player default. Replacing the player's kernel
at its own publications by the honest one then weakly raises its expected
payoff under every public scheduler: wherever the original kernel deviates,
the player defaults, and defaults are absorbing.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

variable (graph) in
/-- Play the honest kernel at the owner's publications and the given policy elsewhere. -/
def honestAtPublications (who : Player) (policy honest : graph.BehavioralPolicy who) :
    graph.BehavioralPolicy who :=
  fun event actor observation active =>
    if (graph.outputLayout event).IsPublication then honest event actor observation active
    else policy event actor observation active

variable (graph) in
/-- At every active publication of its owner the honest kernel plays one
action, and every other action there makes the owner default. -/
def OpensDecisively (who : Player) (honest : graph.BehavioralPolicy who) : Prop :=
  ∀ (config : graph.Config) (event : graph.EventId) (ready : config.cut.Ready event)
    (actor : graph.actor? event = some who), (graph.outputLayout event).IsPublication →
    ∀ (active : who ∉ config.defaulted),
      ∃ opened, honest event actor (graph.playerObserve who config) active = PMF.pure opened ∧
        ∀ action, action ≠ opened → ∀ next ∈ (config.step event ready action).support,
          who ∈ next.defaulted

/-- Every result of a run keeps the defaults already present. -/
theorem runPlan_defaulted_mono (plan : graph.EventPlan) :
    ∀ fuel (config : graph.Config), ∀ result ∈ (graph.runPlan plan fuel config).support,
      config.defaulted ⊆ result.defaulted := by
  intro fuel
  induction fuel with
  | zero =>
      intro config result member
      rw [EventGraph.runPlan, PMF.support_pure, Set.mem_singleton_iff] at member
      rw [member]
  | succ fuel ih =>
      intro config result member
      by_cases terminal : config.cut.Terminal
      · rw [EventGraph.runPlan, dite_eq_left terminal, PMF.support_pure,
          Set.mem_singleton_iff] at member
        rw [member]
      · rw [EventGraph.runPlan, dite_eq_right terminal, PMF.support_bind] at member
        simp only [Set.mem_iUnion] at member
        obtain ⟨choice, _, rest⟩ := member
        rw [PMF.support_bind] at rest
        simp only [Set.mem_iUnion] at rest
        obtain ⟨next, stepped, last⟩ := rest
        exact (config.defaulted_step choice.1.1 choice.1.2 choice.2 next stepped).trans
          (ih next result last)

/-- The value of a payoff from one configuration under a profile and a scheduler. -/
def runValue (profile : graph.BehavioralProfile) (scheduler : graph.PublicScheduler)
    (payoff : graph.Config → ℝ) (config : graph.Config) : ℝ :=
  expect (graph.runPlan (graph.policyPlan profile scheduler) config.remaining config) payoff

theorem runPlan_policyPlan_support_finite (finite : graph.FiniteActions)
    (profile : graph.BehavioralProfile) (scheduler : graph.PublicScheduler) (fuel : Nat)
    (config : graph.Config) :
    (graph.runPlan (graph.policyPlan profile scheduler) fuel config).support.Finite :=
  graph.runPlan_support_finite _
    (graph.policyPlan_support_finite profile (finite.profileFiniteSupport profile) scheduler)
    fuel config

/-- One step of the value recursion. -/
theorem runValue_step (finite : graph.FiniteActions) (profile : graph.BehavioralProfile)
    (scheduler : graph.PublicScheduler) (payoff : graph.Config → ℝ) (config : graph.Config)
    (notTerminal : ¬ config.cut.Terminal) :
    runValue profile scheduler payoff config =
      expect (scheduler (graph.publicObserve config) config.cut.enabled
        (enabled_nonempty_of_not_terminal config notTerminal)) fun selected =>
          expect (eventStep profile config selected.1
            ((EventOrder.Cut.mem_enabled _ _).mp selected.2))
            (runValue profile scheduler payoff) := by
  obtain ⟨rest, restEq⟩ : ∃ rest, config.remaining = rest + 1 := by
    have positive : config.remaining ≠ 0 :=
      fun zero => notTerminal ((config.terminal_iff_remaining_zero).mpr zero)
    exact ⟨config.remaining - 1, by omega⟩
  unfold runValue
  rw [restEq, runPlan_policyPlan_succ profile scheduler rest config notTerminal,
    expect_bind_tower _ _ _ (payoffIntegrable_of_finite_support _ _ (by
      rw [← runPlan_policyPlan_succ profile scheduler rest config notTerminal]
      exact runPlan_policyPlan_support_finite finite profile scheduler _ _))]
  apply expect_congr_on_support
  intro selected _
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_finite_support _ _ (by
    rw [PMF.support_bind]
    exact (eventStep_support_finite profile (finite.profileFiniteSupport profile) config _
      _).biUnion fun next _ => runPlan_policyPlan_support_finite finite profile scheduler rest
        next))]
  apply expect_congr_on_support
  intro next member
  unfold eventStep at member
  rw [PMF.support_bind] at member
  simp only [Set.mem_iUnion] at member
  obtain ⟨action, _, stepped⟩ := member
  have consumed := config.remaining_step _ _ action next stepped
  rw [(by omega : next.remaining = rest)]

/-- A payoff never below the excluded value has value at least the excluded value. -/
theorem le_runValue (finite : graph.FiniteActions) (profile : graph.BehavioralProfile)
    (scheduler : graph.PublicScheduler) {payoff : graph.Config → ℝ} {excluded : ℝ}
    (low : ∀ config, excluded ≤ payoff config) (config : graph.Config) :
    excluded ≤ runValue profile scheduler payoff config := by
  unfold runValue
  have bound := expect_mono (μ := graph.runPlan (graph.policyPlan profile scheduler)
      config.remaining config) (f := fun _ => excluded) (g := payoff)
    (fun result _ => low result) (payoffIntegrable_constant _ _)
    (payoffIntegrable_of_finite_support _ _
      (runPlan_policyPlan_support_finite finite profile scheduler _ _))
  rwa [expect_constant] at bound

/-- Once a player has defaulted, its exclusion payoff is the excluded value. -/
theorem runValue_of_defaulted (profile : graph.BehavioralProfile)
    (scheduler : graph.PublicScheduler) {payoff : graph.Config → ℝ} {excluded : ℝ} {who : Player}
    (atDefault : ∀ config, who ∈ config.defaulted → payoff config = excluded)
    (config : graph.Config) (defaulted : who ∈ config.defaulted) :
    runValue profile scheduler payoff config = excluded := by
  unfold runValue
  rw [expect_congr_on_support (g := fun _ => excluded) fun result member =>
    atDefault result (runPlan_defaulted_mono _ _ config result member defaulted),
    expect_constant]

theorem actionLaw_support_finite (finite : graph.FiniteActions)
    (profile : graph.BehavioralProfile) (config : graph.Config) (event : graph.EventId) :
    (actionLaw profile config event).support.Finite := by
  cases ownerEq : (graph.nodes event).actor with
  | none => rw [actionLaw_of_ownerless _ _ ownerEq]; simp
  | some owner =>
      rw [actionLaw_of_actor _ _ ownerEq]
      by_cases inactive : owner ∈ config.defaulted
      · rw [dite_eq_left inactive]; simp
      · rw [dite_eq_right inactive]
        exact finite.profileFiniteSupport profile _ _ _ _ _

/-- **Withholding coupling.** Against an exclusion payoff, playing the
decisive honest kernel at the player's own publications weakly raises its
value from every configuration, under every public scheduler. -/
theorem honestAtPublications_runValue_le (finite : graph.FiniteActions)
    (profile : graph.BehavioralProfile) (who : Player) (honest : graph.BehavioralPolicy who)
    (decisive : graph.OpensDecisively who honest) (scheduler : graph.PublicScheduler)
    {payoff : graph.Config → ℝ} {excluded : ℝ} (low : ∀ config, excluded ≤ payoff config)
    (atDefault : ∀ config, who ∈ config.defaulted → payoff config = excluded) :
    ∀ fuel (config : graph.Config), config.remaining = fuel →
      runValue profile scheduler payoff config ≤
        runValue (Profile.update (sig := graph.gameSignature) profile who
          (graph.honestAtPublications who (profile who) honest)) scheduler payoff config := by
  let improved := Profile.update (sig := graph.gameSignature) profile who
    (graph.honestAtPublications who (profile who) honest)
  intro fuel
  induction fuel with
  | zero =>
      intro config remaining
      unfold runValue
      rw [remaining]
      simp only [EventGraph.runPlan, expect_pure, le_refl]
  | succ fuel ih =>
      intro config remaining
      by_cases defaulted : who ∈ config.defaulted
      · rw [runValue_of_defaulted profile scheduler atDefault config defaulted]
        exact le_runValue finite _ scheduler low config
      have notTerminal : ¬ config.cut.Terminal := fun terminal => by
        have := (config.terminal_iff_remaining_zero).mp terminal
        omega
      rw [runValue_step finite profile scheduler payoff config notTerminal,
        runValue_step finite improved scheduler payoff config notTerminal]
      apply expect_mono _ (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
      intro selected _
      let event := selected.1
      have ready : config.cut.Ready event := (EventOrder.Cut.mem_enabled _ _).mp selected.2
      have next (action : graph.Action event) (stepped : graph.Config)
          (steppedMember : stepped ∈ (config.step event ready action).support) :
          stepped.remaining = fuel := by
        have := config.remaining_step event ready action stepped steppedMember
        omega
      have stepIntegrable (action : graph.Action event) (value : graph.Config → ℝ) :
          PayoffIntegrable (config.step event ready action) value :=
        payoffIntegrable_of_finite_support _ _ (config.step_support_finite event ready action)
      have eventIntegrable (chosen : graph.BehavioralProfile) (value : graph.Config → ℝ) :
          PayoffIntegrable (eventStep chosen config event ready) value :=
        payoffIntegrable_of_finite_support _ _
          (eventStep_support_finite chosen (finite.profileFiniteSupport chosen) config event ready)
      by_cases owned : graph.actor? event = some who ∧ (graph.outputLayout event).IsPublication
      · obtain ⟨actor, publication⟩ := owned
        obtain ⟨opened, honestOpens, othersDefault⟩ :=
          decisive config event ready actor publication defaulted
        have improvedLaw : actionLaw improved config event = PMF.pure opened := by
          rw [actionLaw_of_actor improved config actor, dite_eq_right defaulted]
          simp only [improved, Profile.update_same, honestAtPublications, ite_eq_left publication]
          exact honestOpens
        change expect ((actionLaw profile config event).bind (config.step event ready)) _ ≤
          expect ((actionLaw improved config event).bind (config.step event ready)) _
        rw [improvedLaw, PMF.pure_bind, expect_bind_tower _ _ _ (eventIntegrable profile _)]
        have target := le_runValue finite improved scheduler low
        calc _ ≤ expect (actionLaw profile config event) (fun _ =>
              expect (config.step event ready opened) (runValue improved scheduler payoff)) := by
              apply expect_mono _ (payoffIntegrable_of_finite_support _ _
                (actionLaw_support_finite finite profile config event))
                (payoffIntegrable_constant _ _)
              intro action _
              by_cases same : action = opened
              · subst same
                exact expect_mono (fun stepped steppedMember => ih stepped
                    (next action stepped steppedMember))
                  (stepIntegrable _ _) (stepIntegrable _ _)
              · rw [expect_congr_on_support (g := fun _ => excluded) fun stepped steppedMember =>
                  runValue_of_defaulted profile scheduler atDefault stepped
                    (othersDefault action same stepped steppedMember), expect_constant]
                have bound := expect_mono (μ := config.step event ready opened)
                  (f := fun _ => excluded) (g := runValue improved scheduler payoff)
                  (fun stepped _ => target stepped) (payoffIntegrable_constant _ _)
                  (stepIntegrable _ _)
                rwa [expect_constant] at bound
          _ = _ := expect_constant _ _
      · have sameLaw : actionLaw improved config event = actionLaw profile config event := by
          cases ownerEq : (graph.nodes event).actor with
          | none => rw [actionLaw_of_ownerless _ _ ownerEq, actionLaw_of_ownerless _ _ ownerEq]
          | some owner =>
              rw [actionLaw_of_actor _ _ ownerEq, actionLaw_of_actor _ _ ownerEq]
              by_cases inactive : owner ∈ config.defaulted
              · rw [dite_eq_left inactive, dite_eq_left inactive]
              rw [dite_eq_right inactive, dite_eq_right inactive]
              by_cases same : owner = who
              · subst owner
                have plain : ¬ (graph.outputLayout event).IsPublication :=
                  fun publication => owned ⟨ownerEq, publication⟩
                simp only [improved, Profile.update_same, honestAtPublications, ite_eq_right plain]
              · simp only [improved, Profile.update_of_ne _ _ same]
        change expect ((actionLaw profile config event).bind (config.step event ready)) _ ≤
          expect ((actionLaw improved config event).bind (config.step event ready)) _
        rw [sameLaw]
        change expect (eventStep profile config event ready) _ ≤
          expect (eventStep profile config event ready) _
        apply expect_mono _ (eventIntegrable profile _) (eventIntegrable profile _)
        intro stepped member
        unfold eventStep at member
        rw [PMF.support_bind] at member
        simp only [Set.mem_iUnion] at member
        obtain ⟨action, _, steppedMember⟩ := member
        exact ih stepped (next action stepped steppedMember)

end Vegas.EventGraph
