/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.CommitRevealAuction
import Vegas.Compile.EventGraphPolicy
import Vegas.EventGraph.SequentialLaw
import Vegas.EventGraph.CanonicalStep

/-! # Withholding decisions depend on the order of concurrent reveals

The value-only auction profile reveals conditionally. Its two ready foreign
publications have different terminal store laws under its actual raw policies.
This concerns unrestricted source profiles, not mandatory-disclosure intended
profiles or sequential-equilibrium preservation.
-/

noncomputable section
namespace Vegas.Examples.ConcurrentRevealOrderLaw
open SourceProgram EventGraph
open CommitRevealAuction
abbrev graph := (toEventGraph program).withMode .concurrentReveals
instance : NeZero (toEventGraph program).order.eventCount := ⟨by decide⟩
instance : NeZero graph.order.eventCount := ⟨by decide⟩
abbrev initial : graph.Config := Config.initial (encodeInputs (Env.empty (CellVal simpleExpr)))
theorem first_ready : initial.cut.Ready 0 := by decide
abbrev first : graph.Config := initial.complete 0 first_ready (some (.success 6)) (.success 6)
theorem second_ready : first.cut.Ready 1 := by
  constructor
  · decide
  · intro prior member
    have earlier := graph.order.predecessor_lt member
    change prior.val < 1 at earlier
    have same : prior = 0 := Fin.ext (by change prior.val = 0; omega)
    subst prior
    decide
abbrev bound : graph.Config := first.complete 1 second_ready (some (.success 4)) (.success 4)
theorem reveals_independent : (toEventGraph program).IndependentReveals 2 3 := by
  constructor
  · trivial
  constructor
  · trivial
  constructor
  · decide
  · decide

theorem alice_ready : bound.cut.Ready 2 := by
  constructor
  · decide
  · intro prior member
    have earlier := graph.order.predecessor_lt member
    change prior.val < 2 at earlier
    fin_cases prior
    · decide
    · decide
    · norm_num [graph, toEventGraph, program, eventCount, EventOrder.sequential] at earlier
    · norm_num [graph, toEventGraph, program, eventCount, EventOrder.sequential] at earlier

theorem bob_ready : bound.cut.Ready 3 := by
  constructor
  · decide
  · intro prior member
    have earlier := graph.order.predecessor_lt member
    change prior.val < 3 at earlier
    fin_cases prior
    · decide
    · decide
    · exact False.elim ((((toEventGraph program).mem_revealRelaxedPredecessors 2 3).mp
        member).2 reveals_independent)
    · norm_num [graph, toEventGraph, program, eventCount, EventOrder.sequential] at earlier
abbrev disclosed : graph.Config := bound.complete 2 alice_ready true (.success 6)
abbrev compiled := (toEventGraph program).toModeProfile .concurrentReveals
  (compileEventProfile program (fun who => (profile 6 who).1))
theorem bob_actor : graph.actor? 3 = some Player.bob := by rfl
theorem bob_before_alice :
    compiled Player.bob 3 bob_actor (graph.playerObserve Player.bob bound) (by decide) =
    PMF.pure true := by rfl
theorem bob_after_alice :
    compiled Player.bob 3 bob_actor (graph.playerObserve Player.bob disclosed) (by decide) =
    PMF.pure false := by rfl
theorem initial_step : initial.step 0 first_ready (some (.success 6)) = PMF.pure first := by
  rw [initial.step_eq_map_of_eval 0 first_ready (some (.success 6))
    (PMF.pure (PublicationResult.success (6 : Int))) (by rfl)]
  exact PMF.pure_map _ _

theorem first_step : first.step 1 second_ready (some (.success 4)) = PMF.pure bound := by
  rw [first.step_eq_map_of_eval 1 second_ready (some (.success 4))
    (PMF.pure (PublicationResult.success (4 : Int))) (by rfl)]
  exact PMF.pure_map _ _

theorem bound_reachable : Config.Reachable initial.inputs bound := by
  have previous : Config.Reachable initial.inputs first :=
    .step .initial 0 first_ready (some (.success 6)) first (by rw [initial_step]; simp)
  exact .step previous 1 second_ready (some (.success 4)) bound (by rw [first_step]; simp)
theorem disclosed_bob_ready : disclosed.cut.Ready 3 :=
  bob_ready.after_complete alice_ready (by decide)

abbrev bobFirst : graph.Config := bound.complete 3 bob_ready true (.success 4)
abbrev bobSecond : graph.Config := disclosed.complete 3 disclosed_bob_ready false .failure

theorem bob_first_step : bound.step 3 bob_ready true = PMF.pure bobFirst := by
  rw [bound.step_eq_map_of_eval 3 bob_ready true
    (PMF.pure (PublicationResult.success (4 : Int))) (by rfl)]
  exact PMF.pure_map _ _

theorem bob_second_step : disclosed.step 3 disclosed_bob_ready false = PMF.pure bobSecond := by
  rw [disclosed.step_eq_map_of_eval 3 disclosed_bob_ready false
    (PMF.pure (PublicationResult.failure : PublicationResult Int)) (by rfl)]
  exact PMF.pure_map _ _

abbrev bobFirst_alice_ready : bobFirst.cut.Ready 2 :=
  alice_ready.after_complete bob_ready (by decide)
abbrev bobFirst_terminal : graph.Config :=
  bobFirst.complete 2 bobFirst_alice_ready true (.success 6)

theorem bob_first_alice_step :
    bobFirst.step 2 bobFirst_alice_ready true = PMF.pure bobFirst_terminal := by
  rw [bobFirst.step_eq_map_of_eval 2 bobFirst_alice_ready true
    (PMF.pure (PublicationResult.success (6 : Int))) (by rfl)]
  exact PMF.pure_map _ _

theorem alice_step : bound.step 2 alice_ready true = PMF.pure disclosed := by
  rw [bound.step_eq_map_of_eval 2 alice_ready true
    (PMF.pure (PublicationResult.success (6 : Int))) (by rfl)]
  exact PMF.pure_map _ _

theorem terminals_differ : bobFirst_terminal.store ≠ bobSecond.store := by
  intro same
  have stored := congrFun same (.inr 3)
  change some (PublicationResult.success (4 : Int)) = some PublicationResult.failure at stored
  cases stored

theorem alice_actor : graph.actor? 2 = some Player.alice := by rfl

theorem alice_before :
    compiled Player.alice 2 alice_actor
      (graph.playerObserve Player.alice bound) (by decide) = PMF.pure true := by rfl

theorem alice_after_bob :
    compiled Player.alice 2 alice_actor
      (graph.playerObserve Player.alice bobFirst) (by decide) = PMF.pure true := by rfl

/-- Prefer Bob's ready reveal, then use the ordinary canonical scheduler. -/
def bobFirstScheduler : graph.PublicScheduler := fun observation enabled nonempty =>
  if member : (3 : graph.EventId) ∈ enabled then PMF.pure ⟨3, member⟩
  else graph.canonicalScheduler observation enabled nonempty

/-- Serving Bob first executes the actual two raw policy callbacks. -/
theorem bob_first_policy_law :
    graph.runPlan (graph.policyPlan compiled bobFirstScheduler) 2 bound =
      PMF.pure bobFirst_terminal := by
  have notTerminal : ¬ bound.cut.Terminal := by decide
  have readyMem : (3 : graph.EventId) ∈ bound.cut.enabled :=
    (EventOrder.Cut.mem_enabled _ _).2 bob_ready
  have plan : graph.policyPlan compiled bobFirstScheduler bound notTerminal =
      PMF.pure ⟨⟨3, bob_ready⟩, true⟩ := by
    unfold policyPlan bobFirstScheduler
    dsimp only
    rw [dite_eq_left readyMem, PMF.pure_bind]
    change (compiled Player.bob 3 bob_actor (graph.playerObserve Player.bob bound)
      (by decide)).map _ = _
    rw [bob_before_alice, PMF.pure_map]
  have afterPlan : ∀ terminal,
      graph.policyPlan compiled bobFirstScheduler bobFirst terminal =
        graph.policyPlan compiled graph.canonicalScheduler bobFirst terminal := by
    intro terminal
    unfold policyPlan bobFirstScheduler
    dsimp only
    have unavailable : (3 : graph.EventId) ∉ bobFirst.cut.enabled := by
      intro enabled
      exact ((EventOrder.Cut.mem_enabled _ _).1 enabled).1 (by decide)
    rw [dite_eq_right unavailable]
  rw [runPlan, dite_eq_right notTerminal, plan, PMF.pure_bind,
    bob_first_step, PMF.pure_bind]
  have sameRun : graph.runPlan (graph.policyPlan compiled bobFirstScheduler) 1 bobFirst =
      graph.runPlan (graph.policyPlan compiled graph.canonicalScheduler) 1 bobFirst := by
    rw [runPlan, runPlan, dite_eq_right (by decide), dite_eq_right (by decide), afterPlan]
    simp only [runPlan]
  rw [sameRun, graph.runPlan_canonical_actor compiled 0 bobFirst 2 bobFirst_alice_ready
    (by decide) Player.alice alice_actor (by decide), alice_after_bob, PMF.pure_bind,
    bob_first_alice_step, PMF.pure_bind]
  rfl

/-- Serving Alice first executes Bob's resulting withholding callback. -/
theorem alice_first_policy_law :
    graph.runPlan (graph.policyPlan compiled graph.canonicalScheduler) 2 bound =
      PMF.pure bobSecond := by
  rw [graph.runPlan_canonical_actor compiled 1 bound 2 alice_ready (by decide)
    Player.alice alice_actor (by decide), alice_before, PMF.pure_bind,
    alice_step, PMF.pure_bind]
  rw [graph.runPlan_canonical_actor compiled 0 disclosed 3 disclosed_bob_ready (by decide)
    Player.bob bob_actor (by decide), bob_after_alice, PMF.pure_bind,
    bob_second_step, PMF.pure_bind]
  rfl

theorem bobFirst_cut_terminal : bobFirst_terminal.cut.Terminal := by decide

theorem bobSecond_cut_terminal : bobSecond.cut.Terminal := by decide

theorem terminal_store_laws_differ :
    (graph.runPlan (graph.policyPlan compiled bobFirstScheduler) 2 bound).map Config.store ≠
    (graph.runPlan (graph.policyPlan compiled graph.canonicalScheduler) 2 bound).map
      Config.store := by
  rw [bob_first_policy_law, alice_first_policy_law, PMF.pure_map, PMF.pure_map]
  intro same
  have values := congrArg (fun law : PMF (EventGraph.Store graph.layout) =>
    law bobFirst_terminal.store) same
  have different := terminals_differ
  simp [PMF.pure_apply, different] at values

end Vegas.Examples.ConcurrentRevealOrderLaw
