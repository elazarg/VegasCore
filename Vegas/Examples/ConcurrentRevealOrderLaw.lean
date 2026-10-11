/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitRevealAuction
import Vegas.Compile.EventGraphPolicy
import Vegas.EventGraph.ExecutionMode
import Vegas.EventGraph.NormalizedPolicy

/-! # Withholding decisions depend on the order of concurrent reveals

The existing value-only auction profile reveals conditionally. Its two ready
foreign publications have different terminal store laws under the actual
normalized compiled kernels. This concerns unrestricted source profiles, not
mandatory-disclosure intended profiles or sequential-equilibrium preservation.
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
abbrev first : graph.Config := initial.complete 0 first_ready (.success 6) (.success 6)
theorem second_ready : first.cut.Ready 1 := by decide
abbrev bound : graph.Config := first.complete 1 second_ready (.success 4) (.success 4)
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
    fin_cases prior
    · decide
    · decide
    · norm_num [graph, toEventGraph, program, eventCount, EventGraph.barrierOrder] at earlier
    · norm_num [graph, toEventGraph, program, eventCount, EventGraph.barrierOrder] at earlier

theorem bob_ready : bound.cut.Ready 3 := by
  constructor
  · decide
  · intro prior member
    have earlier := graph.order.predecessor_lt member
    fin_cases prior
    · decide
    · decide
    · exact False.elim ((((toEventGraph program).mem_revealRelaxedPredecessors 2 3).mp
        member).2 reveals_independent)
    · norm_num [graph, toEventGraph, program, eventCount, EventGraph.barrierOrder] at earlier
abbrev disclosed : graph.Config := bound.complete 2 alice_ready true (.success 6)
abbrev compiled := (toEventGraph program).toModeProfile .concurrentReveals
  (compileEventProfile program (fun who => (profile 6 who).1))
theorem bob_actor : graph.actor? 3 = some Player.bob := by rfl
theorem bob_before_alice :
    compiled Player.bob 3 bob_actor (graph.playerObserve Player.bob bound) =
    PMF.pure true := by rfl
theorem bob_after_alice :
    compiled Player.bob 3 bob_actor (graph.playerObserve Player.bob disclosed) =
    PMF.pure false := by rfl
theorem normalized_bob_before_alice :
    graph.normalizePolicy Player.bob (compiled Player.bob) 3 bob_actor
      (graph.playerObserve Player.bob bound) = PMF.pure true := by rfl

theorem normalized_bob_after_alice :
    graph.normalizePolicy Player.bob (compiled Player.bob) 3 bob_actor
      (graph.playerObserve Player.bob disclosed) = PMF.pure false := by rfl

theorem initial_step : initial.step 0 first_ready (.success 6) = PMF.pure first := by
  rw [initial.step_eq_map_of_eval 0 first_ready (.success 6)
    (PMF.pure (PublicationResult.success (6 : Int))) (by rfl)]
  exact PMF.pure_map _ _

theorem first_step : first.step 1 second_ready (.success 4) = PMF.pure bound := by
  rw [first.step_eq_map_of_eval 1 second_ready (.success 4)
    (PMF.pure (PublicationResult.success (4 : Int))) (by rfl)]
  exact PMF.pure_map _ _

theorem bound_reachable : Config.Reachable initial.inputs bound := by
  have previous : Config.Reachable initial.inputs first :=
    .step .initial 0 first_ready (.success 6) first (by rw [initial_step]; simp)
  exact .step previous 1 second_ready (.success 4) bound (by rw [first_step]; simp)
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

theorem not_readyIndependent : ¬ graph.ReadyIndependent compiled := by
  intro independent
  have same := independent.normalizePolicy_complete_foreign bound 3 2 bob_ready alice_ready
    bob_actor Player.alice (by rfl) (by decide) true (.success 6)
  change graph.normalizePolicy Player.bob (compiled Player.bob) 3 bob_actor
      (graph.playerObserve Player.bob disclosed) =
    graph.normalizePolicy Player.bob (compiled Player.bob) 3 bob_actor
      (graph.playerObserve Player.bob bound) at same
  rw [normalized_bob_before_alice, normalized_bob_after_alice] at same
  have values := congrArg (fun law : PMF Bool => law false) same
  simp at values

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

theorem normalized_alice_before :
    graph.normalizePolicy Player.alice (compiled Player.alice) 2 alice_actor
      (graph.playerObserve Player.alice bound) = PMF.pure true := by rfl

theorem normalized_alice_after_bob :
    graph.normalizePolicy Player.alice (compiled Player.alice) 2 alice_actor
      (graph.playerObserve Player.alice bobFirst) = PMF.pure true := by rfl

theorem bob_first_policy_law :
    policyStepThen compiled bound 3 2 bob_ready alice_ready (by decide)
      Player.bob Player.alice bob_actor alice_actor = PMF.pure bobFirst_terminal := by
  unfold policyStepThen
  rw [normalized_bob_before_alice, PMF.pure_bind]
  trans (bound.step 3 bob_ready true).bind (fun _ => PMF.pure bobFirst_terminal)
  · apply GameTheory.Math.Probability.bindOnSupport_eq_bind_of_eq_on_support
    intro after member
    rw [bob_first_step, PMF.mem_support_pure_iff] at member
    subst after
    rw [normalized_alice_after_bob, PMF.pure_bind, bob_first_alice_step]
  · rw [bob_first_step, PMF.pure_bind]

theorem alice_first_policy_law :
    policyStepThen compiled bound 2 3 alice_ready bob_ready (by decide)
      Player.alice Player.bob alice_actor bob_actor = PMF.pure bobSecond := by
  unfold policyStepThen
  rw [normalized_alice_before, PMF.pure_bind]
  trans (bound.step 2 alice_ready true).bind (fun _ => PMF.pure bobSecond)
  · apply GameTheory.Math.Probability.bindOnSupport_eq_bind_of_eq_on_support
    intro after member
    rw [alice_step, PMF.mem_support_pure_iff] at member
    subst after
    rw [normalized_bob_after_alice, PMF.pure_bind, bob_second_step]
  · rw [alice_step, PMF.pure_bind]

theorem bobFirst_cut_terminal : bobFirst_terminal.cut.Terminal := by decide

theorem bobSecond_cut_terminal : bobSecond.cut.Terminal := by decide

theorem terminal_store_laws_differ :
    (policyStepThen compiled bound 3 2 bob_ready alice_ready (by decide)
      Player.bob Player.alice bob_actor alice_actor).map Config.store ≠
    (policyStepThen compiled bound 2 3 alice_ready bob_ready (by decide)
      Player.alice Player.bob alice_actor bob_actor).map Config.store := by
  rw [bob_first_policy_law, alice_first_policy_law, PMF.pure_map, PMF.pure_map]
  intro same
  have values := congrArg (fun law : PMF (EventGraph.Store graph.layout) =>
    law bobFirst_terminal.store) same
  have different := terminals_differ
  simp [PMF.pure_apply, different] at values

end Vegas.Examples.ConcurrentRevealOrderLaw
