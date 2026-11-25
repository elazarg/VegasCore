module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphCanonical
import Vegas.EventGraph.ExecutionOrder
import Vegas.EventGraph.SequentialNormalization

@[expose] public section

/-! # Public scheduling of source information graphs -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The source information order makes the enabled-event type a singleton at every
nonterminal cut, so every public scheduler gives the same policy plan. -/
theorem toInformationGraph_policyPlan_eq {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (profile : (toInformationGraph program).BehavioralProfile)
    (first second : (toInformationGraph program).PublicScheduler) :
    (toInformationGraph program).policyPlan profile first =
      (toInformationGraph program).policyPlan profile second := by
  funext config notTerminal
  let nonempty := EventGraph.enabled_nonempty_of_not_terminal config notTerminal
  let witness : {event : (toInformationGraph program).EventId // event ∈ config.cut.enabled} :=
    ⟨config.cut.enabled.min' nonempty, Finset.min'_mem _ nonempty⟩
  let : Subsingleton
      {event : (toInformationGraph program).EventId // event ∈ config.cut.enabled} :=
    ⟨fun left right => Subtype.ext (EventOrder.Cut.ready_unique config.cut
      ((EventOrder.Cut.mem_enabled _ _).mp left.2)
      ((EventOrder.Cut.mem_enabled _ _).mp right.2))⟩
  have selected : first ((toInformationGraph program).publicObserve config)
        config.cut.enabled nonempty =
      second ((toInformationGraph program).publicObserve config) config.cut.enabled nonempty :=
    (eq_pure_of_subsingleton _ witness).trans (eq_pure_of_subsingleton _ witness).symm
  unfold EventGraph.policyPlan
  dsimp only
  rw [selected]

/-- Every graph behavioral profile has the same complete configuration law
under all public schedulers of its source information graph. -/
theorem toInformationGraph_runPolicies_eq {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (profile : (toInformationGraph program).BehavioralProfile)
    (first second : (toInformationGraph program).PublicScheduler)
    (inputs : (toInformationGraph program).Inputs) :
    (toInformationGraph program).runPolicies first profile inputs =
      (toInformationGraph program).runPolicies second profile inputs := by
  unfold EventGraph.runPolicies
  rw [toInformationGraph_policyPlan_eq program profile first second]

/-- Every supported information graph run completes all instructions in source order. -/
theorem toInformationGraph_runs_follow_source_order
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (scheduler : (toInformationGraph program).PublicScheduler)
    (profile : (toInformationGraph program).BehavioralProfile)
    (inputs : (toInformationGraph program).Inputs) (final : (toInformationGraph program).Config)
    (supported : final ∈
      ((toInformationGraph program).runPolicies scheduler profile inputs).support) :
    final.history.map (fun completion => completion.event.val) =
      List.range (eventCount program) := by
  let graph := toInformationGraph program
  have reachable := graph.run_reachable inputs (graph.policyPlan profile scheduler) final supported
  have terminal := graph.runPolicies_terminal scheduler profile inputs final supported
  have length : final.history.length = eventCount program := by
    change final.history.length = graph.order.eventCount
    simpa only [List.length_map] using (reachable.topological terminal).length
  exact (EventGraph.history_map_val_of_reachable
    (fun prior event earlier => (EventOrder.sequential.mem_predecessors prior event).mpr earlier)
    reachable).trans (congrArg List.range length)

/-- Attaching terminality certificates preserves exact scheduler independence
of the complete graph configuration, including public defaults and own choices. -/
theorem toInformationGraph_terminalOutcomes_eq {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (profile : (toInformationGraph program).BehavioralProfile)
    (first second : (toInformationGraph program).PublicScheduler)
    (inputs : (toInformationGraph program).Inputs) :
    (toInformationGraph program).terminalOutcomes first profile inputs =
      (toInformationGraph program).terminalOutcomes second profile inputs := by
  apply pmf_map_injective (f := Subtype.val) Subtype.val_injective
  rw [EventGraph.terminalOutcomes_map_val, EventGraph.terminalOutcomes_map_val]
  exact toInformationGraph_runPolicies_eq program profile first second inputs

/-- Every public schedule preserves the complete source configuration law. -/
theorem scheduled_terminalConfig_distribution_eq
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (scheduler : (toInformationGraph program).PublicScheduler)
    (profile : BehavioralProfile program) (state : State L Γ) :
    ((toInformationGraph program).terminalOutcomes scheduler
        (compileEventProfile program profile) (encodeInputs state)).map
      (terminalConfig program) = SourceProgram.run program profile state := by
  rw [toInformationGraph_terminalOutcomes_eq program (compileEventProfile program profile)
    scheduler (toInformationGraph program).canonicalScheduler (encodeInputs state)]
  exact canonical_terminalConfig_distribution program profile state

/-- Every public schedule preserves the full typed-state projection of source execution. -/
theorem scheduled_terminalState_distribution
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (scheduler : (toInformationGraph program).PublicScheduler)
    (profile : BehavioralProfile program) (state : State L Γ) :
    ((toInformationGraph program).terminalOutcomes scheduler
        (compileEventProfile program profile) (encodeInputs state)).map
      (terminalState program) =
      (SourceProgram.run program profile state).map SourceProgram.Config.state := by
  rw [toInformationGraph_terminalOutcomes_eq program (compileEventProfile program profile)
    scheduler (toInformationGraph program).canonicalScheduler (encodeInputs state)]
  exact canonical_terminalState_distribution program profile state

/-- Arbitrary public scheduling preserves the raw expression-payout projection. -/
theorem scheduled_payout_distribution
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (scheduler : (toInformationGraph program).PublicScheduler)
    (profile : BehavioralProfile program) (state : State L Γ) :
    ((toInformationGraph program).terminalOutcomes scheduler
        (compileEventProfile program profile) (encodeInputs state)).map
      (terminalPayouts program) =
      (SourceProgram.run program profile state).map
        (fun config => program.evaluatePayoffs config.state) := by
  rw [toInformationGraph_terminalOutcomes_eq program (compileEventProfile program profile)
    scheduler (toInformationGraph program).canonicalScheduler (encodeInputs state)]
  exact canonical_payout_distribution program profile state

/-- One compiled graph and profile preserve the complete private-setup law
under every public scheduler, without a finiteness or independence premise. -/
theorem scheduled_setup_distribution (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.informationGraph.PublicScheduler)
    (profile : BehavioralProfile setup.program) :
    (setup.initialDistribution.bind fun initial =>
      (setup.informationGraph.terminalOutcomes scheduler
        (compileEventProfile setup.program profile) (setup.eventInputs initial)).map
          (terminalConfig setup.program)) = setup.run profile := by
  unfold Setup.run
  apply bind_congr_on_support _
  intro initial _
  exact scheduled_terminalConfig_distribution_eq setup.program scheduler profile initial

end Vegas
