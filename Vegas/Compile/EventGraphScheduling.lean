/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphCanonical

/-! # Public scheduling of source-ranked compiled graphs -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Source compilation makes the enabled-event type a singleton at every
nonterminal cut, so every public scheduler gives the same policy plan. -/
theorem toEventGraph_policyPlan_eq {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (profile : (toEventGraph program).BehavioralProfile)
    (first second : (toEventGraph program).PublicScheduler) :
    (toEventGraph program).policyPlan profile first =
      (toEventGraph program).policyPlan profile second := by
  funext config notTerminal
  let nonempty := EventGraph.enabled_nonempty_of_not_terminal config notTerminal
  let witness : {event : (toEventGraph program).EventId // event ∈ config.cut.enabled} :=
    ⟨config.cut.enabled.min' nonempty, Finset.min'_mem _ nonempty⟩
  let : Subsingleton
      {event : (toEventGraph program).EventId // event ∈ config.cut.enabled} :=
    ⟨fun left right => Subtype.ext (EventOrder.Cut.ready_unique config.cut
      ((EventOrder.Cut.mem_enabled _ _).mp left.2)
      ((EventOrder.Cut.mem_enabled _ _).mp right.2))⟩
  have selected : first ((toEventGraph program).publicObserve config)
        config.cut.enabled nonempty =
      second ((toEventGraph program).publicObserve config) config.cut.enabled nonempty :=
    (eq_pure_of_subsingleton _ witness).trans (eq_pure_of_subsingleton _ witness).symm
  unfold EventGraph.policyPlan
  dsimp only
  rw [selected]

/-- Every graph behavioral profile has the same complete configuration law
under all public schedulers of its source-compiled graph. -/
theorem toEventGraph_runPolicies_eq {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (profile : (toEventGraph program).BehavioralProfile)
    (first second : (toEventGraph program).PublicScheduler)
    (inputs : (toEventGraph program).Inputs) :
    (toEventGraph program).runPolicies first profile inputs =
      (toEventGraph program).runPolicies second profile inputs := by
  unfold EventGraph.runPolicies
  rw [toEventGraph_policyPlan_eq program profile first second]

/-- Attaching terminality certificates preserves exact scheduler independence
of the complete graph configuration, including public defaults and own choices. -/
theorem toEventGraph_terminalOutcomes_eq {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (profile : (toEventGraph program).BehavioralProfile)
    (first second : (toEventGraph program).PublicScheduler)
    (inputs : (toEventGraph program).Inputs) :
    (toEventGraph program).terminalOutcomes first profile inputs =
      (toEventGraph program).terminalOutcomes second profile inputs := by
  apply pmf_map_injective (f := Subtype.val) Subtype.val_injective
  rw [EventGraph.terminalOutcomes_map_val, EventGraph.terminalOutcomes_map_val]
  exact toEventGraph_runPolicies_eq program profile first second inputs

/-- Every public schedule preserves the complete source configuration law. -/
theorem scheduled_terminalConfig_law
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (scheduler : (toEventGraph program).PublicScheduler)
    (profile : BehavioralProfile program) (state : State L Γ) :
    ((toEventGraph program).terminalOutcomes scheduler
        (compileEventProfile program profile) (encodeInputs state)).map
      (terminalConfig program) = SourceProgram.run program profile state := by
  rw [toEventGraph_terminalOutcomes_eq program (compileEventProfile program profile)
    scheduler (toEventGraph program).canonicalScheduler (encodeInputs state)]
  exact canonical_terminalConfig_law program profile state

/-- Every public schedule preserves the full typed-state projection of source execution. -/
theorem scheduled_terminalState_law
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (scheduler : (toEventGraph program).PublicScheduler)
    (profile : BehavioralProfile program) (state : State L Γ) :
    ((toEventGraph program).terminalOutcomes scheduler
        (compileEventProfile program profile) (encodeInputs state)).map
      (terminalState program) =
      (SourceProgram.run program profile state).map SourceProgram.Config.state := by
  rw [toEventGraph_terminalOutcomes_eq program (compileEventProfile program profile)
    scheduler (toEventGraph program).canonicalScheduler (encodeInputs state)]
  exact canonical_terminalState_law program profile state

/-- Arbitrary public scheduling preserves the raw expression-payout projection. -/
theorem scheduled_payout_law
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (scheduler : (toEventGraph program).PublicScheduler)
    (profile : BehavioralProfile program) (state : State L Γ) :
    ((toEventGraph program).terminalOutcomes scheduler
        (compileEventProfile program profile) (encodeInputs state)).map
      (terminalPayouts program) =
      (SourceProgram.run program profile state).map
        (fun config => program.evaluatePayoffs config.state) := by
  rw [toEventGraph_terminalOutcomes_eq program (compileEventProfile program profile)
    scheduler (toEventGraph program).canonicalScheduler (encodeInputs state)]
  exact canonical_payout_law program profile state

/-- One compiled graph and profile preserve the complete private-setup law
under every public scheduler, without a finiteness or independence premise. -/
theorem scheduled_setup_law (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.eventGraph.PublicScheduler)
    (profile : BehavioralProfile setup.program) :
    (setup.initialLaw.bind fun initial =>
      (setup.eventGraph.terminalOutcomes scheduler
        (compileEventProfile setup.program profile) (setup.eventInputs initial)).map
          (terminalConfig setup.program)) = setup.run profile := by
  unfold Setup.run
  apply bind_congr_on_support _
  intro initial _
  exact scheduled_terminalConfig_law setup.program scheduler profile initial

end Vegas
