/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphInputs
import Vegas.Compile.EventGraphLaw

/-! # Whole-program canonical event-graph law

The suffix correspondence specializes to initial configurations and the total
terminal decoder. Typed-state and expression-payout laws are projections of
the complete configuration law.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Canonical compiled execution preserves the complete source configuration,
including public default history and actual own choices. -/
theorem canonical_terminalConfig_law
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (profile : BehavioralProfile program)
    (state : State L Γ) :
    ((toEventGraph program).terminalOutcomes
        (toEventGraph program).canonicalScheduler
        (compileEventProfile program profile) (encodeInputs state)).map
      (terminalConfig program) =
    SourceProgram.run program profile state := by
  apply pmf_map_injective (f := some) (Option.some_injective _)
  rw [terminalOutcomes_map_decodeConfig]
  have law := runFrom_option_law program profile program profile
    (ContextRefs.initial Γ (outputLayout program)) (SourceProgram.Config.initial state)
    (outputEmbedding program) (initialRefsBefore program) 0
    (CompiledPolicySuffix.whole program profile)
    (EventGraph.Config.initial (graph := toEventGraph program) (encodeInputs state))
    (EventOrder.Cut.empty_isPrefix (toEventGraph program).order)
    (initialConfig_agrees program state) rfl rfl
  exact law

/-- Reading the typed state from canonical compiled execution has exactly the
typed-state projection of the source execution law. -/
theorem canonical_terminalState_law
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (profile : BehavioralProfile program)
    (state : State L Γ) :
    ((toEventGraph program).terminalOutcomes
        (toEventGraph program).canonicalScheduler
        (compileEventProfile program profile) (encodeInputs state)).map
      (terminalState program) =
    (SourceProgram.run program profile state).map SourceProgram.Config.state := by
  have law := congrArg
    (fun law : PMF (SourceProgram.Config Player L program.terminalCtx) =>
      law.map SourceProgram.Config.state)
    (canonical_terminalConfig_law program profile state)
  simpa only [PMF.map_comp, terminalConfig, Function.comp_def] using law

/-- Canonical compiled execution preserves the raw integer expression-payout law. -/
theorem canonical_payout_law
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (profile : BehavioralProfile program)
    (state : State L Γ) :
    ((toEventGraph program).terminalOutcomes
        (toEventGraph program).canonicalScheduler
        (compileEventProfile program profile) (encodeInputs state)).map
      (terminalPayouts program) =
    (SourceProgram.run program profile state).map
      (fun config => program.evaluatePayoffs config.state) := by
  calc
    _ = ((toEventGraph program).terminalOutcomes
          (toEventGraph program).canonicalScheduler
          (compileEventProfile program profile) (encodeInputs state)).map
        ((fun config => program.evaluatePayoffs config.state) ∘ terminalConfig program) := by
      apply congrArg (fun readout =>
        ((toEventGraph program).terminalOutcomes
          (toEventGraph program).canonicalScheduler
          (compileEventProfile program profile) (encodeInputs state)).map readout)
      funext result
      exact terminalPayouts_eq_source program result
    _ = _ := by
      rw [← PMF.map_comp, canonical_terminalConfig_law program profile state]

/-- One compiled graph and behavioral profile preserve the full source law
across an arbitrary distribution of private and public initial states. -/
theorem canonical_setup_law
    (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) :
    ((setup.eventGraph.canonicalGame
        (setup.initialLaw.map fun initial => setup.eventInputs initial)).play
      (compileEventProfile setup.program profile)).map
        (terminalConfig setup.program) =
      setup.run profile := by
  unfold EventGraph.canonicalGame EventGraph.gameForm Setup.run
  simp only [PMF.map_bind, PMF.bind_map]
  apply bind_congr_on_support _
  intro initial member
  exact canonical_terminalConfig_law setup.program profile initial

/-- One canonical compiled graph preserves raw integer expression payouts
across a distributed private and public initial-state law. -/
theorem canonical_setup_payout_law
    (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) :
    ((setup.eventGraph.canonicalGame
        (setup.initialLaw.map fun initial => setup.eventInputs initial)).play
      (compileEventProfile setup.program profile)).map
        (terminalPayouts setup.program) =
      (setup.run profile).map (fun config => setup.program.evaluatePayoffs config.state) := by
  calc
    _ = ((setup.eventGraph.canonicalGame
          (setup.initialLaw.map fun initial => setup.eventInputs initial)).play
        (compileEventProfile setup.program profile)).map
          ((fun config => setup.program.evaluatePayoffs config.state) ∘
            terminalConfig setup.program) := by
      apply congrArg (fun readout =>
        ((setup.eventGraph.canonicalGame
          (setup.initialLaw.map fun initial => setup.eventInputs initial)).play
          (compileEventProfile setup.program profile)).map readout)
      funext result
      exact terminalPayouts_eq_source setup.program result
    _ = _ := by
      rw [← PMF.map_comp, canonical_setup_law setup profile]

end Vegas
