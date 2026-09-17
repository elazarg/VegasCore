/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphInputs
import Vegas.Compile.EventGraphLaw

/-! # Whole-program canonical event-graph law

This module instantiates the suffix execution theorem at the actual initial
configuration and removes its internal partial decoder using terminal store
availability.  It adds no simulation hypothesis.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Executing the compiled graph with its canonical scheduler and then reading
its terminal source state has exactly the original source execution law. -/
theorem canonical_terminalState_law
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (profile : BehavioralProfile program)
    (state : State L Γ) :
    ((toEventGraph program).terminalOutcomes
        (toEventGraph program).canonicalScheduler
        (compileEventProfile program profile) (encodeInputs state)).map
      (terminalState program) =
    SourceProgram.run program profile state := by
  apply FinDist.map_injective (f := some) (Option.some_injective _)
  rw [terminalOutcomes_map_decode]
  have law := runWith_option_law program profile program profile
    (ContextRefs.initial Γ (outputLayout program)) (Revelations.initial Γ) []
    (outputEmbedding program) (initialRefsBefore program) 0
    (CompiledPolicySuffix.whole program profile)
    (Vegas.EventGraph.Config.initial
      (graph := toEventGraph program) (encodeInputs state))
    (Vegas.EventOrder.Cut.empty_isPrefix (toEventGraph program).order)
    state (initialConfig_agrees program state) (fun _ => []) rfl
  change _ = (runWith program profile state [] (Revelations.initial Γ) (fun _ => [])).map some
  rw [← law]
  rw [FinDist.map_comp]
  rfl

/-- Canonical compiled execution preserves the executable integer payout law,
not only the decoded terminal source-state law. -/
theorem canonical_payout_law
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (profile : BehavioralProfile program)
    (state : State L Γ) :
    ((toEventGraph program).terminalOutcomes
        (toEventGraph program).canonicalScheduler
        (compileEventProfile program profile) (encodeInputs state)).map
      (terminalPayouts program) =
    (SourceProgram.run program profile state).map program.evaluatePayoffs := by
  calc
    _ = ((toEventGraph program).terminalOutcomes
          (toEventGraph program).canonicalScheduler
          (compileEventProfile program profile) (encodeInputs state)).map
        (program.evaluatePayoffs ∘ terminalState program) := by
      apply congrArg (fun readout =>
        ((toEventGraph program).terminalOutcomes
          (toEventGraph program).canonicalScheduler
          (compileEventProfile program profile) (encodeInputs state)).map readout)
      funext result
      exact terminalPayouts_eq_source program result
    _ = _ := by
      rw [← FinDist.map_comp,
        canonical_terminalState_law program profile state]

/-- A single compiled graph and behavioral profile serve an entire finite law
of private/public initial source states. -/
theorem canonical_setup_law
    (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) :
    ((setup.eventGraph.canonicalGame
        (setup.initialLaw.map fun initial => setup.eventInputs initial)).play
      (compileEventProfile setup.program profile)).map
        (terminalState setup.program) =
      setup.run profile := by
  unfold Vegas.EventGraph.canonicalGame Vegas.EventGraph.gameForm Setup.run
  simp only [FinDist.map_bind, FinDist.bind_map]
  apply FinDist.bind_congr
  intro initial member
  exact canonical_terminalState_law setup.program profile initial

/-- One canonical compiled graph also preserves executable payout laws across
a distributed private initial-state law. -/
theorem canonical_setup_payout_law
    (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) :
    ((setup.eventGraph.canonicalGame
        (setup.initialLaw.map fun initial => setup.eventInputs initial)).play
      (compileEventProfile setup.program profile)).map
        (terminalPayouts setup.program) =
      (setup.run profile).map setup.program.evaluatePayoffs := by
  calc
    _ = ((setup.eventGraph.canonicalGame
          (setup.initialLaw.map fun initial => setup.eventInputs initial)).play
        (compileEventProfile setup.program profile)).map
          (setup.program.evaluatePayoffs ∘
            terminalState setup.program) := by
      apply congrArg (fun readout =>
        ((setup.eventGraph.canonicalGame
          (setup.initialLaw.map fun initial => setup.eventInputs initial)).play
          (compileEventProfile setup.program profile)).map readout)
      funext result
      exact terminalPayouts_eq_source setup.program result
    _ = _ := by
      rw [← FinDist.map_comp, canonical_setup_law setup profile]

end Vegas.SourceProgram.EventLowering
