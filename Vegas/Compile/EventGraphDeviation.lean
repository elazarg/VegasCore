/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphPolicyAlignment
import Vegas.Compile.EventGraphScheduling
import Vegas.EventGraph.PolicyCongruence

/-! # Exact deviation backtranslation for compiled graphs

Each graph replacement is one source policy chosen before private setup.
Generated sequential dependencies make the complete law independent of public
scheduling; no scheduler mixture or finite-alphabet premise is required.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- One backtranslated policy implements a canonical graph deviation exactly,
including every typed cell, original choice and public default record. -/
theorem canonical_deviation_terminalConfig_law
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (profile : BehavioralProfile program)
    (who : Player) (replacement : (toEventGraph program).BehavioralPolicy who)
    (state : State L Γ) :
    ((toEventGraph program).terminalOutcomes (toEventGraph program).canonicalScheduler
      (Profile.update (sig := (toEventGraph program).gameSignature)
        (compileEventProfile program profile) who replacement) (encodeInputs state)).map
          (terminalConfig program) =
      SourceProgram.run program
        (Profile.update (sig := SourceProgram.gameSignature program) profile who
          (backtranslateEventPolicy program who replacement)) state := by
  let graph := toEventGraph program
  let translated := Profile.update (sig := SourceProgram.gameSignature program) profile who
    (backtranslateEventPolicy program who replacement)
  have kernels : graph.runPolicies graph.canonicalScheduler
      (compileEventProfile program translated) (encodeInputs state) =
      graph.runPolicies graph.canonicalScheduler
        (Profile.update (sig := graph.gameSignature)
          (compileEventProfile program profile) who replacement) (encodeInputs state) := by
    apply EventGraph.runPolicies_canonical_eq_of_reachable
    intro config reachable offset ordered event ready rank owner actor active
    rw [show compileEventProfile program translated =
        Profile.update (sig := graph.gameSignature) (compileEventProfile program profile) who
          (compileEventPolicy program who (backtranslateEventPolicy program who replacement)) from
      compileEventProfile_update program profile who _]
    by_cases same : owner = who
    · subst owner
      simp only [Profile.update_same]
      exact compileEventPolicy_backtranslate_at_prefix program who replacement
        (encodeInputs state) config reachable offset ordered event ready rank actor active
    · simp only [Profile.update_of_ne _ _ same]
  have outcomes : graph.terminalOutcomes graph.canonicalScheduler
      (compileEventProfile program translated) (encodeInputs state) =
      graph.terminalOutcomes graph.canonicalScheduler
        (Profile.update (sig := graph.gameSignature)
          (compileEventProfile program profile) who replacement) (encodeInputs state) := by
    apply pmf_map_injective (f := Subtype.val) Subtype.val_injective
    simpa only [EventGraph.terminalOutcomes_map_val] using kernels
  rw [← outcomes]
  exact canonical_terminalConfig_law program translated state

/-- Every public scheduler admits the same exact single-policy backtranslation. -/
theorem scheduled_deviation_terminalConfig_law
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (scheduler : (toEventGraph program).PublicScheduler) (profile : BehavioralProfile program)
    (who : Player) (replacement : (toEventGraph program).BehavioralPolicy who)
    (state : State L Γ) :
    ((toEventGraph program).terminalOutcomes scheduler
      (Profile.update (sig := (toEventGraph program).gameSignature)
        (compileEventProfile program profile) who replacement) (encodeInputs state)).map
          (terminalConfig program) =
      SourceProgram.run program
        (Profile.update (sig := SourceProgram.gameSignature program) profile who
          (backtranslateEventPolicy program who replacement)) state := by
  rw [toEventGraph_terminalOutcomes_eq program _ scheduler
    (toEventGraph program).canonicalScheduler]
  exact canonical_deviation_terminalConfig_law program profile who replacement state

/-- Typed terminal-state deviation correspondence is a projection of the full law. -/
theorem canonical_deviation_terminalState_law
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (profile : BehavioralProfile program)
    (who : Player) (replacement : (toEventGraph program).BehavioralPolicy who)
    (state : State L Γ) :
    ((toEventGraph program).terminalOutcomes (toEventGraph program).canonicalScheduler
      (Profile.update (sig := (toEventGraph program).gameSignature)
        (compileEventProfile program profile) who replacement) (encodeInputs state)).map
          (terminalState program) =
      (SourceProgram.run program
        (Profile.update (sig := SourceProgram.gameSignature program) profile who
          (backtranslateEventPolicy program who replacement)) state).map Config.state := by
  have law := congrArg (PMF.map Config.state)
    (canonical_deviation_terminalConfig_law program profile who replacement state)
  simpa only [PMF.map_comp, terminalConfig, Function.comp_def] using law

/-- A canonical replacement has one distributed source law across arbitrary
correlated private/public initial states, with opponents unchanged. -/
theorem canonical_setup_deviation_law (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) (who : Player)
    (replacement : setup.eventGraph.BehavioralPolicy who) :
    ((setup.eventGraph.canonicalGame
      (setup.initialLaw.map fun initial => setup.eventInputs initial)).play
      (Profile.update (sig := setup.eventGraph.gameSignature)
        (compileEventProfile setup.program profile) who replacement)).map
          (terminalConfig setup.program) =
      setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program) profile who
        (backtranslateEventPolicy setup.program who replacement)) := by
  unfold EventGraph.canonicalGame EventGraph.gameForm Setup.run
  simp only [PMF.map_bind, PMF.bind_map]
  apply bind_congr_on_support _
  intro initial _
  exact canonical_deviation_terminalConfig_law setup.program profile who replacement initial

/-- Exact distributed deviation backtranslation for every public scheduler.
The source policy is independent of the sampled initial state; no mixture,
finite-history, finite-payload or finite-initial-law premise occurs. -/
theorem scheduled_setup_deviation_law (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.eventGraph.PublicScheduler) (profile : BehavioralProfile setup.program)
    (who : Player) (replacement : setup.eventGraph.BehavioralPolicy who) :
    (setup.initialLaw.bind fun initial =>
      (setup.eventGraph.terminalOutcomes scheduler
        (Profile.update (sig := setup.eventGraph.gameSignature)
          (compileEventProfile setup.program profile) who replacement)
        (setup.eventInputs initial)).map (terminalConfig setup.program)) =
      setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program) profile who
        (backtranslateEventPolicy setup.program who replacement)) := by
  unfold Setup.run
  apply bind_congr_on_support _
  intro initial _
  exact scheduled_deviation_terminalConfig_law setup.program scheduler profile who replacement
    initial

/-- Finite source binding alphabets give finite graph action types. -/
theorem toEventGraph_finiteActions {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (finite : program.FiniteBindingTypes) :
    (toEventGraph program).FiniteActions := fun event =>
  outputLayout_action_finite program finite event

end Vegas
