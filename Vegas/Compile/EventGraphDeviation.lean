module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphPolicyAlignment
public import Vegas.Compile.EventGraphScheduling
public import Vegas.EventGraph.PolicyCongruence

@[expose] public section

/-! # Exact deviation backtranslation for source information graphs

Each graph replacement is one source policy chosen before private setup.
The source information dependencies make the complete law independent of public
scheduling; no scheduler mixture or finite-alphabet premise is required.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- At canonical configurations, one backtranslated policy preserves the full
graph law when compiled against the original opponents. -/
theorem canonical_deviation_runPolicies_distribution
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (profile : BehavioralProfile program)
    (who : Player) (replacement : (toInformationGraph program).BehavioralPolicy who)
    (inputs : (toInformationGraph program).Inputs) :
    let graph := toInformationGraph program
    graph.runPolicies graph.canonicalScheduler
        (compileEventProfile program (Profile.update (sig := SourceProgram.gameSignature program)
          profile who (backtranslateEventPolicy program who replacement))) inputs =
      graph.runPolicies graph.canonicalScheduler
        (Profile.update (sig := graph.gameSignature)
          (compileEventProfile program profile) who replacement) inputs := by
  intro graph
  let translated := Profile.update (sig := SourceProgram.gameSignature program) profile who
    (backtranslateEventPolicy program who replacement)
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
      inputs config reachable offset ordered event ready rank actor active
  · simp only [Profile.update_of_ne _ _ same]

/-- One backtranslated policy implements a canonical graph deviation exactly,
including every typed cell, original choice and public default record. -/
theorem canonical_deviation_terminalConfig_distribution
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (profile : BehavioralProfile program)
    (who : Player) (replacement : (toInformationGraph program).BehavioralPolicy who)
    (state : State L Γ) :
    ((toInformationGraph program).terminalOutcomes (toInformationGraph program).canonicalScheduler
      (Profile.update (sig := (toInformationGraph program).gameSignature)
        (compileEventProfile program profile) who replacement) (encodeInputs state)).map
          (terminalConfig program) =
      SourceProgram.run program
        (Profile.update (sig := SourceProgram.gameSignature program) profile who
          (backtranslateEventPolicy program who replacement)) state := by
  let graph := toInformationGraph program
  let translated := Profile.update (sig := SourceProgram.gameSignature program) profile who
    (backtranslateEventPolicy program who replacement)
  have kernels := canonical_deviation_runPolicies_distribution program profile who replacement
    (encodeInputs state)
  have outcomes : graph.terminalOutcomes graph.canonicalScheduler
      (compileEventProfile program translated) (encodeInputs state) =
      graph.terminalOutcomes graph.canonicalScheduler
        (Profile.update (sig := graph.gameSignature)
          (compileEventProfile program profile) who replacement) (encodeInputs state) := by
    apply pmf_map_injective (f := Subtype.val) Subtype.val_injective
    simpa only [EventGraph.terminalOutcomes_map_val, translated, graph] using kernels
  rw [← outcomes]
  exact canonical_terminalConfig_distribution program translated state

/-- Every public scheduler admits the same exact single-policy backtranslation. -/
theorem scheduled_deviation_terminalConfig_distribution
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (scheduler : (toInformationGraph program).PublicScheduler) (profile : BehavioralProfile program)
    (who : Player) (replacement : (toInformationGraph program).BehavioralPolicy who)
    (state : State L Γ) :
    ((toInformationGraph program).terminalOutcomes scheduler
      (Profile.update (sig := (toInformationGraph program).gameSignature)
        (compileEventProfile program profile) who replacement) (encodeInputs state)).map
          (terminalConfig program) =
      SourceProgram.run program
        (Profile.update (sig := SourceProgram.gameSignature program) profile who
          (backtranslateEventPolicy program who replacement)) state := by
  rw [toInformationGraph_terminalOutcomes_eq program _ scheduler
    (toInformationGraph program).canonicalScheduler]
  exact canonical_deviation_terminalConfig_distribution program profile who replacement state

/-- Typed terminal-state deviation correspondence is a projection of the full law. -/
theorem canonical_deviation_terminalState_distribution
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (profile : BehavioralProfile program)
    (who : Player) (replacement : (toInformationGraph program).BehavioralPolicy who)
    (state : State L Γ) :
    ((toInformationGraph program).terminalOutcomes (toInformationGraph program).canonicalScheduler
      (Profile.update (sig := (toInformationGraph program).gameSignature)
        (compileEventProfile program profile) who replacement) (encodeInputs state)).map
          (terminalState program) =
      (SourceProgram.run program
        (Profile.update (sig := SourceProgram.gameSignature program) profile who
          (backtranslateEventPolicy program who replacement)) state).map Config.state := by
  have law := congrArg (PMF.map Config.state)
    (canonical_deviation_terminalConfig_distribution program profile who replacement state)
  simpa only [PMF.map_comp, terminalConfig, Function.comp_def] using law

/-- A canonical replacement has one distributed source law across arbitrary
correlated private/public initial states, with opponents unchanged. -/
theorem canonical_setup_deviation_distribution (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) (who : Player)
    (replacement : setup.informationGraph.BehavioralPolicy who) :
    ((setup.informationGraph.canonicalGame
      (setup.initialDistribution.map fun initial => setup.eventInputs initial)).play
      (Profile.update (sig := setup.informationGraph.gameSignature)
        (compileEventProfile setup.program profile) who replacement)).map
          (terminalConfig setup.program) =
      setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program) profile who
        (backtranslateEventPolicy setup.program who replacement)) := by
  unfold EventGraph.canonicalGame EventGraph.gameForm Setup.run
  simp only [PMF.map_bind, PMF.bind_map]
  apply bind_congr_on_support _
  intro initial _
  exact canonical_deviation_terminalConfig_distribution setup.program profile who replacement
    initial

/-- Exact distributed deviation backtranslation for every public scheduler.
The source policy is independent of the sampled initial state; no mixture,
finite-history, finite-payload or finite-initial-law premise occurs. -/
theorem scheduled_setup_deviation_distribution (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.informationGraph.PublicScheduler) (profile : BehavioralProfile setup.program)
    (who : Player) (replacement : setup.informationGraph.BehavioralPolicy who) :
    (setup.initialDistribution.bind fun initial =>
      (setup.informationGraph.terminalOutcomes scheduler
        (Profile.update (sig := setup.informationGraph.gameSignature)
          (compileEventProfile setup.program profile) who replacement)
        (setup.eventInputs initial)).map (terminalConfig setup.program)) =
      setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program) profile who
        (backtranslateEventPolicy setup.program who replacement)) := by
  unfold Setup.run
  apply bind_congr_on_support _
  intro initial _
  exact scheduled_deviation_terminalConfig_distribution setup.program scheduler profile who
    replacement
    initial

/-- Simultaneous behavioral replacements on any coalition admit one source
profile that keeps the original policies of players outside the coalition.
The same profile preserves the full terminal configuration law at every
initial state and under every public scheduler. -/
theorem coalition_deviation_terminalConfig_distribution
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (profile : BehavioralProfile program)
    (coalition : Set Player) (deviation : (toInformationGraph program).BehavioralProfile)
    (outsiders : ∀ who ∉ coalition, deviation who = compileEventProfile program profile who) :
    ∃ translated : BehavioralProfile program,
      (∀ who ∉ coalition, translated who = profile who) ∧
      ∀ (state : State L Γ) (scheduler : (toInformationGraph program).PublicScheduler),
        ((toInformationGraph program).terminalOutcomes scheduler deviation (encodeInputs state)).map
            (terminalConfig program) = SourceProgram.run program translated state := by
  classical
  let graph := toInformationGraph program
  let translated : BehavioralProfile program := fun who =>
    if who ∈ coalition then backtranslateEventPolicy program who (deviation who) else profile who
  refine ⟨translated, fun who outside => ite_eq_right outside, ?_⟩
  intro state scheduler
  have kernels : graph.runPolicies graph.canonicalScheduler (compileEventProfile program translated)
      (encodeInputs state) = graph.runPolicies graph.canonicalScheduler deviation
        (encodeInputs state) := by
    apply EventGraph.runPolicies_canonical_eq_of_reachable
    intro config reachable offset ordered event ready rank who actor active
    by_cases member : who ∈ coalition
    · simp only [compileEventProfile, translated, ite_eq_left member]
      exact compileEventPolicy_backtranslate_at_prefix program who (deviation who)
        (encodeInputs state) config reachable offset ordered event ready rank actor active
    · rw [outsiders who member]
      simp only [compileEventProfile, translated, ite_eq_right member]
  have outcomes : graph.terminalOutcomes graph.canonicalScheduler
      (compileEventProfile program translated) (encodeInputs state) =
      graph.terminalOutcomes graph.canonicalScheduler deviation (encodeInputs state) := by
    apply pmf_map_injective (f := Subtype.val) Subtype.val_injective
    simpa only [EventGraph.terminalOutcomes_map_val] using kernels
  rw [toInformationGraph_terminalOutcomes_eq program deviation scheduler graph.canonicalScheduler,
    ← outcomes]
  exact canonical_terminalConfig_distribution program translated state

/-- The coalition backtranslation preserves the complete law with correlated
initial draws. One source profile works for every public scheduler. -/
theorem setup_coalition_deviation_distribution (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) (coalition : Set Player)
    (deviation : setup.informationGraph.BehavioralProfile)
    (outsiders : ∀ who ∉ coalition,
      deviation who = compileEventProfile setup.program profile who) :
    ∃ translated : BehavioralProfile setup.program,
      (∀ who ∉ coalition, translated who = profile who) ∧
      ∀ scheduler : setup.informationGraph.PublicScheduler,
        (setup.initialDistribution.bind fun initial =>
          (setup.informationGraph.terminalOutcomes scheduler deviation
            (setup.eventInputs initial)).map (terminalConfig setup.program)) =
          setup.run translated := by
  obtain ⟨translated, unchanged, law⟩ :=
    coalition_deviation_terminalConfig_distribution setup.program profile coalition deviation
      outsiders
  refine ⟨translated, unchanged, fun scheduler => ?_⟩
  unfold Setup.run
  apply bind_congr_on_support _
  intro initial _
  exact law initial scheduler

/-- Finite source binding alphabets give finite graph action types. -/
theorem toInformationGraph_finiteActions {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (finite : program.FiniteBindingTypes) :
    (toInformationGraph program).FiniteActions := fun event =>
  outputLayout_action_finite program finite event

end Vegas
