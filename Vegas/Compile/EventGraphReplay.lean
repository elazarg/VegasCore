module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.RecordedReplay
public import Vegas.Compile.EventGraphPolicyAlignment
public import Vegas.EventGraph.PolicyCongruence
public import Vegas.Source.ProtocolBehavioralEvaluation
public import Vegas.Source.ValueBindingAdmission

@[expose] public section

/-! # Source histories for actual compiled event records

Backtranslation preserves the canonical law of any whole graph profile. Combined
with canonical record replay, this gives a genuine full-interface source history
for every reachable compiled terminal configuration with actor-local seriality.
The source history retains the complete typed configuration and own actions.
Its ex-post witness is not a uniform deviation or equilibrium compiler.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- An arbitrary whole graph profile has its canonical source backtranslation. -/
theorem canonical_profile_terminalConfig_distribution
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O)
    (profile : (toInformationGraph program).BehavioralProfile) (state : State L Γ) :
    ((toInformationGraph program).terminalOutcomes (toInformationGraph program).canonicalScheduler
      profile (encodeInputs state)).map (terminalConfig program) =
    SourceProgram.run program (fun owner => backtranslateEventPolicy program owner (profile owner))
      state := by
  let source : BehavioralProfile program :=
    fun owner => backtranslateEventPolicy program owner (profile owner)
  have kernels : (toInformationGraph program).runPolicies
      (toInformationGraph program).canonicalScheduler (compileEventProfile program source)
        (encodeInputs state) =
    (toInformationGraph program).runPolicies (toInformationGraph program).canonicalScheduler
      profile (encodeInputs state) := by
    apply EventGraph.runPolicies_canonical_eq_of_reachable
    intro config reachable offset ordered event ready rank owner actor active
    exact compileEventPolicy_backtranslate_at_prefix program owner (profile owner)
      (encodeInputs state) config reachable offset ordered event ready rank actor active
  have outcomes : (toInformationGraph program).terminalOutcomes
      (toInformationGraph program).canonicalScheduler (compileEventProfile program source)
        (encodeInputs state) =
    (toInformationGraph program).terminalOutcomes (toInformationGraph program).canonicalScheduler
      profile (encodeInputs state) := by
    apply pmf_map_injective (f := Subtype.val) Subtype.val_injective
    simpa only [EventGraph.terminalOutcomes_map_val] using kernels
  rw [← outcomes]
  exact canonical_terminalConfig_distribution program source state

/-- Source decoding of an actual terminal record table is supported by a genuine source run.
The source profile may depend on that ex-post table; this is a reachability result. -/
private theorem terminalConfig_mem_source_run_of_reachable
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (deps : (toEventGraph program).Dependencies)
    (serial : ((toEventGraph program).withDependencies deps).ActorSerial)
    (state : State L Γ) (final : ((toEventGraph program).withDependencies deps).Config)
    (reach : final.Reachable (encodeInputs state)) (terminal : final.cut.Terminal) :
    ∃ source : BehavioralProfile program,
      terminalConfig program ⟨EventGraph.rankedConfig
          (graph := (toEventGraph program).withDependencies deps)
          final terminal,
        EventGraph.rankedConfig_terminal
          (graph := (toEventGraph program).withDependencies deps)
          final terminal⟩ ∈
      (SourceProgram.run program source state).support := by
  obtain ⟨profile, supported⟩ :=
    serial.exists_canonical_replay (encodeInputs state) final reach terminal
  change EventGraph.rankedConfig
          (graph := (toEventGraph program).withDependencies deps)
          final terminal ∈
    ((toInformationGraph program).runPolicies (toInformationGraph program).canonicalScheduler
      profile (encodeInputs state)).support at supported
  have terminalSupported : (⟨EventGraph.rankedConfig
          (graph := (toEventGraph program).withDependencies deps)
          final terminal,
        EventGraph.rankedConfig_terminal
          (graph := (toEventGraph program).withDependencies deps)
          final terminal⟩ :
        {config : (toInformationGraph program).Config // config.cut.Terminal}) ∈
      ((toInformationGraph program).terminalOutcomes (toInformationGraph program).canonicalScheduler
        profile (encodeInputs state)).support := by
    rw [← EventGraph.terminalOutcomes_map_val (toInformationGraph program)
      (toInformationGraph program).canonicalScheduler profile (encodeInputs state),
      PMF.support_map] at supported
    obtain ⟨actual, member, same⟩ := supported
    have equal : actual = ⟨EventGraph.rankedConfig
          (graph := (toEventGraph program).withDependencies deps)
          final terminal,
        EventGraph.rankedConfig_terminal
          (graph := (toEventGraph program).withDependencies deps)
          final terminal⟩ := Subtype.ext same
    exact equal ▸ member
  refine ⟨fun owner => backtranslateEventPolicy program owner (profile owner), ?_⟩
  rw [← canonical_profile_terminalConfig_distribution program profile state, PMF.support_map]
  exact ⟨_, terminalSupported, rfl⟩

/-- Actual terminal graph records admit a genuine full-interface source history. -/
theorem source_history_of_graph_terminal_reachable
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (deps : (toEventGraph program).Dependencies)
    (serial : ((toEventGraph program).withDependencies deps).ActorSerial)
    (state : State L Γ) (final : ((toEventGraph program).withDependencies deps).Config)
    (reach : final.Reachable (encodeInputs state)) (terminal : final.cut.Terminal) :
    ∃ history : (executionProtocol program (CommitmentInterface.forfeiture program)
        (Config.initial state)).History,
      ProtocolState.readout program history.state = some
        (terminalConfig program
          ⟨EventGraph.rankedConfig
              (graph := (toEventGraph program).withDependencies deps) final terminal,
            EventGraph.rankedConfig_terminal
              (graph := (toEventGraph program).withDependencies deps) final terminal⟩) := by
  obtain ⟨source, supported⟩ :=
    terminalConfig_mem_source_run_of_reachable program deps serial state final reach terminal
  let result := terminalConfig program
    ⟨EventGraph.rankedConfig (graph := (toEventGraph program).withDependencies deps)
        final terminal,
      EventGraph.rankedConfig_terminal (graph := (toEventGraph program).withDependencies deps)
        final terminal⟩
  have someSupported : some result ∈ ((SourceProgram.run program source state).map some).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨_, supported, rfl⟩
  change some result ∈
    ((runFrom program source (Config.initial state)).map some).support at someSupported
  rw [← protocol_runBehavioral_eq program (CommitmentInterface.forfeiture program)
    (Config.initial state) source
    (fun owner => (source owner).admitted_forfeiture program), PMF.support_map] at someSupported
  obtain ⟨history, _member, readout⟩ := someSupported
  exact ⟨history, readout⟩

end Vegas
