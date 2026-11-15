module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.BindingReveal
public import Vegas.Compile.RevealFailureReadout
public import Vegas.EventGraph.ResolutionProvenance
public import Vegas.EventGraph.RankedConfig

@[expose] public section

/-! # Failed compiled bindings cannot be repaired

Every source binding has its actual subject reveal. A stored binding failure
therefore forces an owned failed publication and public default at completion,
under every valid dependency choice and arbitrary later strategic actions.
-/

noncomputable section

namespace Vegas

open Vegas.EventGraph SourceProgram GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]

/-- Accepted failed bindings cannot be repaired by concurrent completions. -/
theorem failed_publication_of_failed_compiled_binding
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (deps : (toEventGraph program).Dependencies)
    {inputs : ((toEventGraph program).withDependencies deps).Inputs}
    {config : ((toEventGraph program).withDependencies deps).Config}
    (reach : config.Reachable inputs) (terminal : config.cut.Terminal)
    (event : Fin (eventCount program)) (owner : Player) (payload : L.Ty)
    (binding : outputLayout program event = .binding owner payload)
    (failed : (⟨.inr event, binding⟩ : FieldRef
      ((toEventGraph program).withDependencies deps).layout (.binding owner payload)).get?
        config.store = some .failure) :
    ∃ reveal, ((toEventGraph program).withDependencies deps).actor? reveal = some owner ∧
      (outputLayout program reveal).IsPublication ∧
      ∃ value, config.outputs reveal = some value ∧ EventField.FailedValue _ value := by
  let graph := (toEventGraph program).withDependencies deps
  let subject : FieldRef graph.layout (.binding owner payload) := ⟨.inr event, binding⟩
  obtain ⟨reveal, owned, publication, resolves⟩ :=
    withDependencies_binding_subject program deps event binding
  obtain ⟨outputEq, checks, codeEq⟩ :=
    (graph.nodes reveal).eq_resolve_of_resolutionField subject resolves
  refine ⟨reveal, owned, publication, ?_⟩
  exact config.failed_output_of_publication_read reveal payload outputEq
    (reach.failed_publication_read_of_failed_subject terminal reveal owner payload subject checks
      outputEq codeEq failed)

/-- Every terminal continuation after a stored failed binding publicly excludes its owner. -/
theorem defaulted_of_failed_compiled_binding
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (deps : (toEventGraph program).Dependencies)
    {inputs : ((toEventGraph program).withDependencies deps).Inputs}
    {config : ((toEventGraph program).withDependencies deps).Config}
    (reach : config.Reachable inputs) (terminal : config.cut.Terminal)
    (event : Fin (eventCount program)) (owner : Player) (payload : L.Ty)
    (binding : outputLayout program event = .binding owner payload)
    (failed : (⟨.inr event, binding⟩ : FieldRef
      ((toEventGraph program).withDependencies deps).layout (.binding owner payload)).get?
        config.store = some .failure) :
    owner ∈ config.defaulted := by
  obtain ⟨reveal, actor, publication, failedOutput⟩ :=
    failed_publication_of_failed_compiled_binding program deps reach terminal event owner payload
      binding failed
  exact reach.defaulted_of_failed_publication reveal owner actor publication failedOutput

/-- A stored failed binding incurs at least one own failed reveal in the full source readout. -/
theorem failedReveals_pos_of_failed_compiled_binding
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (deps : (toEventGraph program).Dependencies)
    {inputs : ((toEventGraph program).withDependencies deps).Inputs}
    {config : ((toEventGraph program).withDependencies deps).Config}
    (reach : config.Reachable inputs) (terminal : config.cut.Terminal)
    (event : Fin (eventCount program)) (owner : Player) (payload : L.Ty)
    (binding : outputLayout program event = .binding owner payload)
    (failed : (⟨.inr event, binding⟩ : FieldRef
      ((toEventGraph program).withDependencies deps).layout (.binding owner payload)).get?
        config.store = some .failure) :
    1 ≤ failedReveals program owner
      (publicOutcome program (terminalConfig program
        ⟨rankedConfig (graph := (toEventGraph program).withDependencies deps) config terminal,
          rankedConfig_terminal (graph := (toEventGraph program).withDependencies deps)
            config terminal⟩)) := by
  obtain ⟨reveal, actor, publication, failedOutput⟩ :=
    failed_publication_of_failed_compiled_binding program deps reach terminal event owner payload
      binding failed
  exact failedReveals_pos_of_failed_output program _ reveal owner publication
    ((eventOwner?_eq_actor program reveal).trans actor) failedOutput

end Vegas
