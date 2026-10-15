/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphState
import Vegas.EventGraph.ConfigRestriction
import Vegas.Source.RegistryFailureExtension
import Vegas.Source.CommitRecoveryNonCommitPath

/-! # Actual completed samples and their typed recovery successors -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] in
private theorem recorded_sample_value {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {Γ : SourceCtx Player L} {payload : L.Ty}
    (refs : ContextRefs layout Γ) (state : State L Γ) (store : Store layout)
    (agree : refs.Agrees state store) (sourceLaw : L.DistExpr (SourcePublicCtx L Γ) payload)
    {kind : EventField Player L} (node : EventCode layout kind)
    (outputEq : kind = .publicData payload)
    (codeEq : cast (congrArg (EventCode layout) outputEq) node =
      .sample payload (compilePublicDist refs sourceLaw))
    (action : kind.Action) (law : PMF kind.Value) (value : kind.Value)
    (evaluated : node.eval? action store = some law) (supported : value ∈ law.support) :
    ∃ sampled : L.Val payload,
      sampled ∈ (L.evalDist sourceLaw (sourcePublicEnv state)).support ∧
      cast (congrArg (fun field => Option field.Value) outputEq) (some value) = some sampled := by
  cases outputEq
  simp only [cast_eq] at codeEq
  subst node
  have actual : (EventCode.sample payload (compilePublicDist refs sourceLaw)).eval? action store =
      some (L.evalDist sourceLaw (sourcePublicEnv state)) := by
    change (compilePublicDist refs sourceLaw).eval? store = _
    rw [PublicDist.eval?, compilePublicDist_evalLaw? refs state store agree sourceLaw]
    rfl
  have same := Option.some.inj (evaluated.symm.trans actual)
  exact ⟨value, same ▸ supported, rfl⟩

/-- A completed sample in an actual reachable graph state supplies a genuine
supported source recovery step, without any global service or completion law. -/
theorem completed_sample_source_successor {graph : Vegas.EventGraph Player L}
    {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (sourceLaw : L.DistExpr (SourcePublicCtx L Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: Γ) O)
    (config : graph.Config) {inputs : graph.Inputs} (reachable : config.Reachable inputs)
    (event : graph.EventId) (completed : event ∈ config.cut.completed)
    (outputEq : graph.outputLayout event = .publicData payload)
    (refs : ContextRefs graph.layout Γ) (entry : SourceProgram.Config Player L Γ)
    (registry : Registry Γ)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .sample payload (compilePublicDist refs sourceLaw))
    (agree : refs.Agrees entry.state config.store)
    (guards : Registry.FailureExtension entry.registry registry entry.state)
    (failures : Revelations.PreservesFailures entry.revelations entry.state) :
    ∃ sampled : L.Val payload,
      sampled ∈ (L.evalDist sourceLaw (sourcePublicEnv entry.state)).support ∧
      let after := sampleSuccessor name entry sampled
      (refs.cons (name := name) (cell := .publicData payload)
        ⟨.inr event, outputEq⟩).Agrees after.state config.store ∧
      Registry.FailureExtension after.registry registry.weaken after.state ∧
      Revelations.PreservesFailures after.revelations after.state ∧
      ∀ excluded generation,
        (commitRecoveryProtocol (.sample name fresh sourceLaw next) entry).Successor
          (CommitRecoveryState.atPoint (Sum.inr (ProtocolState.entry next after)) excluded
            generation)
          (CommitRecoveryState.atPoint (Sum.inl entry) excluded generation) := by
  obtain ⟨⟨selected, action⟩, recorded, named⟩ :=
    List.mem_map.mp ((config.history_exact event).mpr completed)
  change selected = event at named
  subst selected
  obtain ⟨law, value, stored, evaluated, supported⟩ :=
    reachable.history_output_semantics ⟨event, action⟩ recorded
  obtain ⟨sampled, sampledSupport, sampledStored⟩ :=
    recorded_sample_value refs entry.state config.store agree sourceLaw (graph.nodes event)
      outputEq codeEq action law value evaluated supported
  refine ⟨sampled, sampledSupport, ?_, ?_, ?_, ?_⟩
  · apply ContextRefs.Agrees.cons refs entry.state config.store agree
      (name := name) (cell := .publicData payload) ⟨.inr event, outputEq⟩ sampled
    change cast (congrArg (fun field => Option field.Value) outputEq)
      (config.outputs event) = _
    rw [stored]
    exact sampledStored
  · exact guards.weaken (name := name) (cell := .publicData payload) sampled
  · exact Revelations.PreservesFailures.weaken failures (name := name)
      (cell := .publicData payload) sampled
  · intro excluded generation
    apply CommitRecoveryState.nonCommit_successor (.sample name fresh sourceLaw next) entry
      (Sum.inl entry) excluded generation rfl (fun impossible => impossible) (fun _ => none)
      (Sum.inr (ProtocolState.entry next (sampleSuccessor name entry sampled)), excluded)
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨sampled, sampledSupport, rfl⟩

end Vegas
