/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledRevealPhase
import Vegas.Game.CompiledRevealLayout
import Vegas.Source.CommitRecoveryNonCommitPath
import Vegas.Pending.PhaseRawCheckpoint

/-! # Typed source recovery at completed physical reveal boundaries -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)
  (refs : ContextRefs (graphLayout setup.program) Γ)
  (revelations : Revelations Γ) (registry : Registry Γ)
  (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
  (before : ContextRefsBefore refs embedding) (offset : Nat)
  (compiled : CompiledSuffix setup.program program refs revelations registry embedding before
    offset)
  (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
  (kind : phase.kind = .reveal) (low : phase.low = offset) (count : Nat)
  (high : phase.high = offset + count)

/-- Completed phase records reconstruct the exact permanent excluded set and
a realized legal auxiliary-source path, including every active disclosure and
the absence of owned actions at automatic excluded slots. -/
theorem sourceRecovery_of_completed_revealPhase
    (native : RecoveryState ((toEventGraph setup.program).withMode mode))
    {inputs : ((toEventGraph setup.program).withMode mode).Inputs}
    (reachable : native.native.config.Reachable inputs)
    (inherited : Finset Player)
    (record : SuffixExclusionRecord offset inherited native)
    (prefixEnd : native.native.config.cut.IsPrefix (offset + count))
    (ordered : native.OrderedPublicFailures offset inherited)
    (entry : SourceProgram.Config Player L Γ)
    (agree : refs.Agrees entry.state native.native.config.store)
    (guards : Registry.FailureExtension entry.registry registry entry.state)
    (failures : Revelations.PreservesFailures entry.revelations entry.state)
    (sameRevelations : (@Config.revelations Player L Γ entry) = @revelations)
    (unique : (Γ.map Prod.fst).Nodup) :
    let prefixed := compiled.revealPrefix_of_phase setup.program mode program refs revelations
      registry embedding before offset phase kind low count high
    ∃ final : SourceProgram.Config Player L (revealTail count program prefixed).context,
      (revealTailRefs setup count program prefixed refs embedding).Agrees
        final.state native.native.config.store ∧
      Registry.FailureExtension final.registry
        (revealTailRegistry count program prefixed registry) final.state ∧
      Revelations.PreservesFailures final.revelations final.state ∧
      (@Config.revelations Player L _ final) =
        (revealTailRevelations count program prefixed revelations :
          Revelations (revealTail count program prefixed).context) ∧
      Relation.ReflTransGen
        (fun left right : ProtocolState program × Finset Player =>
          ¬ ProtocolState.terminal program left.1 ∧
          ProtocolState.atCommit program left.1 = false ∧
          ∃ joint, right ∈ (ProtocolState.recoveryStep program left.1 left.2 joint).support)
        (ProtocolState.entry program entry, inherited)
        ((revealTail count program prefixed).lift (ProtocolState.entry _ final),
          native.excluded) ∧
      ∀ generation, (commitRecoveryProtocol program entry).Reaches
        (CommitRecoveryState.atPoint (ProtocolState.entry program entry) inherited generation)
        (CommitRecoveryState.atPoint
          ((revealTail count program prefixed).lift (ProtocolState.entry _ final))
          native.excluded generation) := by
  let prefixed := compiled.revealPrefix_of_phase setup.program mode program refs revelations
    registry embedding before offset phase kind low count high
  have completed : ∀ index : Fin (eventCount program), index.val < count →
      embedding.event index ∈ native.native.config.cut.completed := by
    intro index inside
    apply (prefixEnd.2 _).mpr
    rw [compiled.rankEq]
    omega
  obtain ⟨final, excluded, finalAgree, finalGuards, finalFailures, finalRevelations,
    members, path⟩ := completed_reveal_phase_source_path setup mode count program prefixed refs
      revelations registry embedding before offset compiled native reachable entry inherited agree
      guards failures sameRevelations unique ordered completed
  have excludedEq : excluded = native.excluded := by
    apply Finset.ext
    intro who
    rw [members, record.excluded]
    constructor
    · rintro (old | ⟨index, inside, acting, failed⟩)
      · exact Or.inl old
      · exact Or.inr ⟨embedding.event index, by rw [compiled.rankEq]; omega, acting, failed⟩
    · rintro (old | ⟨event, lower, acting, failed⟩)
      · exact Or.inl old
      · have upper := (prefixEnd.2 event).mp failed.completed
        have total := compiled.countEq
        have eventBound : event.val < eventCount setup.program := event.isLt
        let index : Fin (eventCount program) := ⟨event.val - offset, by omega⟩
        have same : embedding.event index = event := by
          apply Fin.ext
          rw [compiled.rankEq]
          dsimp only [index]
          omega
        exact Or.inr ⟨index, by dsimp only [index]; omega, same.symm ▸ acting,
          same.symm ▸ failed⟩
  subst excluded
  refine ⟨final, finalAgree, finalGuards, finalFailures, finalRevelations, path, ?_⟩
  intro generation
  exact CommitRecoveryState.reaches_of_nonCommit_path program entry generation _ _ path

end Vegas
