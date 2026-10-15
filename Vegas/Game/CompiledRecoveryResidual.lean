/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceCommitBlock
import Vegas.Compile.EventGraphSuffix
import Vegas.Source.CommitRecoveryPoint
import Vegas.Source.CommitRecoveryStep

/-! # Syntax-derived recovery residuals in the actual compiled node table -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeOpen)

/-- At every bounded rank, the existing residual-program carrier has a
syntax-derived lift and the exact compiled suffix. Recovery steps and retained
recall commute with that lift; no source-state correspondence is assumed. -/
theorem CompiledSuffix.exists_recoveryResidual :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (refs : ContextRefs (graphLayout whole) Γ)
    (revelations : Revelations Γ) (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
    (before : ContextRefsBefore refs embedding) (offset : Nat),
    CompiledSuffix whole program refs revelations registry embedding before offset →
    count ≤ eventCount program →
    ∃ residual : ResidualProgram program,
    ∃ tailRefs : ContextRefs (graphLayout whole) residual.context,
    ∃ tailRevelations : Revelations residual.context,
    ∃ tailRegistry : Registry residual.context,
    ∃ tailEmbedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) residual.tail,
    ∃ tailBefore : ContextRefsBefore tailRefs tailEmbedding,
      CompiledSuffix whole residual.tail tailRefs tailRevelations tailRegistry
        tailEmbedding tailBefore (offset + count) ∧
      Function.Injective residual.lift ∧
      (∀ point, ProtocolState.remaining program (residual.lift point) =
        ProtocolState.remaining residual.tail point) ∧
      (∀ point, ProtocolState.actor program (residual.lift point) =
        ProtocolState.actor residual.tail point) ∧
      (∀ point, ProtocolState.atCommit program (residual.lift point) =
        ProtocolState.atCommit residual.tail point) ∧
      (∀ point, ProtocolState.commitOwners program (residual.lift point) =
        ProtocolState.commitOwners residual.tail point) ∧
      (∀ point, ProtocolState.commitEnd program (residual.lift point) =
        ProtocolState.commitEnd residual.tail point) ∧
      (∀ point, residual.lift (ProtocolState.automaticCommitBlock residual.tail point) =
        ProtocolState.automaticCommitBlock program (residual.lift point)) ∧
      (∀ point, ProtocolState.history program (residual.lift point) =
        ProtocolState.history residual.tail point) ∧
      (∀ point past, residual.lift (ProtocolState.withHistory residual.tail point past) =
        ProtocolState.withHistory program (residual.lift point) past) ∧
      (∀ point excluded joint,
        ProtocolState.recoveryStep program (residual.lift point) excluded joint =
          (ProtocolState.recoveryStep residual.tail point excluded joint).map
            (fun result => (residual.lift result.1, result.2))) ∧
      (∀ who point, ProtocolView.recoveryAvailable who program
        (ProtocolState.observe who program (residual.lift point)) =
        ProtocolView.recoveryAvailable who residual.tail
          (ProtocolState.observe who residual.tail point)) := by
  intro count
  induction count with
  | zero =>
      intro Γ O program refs revelations registry embedding before offset compiled _bounded
      refine ⟨⟨Γ, O, program, id⟩, refs, revelations, registry, embedding, before, ?_,
        Function.injective_id, (fun _ => rfl), (fun _ => rfl), (fun _ => rfl), (fun _ => rfl),
        (fun _ => rfl), (fun _ => rfl), (fun _ => rfl), (fun _ _ => rfl), ?_⟩
      · simpa only [Nat.add_zero] using compiled
      · constructor
        · intro point excluded joint
          exact (PMF.map_id _).symm
        · intro who point
          rfl
  | succ count ih =>
      intro Γ O program refs revelations registry embedding before offset compiled bounded
      cases program with
      | ret _ => simp only [eventCount] at bounded; omega
      | sample name fresh law next =>
          have nextCompiled := compiled.sampleTail (_openNames := O) whole fresh law next refs
            revelations registry embedding before offset
          obtain ⟨residual, tailRefs, tailRevelations, tailRegistry, tailEmbedding, tailBefore,
            aligned, injective, remaining, actor, commit, owners, endpoint, automatic, history,
            memory, step, menus⟩ :=
            ih next _ _ _ _ _ (offset + 1) nextCompiled (by
              simp only [eventCount] at bounded
              omega)
          refine ⟨⟨residual.context, residual.names, residual.tail,
              fun point => Sum.inr (residual.lift point)⟩,
            tailRefs, tailRevelations, tailRegistry, tailEmbedding, tailBefore, ?_, ?_, ?_,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · convert aligned using 1; omega
          · intro left right same
            exact injective (Sum.inr.inj same)
          · intro point
            exact remaining point
          · intro point
            exact actor point
          · intro point
            exact commit point
          · intro point
            exact owners point
          · intro point
            exact endpoint point
          · intro point
            exact congrArg Sum.inr (automatic point)
          · intro point
            exact history point
          · intro point past
            exact congrArg Sum.inr (memory point past)
          · intro point excluded joint
            change ((ProtocolState.recoveryStep next (residual.lift point) excluded joint).map
              (fun result => (Sum.inr result.1, result.2))) = _
            rw [step]
            simp only [PMF.map_comp, Function.comp_def]
          · intro who point
            exact menus who point
      | commit name owner fresh guard next =>
          have nextCompiled := compiled.commitTail whole fresh guard next refs revelations registry
            embedding before offset
          obtain ⟨residual, tailRefs, tailRevelations, tailRegistry, tailEmbedding, tailBefore,
            aligned, injective, remaining, actor, commit, owners, endpoint, automatic, history,
            memory, step, menus⟩ :=
            ih next _ _ _ _ _ (offset + 1) nextCompiled (by
              simp only [eventCount] at bounded
              omega)
          refine ⟨⟨residual.context, residual.names, residual.tail,
              fun point => Sum.inr (residual.lift point)⟩,
            tailRefs, tailRevelations, tailRegistry, tailEmbedding, tailBefore, ?_, ?_, ?_,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · convert aligned using 1; omega
          · intro left right same
            exact injective (Sum.inr.inj same)
          · intro point
            exact remaining point
          · intro point
            exact actor point
          · intro point
            exact commit point
          · intro point
            exact owners point
          · intro point
            exact endpoint point
          · intro point
            exact congrArg Sum.inr (automatic point)
          · intro point
            exact history point
          · intro point past
            exact congrArg Sum.inr (memory point past)
          · intro point excluded joint
            change ((ProtocolState.recoveryStep next (residual.lift point) excluded joint).map
              (fun result => (Sum.inr result.1, result.2))) = _
            rw [step]
            simp only [PMF.map_comp, Function.comp_def]
          · intro who point
            exact menus who point
      | reveal published owner name fresh selected unresolved next =>
          have nextCompiled := compiled.revealTail whole fresh selected unresolved next refs
            revelations registry embedding before offset
          obtain ⟨residual, tailRefs, tailRevelations, tailRegistry, tailEmbedding, tailBefore,
            aligned, injective, remaining, actor, commit, owners, endpoint, automatic, history,
            memory, step, menus⟩ :=
            ih next _ _ _ _ _ (offset + 1) nextCompiled (by
              simp only [eventCount] at bounded
              omega)
          refine ⟨⟨residual.context, residual.names, residual.tail,
              fun point => Sum.inr (residual.lift point)⟩,
            tailRefs, tailRevelations, tailRegistry, tailEmbedding, tailBefore, ?_, ?_, ?_,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · convert aligned using 1; omega
          · intro left right same
            exact injective (Sum.inr.inj same)
          · intro point
            exact remaining point
          · intro point
            exact actor point
          · intro point
            exact commit point
          · intro point
            exact owners point
          · intro point
            exact endpoint point
          · intro point
            exact congrArg Sum.inr (automatic point)
          · intro point
            exact history point
          · intro point past
            exact congrArg Sum.inr (memory point past)
          · intro point excluded joint
            change ((ProtocolState.recoveryStep next (residual.lift point) excluded joint).map
              (fun result => (Sum.inr result.1, result.2))) = _
            rw [step]
            simp only [PMF.map_comp, Function.comp_def]
          · intro who point
            exact menus who point

end Vegas
