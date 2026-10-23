/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.CommitBlockReferences
import Vegas.Compile.EventGraphSuffix
import Vegas.Compile.CompiledReadoutSuffix
import Vegas.Compile.ProtocolViewSuffix
import Vegas.Source.CommitRecoveryBlockEmbedding
import Vegas.Source.CommitPhaseRegistry

/-! # Exact compiled suffixes following actual typed commitment attempts -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO)

/-- Advancing the actual typed attempt retains the exact compiler suffix,
including its unchanged static registry and the attempt's revelations. This
does not equate static guard obligations with the source registry. -/
theorem SourceProgram.CommitPrefix.Attempt.compiledTail
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {block : SourceProgram.CommitPrefix Γ O Δ P}
    {entry : SourceProgram.Config Player L Γ} {excluded : Finset Player}
    {finished : SourceProgram.Config Player L Δ} {afterExcluded : Finset Player}
    (attempt : block.Attempt entry excluded finished afterExcluded) :
    ∀ (suffix : SourceProgram Player L Δ P)
    (refs : ContextRefs (graphLayout whole) Γ) (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (before : ContextRefsBefore refs embedding) (offset : Nat),
    CompiledSuffix whole (block.prepend suffix) refs entry.revelations registry
      embedding before offset →
    CompiledReadoutSuffix whole (block.prepend suffix) refs embedding →
    (lift : ProtocolState (block.prepend suffix) → ProtocolState whole) →
    ProtocolViewSuffix whole (block.prepend suffix) refs embedding lift →
    ∃ finalEmbedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) suffix,
    ∃ finalBefore : ContextRefsBefore
      (commitBlockRefs whole block suffix embedding refs) finalEmbedding,
      CompiledSuffix whole suffix (commitBlockRefs whole block suffix embedding refs)
        finished.revelations (block.guardRegistry registry) finalEmbedding finalBefore
        (offset + block.length) ∧
      CompiledReadoutSuffix whole suffix (commitBlockRefs whole block suffix embedding refs)
        finalEmbedding ∧
      Nonempty (ProtocolViewSuffix whole suffix (commitBlockRefs whole block suffix embedding refs)
        finalEmbedding (fun point => lift (block.liftPoint suffix point))) := by
  induction attempt with
  | nil =>
      intro suffix refs registry embedding before offset compiled readout lift views
      refine ⟨embedding, before, ?_, readout, ⟨views⟩⟩
      simpa only [CommitPrefix.length, CommitPrefix.prepend, commitBlockRefs,
        CommitPrefix.guardRegistry, Nat.add_zero] using compiled
  | @active Γ O Δ P name owner payload fresh guard rest config excluded finished afterExcluded
      active choice missed missingFailure later ih =>
      intro suffix refs registry embedding before offset compiled readout lift views
      let zero : Fin (eventCount ((SourceProgram.CommitPrefix.commit name owner fresh guard
          rest).prepend suffix)) := ⟨0, by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]
        omega⟩
      let tailEmbedding := embedding.tail (rest.prepend suffix) (by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      let headRef : FieldRef (graphLayout whole) (.binding owner payload) :=
        ⟨.inr (embedding.event zero), by
          change outputLayout whole (embedding.event zero) = .binding owner payload
          simpa only [zero, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
            Fin.cases_zero] using embedding.layout_eq zero⟩
      let tailRefs := refs.cons (name := name) (cell := .commitment owner payload) headRef
      have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
        intro readName cell selected remaining
        cases selected with
        | here =>
            change (embedding.event zero).val < (embedding.event (Fin.succ remaining)).val
            apply embedding.strictMono
            change 0 < remaining.val + 1
            omega
        | there selected => exact before selected (Fin.succ remaining)
      let obligation : Obligation ((name, .commitment owner payload) :: Γ) :=
        { owner := owner, subject := name, payload := payload, source := .here,
          guard := guard.weaken }
      have nextCompiled : CompiledSuffix whole (rest.prepend suffix) tailRefs
          (commitSuccessor name guard config choice).revelations
          (obligation :: registry.weaken) tailEmbedding tailBefore (offset + 1) :=
        compiled.commitTail whole fresh guard (rest.prepend suffix) refs config.revelations
          registry embedding before offset
      have nextReadout : CompiledReadoutSuffix whole (rest.prepend suffix) tailRefs
          tailEmbedding :=
        readout.commitTail whole fresh guard (rest.prepend suffix) refs embedding
      obtain ⟨finalEmbedding, finalBefore, aligned, terminalAligned, ⟨finalViews⟩⟩ :=
        ih suffix tailRefs
        (obligation :: registry.weaken) tailEmbedding tailBefore (offset + 1) nextCompiled
        nextReadout (fun point => lift (Sum.inr point))
        (ProtocolViewSuffix.commitTail whole fresh guard (rest.prepend suffix) refs embedding
          lift views)
      refine ⟨finalEmbedding, finalBefore, ?_, terminalAligned, ⟨finalViews⟩⟩
      convert aligned using 1
      · rfl
      · rfl
      · change offset + (rest.length + 1) = offset + 1 + rest.length
        omega
  | @excluded Γ O Δ P name owner payload fresh guard rest config excluded finished afterExcluded
      inactive later ih =>
      intro suffix refs registry embedding before offset compiled readout lift views
      let zero : Fin (eventCount ((SourceProgram.CommitPrefix.commit name owner fresh guard
          rest).prepend suffix)) := ⟨0, by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]
        omega⟩
      let tailEmbedding := embedding.tail (rest.prepend suffix) (by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      let headRef : FieldRef (graphLayout whole) (.binding owner payload) :=
        ⟨.inr (embedding.event zero), by
          change outputLayout whole (embedding.event zero) = .binding owner payload
          simpa only [zero, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
            Fin.cases_zero] using embedding.layout_eq zero⟩
      let tailRefs := refs.cons (name := name) (cell := .commitment owner payload) headRef
      have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
        intro readName cell selected remaining
        cases selected with
        | here =>
            change (embedding.event zero).val < (embedding.event (Fin.succ remaining)).val
            apply embedding.strictMono
            change 0 < remaining.val + 1
            omega
        | there selected => exact before selected (Fin.succ remaining)
      let obligation : Obligation ((name, .commitment owner payload) :: Γ) :=
        { owner := owner, subject := name, payload := payload, source := .here,
          guard := guard.weaken }
      have nextCompiled : CompiledSuffix whole (rest.prepend suffix) tailRefs
          (automaticCommit name owner payload config).revelations
          (obligation :: registry.weaken) tailEmbedding tailBefore (offset + 1) :=
        compiled.commitTail whole fresh guard (rest.prepend suffix) refs config.revelations
          registry embedding before offset
      have nextReadout : CompiledReadoutSuffix whole (rest.prepend suffix) tailRefs
          tailEmbedding :=
        readout.commitTail whole fresh guard (rest.prepend suffix) refs embedding
      obtain ⟨finalEmbedding, finalBefore, aligned, terminalAligned, ⟨finalViews⟩⟩ :=
        ih suffix tailRefs
        (obligation :: registry.weaken) tailEmbedding tailBefore (offset + 1) nextCompiled
        nextReadout (fun point => lift (Sum.inr point))
        (ProtocolViewSuffix.commitTail whole fresh guard (rest.prepend suffix) refs embedding
          lift views)
      refine ⟨finalEmbedding, finalBefore, ?_, terminalAligned, ⟨finalViews⟩⟩
      convert aligned using 1
      · rfl
      · rfl
      · change offset + (rest.length + 1) = offset + 1 + rest.length
        omega

end Vegas
