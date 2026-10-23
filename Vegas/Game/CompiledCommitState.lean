/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CompiledCommitOmissions
import Vegas.Compile.CommitBlockReferences
import Vegas.Pending.CompletedBindingReadback
import Vegas.Pending.PhaseAcceptedOrder

/-! # Typed state readback for complete physical commitment phases -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeOpen) (mode : EventGraph.ExecutionMode)

/-- Reading a completed interval of actual accepted bindings reconstructs its
source environment, including automatic slots and accepted unusable values. -/
theorem decodeCommitAttempt_state_agrees {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (refs : ContextRefs (graphLayout whole) Γ)
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player) (offset : Nat)
    (ranked : ∀ index, (embedding.event index).val = offset + index.val)
    (valid : native.BindingInvariant)
    (receipts : BindingReceiptOrder offset excluded native.accepted)
    (agree : refs.Agrees entry.state native.config.store)
    (completed : ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
      embedding.event index ∈ native.config.cut.completed) :
    (commitBlockRefs whole block suffix embedding refs).Agrees
      (decodeCommitAttempt whole mode block suffix embedding native entry excluded).1.state
      native.config.store := by
  induction block generalizing offset excluded with
  | nil => exact agree
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      let zero : Fin (eventCount ((SourceProgram.CommitPrefix.commit name owner fresh guard
          rest).prepend suffix)) := ⟨0, by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]
        omega⟩
      let laterEmbedding := embedding.tail (rest.prepend suffix) (by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      have headRank : (embedding.event zero).val = offset := by
        simpa only [zero, Nat.add_zero] using ranked zero
      have headOutput : ((toEventGraph whole).withMode mode).outputLayout
          (embedding.event zero) = .binding owner payload := by
        change outputLayout whole (embedding.event zero) = .binding owner payload
        simpa only [zero, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
          Fin.cases_zero] using
          embedding.layout_eq zero
      let headRef : EventGraph.FieldRef (graphLayout whole) (.binding owner payload) :=
        ⟨.inr (embedding.event zero), headOutput⟩
      have headRead := valid.binding_read headRef (embedding.event zero) rfl
        (completed zero (by simp only [zero, SourceProgram.CommitPrefix.length]; omega))
      have laterRank : ∀ index, (laterEmbedding.event index).val = offset + 1 + index.val := by
        intro index
        change (embedding.event (Fin.succ index)).val = offset + 1 + index.val
        rw [ranked]
        simp only [Fin.val_succ]
        omega
      have laterCompleted : ∀ index : Fin (eventCount (rest.prepend suffix)),
          index.val < rest.length → laterEmbedding.event index ∈ native.config.cut.completed := by
        intro index inside
        exact completed (Fin.succ index) (by
          change index.val + 1 < rest.length + 1
          omega)
      let tailRefs : ContextRefs (graphLayout whole) ((name, .commitment owner payload) :: Γ) :=
        refs.cons headRef
      intro readName readCell source
      by_cases inactive : owner ∈ excluded
      · have omitted : native.accepted (.inr (embedding.event zero)) = none := by
          cases found : native.accepted (.inr (embedding.event zero)) with
          | none => rfl
          | some candidate =>
              exact ((receipts _ owner payload candidate (by omega) headOutput found).1
                inactive).elim
        change headRef.get? native.config.store = some
          ((native.accepted (.inr (embedding.event zero))).elim PublicationResult.failure
            (fun candidate => native.bindingResult candidate payload)) at headRead
        rw [omitted, Option.elim_none] at headRead
        let nextEntry := automaticCommit name owner payload entry
        have extended : tailRefs.Agrees nextEntry.state native.config.store :=
          ContextRefs.Agrees.cons refs entry.state native.config.store agree
            (name := name) (cell := .commitment owner payload) headRef
            PublicationResult.failure headRead
        have later : (commitBlockRefs whole rest suffix laterEmbedding tailRefs).Agrees
            (decodeCommitAttempt whole mode rest suffix laterEmbedding native nextEntry
              excluded).1.state native.config.store :=
          ih suffix laterEmbedding tailRefs nextEntry excluded (offset + 1) laterRank
            (receipts.raise_low (by omega)) extended laterCompleted
        dsimp only [commitBlockRefs, decodeCommitAttempt, OutputEmbedding.tail,
          SourceProgram.CommitPrefix.prepend]
        rw [dite_eq_left inactive]
        exact later source
      · let choice := (native.accepted (.inr (embedding.event zero))).elim
          PublicationResult.failure (fun candidate => native.bindingResult candidate payload)
        let nextEntry := commitSuccessor name guard entry choice
        have extended : tailRefs.Agrees nextEntry.state native.config.store :=
          ContextRefs.Agrees.cons refs entry.state native.config.store agree
            (name := name) (cell := .commitment owner payload) headRef choice headRead
        have nextReceipts : BindingReceiptOrder (offset + 1)
            (excludeCommit excluded owner (native.accepted (.inr (embedding.event zero))).isNone)
            native.accepted := by
          cases found : native.accepted (.inr (embedding.event zero)) with
          | none =>
              simpa only [Option.isNone_none, excludeCommit, ↓reduceIte] using
                receipts.after_missing (embedding.event zero) headRank owner payload headOutput
                  found
          | some candidate =>
              simpa only [Option.isNone_some, excludeCommit, Bool.false_eq_true, ↓reduceIte] using
                receipts.raise_low (show offset ≤ offset + 1 by omega)
        have later : (commitBlockRefs whole rest suffix laterEmbedding tailRefs).Agrees
            (decodeCommitAttempt whole mode rest suffix laterEmbedding native nextEntry
              (excludeCommit excluded owner
                (native.accepted (.inr (embedding.event zero))).isNone)).1.state
            native.config.store :=
          ih suffix laterEmbedding tailRefs nextEntry _ (offset + 1) laterRank
            nextReceipts extended laterCompleted
        dsimp only [commitBlockRefs, decodeCommitAttempt, OutputEmbedding.tail,
          SourceProgram.CommitPrefix.prepend]
        rw [dite_eq_right inactive]
        exact later source

end Vegas
