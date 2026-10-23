/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledCommitAttempt
import Vegas.Source.CommitPhaseRegistry
import Vegas.Source.RegistryFailureExtension

/-! # Exact guard registry readback for recovered commitment blocks -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeOpen) (mode : EventGraph.ExecutionMode)

/-- The static compiler registry extends the actual decoded source registry only
by obligations on failed bindings supplied automatically for excluded slots. -/
theorem decodeCommitAttempt_registry_extension {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (registry : Registry Γ)
    (valid : Registry.FailureExtension entry.registry registry entry.state) :
    Registry.FailureExtension
      (decodeCommitAttempt whole mode block suffix embedding native entry excluded).1.registry
      (block.guardRegistry registry)
      (decodeCommitAttempt whole mode block suffix embedding native entry excluded).1.state := by
  induction block generalizing excluded with
  | nil => exact valid
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      let zero : Fin (eventCount ((SourceProgram.CommitPrefix.commit name owner fresh guard
          rest).prepend suffix)) := ⟨0, by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]
        omega⟩
      let laterEmbedding := embedding.tail (rest.prepend suffix) (by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      let obligation : Obligation ((name, .commitment owner payload) :: Γ) :=
        { owner := owner, subject := name, payload := payload, source := .here,
          guard := guard.weaken }
      by_cases inactive : owner ∈ excluded
      · have extended : Registry.FailureExtension
            (automaticCommit name owner payload entry).registry
            (obligation :: registry.weaken) (automaticCommit name owner payload entry).state :=
          (valid.weaken (name := name) (cell := .commitment owner payload)
            PublicationResult.failure).failed_cons obligation rfl
        have later := ih suffix laterEmbedding (automaticCommit name owner payload entry)
          excluded (obligation :: registry.weaken) extended
        dsimp only [decodeCommitAttempt, SourceProgram.CommitPrefix.guardRegistry,
          OutputEmbedding.tail, SourceProgram.CommitPrefix.prepend]
        rw [dite_eq_left inactive]
        exact later
      · let choice := (native.accepted (.inr (embedding.event zero))).elim
          PublicationResult.failure (fun candidate => native.bindingResult candidate payload)
        have extended : Registry.FailureExtension
            (commitSuccessor name guard entry choice).registry
            (obligation :: registry.weaken) (commitSuccessor name guard entry choice).state :=
          (valid.weaken (name := name) (cell := .commitment owner payload) choice).cons obligation
        have later := ih suffix laterEmbedding (commitSuccessor name guard entry choice)
          (excludeCommit excluded owner (native.accepted (.inr (embedding.event zero))).isNone)
          (obligation :: registry.weaken) extended
        dsimp only [decodeCommitAttempt, SourceProgram.CommitPrefix.guardRegistry,
          OutputEmbedding.tail, SourceProgram.CommitPrefix.prepend]
        rw [dite_eq_right inactive]
        exact later

end Vegas
