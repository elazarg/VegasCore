/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledCommitPhase
import Vegas.Pending.EventBindingReadback

/-! # Source attempts read from actual native commitment tables

Accepted handles supply their fixed typed meaning. A missing handle is recorded
separately, and only that physical omission grows permanent exclusion. Slots of
an already excluded owner add no source action or guard obligation.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeOpen) (mode : EventGraph.ExecutionMode)

/-- Decode every actual accepted choice in source order, retaining precisely
active owned actions and the actual-miss distinction of the physical table. -/
def decodeCommitAttempt : {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    (block : SourceProgram.CommitPrefix Γ O Δ P) →
    (suffix : SourceProgram Player L Δ P) →
    OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) (block.prepend suffix) →
    EventGraphRuntime.State ((toEventGraph whole).withMode mode) →
    (entry : SourceProgram.Config Player L Γ) → (excluded : Finset Player) →
    Σ finished : SourceProgram.Config Player L Δ,
      Σ afterExcluded : Finset Player, block.Attempt entry excluded finished afterExcluded
  | _, _, _, _, .nil, _suffix, _embedding, _native, entry, excluded =>
      ⟨entry, excluded, .nil entry excluded⟩
  | _, _, _, _, .commit name owner fresh guard rest, suffix, embedding, native, entry,
      excluded =>
      let event := embedding.event ⟨0, by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]
        omega⟩
      let laterEmbedding := embedding.tail (rest.prepend suffix) (by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      if inactive : owner ∈ excluded then
        let later := decodeCommitAttempt rest suffix laterEmbedding native
          (automaticCommit name owner _ entry) excluded
        ⟨later.1, later.2.1, .excluded inactive later.2.2⟩
      else
        let accepted := native.accepted (.inr event)
        let choice := accepted.elim PublicationResult.failure (fun candidate =>
          native.bindingResult candidate _)
        let missed := accepted.isNone
        have missingFailure : missed = true → choice = .failure := by
          cases found : accepted <;> simp only [missed, choice, found, Option.isNone_none,
            Option.isNone_some, Option.elim_none, Bool.false_eq_true, false_implies, implies_true]
        let later := decodeCommitAttempt rest suffix laterEmbedding native
          (commitSuccessor name guard entry choice) (excludeCommit excluded owner missed)
        ⟨later.1, later.2.1, .active inactive choice missed missingFailure later.2.2⟩

end Vegas
