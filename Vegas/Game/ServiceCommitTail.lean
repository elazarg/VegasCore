/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceBlockDecode

/-! # The compiled residual after leading commitments

After `count` leading commitments of a residual program, the residual program
(`Vegas.commitTail`) carries its own compiled data: the references of its
context (`Vegas.commitTailRefs`), the embedding of its events
(`Vegas.commitTailEmbedding`), its obligation registry and revelations, and its
compiled policy suffix (`Vegas.CompiledPolicySuffix.commitTailMany`). The
prefix decoder of the program reads through the commitments into the residual
one (`Vegas.decodeSourcePrefix?_commitTail`).
-/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

variable (setup) in
/-- The context references after leading commitments. -/
def commitTailRefs : (count : Nat) → {Γ : SourceCtx Player L} → {names : Finset VarId} →
    (program : SourceProgram Player L Γ names) → (prefixed : CommitPrefix program count) →
    ContextRefs (graphLayout setup.program) Γ →
    OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program →
      ContextRefs (graphLayout setup.program) (commitTail count program prefixed).context
  | 0, _, _, _, _, refs, _ => refs
  | count + 1, _, _, .commit name _ _ _ next, prefixed, refs, embedding =>
      commitTailRefs count next prefixed
        (refs.cons (name := name) ⟨.inr (embedding.event ⟨0, by simp [eventCount]⟩),
          commit_headLayout embedding⟩)
        (embedding.tail next (by simp [eventCount]) (fun _ => rfl))
  | _ + 1, _, _, .ret _, prefixed, _, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed, _, _ => prefixed.elim
  | _ + 1, _, _, .reveal _ _ _ _ _ _ _, prefixed, _, _ => prefixed.elim

variable (setup) in
/-- The output embedding after leading commitments. -/
def commitTailEmbedding : (count : Nat) → {Γ : SourceCtx Player L} → {names : Finset VarId} →
    (program : SourceProgram Player L Γ names) → (prefixed : CommitPrefix program count) →
    OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program →
      OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (commitTail count program prefixed).tail
  | 0, _, _, _, _, embedding => embedding
  | count + 1, _, _, .commit _ _ _ _ next, prefixed, embedding =>
      commitTailEmbedding count next prefixed
        (embedding.tail next (by simp [eventCount]) (fun _ => rfl))
  | _ + 1, _, _, .ret _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .reveal _ _ _ _ _ _ _, prefixed, _ => prefixed.elim

/-- The obligation registry after leading commitments. -/
def commitTailRegistry : (count : Nat) → {Γ : SourceCtx Player L} → {names : Finset VarId} →
    (program : SourceProgram Player L Γ names) → (prefixed : CommitPrefix program count) →
    Registry Γ → Registry (commitTail count program prefixed).context
  | 0, _, _, _, _, registry => registry
  | count + 1, _, _, .commit (payload := payload) name owner _ guard next, prefixed, registry =>
      commitTailRegistry count next prefixed
        ({ owner := owner, subject := name, payload := payload, source := .here,
            guard := guard.weaken } :: registry.weaken)
  | _ + 1, _, _, .ret _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .reveal _ _ _ _ _ _ _, prefixed, _ => prefixed.elim

/-- The revelations after leading commitments. -/
def commitTailRevelations : (count : Nat) → {Γ : SourceCtx Player L} →
    {names : Finset VarId} → (program : SourceProgram Player L Γ names) →
    (prefixed : CommitPrefix program count) →
    Revelations Γ → Revelations (commitTail count program prefixed).context
  | 0, _, _, _, _, revelations => revelations
  | count + 1, _, _, .commit _ _ _ _ next, prefixed, revelations =>
      commitTailRevelations count next prefixed revelations.weaken
  | _ + 1, _, _, .ret _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .reveal _ _ _ _ _ _ _, prefixed, _ => prefixed.elim

/-- The residual references precede the residual embedding. -/
theorem commitTailRefsBefore :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (prefixed : CommitPrefix program count)
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program),
      ContextRefsBefore refs embedding →
      ContextRefsBefore (commitTailRefs setup count program prefixed refs embedding)
        (commitTailEmbedding setup count program prefixed embedding) := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed refs embedding before; exact before
  | succ count ih =>
      intro Γ names program prefixed refs embedding before
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ _ => exact prefixed.elim
      | @commit Γ names name owner payload fresh guard next =>
          apply ih next prefixed
          intro readName cell source remaining
          cases source with
          | here =>
              change (embedding.event ⟨0, by simp [eventCount]⟩).val <
                (embedding.event (Fin.succ remaining)).val
              apply embedding.strictMono
              exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
          | there source => exact before source (Fin.succ remaining)

/-- **The residual compiled policy suffix.** A compiled policy suffix at rank
`offset` gives one for the residual after `count` leading commitments, at rank
`offset + count`. -/
theorem CompiledPolicySuffix.commitTailMany (wholeProfile : BehavioralProfile setup.program) :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (prefixed : CommitPrefix program count)
      (profile : BehavioralProfile program)
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (revelations : Revelations Γ) (registry : Registry Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding) (offset : Nat),
      CompiledPolicySuffix setup.program wholeProfile program profile refs revelations registry
        embedding refsBefore offset →
      CompiledPolicySuffix setup.program wholeProfile (Vegas.commitTail count program prefixed).tail
        (commitTailProfile count program prefixed profile)
        (commitTailRefs setup count program prefixed refs embedding)
        (commitTailRevelations count program prefixed revelations)
        (commitTailRegistry count program prefixed registry)
        (commitTailEmbedding setup count program prefixed embedding)
        (commitTailRefsBefore count program prefixed refs embedding refsBefore)
        (offset + count) := by
  intro count
  induction count with
  | zero =>
      intro Γ names program prefixed profile refs revelations registry embedding refsBefore
        offset aligned
      exact aligned
  | succ count ih =>
      intro Γ names program prefixed profile refs revelations registry embedding refsBefore
        offset aligned
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ _ => exact prefixed.elim
      | @commit Γ names name owner payload fresh guard next =>
          have step := aligned.commitTail setup.program wholeProfile fresh guard next profile refs
            revelations registry embedding refsBefore offset
          have later := ih next prefixed (afterCommit profile) _ _ _ _ _ (offset + 1) step
          rw [show offset + (count + 1) = offset + 1 + count by omega]
          exact later

/-- The residual profile keeps effective disclosures. -/
theorem effective_commitTail {who : Player} :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (prefixed : CommitPrefix program count)
      (profile : BehavioralProfile program) (registry : Registry Γ)
      (revelations : Revelations Γ),
      (profile who).EffectiveDisclosures program registry revelations →
      ((commitTailProfile count program prefixed profile) who).EffectiveDisclosures
        (commitTail count program prefixed).tail
        (commitTailRegistry count program prefixed registry)
        (commitTailRevelations count program prefixed revelations) := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed profile registry revelations effective; exact effective
  | succ count ih =>
      intro Γ names program prefixed profile registry revelations effective
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ _ => exact prefixed.elim
      | @commit Γ names name owner payload fresh guard next =>
          exact ih next prefixed (afterCommit profile) _ _ effective

/-- **The prefix decoder reads through leading commitments.** -/
theorem decodeSourcePrefix?_commitTail :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (prefixed : CommitPrefix program count)
      (refs : ContextRefs (graphLayout setup.program) Γ) (registry : Registry Γ)
      (revelations : Revelations Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (more : Nat) (store : EventGraph.Store (graphLayout setup.program))
      (history : History Player L),
      decodeSourcePrefix? program refs registry revelations embedding.ref (count + more) store
          history =
        (decodeSourcePrefix? (commitTail count program prefixed).tail
          (commitTailRefs setup count program prefixed refs embedding)
          (commitTailRegistry count program prefixed registry)
          (commitTailRevelations count program prefixed revelations)
          (commitTailEmbedding setup count program prefixed embedding).ref more store
          history).map (commitTail count program prefixed).lift := by
  intro count
  induction count with
  | zero =>
      intro Γ names program prefixed refs registry revelations embedding more store history
      simp only [Nat.zero_add, commitTail, commitTailRefs, commitTailRegistry,
        commitTailRevelations, commitTailEmbedding]
      rw [Option.map_id]
      rfl
  | succ count ih =>
      intro Γ names program prefixed refs registry revelations embedding more store history
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ _ => exact prefixed.elim
      | @commit Γ names name owner payload fresh guard next =>
          rw [show count + 1 + more = (count + more) + 1 by omega, decodeSourcePrefix?_commit]
          exact (congrArg (Option.map Sum.inr) (ih next prefixed _ _ _
            (embedding.tail next (by simp [eventCount]) (fun _ => rfl)) more store history)).trans
            (by rw [Option.map_map]; rfl)

/-- The residual states embed injectively. -/
theorem commitTail_lift_injective : ∀ (count : Nat) {Γ : SourceCtx Player L}
    {names : Finset VarId} (program : SourceProgram Player L Γ names)
    (prefixed : CommitPrefix program count),
    Function.Injective (commitTail count program prefixed).lift := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed; exact Function.injective_id
  | succ count ih =>
      intro Γ names program prefixed
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ next => exact Sum.inr_injective.comp (ih next prefixed)

/-- The prefix decoder through leading commitments, at the residual's entry. -/
theorem decodeSourcePrefix?_commitTail_entry (count : Nat) {Γ : SourceCtx Player L}
    {names : Finset VarId} (program : SourceProgram Player L Γ names)
    (prefixed : CommitPrefix program count)
    (refs : ContextRefs (graphLayout setup.program) Γ) (registry : Registry Γ)
    (revelations : Revelations Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      program) (store : EventGraph.Store (graphLayout setup.program))
    (history : History Player L) :
    decodeSourcePrefix? program refs registry revelations embedding.ref count store history =
      (decodeState? (commitTailRefs setup count program prefixed refs embedding) store).map
        fun state => (commitTail count program prefixed).lift (ProtocolState.entry _
          ⟨state, commitTailRegistry count program prefixed registry,
            commitTailRevelations count program prefixed revelations, history⟩) := by
  have through := decodeSourcePrefix?_commitTail count program prefixed refs registry
    revelations embedding 0 store history
  rw [Nat.add_zero] at through
  rw [through]
  simp only [decodeSourcePrefix?, Option.map_map]
  rfl

/-- Recover the residual protocol view after leading commitments. -/
def commitTailRecover (who : Player) : (count : Nat) → {Γ : SourceCtx Player L} →
    {names : Finset VarId} → (program : SourceProgram Player L Γ names) →
    (prefixed : CommitPrefix program count) → Option (ProtocolView who program) →
      Option (ProtocolView who (commitTail count program prefixed).tail)
  | 0, _, _, _, _, view => view
  | count + 1, _, _, .commit _ _ _ _ next, prefixed, view =>
      commitTailRecover who count next prefixed (view.bind (Sum.elim (fun _ => none) some))
  | _ + 1, _, _, .ret _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .reveal _ _ _ _ _ _ _, prefixed, _ => prefixed.elim

/-- The program's view of an embedded residual state determines the residual
view. -/
theorem commitTailRecover_spec (who : Player) : ∀ (count : Nat) {Γ : SourceCtx Player L}
    {names : Finset VarId} (program : SourceProgram Player L Γ names)
    (prefixed : CommitPrefix program count)
    (state : Option (ProtocolState (commitTail count program prefixed).tail)),
    commitTailRecover who count program prefixed
        ((state.map (commitTail count program prefixed).lift).map
          (ProtocolState.observe who program)) =
      state.map (ProtocolState.observe who _) := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed state; cases state <;> rfl
  | succ count ih =>
      intro Γ names program prefixed state
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ next =>
          have later := ih next prefixed state
          cases state with
          | none => exact later
          | some state => exact later

/-- **Leading commitments compile to bindings.** In a compiled suffix, every
event among the first `count` leading commitments has a bind node. -/
theorem CompiledSuffix.commitPrefix_bind {mode : EventGraph.ExecutionMode} :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (_prefixed : CommitPrefix program count)
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (revelations : Revelations Γ) (registry : Registry Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding) (offset : Nat),
      CompiledSuffix setup.program program refs revelations registry embedding refsBefore
        offset →
      ∀ index : Fin (eventCount program), index.val < count →
        ∃ owner payload outputEq codeEq,
          EventGraphRuntime.nodeView (serviceGraph setup mode) (embedding.event index) =
            .bind owner payload outputEq codeEq := by
  intro count
  induction count with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ index below; omega
  | succ count ih =>
      intro Γ names program prefixed refs revelations registry embedding refsBefore offset
        suffix index below
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ _ => exact prefixed.elim
      | @commit Γ names name owner payload fresh guard next =>
          rcases index with ⟨position, bounded⟩
          cases position with
          | zero =>
              have outputEq : (serviceGraph setup mode).outputLayout
                  (embedding.event ⟨0, bounded⟩) = .binding owner payload := by
                change outputLayout setup.program _ = _
                simpa [outputLayout, eventCount] using embedding.layout_eq ⟨0, bounded⟩
              have codeEq : cast (congrArg (EventGraph.EventCode
                  (serviceGraph setup mode).layout) outputEq)
                  ((serviceGraph setup mode).nodes (embedding.event ⟨0, bounded⟩)) =
                    .bind owner payload := by
                change cast (congrArg (EventGraph.EventCode (graphLayout setup.program))
                  outputEq) ((toEventGraph setup.program).nodes _) = _
                simpa [compileRankedNodes] using suffix.nodeEq ⟨0, bounded⟩
              exact ⟨owner, payload, outputEq, codeEq,
                EventGraphRuntime.nodeView_eq_bind _ _⟩
          | succ position =>
              exact ih next prefixed _ _ _
                (embedding.tail next (by simp [eventCount]) (fun _ => rfl)) _ (offset + 1)
                (suffix.commitTail setup.program fresh guard next refs revelations registry
                  embedding refsBefore offset)
                ⟨position, by simp only [eventCount] at bounded; omega⟩ (by simp at below; omega)

end Vegas
