/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledRevealPresent

/-! # Intended compiled publication evaluation at ready partial source cuts -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A source reveal telescope still begins with a reveal immediately before
its next coordinate. -/
theorem RevealPrefix.revealTail_one :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (prefixed : RevealPrefix program count),
    RevealPrefix program (count + 1) → RevealPrefix (revealTail count program prefixed).tail 1 := by
  intro count
  induction count with
  | zero => intro Γ O program prefixed next; exact next
  | succ count ih =>
      intro Γ O program prefixed later
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ next => exact ih next prefixed later

/-- A ready first source disclosure computes its successful binding using
only the present source fields and its actual available footprint. -/
theorem compiled_intended_head_reveal_success
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (reveals : RevealPrefix program 1)
    (refs : ContextRefs (graphLayout setup.program) Γ) (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (before : ContextRefsBefore refs embedding) (offset : Nat)
    (entry : SourceProgram.Config Player L Γ)
    (compiled : CompiledSuffix setup.program program refs entry.revelations registry
      embedding before offset)
    (native : RecoveryState (serviceGraph setup mode))
    (intended : entry.Intended O)
    (agree : refs.PresentAgrees entry.state native.native.config.store)
    (guards : Registry.FailureExtension entry.registry registry entry.state)
    (event : (serviceGraph setup mode).EventId) (rank : event.val = offset)
    (ready : native.native.config.cut.Ready event) :
    ∃ owner payload binding checks outputEq codeEq,
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq ∧
      ∃ value, EventCode.resolveOutput? binding checks true native.native.config.store =
        some (.success value) := by
  cases program with
  | ret _ => exact reveals.elim
  | sample _ _ _ _ => exact reveals.elim
  | commit _ _ _ _ _ => exact reveals.elim
  | @reveal Γ O published owner name payload fresh source unresolved next =>
      let zero : Fin (eventCount (.reveal published owner name fresh source unresolved next)) :=
        ⟨0, by simp only [eventCount]; omega⟩
      have same : embedding.event zero = event := Fin.ext (by
        rw [compiled.rankEq]
        change offset + 0 = event.val
        omega)
      have zeroOutputEq : (serviceGraph setup mode).outputLayout (embedding.event zero) =
          .publication payload := (embedding.layout_eq zero).trans rfl
      have zeroCodeEq : cast (congrArg (EventCode (graphLayout setup.program)) zeroOutputEq)
          ((serviceGraph setup mode).nodes (embedding.event zero)) =
          .resolve owner payload (refs.get source)
            (compileChecks (published := published) refs registry entry.revelations source) := by
        change cast (congrArg (EventCode (graphLayout setup.program)) zeroOutputEq)
          ((toEventGraph setup.program).nodes _) = _
        simpa only [zero, compileRankedNodes, outputLayout, Fin.mk_zero, Fin.cases_zero]
          using compiled.nodeEq zero
      have transport : ∀ (other : (serviceGraph setup mode).EventId),
          embedding.event zero = other →
          ∃ outputEq : (serviceGraph setup mode).outputLayout other = .publication payload,
            cast (congrArg (EventCode (graphLayout setup.program)) outputEq)
                ((serviceGraph setup mode).nodes other) =
              .resolve owner payload (refs.get source)
                (compileChecks (published := published) refs registry
                  entry.revelations source) := by
        intro other equal
        cases equal
        exact ⟨zeroOutputEq, zeroCodeEq⟩
      obtain ⟨outputEq, codeEq⟩ := transport event same
      have reads : ((serviceGraph setup mode).nodes event).readFields =
          (EventCode.resolve owner payload (refs.get source)
            (compileChecks (published := published) refs registry
              entry.revelations source)).readFields :=
        (EventCode.readFields_cast outputEq _).symm.trans
          (congrArg EventCode.readFields codeEq)
      obtain ⟨value, resolved⟩ := resolveOutput_of_present_intended refs entry registry source
        native.native.config.store agree guards intended (fun field member =>
          native.native.config.read_available ready (reads.symm ▸ member))
      exact ⟨owner, payload, refs.get source, _, outputEq, codeEq,
        nodeView_eq_resolve outputEq codeEq, value, resolved⟩

end Vegas
