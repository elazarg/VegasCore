/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledRevealPhase
import Vegas.Game.CompiledRevealTail
import Vegas.Compile.PresentContextEvaluation
import Vegas.Pending.PhaseFailureCoverage

/-! # Intended source reveal meanings at partial physical publication cuts -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Virtual TRUE source reveals preserve intendedness and the meaning of every
physically present typed reference. Independent publications may remain absent;
no physical completion or synthetic history is asserted for those holes. -/
theorem intended_reveal_prefix_present :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {O : Finset VarId}
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (program : SourceProgram Player L Γ O) (prefixed : RevealPrefix program count)
    (refs : ContextRefs (graphLayout setup.program) Γ) (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (before : ContextRefsBefore refs embedding) (offset : Nat)
    (entry : SourceProgram.Config Player L Γ)
    (_compiled : CompiledSuffix setup.program program refs entry.revelations registry
      embedding before offset)
    (native : RecoveryState (serviceGraph setup mode))
    {inputs : (serviceGraph setup mode).Inputs}
    (_reachable : native.native.config.Reachable inputs)
    (_coverage : native.FailureCoverage) (_clear : native.excluded = ∅)
    (_intended : entry.Intended O)
    (_agree : refs.PresentAgrees entry.state native.native.config.store)
    (_bindings : ∀ {name owner payload} (selected : HasVar Γ name (.commitment owner payload)),
      (refs.get selected).get? native.native.config.store = some (entry.state.get selected))
    (_guards : Registry.FailureExtension entry.registry registry entry.state),
    ∃ final : SourceProgram.Config Player L (revealTail count program prefixed).context,
      final.Intended (revealTail count program prefixed).names ∧
      (revealTailRefs setup count program prefixed refs embedding).PresentAgrees
        final.state native.native.config.store ∧
      (∀ {name owner payload}
        (selected : HasVar (revealTail count program prefixed).context name
          (.commitment owner payload)),
        ((revealTailRefs setup count program prefixed refs embedding).get selected).get?
          native.native.config.store = some (final.state.get selected)) ∧
      Registry.FailureExtension final.registry
        (revealTailRegistry count program prefixed registry) final.state ∧
      (@Config.revelations Player L _ final) =
        (revealTailRevelations count program prefixed entry.revelations :
          Revelations (revealTail count program prefixed).context) := by
  intro count
  induction count with
  | zero =>
      intro Γ O setup mode program prefixed refs registry embedding before offset entry compiled
        native inputs reachable coverage clear intended agree bindings guards
      exact ⟨entry, intended, agree, bindings, guards, rfl⟩
  | succ count ih =>
      intro Γ O setup mode program prefixed refs registry embedding before offset entry compiled
        native inputs reachable coverage clear intended agree bindings guards
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | @reveal Γ O published owner name payload fresh source unresolved next =>
          let zero : Fin (eventCount (.reveal published owner name fresh source unresolved next)) :=
            ⟨0, by simp only [eventCount]; omega⟩
          let event := embedding.event zero
          have outputEq : (serviceGraph setup mode).outputLayout event = .publication payload := by
            change outputLayout setup.program (embedding.event zero) = .publication payload
            simpa only [zero, outputLayout, Fin.mk_zero, Fin.cases_zero] using
              embedding.layout_eq zero
          have codeEq : cast (congrArg (EventCode (graphLayout setup.program)) outputEq)
              ((toEventGraph setup.program).nodes event) =
              .resolve owner payload (refs.get source)
                (compileChecks (published := published) refs registry
                  entry.revelations source) := by
            simpa only [event, zero, compileRankedNodes, outputLayout, Fin.mk_zero, Fin.cases_zero]
              using compiled.nodeEq zero
          have acting : (serviceGraph setup mode).actor? event = some owner :=
            (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
          let after := revealSuccessor published source entry true
          have nextIntended := (intended.reveal fresh source).1
          let tailEmbedding := embedding.tail next (by simp only [eventCount]) (fun _ => rfl)
          let tailRefs := refs.cons (name := published) (cell := .publication payload)
            (⟨.inr event, outputEq⟩ : FieldRef (graphLayout setup.program) (.publication payload))
          have nextAgree : tailRefs.PresentAgrees after.state native.native.config.store := by
            intro readName cell selected value stored
            cases selected with
            | here =>
                cases value with
                | failure =>
                    have failed := (publication_failure_iff_read native.native event
                      (refs.get source) _ outputEq codeEq .failure stored).mpr rfl
                    have excluded := coverage.covered event owner acting failed
                    rw [clear] at excluded
                    exact (Finset.notMem_empty _ excluded).elim
                | success value =>
                    have physical := reachable.publication_binding event owner payload
                      (refs.get source) _ outputEq codeEq value stored
                    have same := Option.some.inj (physical.symm.trans (bindings source))
                    rw [intended.reveal_state (published := published) source]
                    exact same
            | there selected =>
                exact agree selected value stored
          have nextBindings : ∀ {readName other τ}
              (selected : HasVar ((published, .publication payload) :: Γ) readName
                (.commitment other τ)),
              (tailRefs.get selected).get? native.native.config.store =
                some (after.state.get selected) := by
            intro readName other τ selected
            cases selected with
            | there selected => exact bindings selected
          have nextGuards : Registry.FailureExtension after.registry registry.weaken
              after.state := by
            change Registry.FailureExtension entry.registry.weaken registry.weaken after.state
            rw [intended.reveal_state (published := published) source]
            exact guards.weaken (name := published) (cell := .publication payload)
              (entry.state.get source : PublicationResult (L.Val payload))
          have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
            intro readName cell selected remaining
            cases selected with
            | here =>
                change (embedding.event zero).val < (embedding.event (Fin.succ remaining)).val
                apply embedding.strictMono
                change 0 < remaining.val + 1
                omega
            | there selected => exact before selected (Fin.succ remaining)
          have nextCompiled : CompiledSuffix setup.program next tailRefs after.revelations
              registry.weaken tailEmbedding tailBefore (offset + 1) :=
            compiled.revealTail setup.program fresh source unresolved next refs
              entry.revelations registry embedding before offset
          obtain ⟨final, finalIntended, finalAgree, finalBindings, finalGuards, finalRevelations⟩ :=
            ih setup mode next prefixed tailRefs registry.weaken tailEmbedding tailBefore
              (offset + 1) after nextCompiled native reachable coverage clear nextIntended
                nextAgree nextBindings nextGuards
          exact ⟨final, finalIntended, finalAgree, finalBindings, finalGuards, finalRevelations⟩

end Vegas
