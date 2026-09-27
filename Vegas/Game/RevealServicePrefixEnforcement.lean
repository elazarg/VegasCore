/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceOrdinaryComparison
import Vegas.Game.RevealServicePrefix
import Vegas.Game.SourceInformation

/-! # Extra packet classification at actual source prefixes

The existing compiler suffix identifies the current reveal node. The complete
checkpoint invariant then classifies every extra effective response as a fresh
submission carrying rejection or public format evidence. No policy incentives
or information-set correspondence are assumed.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem suffix_extra_submission
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (who : Player)
    (wholeProfile : BehavioralProfile setup.program) (initial : State L setup.context) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames), program.RevealOnly →
      ∀ (profile : BehavioralProfile program)
      (refs : ContextRefs (graphLayout setup.program) Γ) (revelations : Revelations Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding) (offset : Nat),
      CompiledPolicySuffix setup.program wholeProfile program profile refs revelations []
        embedding refsBefore offset →
      ∀ (count : Nat), count < eventCount program →
      ∀ (source : ProtocolState program) (execution : (application setup leaks).Execution),
      PrefixCheckpoint setup leaks initial program refs revelations embedding.ref
        offset count source execution →
      ∀ event : (graph setup).EventId, event.val = offset + count →
      (graph setup).actor? event = some who →
      execution.application.serviceGrant = some event →
      ∀ response : (application setup leaks).Action,
      response ∈ (bounds.menu (runtime setup) leaks).actions who
        (execution.recall who) (execution.observe (application setup leaks) who) →
      response ∉ ordinaryActions setup leaks bounds who (execution.recall who)
        (execution.observe (application setup leaks) who) →
      ∃ submission, response = ⟨some (.submit submission)⟩ ∧
        let state := (application setup leaks).submit execution.application who submission
        let packet := submission.emit state who (execution.network.known who)
        (application setup leaks).handle state
            ⟨(who, execution.network.nextSerial who), packet⟩ = none ∨
          certifiedOpening packet = false := by
  intro Γ openNames program
  induction program with
  | ret payoffs =>
      intro _reveals profile refs revelations embedding refsBefore offset aligned count within
      exact (Nat.not_lt_zero count within).elim
  | sample name fresh law next ih =>
      intro impossible
      exact impossible.elim
  | commit name owner fresh guard next ih =>
      intro impossible
      exact impossible.elim
  | @reveal Γ openNames published owner name payload fresh selected unresolved next ih =>
      intro reveals profile refs revelations embedding refsBefore offset aligned count within
        source execution related event eventRank actor granted response effective excluded
      cases count with
      | zero =>
          obtain ⟨source, rfl, _sourceRevelations, checkpoint⟩ := related
          let index : Fin (eventCount
            (.reveal published owner name fresh selected unresolved next)) :=
              ⟨0, by simp [eventCount]⟩
          have head : embedding.event index = event := by
            apply Fin.ext
            simpa only [index, Nat.add_zero] using (aligned.graphSuffix.rankEq index).trans
              eventRank.symm
          have ownerEq : owner = who := by
            have ownership := aligned.actorEq index
            change (toEventGraph setup.program).actor? (embedding.event index) = _ at ownership
            rw [head] at ownership
            change (toEventGraph setup.program).actor? event = some who at actor
            exact Option.some.inj (ownership.symm.trans actor)
          subst who
          have outputEq : (graph setup).outputLayout (embedding.event index) =
              .publication payload := embedding.layout_eq index
          have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
              ((graph setup).nodes (embedding.event index)) =
              .resolve owner payload (refs.get selected) [] :=
            reveal_head_code setup fresh selected unresolved next refs revelations
              embedding refsBefore offset aligned.graphSuffix
          have node : nodeView (graph setup) (embedding.event index) =
              .resolve owner payload (refs.get selected) [] outputEq codeEq := by
            cases viewed : nodeView (graph setup) (embedding.event index) with
            | bind other otherPayload kind code => cases kind.symm.trans outputEq
            | sample otherPayload law kind code => cases kind.symm.trans outputEq
            | resolve other otherPayload binding checks kind code =>
                have same : otherPayload = payload := EventGraph.EventField.publication.inj
                  (kind.symm.trans outputEq)
                subst otherPayload
                have codes : EventGraph.EventCode.resolve other payload binding checks =
                    .resolve owner payload (refs.get selected) [] := code.symm.trans codeEq
                cases codes
                rfl
          exact checkpoint_extra_submission setup leaks bounds source refs offset execution
            checkpoint selected (embedding.event index) (by rw [head]; omega)
            (by rw [head]; exact actor) outputEq codeEq node
            (by rw [head]; exact granted) response effective excluded
      | succ count =>
          cases source with
          | inl config => exact related.elim
          | inr source =>
              let index : Fin (eventCount
                (.reveal published owner name fresh selected unresolved next)) :=
                  ⟨0, by simp [eventCount]⟩
              let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
              let resultRef : EventGraph.FieldRef (graphLayout setup.program)
                  (.publication payload) :=
                    ⟨.inr (embedding.event index), embedding.layout_eq index⟩
              let tailRefs := refs.cons (name := published) (cell := .publication payload) resultRef
              have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
                intro readName cell ref remaining
                cases ref with
                | here =>
                    change (embedding.event index).val < (embedding.event (Fin.succ remaining)).val
                    apply embedding.strictMono
                    exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
                | there ref => exact refsBefore ref (Fin.succ remaining)
              have tailAligned : CompiledPolicySuffix setup.program wholeProfile next
                  (afterReveal profile) tailRefs (revelations.reveal selected)
                  [] tailEmbedding tailBefore (offset + 1) := by
                simpa only [Registry.weaken, List.map_nil, tailRefs, resultRef, index,
                  tailEmbedding, OutputEmbedding.ref] using aligned.revealTail
                    (whole := setup.program) (wholeProfile := wholeProfile) fresh selected
                    unresolved next profile refs revelations [] embedding refsBefore offset
              exact ih reveals (afterReveal profile) tailRefs (revelations.reveal selected)
                tailEmbedding tailBefore (offset + 1) tailAligned count
                (by simpa [eventCount] using within) source execution related event (by omega)
                actor granted response effective excluded

theorem prefix_extra_submission
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (who : Player)
    (reveals : setup.program.RevealOnly) (initial : State L setup.context)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (source : ProtocolState setup.program) (execution : (application setup leaks).Execution)
    (related : PrefixCheckpoint setup leaks initial setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (Revelations.initial setup.context) (outputRef setup.program) 0 event.val source execution)
    (granted : execution.application.serviceGrant = some event)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions who
      (execution.recall who) (execution.observe (application setup leaks) who))
    (extra : response ∉ ordinaryActions setup leaks bounds who (execution.recall who)
      (execution.observe (application setup leaks) who)) :
    ∃ submission, response = ⟨some (.submit submission)⟩ ∧
      let state := (application setup leaks).submit execution.application who submission
      let packet := submission.emit state who (execution.network.known who)
      (application setup leaks).handle state
          ⟨(who, execution.network.nextSerial who), packet⟩ = none ∨
        certifiedOpening packet = false := by
  let profile : BehavioralProfile setup.program :=
    fun owner => RevealOnly.uniformPolicy owner setup.program reveals
  exact suffix_extra_submission setup leaks bounds who profile initial setup.program reveals
    profile (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) (outputEmbedding setup.program)
    (initialRefsBefore setup.program) 0 (CompiledPolicySuffix.whole setup.program profile)
    event.val event.isLt source execution related event (by omega) owned granted
    response effective extra

end Vegas.SourceProgram.RevealService
