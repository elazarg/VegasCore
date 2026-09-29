/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServicePrefix
import Vegas.Game.RevealServicePerturbation
import Vegas.Game.SourceContinuation
import Vegas.Game.RevealServiceRosterCheckpoint

/-! # Source action marginals at every native owner checkpoint

The existing compiler alignment recovers the original policy at the decoded
source observation. The statement holds at every operational checkpoint,
without assuming positive probability under the compiled policy.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem owner_choices_at_prefix
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    (wholeProfile : BehavioralProfile setup.program) (who : Player)
    (initial : State L setup.context) (initialSupport : initial ∈ setup.initialLaw.support) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames) (_reveals : program.RevealOnly)
      (profile : BehavioralProfile program)
      (refs : ContextRefs (graphLayout setup.program) Γ) (revelations : Revelations Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding) (offset : Nat),
      CompiledPolicySuffix setup.program wholeProfile program profile refs revelations []
        embedding refsBefore offset →
      ∀ (count : Nat), count < eventCount program →
      ∀ (state : ProtocolState program) (execution : (application setup leaks).Execution),
      PublicPrefixCheckpoint setup leaks initial program refs revelations embedding.ref
        offset count state execution →
      ∀ event : (graph setup).EventId, event.val = offset + count →
      (graph setup).actor? event = some who →
      execution.application.serviceGrant = some event →
      sourceChoiceLaw setup leaks wholeProfile who
          (execution.observe (application setup leaks) who) =
        ((profile who).protocolAction program (ProtocolState.observe who program state)).map
          OwnAction.disclosure ∧
      (∃ opening, opening? setup leaks who (execution.recall who)
          (execution.observe (application setup leaks) who) = some opening ∧
        opening ∈ ((bounds.withInitialValues (initialLaw setup)).menu (runtime setup) leaks).actions
          who (execution.recall who) (execution.observe (application setup leaks) who)) ∧
      ∃ candidate raw,
        rosterOpening? setup leaks who event (execution.observe (application setup leaks) who) =
          some (candidate, raw) ∧ candidate.1 = who ∧
        execution.application.candidates.lookup candidate = .openable raw ∧
        (bounds.withInitialValues (initialLaw setup)).AllowsHandle candidate ∧
        raw ∈ (bounds.withInitialValues (initialLaw setup)).values := by
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
        state execution related event eventRank actor granted
      cases count with
      | zero =>
          obtain ⟨source, rfl, sourceRevelations, checkpoint⟩ := related
          let index : Fin (eventCount
            (.reveal published owner name fresh selected unresolved next)) :=
              ⟨0, by simp [eventCount]⟩
          have headRank := aligned.graphSuffix.rankEq index
          have head : embedding.event index = event := by
            apply Fin.ext
            simpa only [index, Nat.add_zero] using headRank.trans eventRank.symm
          have ownerEq : owner = who := by
            have ownership := aligned.actorEq index
            change (toEventGraph setup.program).actor? (embedding.event index) = _ at ownership
            rw [head] at ownership
            change (toEventGraph setup.program).actor? event = some who at actor
            exact Option.some.inj (ownership.symm.trans actor)
          subst who
          have alignedSource : CompiledPolicySuffix setup.program wholeProfile
              (.reveal published owner name fresh selected unresolved next) profile refs
              source.revelations [] embedding refsBefore offset := by
            rw [sourceRevelations]
            exact aligned
          have law := sourceChoiceLaw_reveal setup leaks fresh selected unresolved next
            wholeProfile profile refs source embedding refsBefore offset alignedSource
            execution checkpoint.agrees checkpoint.history (by
              change execution.application.serviceGrant = some (embedding.event index)
              rw [head]
              exact granted)
          refine ⟨?_, ?_⟩
          · rw [law]
            simp only [ProtocolState.entry, ProtocolState.observe, Sum.elim_inl,
              BehavioralPolicy.protocolAction, dite_true, PMF.map_comp,
              Function.comp_def, OwnAction.disclosure, revealKernel]
            exact (PMF.map_id _).symm
          · have outputEq : (graph setup).outputLayout (embedding.event index) =
                .publication payload := embedding.layout_eq index
            have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
                ((graph setup).nodes (embedding.event index)) =
                .resolve owner payload (refs.get selected) [] :=
              reveal_head_code setup fresh selected unresolved next refs revelations
                embedding refsBefore offset aligned.graphSuffix
            have node : nodeView (graph setup) (embedding.event index) =
                .resolve owner payload (refs.get selected) [] outputEq codeEq :=
              EventGraphRuntime.nodeView_eq_resolve _ _
            obtain ⟨value, bound⟩ := checkpoint.openable selected
            obtain ⟨candidate, associated, owned, fixed, found⟩ :=
              opening_at_checkpoint setup leaks selected source.state refs execution
                checkpoint.agrees checkpoint.binding (embedding.event index)
                (by rw [head]; exact actor) outputEq codeEq node
                (by rw [head]; exact granted) value bound
            refine ⟨⟨_, found, opening_available_of_initial_tables setup leaks bounds initial
              initialSupport execution checkpoint.accepted checkpoint.candidates _ candidate
                associated owner owned ⟨payload, value⟩ fixed (embedding.event index)⟩, ?_⟩
            obtain ⟨rawCandidate, rawAssociated, rawOwned, rawFixed, rawFound⟩ :=
              roster_opening_at_checkpoint setup leaks selected source.state refs execution
                checkpoint.agrees checkpoint.binding (embedding.event index) outputEq codeEq
                node value bound
            refine ⟨rawCandidate, ⟨payload, value⟩, ?_, rawOwned, rawFixed, ?_⟩
            · simpa only [head] using rawFound
            · exact opening_data_covered setup leaks bounds initial initialSupport execution
                checkpoint.accepted checkpoint.candidates _ rawCandidate rawAssociated
                ⟨payload, value⟩ rawFixed
      | succ count =>
          cases state with
          | inl source => exact related.elim
          | inr state =>
              let index : Fin (eventCount
                (.reveal published owner name fresh selected unresolved next)) :=
                  ⟨0, by simp [eventCount]⟩
              let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
              let resultRef : EventGraph.FieldRef (graphLayout setup.program)
                (.publication payload) := ⟨.inr (embedding.event index), embedding.layout_eq index⟩
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
              have bound : count < eventCount next := by simpa [eventCount] using within
              have law := ih reveals (afterReveal profile) tailRefs (revelations.reveal selected)
                tailEmbedding tailBefore (offset + 1) tailAligned count bound state execution
                related event (by omega) actor granted
              simpa only [ProtocolState.observe, Sum.elim_inr, BehavioralPolicy.protocolAction,
                afterReveal] using law

end Vegas
