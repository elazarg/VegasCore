/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServicePrefixLaw

/-! # One ordinary response followed by the source continuation

The immediate response may be any physical alias. Only its Boolean source
choice affects the terminal source law when later play follows the compiled
continuation. Native recall is retained throughout the actual execution.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A conditional source-step law, before averaging over the first response.
The source joint action is interpreted by the existing source step; callers
apply this equation to legal source choices. -/
theorem prefix_response_option_law
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (wholeProfile : BehavioralProfile setup.program)
    (players : Player → (application setup leaks).Policy)
    (watcherPolicy : players watcher = (application setup leaks).reportFirstUnpublished)
    (ordinary : ∀ who, who ≠ watcher → ∀ past view response,
      response ∈ (players who past view).support → response ∈
        ordinaryActions setup leaks (bounds.withInitialValues (initialLaw setup)) who past view)
    (projects : ∀ who, who ≠ watcher → ∀ past view opening,
      opening? setup leaks who past view = some opening →
      opening ∈ ((bounds.withInitialValues (initialLaw setup)).menu (runtime setup) leaks).actions
        who past view →
      (players who past view).map (sourceChoice setup leaks) =
        sourceChoiceLaw setup leaks wholeProfile who view)
    (initial : State L setup.context) (initialSupport : initial ∈ setup.initialLaw.support) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames) (_reveals : program.RevealOnly)
      (profile : BehavioralProfile program)
      (refs : ContextRefs (graphLayout setup.program) Γ) (revelations : Revelations Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding) (offset : Nat),
      CompiledPolicySuffix setup.program wholeProfile program profile refs revelations []
        embedding refsBefore offset →
      ∀ (count : Nat) (inside : count < eventCount program) (state : ProtocolState program)
        (execution : (application setup leaks).Execution),
      PrefixCheckpoint setup leaks initial program refs revelations embedding.ref
        offset count state execution →
      ∀ (who : Player) (_owned : (graph setup).actor? (embedding.event ⟨count, inside⟩) = some who),
      execution.application.serviceGrant = some (embedding.event ⟨count, inside⟩) →
      ∀ (response : (application setup leaks).Action),
      response ∈ ordinaryActions setup leaks (bounds.withInitialValues (initialLaw setup))
        who (execution.recall who) (execution.observe (application setup leaks) who) →
      ∀ (joint : Player → Option (OwnAction Player L)),
      OwnAction.disclosure (joint who) = sourceChoice setup leaks response →
      ((runtime setup).runInteractionPlan leaks players
        ((runtime setup).reportNetwork leaks watcher)
        ((((List.finRange (eventCount program)).drop count).flatMap fun index =>
          block setup watcher (embedding.event index)).drop 2)
        (execution.respond (application setup leaks) who response)).map
        (fun final => decodeState? (terminalRefsWith program refs embedding.ref)
          final.application.config.store) =
        ((ProtocolState.step program state joint).bind
          (ProtocolState.continuationLaw program profile)).map some := by
  intro Γ openNames program
  induction program with
  | ret payoffs =>
      intro reveals profile refs revelations embedding refsBefore offset aligned count inside
      simp only [eventCount] at inside
      omega
  | sample name fresh law next ih => intro impossible; exact impossible.elim
  | commit name owner fresh guard next ih => intro impossible; exact impossible.elim
  | @reveal Γ openNames published owner name payload fresh selected unresolved next ih =>
      intro reveals profile refs revelations embedding refsBefore offset aligned count inside state
        execution related who owned granted response member joint chosen
      cases count with
      | zero =>
          obtain ⟨source, rfl, revelationsEq, checkpoint⟩ := related
          rw [← revelationsEq] at aligned
          let index : Fin (eventCount
            (.reveal published owner name fresh selected unresolved next)) :=
              ⟨0, by simp [eventCount]⟩
          let event := embedding.event index
          have eventRank : event.val = offset := by
            simpa [event, index] using aligned.graphSuffix.rankEq index
          have actor : (graph setup).actor? event = some owner := by
            change (toEventGraph setup.program).actor? event = some owner
            simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
          have sameOwner : who = owner := Option.some.inj (owned.symm.trans actor)
          subst who
          have outputEq : (graph setup).outputLayout event = .publication payload :=
            embedding.layout_eq index
          have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
              ((graph setup).nodes event) = .resolve owner payload (refs.get selected) [] :=
            reveal_head_code setup fresh selected unresolved next refs source.revelations
              embedding refsBefore offset aligned.graphSuffix
          have node : nodeView (graph setup) event =
              .resolve owner payload (refs.get selected) [] outputEq codeEq :=
            EventGraphRuntime.nodeView_eq_resolve _ _
          let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
          let resultRef : EventGraph.FieldRef (graphLayout setup.program) (.publication payload) :=
            ⟨.inr event, outputEq⟩
          let tailRefs := refs.cons (name := published) (cell := .publication payload) resultRef
          have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
            intro readName cell ref remaining
            cases ref with
            | here =>
                change (embedding.event index).val < (embedding.event (Fin.succ remaining)).val
                apply embedding.strictMono
                exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
            | there ref => exact refsBefore ref (Fin.succ remaining)
          have decoded (disclose : Bool) : decodeEventAction setup.program event
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
              some (.reveal owner name disclose) := by
            have embedded := aligned.actionEq index
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
            simpa [event, index, outputEq, decodeEventAction] using embedded
          obtain ⟨after, afterLaw, afterCheckpoint, _afterRecall⟩ :=
            checkpoint.reveal_response (bounds.withInitialValues (initialLaw setup)) players
              watcher watcherPolicy published selected event eventRank actor outputEq codeEq node
              (fun ref => refsBefore ref index) decoded granted response member
          have nextAligned : CompiledPolicySuffix setup.program wholeProfile next
              (afterReveal profile) tailRefs
              (revealSuccessor published selected source
                (sourceChoice setup leaks response)).revelations
              [] tailEmbedding tailBefore (offset + 1) := by
            simpa only [Registry.weaken, List.map_nil, revealSuccessor, tailRefs, resultRef,
              tailEmbedding, OutputEmbedding.ref] using
              aligned.revealTail (whole := setup.program) (wholeProfile := wholeProfile)
                fresh selected unresolved next profile refs source.revelations [] embedding
                refsBefore offset
          have tailLaw := run_source_suffix_option_law setup leaks bounds watcher observer
            wholeProfile players watcherPolicy ordinary projects initial initialSupport next reveals
            (afterReveal profile)
            (revealSuccessor published selected source (sourceChoice setup leaks response))
            tailRefs tailEmbedding tailBefore (offset + 1) nextAligned after afterCheckpoint
          let suffix : List (ServiceInstruction (graph setup)) :=
            [.includeLatest event owner, .player watcher, .wire] ++
              List.replicate (event.val + 1) .tick ++ [.expire event]
          let remaining := (List.finRange (eventCount next)).flatMap fun index =>
            block setup watcher (tailEmbedding.event index)
          have planEq : (((List.finRange (eventCount
              (.reveal published owner name fresh selected unresolved next))).drop 0).flatMap
                fun index => block setup watcher (embedding.event index)).drop 2 =
              suffix ++ remaining := by
            simp only [List.drop_zero, eventCount, List.finRange_succ, List.flatMap_cons,
              List.flatMap_map]
            change (block setup watcher event ++ remaining).drop 2 = _
            rw [block_of_owner setup watcher owner event actor]
            simp only [suffix, List.append_assoc, List.cons_append, List.nil_append,
              List.drop_succ_cons, List.drop_zero]
          rw [planEq, runInteractionPlan_append, afterLaw, PMF.pure_bind]
          change _ = ((PMF.pure (Sum.inr (α := Config Player L Γ)
            (ProtocolState.entry next (revealSuccessor published selected source
              (OwnAction.disclosure (joint owner)))))).bind
              (ProtocolState.continuationLaw _ profile)).map some
          rw [PMF.pure_bind]
          change _ = (ProtocolState.continuationLaw next (afterReveal profile)
            (ProtocolState.entry next (revealSuccessor published selected source
              (OwnAction.disclosure (joint owner))))).map some
          rw [chosen, ProtocolState.continuationLaw_entry]
          convert tailLaw using 1
          rfl
      | succ count =>
          cases state with
          | inl source => exact related.elim
          | inr state =>
              let index : Fin (eventCount
                (.reveal published owner name fresh selected unresolved next)) :=
                  ⟨0, by simp [eventCount]⟩
              let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
              let tailRefs := refs.cons (name := published) (cell := .publication payload)
                (embedding.ref index)
              have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
                intro readName cell ref remaining
                cases ref with
                | here =>
                    change (embedding.event index).val <
                      (embedding.event (Fin.succ remaining)).val
                    apply embedding.strictMono
                    exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
                | there ref => exact refsBefore ref (Fin.succ remaining)
              have tailAligned : CompiledPolicySuffix setup.program wholeProfile next
                  (afterReveal profile) tailRefs (revelations.reveal selected)
                  [] tailEmbedding tailBefore (offset + 1) := by
                simpa only [Registry.weaken, List.map_nil, tailRefs, tailEmbedding] using
                  aligned.revealTail (whole := setup.program) (wholeProfile := wholeProfile)
                    fresh selected unresolved next profile refs revelations [] embedding
                    refsBefore offset
              have within : count < eventCount next := by simpa [eventCount] using inside
              have tailLaw := ih reveals (afterReveal profile) tailRefs
                (revelations.reveal selected) tailEmbedding tailBefore (offset + 1) tailAligned
                count within state execution related who owned granted response member joint chosen
              simp only [eventCount, List.finRange_succ, List.drop_succ_cons, ← List.map_drop,
                List.flatMap_map, terminalRefsWith, ProtocolState.step, Sum.elim_inr,
                PMF.bind_map, ProtocolState.continuationLaw]
              convert tailLaw using 1 <;> rfl

end Vegas
