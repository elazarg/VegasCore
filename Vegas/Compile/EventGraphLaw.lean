/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphPolicyLaw
import Vegas.Compile.EventGraphReadout
import Vegas.Compile.EventGraphStep
import Vegas.EventGraph.CanonicalStep

/-! # Exact source-order law for event-graph compilation

The proof runs the ordinary event-graph executor with the canonical public
scheduler.  Its induction invariant relates one residual source program to the
corresponding suffix of the single graph compiled from the whole program.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

omit [DecidableEq Player] in
private theorem canonical_ready_least
    {graph : Vegas.EventGraph Player L} {config : graph.Config}
    {offset : Nat} (ordered : config.cut.IsPrefix offset)
    (event : graph.EventId) (rank : event.val = offset) :
    config.cut.Ready event ∧
      ∀ other, other ∉ config.cut.completed → event.val ≤ other.val := by
  have active : offset < graph.order.eventCount := rank ▸ event.isLt
  have eventEq : event = ⟨offset, active⟩ := Fin.ext rank
  subst event
  refine ⟨ordered.ready active, ?_⟩
  intro other unfinished
  rw [ordered.2] at unfinished
  omega

omit [DecidableEq Player] in
private theorem EventCode.actor_cast {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {left right : Vegas.EventGraph.EventField Player L}
    (same : left = right) (code : Vegas.EventGraph.EventCode layout left) :
    Vegas.EventGraph.EventCode.actor
        (cast (congrArg (Vegas.EventGraph.EventCode layout) same) code) =
      Vegas.EventGraph.EventCode.actor code := by
  cases same
  rfl

omit [DecidableEq Player] in
private theorem EventCode.actionOfActorNone_eq_sample
    {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {output : Vegas.EventGraph.EventField Player L}
    (code : Vegas.EventGraph.EventCode layout output) (payload : L.Ty)
    (law : Vegas.EventGraph.PublicDist layout payload)
    (outputEq : output = .publicData payload)
    (codeEq : cast (congrArg (Vegas.EventGraph.EventCode layout) outputEq) code =
      .sample payload law)
    (ownerless : code.actor = none) :
    Vegas.EventGraph.EventCode.actionOfActorNone code ownerless =
      cast (congrArg Vegas.EventGraph.EventField.Action outputEq.symm) PUnit.unit := by
  cases outputEq
  cases codeEq
  rfl

private theorem cast_finDist_map {A B X : Type} (same : A = B)
    (law : FinDist X) (f : X → A) :
    cast (congrArg FinDist same) (law.map f) =
      law.map (fun value => cast same (f value)) := by
  cases same
  rfl

private theorem cast_finDist_eq_map {A B : Type} (same : A = B)
    (law : FinDist A) :
    cast (congrArg FinDist same) law =
      law.map (fun value => cast same value) := by
  cases same
  exact (FinDist.map_id law).symm

private theorem cast_finDist_inverse {A B : Type} (same : A = B)
    (law : FinDist A) :
    cast (congrArg FinDist same.symm)
        (cast (congrArg FinDist same) law) = law := by
  cases same
  rfl

/-- Exact execution law at every compiled suffix.  The `Option` result is the
actual partial decoder; the theorem proves it is `some` on the entire source
law rather than choosing a default for malformed stores. -/
theorem runWith_option_law
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (wholeUnique : (wholeΓ.map Prod.fst).Nodup)
    (wholeProfile : BehavioralProfile whole) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames)
      (unique : (Γ.map Prod.fst).Nodup)
      (profile : BehavioralProfile program)
      (refs : ContextRefs (graphLayout whole) Γ)
      (publications : PublicationRefs (graphLayout whole) Γ)
      (registry : Registry Γ)
      (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
      (refsBefore : ContextRefsBefore refs embedding)
      (publicationsBefore : PublicationsBeforeAll publications embedding)
      (offset : Nat),
      CompiledPolicySuffix whole wholeUnique wholeProfile program unique profile
        refs publications registry embedding refsBefore publicationsBefore offset →
      ∀ (config : (toEventGraph whole wholeUnique).Config),
      config.cut.IsPrefix offset →
      ∀ (state : State L Γ), refs.Agrees state config.store →
      publications.Agree state config.store →
      ∀ (history : History Player L),
      decodeHistory whole wholeUnique config.history = history →
      ((toEventGraph whole wholeUnique).runPlan
          ((toEventGraph whole wholeUnique).policyPlan
            (compileEventProfile whole wholeUnique wholeProfile)
            (toEventGraph whole wholeUnique).canonicalScheduler)
          (eventCount program) config).map
        (fun final => decodeState?
          (terminalRefsWith program refs embedding.ref)
          (terminalPublicationsWith program unique publications embedding.ref)
          final.store) =
      (runWith program profile state registry history).map some := by
  intro Γ openNames program
  induction program with
  | ret payoffs =>
      intro unique profile refs publications registry embedding refsBefore
        publicationsBefore offset aligned config ordered state refsAgree
        publicationsAgree history historyAgree
      simp only [eventCount, Vegas.EventGraph.runPlan, FinDist.map_pure,
        terminalRefsWith, terminalPublicationsWith, runWith]
      rw [decodeState?_eq_some refs publications state config.store refsAgree
        publicationsAgree]
  | sample name fresh law next ih =>
      intro unique profile refs publications registry embedding refsBefore
        publicationsBefore offset aligned config ordered state refsAgree
        publicationsAgree history historyAgree
      let headIndex : Fin (eventCount (.sample name fresh law next)) :=
        ⟨0, by simp [eventCount]⟩
      let event := embedding.event headIndex
      have rank : event.val = offset := by
        simpa [event, headIndex] using aligned.graphSuffix.rankEq headIndex
      obtain ⟨ready, least⟩ := canonical_ready_least ordered event rank
      have outputEq : (toEventGraph whole wholeUnique).outputLayout event =
          outputLayout (.sample name fresh law next) headIndex := by
        simpa [event, toEventGraph] using embedding.layout_eq headIndex
      have codeEq : cast
          (congrArg (Vegas.EventGraph.EventCode (graphLayout whole)) outputEq)
          ((toEventGraph whole wholeUnique).nodes event) =
          .sample _ (compilePublicDist refs law) := by
        simpa [event, headIndex, compileRankedNodes] using
          aligned.graphSuffix.nodeEq headIndex
      have ownerless : (toEventGraph whole wholeUnique).actor? event = none := by
        simpa [event, headIndex, eventOwner?] using aligned.actorEq headIndex
      have suppliedAction :
          Vegas.EventGraph.EventCode.actionOfActorNone
              ((toEventGraph whole wholeUnique).nodes event) ownerless =
            cast (congrArg Vegas.EventGraph.EventField.Action outputEq.symm)
              PUnit.unit :=
        EventCode.actionOfActorNone_eq_sample
          ((toEventGraph whole wholeUnique).nodes event) _ _ outputEq codeEq ownerless
      rw [show eventCount (.sample name fresh law next) = eventCount next + 1 by
        simp [eventCount]]
      rw [Vegas.EventGraph.runPlan_canonical_ownerless
        (compileEventProfile whole wholeUnique wholeProfile) (eventCount next)
        config event ready least ownerless, suppliedAction]
      rw [sample_step config event ready outputEq refs law codeEq state refsAgree]
      simp only [FinDist.bind_map, FinDist.map_bind, runWith]
      apply FinDist.bind_congr
      intro value valueMem
      let action := cast (congrArg Vegas.EventGraph.EventField.Action outputEq.symm)
        PUnit.unit
      let stored := cast (congrArg Vegas.EventGraph.EventField.Value outputEq.symm) value
      let nextConfig := config.complete event ready action stored
      have oldRefs : refs.Agrees state nextConfig.store := by
        apply ContextRefs.Agrees.complete ready action stored refs state refsAgree
        exact fun source => refsBefore source headIndex
      have oldPublications : publications.Agree state nextConfig.store := by
        apply PublicationRefs.Agree.complete ready action stored publications state
          publicationsAgree
        exact fun source field found =>
          publicationsBefore headIndex source field found
      have storedResult : (embedding.ref headIndex).get? nextConfig.store = some value := by
        exact embedding.ref_get?_complete whole wholeUnique config headIndex ready action
          outputEq value
      obtain ⟨nextRefs, nextPublications⟩ := sample_agrees refs publications state
        nextConfig.store oldRefs oldPublications (embedding.ref headIndex) value storedResult
      have nextPrefix : nextConfig.cut.IsPrefix (offset + 1) := by
        exact ordered.complete_at event ready rank
      have nextHistory :
          decodeHistory whole wholeUnique nextConfig.history = history := by
        have chance : decodeEventAction whole event action = none := by
          have embedded := aligned.actionEq headIndex action
          simpa [event, headIndex, action, outputEq, decodeEventAction] using embedded
        have supported : nextConfig ∈ (config.step event ready action).support := by
          rw [sample_step config event ready outputEq refs law codeEq state refsAgree,
            FinDist.support_map]
          exact ⟨value, valueMem, rfl⟩
        exact (decodeHistory_step_of_none whole wholeUnique config nextConfig event ready
          action chance supported).trans historyAgree
      have tailAligned := aligned.sampleTail (whole := whole)
        (wholeUnique := wholeUnique) (wholeProfile := wholeProfile)
        (_openNames := ∅) fresh law next unique profile refs publications registry embedding
        refsBefore publicationsBefore offset
      exact ih (by simp [fresh, unique]) (afterSample profile)
        (refs.cons (embedding.ref headIndex)) (weakenPublications publications)
        registry.weaken
        (embedding.tail next (by simp [eventCount]) (fun _ => rfl))
        (by
          intro readName cell source remaining
          cases source with
          | here =>
              change (embedding.event headIndex).val <
                (embedding.event (Fin.succ remaining)).val
              apply embedding.strictMono
              exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
          | there source => exact refsBefore source (Fin.succ remaining))
        (by
          intro remaining readOwner readPayload readName source field found
          cases source with
          | there source =>
              change FieldBefore (embedding.event (Fin.succ remaining)) field
              exact publicationsBefore (Fin.succ remaining) source field found)
        (offset + 1) tailAligned nextConfig nextPrefix
        (Env.cons value state) nextRefs nextPublications history nextHistory
  | commit name owner fresh guard next ih =>
      intro unique profile refs publications registry embedding refsBefore
        publicationsBefore offset aligned config ordered state refsAgree
        publicationsAgree history historyAgree
      let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
        ⟨0, by simp [eventCount]⟩
      let event := embedding.event headIndex
      have rank : event.val = offset := by
        simpa [event, headIndex] using aligned.graphSuffix.rankEq headIndex
      obtain ⟨ready, least⟩ := canonical_ready_least ordered event rank
      have outputEq : (toEventGraph whole wholeUnique).outputLayout event =
          outputLayout (.commit name owner fresh guard next) headIndex := by
        simpa [event, toEventGraph] using embedding.layout_eq headIndex
      have codeEq : cast
          (congrArg (Vegas.EventGraph.EventCode (graphLayout whole)) outputEq)
          ((toEventGraph whole wholeUnique).nodes event) =
          .bind owner _ := by
        simpa [event, headIndex, compileRankedNodes] using
          aligned.graphSuffix.nodeEq headIndex
      have actor : (toEventGraph whole wholeUnique).actor? event = some owner := by
        simpa [event, headIndex, eventOwner?] using aligned.actorEq headIndex
      have decodedObservation := decodeObservation?_playerStore_eq_some
        (graph := toEventGraph whole wholeUnique) refs publications owner state config.store
        refsAgree publicationsAgree
      have policyLaw := aligned.policyEq owner headIndex actor
        ((toEventGraph whole wholeUnique).playerObserve owner config)
      rw [decodeCompletions_playerObserve whole wholeUnique config owner, historyAgree] at policyLaw
      change _ = compilePolicyTable (.commit name owner fresh guard next) unique refs
        publications embedding.ref owner (profile owner)
        ⟨0, by simp [eventCount]⟩
        ((toEventGraph whole wholeUnique).playerStore owner config.store)
        (history owner) at policyLaw
      rw [compilePolicyTable_commit_of_decode unique refs publications embedding.ref
          (profile owner) rfl _ _ (sourceObserve owner state) decodedObservation] at policyLaw
      change cast _ _ =
        (commitKernel profile (sourceObserve owner state, history owner)).map
          (BoundValue.resultEquiv _) at policyLaw
      have policyLaw' :
          (compileEventProfile whole wholeUnique wholeProfile) owner event actor
              ((toEventGraph whole wholeUnique).playerObserve owner config) =
            (commitKernel profile (sourceObserve owner state, history owner)).map
              (fun binding => cast
                (congrArg Vegas.EventGraph.EventField.Action outputEq.symm)
                (BoundValue.resultEquiv _ binding)) := by
        have transported := congrArg
          (fun law => cast
            (congrArg FinDist
              (congrArg Vegas.EventGraph.EventField.Action outputEq.symm)) law)
          policyLaw
        rw [cast_finDist_map] at transported
        simpa [event, headIndex, commitKernel] using transported
      rw [show eventCount (.commit name owner fresh guard next) =
          eventCount next + 1 by simp [eventCount]]
      rw [Vegas.EventGraph.runPlan_canonical_actor
        (compileEventProfile whole wholeUnique wholeProfile) (eventCount next)
        config event ready least owner actor, policyLaw']
      simp only [FinDist.bind_map, FinDist.map_bind, runWith]
      apply FinDist.bind_congr
      intro binding bindingMem
      let choice := BoundValue.resultEquiv _ binding
      let action := cast
        (congrArg Vegas.EventGraph.EventField.Action outputEq.symm) choice
      rw [commit_step config event ready outputEq codeEq binding]
      simp only [FinDist.pure_bind]
      let stored := cast
        (congrArg Vegas.EventGraph.EventField.Value outputEq.symm) choice
      let nextConfig := config.complete event ready action stored
      have oldRefs : refs.Agrees state nextConfig.store := by
        apply ContextRefs.Agrees.complete ready action stored refs state refsAgree
        exact fun source => refsBefore source headIndex
      have oldPublications : publications.Agree state nextConfig.store := by
        apply PublicationRefs.Agree.complete ready action stored publications state
          publicationsAgree
        exact fun source field found =>
          publicationsBefore headIndex source field found
      have storedResult : (embedding.ref headIndex).get? nextConfig.store =
          some choice := by
        exact embedding.ref_get?_complete whole wholeUnique config headIndex ready action
          outputEq choice
      obtain ⟨nextRefs, nextPublications⟩ := commit_agrees refs publications state
        nextConfig.store oldRefs oldPublications (embedding.ref headIndex) binding storedResult
      have nextPrefix : nextConfig.cut.IsPrefix (offset + 1) := by
        exact ordered.complete_at event ready rank
      let sourceAction := OwnAction.commit owner name _ binding
      have decodedAction : decodeEventAction whole event action = some sourceAction := by
        have embedded := aligned.actionEq headIndex action
        simpa [event, headIndex, action, choice, sourceAction, outputEq,
          decodeEventAction] using embedded
      have supported : nextConfig ∈ (config.step event ready action).support := by
        rw [commit_step config event ready outputEq codeEq binding]
        simp [nextConfig, action, stored, choice]
      have nextHistory : decodeHistory whole wholeUnique nextConfig.history =
          Function.update history owner
            (history owner ++ [OwnAction.commit owner name _ binding]) := by
        rw [decodeHistory_step_of_some whole wholeUnique config nextConfig event ready
          action sourceAction decodedAction supported]
        simp [sourceAction, sourceActionOwner, historyAgree]
      have tailAligned := aligned.commitTail whole wholeUnique wholeProfile fresh guard next
        unique profile refs publications registry embedding refsBefore publicationsBefore offset
      let obligation : Obligation _ :=
        { owner := owner, subject := name, payload := _, source := .here,
          guard := guard.weaken }
      exact ih (by simp [fresh, unique]) (afterCommit profile)
        (refs.cons (embedding.ref headIndex)) (weakenPublications publications)
        (obligation :: registry.weaken)
        (embedding.tail next (by simp [eventCount]) (fun _ => rfl))
        (by
          intro readName cell source remaining
          cases source with
          | here =>
              change (embedding.event headIndex).val <
                (embedding.event (Fin.succ remaining)).val
              apply embedding.strictMono
              exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
          | there source => exact refsBefore source (Fin.succ remaining))
        (by
          intro remaining readOwner readPayload readName source field found
          cases source with
          | here => cases found
          | there source =>
              change FieldBefore (embedding.event (Fin.succ remaining)) field
              exact publicationsBefore (Fin.succ remaining) source field found)
        (offset + 1) tailAligned nextConfig nextPrefix
        (Env.cons (binding, Interaction.Publication.pending) state)
        nextRefs nextPublications
        (Function.update history owner
          (history owner ++ [OwnAction.commit owner name _ binding])) nextHistory
  | reveal published owner name fresh selected unresolved next ih =>
      intro unique profile refs publications registry embedding refsBefore
        publicationsBefore offset aligned config ordered state refsAgree
        publicationsAgree history historyAgree
      let headIndex : Fin (eventCount
          (.reveal published owner name fresh selected unresolved next)) :=
        ⟨0, by simp [eventCount]⟩
      let event := embedding.event headIndex
      have rank : event.val = offset := by
        simpa [event, headIndex] using aligned.graphSuffix.rankEq headIndex
      obtain ⟨ready, least⟩ := canonical_ready_least ordered event rank
      have outputEq : (toEventGraph whole wholeUnique).outputLayout event =
          outputLayout (.reveal published owner name fresh selected unresolved next)
            headIndex := by
        simpa [event, toEventGraph] using embedding.layout_eq headIndex
      have codeEq : cast
          (congrArg (Vegas.EventGraph.EventCode (graphLayout whole)) outputEq)
          ((toEventGraph whole wholeUnique).nodes event) =
          .resolve owner _ (refs.get selected)
            (registry.map
              (compileGuard refs (proposedOperands publications unique selected))) := by
        simpa [event, headIndex, compileRankedNodes] using
          aligned.graphSuffix.nodeEq headIndex
      have actor : (toEventGraph whole wholeUnique).actor? event = some owner := by
        simpa [event, headIndex, eventOwner?] using aligned.actorEq headIndex
      have decodedObservation := decodeObservation?_playerStore_eq_some
        (graph := toEventGraph whole wholeUnique) refs publications owner state config.store
        refsAgree publicationsAgree
      have policyLaw := aligned.policyEq owner headIndex actor
        ((toEventGraph whole wholeUnique).playerObserve owner config)
      rw [decodeCompletions_playerObserve whole wholeUnique config owner, historyAgree] at policyLaw
      change _ = compilePolicyTable
        (.reveal published owner name fresh selected unresolved next) unique refs
        publications embedding.ref owner (profile owner)
        ⟨0, by simp [eventCount]⟩
        ((toEventGraph whole wholeUnique).playerStore owner config.store)
        (history owner) at policyLaw
      rw [compilePolicyTable_reveal_of_decode unique refs publications embedding.ref
          (profile owner) rfl _ _ (sourceObserve owner state) decodedObservation] at policyLaw
      change cast _ _ =
        revealKernel profile (sourceObserve owner state, history owner) at policyLaw
      have policyLaw' :
          (compileEventProfile whole wholeUnique wholeProfile) owner event actor
              ((toEventGraph whole wholeUnique).playerObserve owner config) =
            (revealKernel profile (sourceObserve owner state, history owner)).map
              (fun disclose => cast
                (congrArg Vegas.EventGraph.EventField.Action outputEq.symm) disclose) := by
        have transported := congrArg
          (fun law => cast
            (congrArg FinDist
              (congrArg Vegas.EventGraph.EventField.Action outputEq.symm)) law)
          policyLaw
        have exactLaw :
            (compileEventProfile whole wholeUnique wholeProfile) owner
                (embedding.event headIndex) actor
                ((toEventGraph whole wholeUnique).playerObserve owner config) =
              (revealKernel profile (sourceObserve owner state, history owner)).map
                (fun disclose => cast
                  (congrArg Vegas.EventGraph.EventField.Action outputEq.symm)
                  disclose) := by
          calc
            _ = cast
                (congrArg FinDist
                  (congrArg Vegas.EventGraph.EventField.Action outputEq.symm))
                (cast
                  (congrArg FinDist
                    (congrArg Vegas.EventGraph.EventField.Action outputEq))
                  ((compileEventProfile whole wholeUnique wholeProfile) owner
                    (embedding.event headIndex) actor
                    ((toEventGraph whole wholeUnique).playerObserve owner config))) :=
              (cast_finDist_inverse
                (congrArg Vegas.EventGraph.EventField.Action outputEq) _).symm
            _ = cast
                (congrArg FinDist
                  (congrArg Vegas.EventGraph.EventField.Action outputEq.symm))
                (revealKernel profile (sourceObserve owner state, history owner)) :=
              transported
            _ = _ := cast_finDist_eq_map _ _
        simpa [event, headIndex] using exactLaw
      rw [show eventCount
          (.reveal published owner name fresh selected unresolved next) =
          eventCount next + 1 by simp [eventCount]]
      rw [Vegas.EventGraph.runPlan_canonical_actor
        (compileEventProfile whole wholeUnique wholeProfile) (eventCount next)
        config event ready least owner actor, policyLaw']
      simp only [FinDist.bind_map, FinDist.map_bind, runWith]
      apply FinDist.bind_congr
      intro disclose discloseMem
      let proposed := boundResult state selected disclose
      let acceptedResult := if registry.ok
          (updatePrivate state selected (resultPublication proposed))
        then proposed else PublicationResult.failure
      let action := cast
        (congrArg Vegas.EventGraph.EventField.Action outputEq.symm) disclose
      rw [reveal_step config event ready outputEq refs publications unique registry
        selected codeEq state refsAgree publicationsAgree disclose]
      simp only [FinDist.pure_bind]
      let stored := cast
        (congrArg Vegas.EventGraph.EventField.Value outputEq.symm) acceptedResult
      let nextConfig := config.complete event ready action stored
      have oldRefs : refs.Agrees state nextConfig.store := by
        apply ContextRefs.Agrees.complete ready action stored refs state refsAgree
        exact fun source => refsBefore source headIndex
      have oldPublications : publications.Agree state nextConfig.store := by
        apply PublicationRefs.Agree.complete ready action stored publications state
          publicationsAgree
        exact fun source field found =>
          publicationsBefore headIndex source field found
      have storedResult : (embedding.ref headIndex).get? nextConfig.store =
          some acceptedResult := by
        exact embedding.ref_get?_complete whole wholeUnique config headIndex ready action
          outputEq acceptedResult
      obtain ⟨nextRefs, nextPublications⟩ := reveal_agrees refs publications unique
        state nextConfig.store oldRefs oldPublications selected (embedding.ref headIndex)
        acceptedResult storedResult
      have nextPrefix : nextConfig.cut.IsPrefix (offset + 1) := by
        exact ordered.complete_at event ready rank
      let sourceAction : OwnAction Player L := OwnAction.reveal owner name disclose
      have decodedAction : decodeEventAction whole event action = some sourceAction := by
        have embedded := aligned.actionEq headIndex action
        simpa [event, headIndex, action, sourceAction, outputEq,
          decodeEventAction] using embedded
      have supported : nextConfig ∈ (config.step event ready action).support := by
        rw [reveal_step config event ready outputEq refs publications unique registry
          selected codeEq state refsAgree publicationsAgree disclose]
        simp [nextConfig, action, stored, acceptedResult, proposed]
      have nextHistory : decodeHistory whole wholeUnique nextConfig.history =
          Function.update history owner
            (history owner ++ [OwnAction.reveal owner name disclose]) := by
        rw [decodeHistory_step_of_some whole wholeUnique config nextConfig event ready
          action sourceAction decodedAction supported]
        simp [sourceAction, sourceActionOwner, historyAgree]
      have tailAligned := aligned.revealTail (whole := whole)
        (wholeUnique := wholeUnique) (wholeProfile := wholeProfile) fresh selected unresolved
        next unique profile refs publications registry embedding refsBefore publicationsBefore
        offset
      let resolved := updatePrivate state selected (resultPublication acceptedResult)
      exact ih (by simp [fresh, unique]) (afterReveal profile)
        (refs.cons (embedding.ref headIndex))
        (resolvePublications publications unique selected (embedding.ref headIndex))
        registry.weaken
        (embedding.tail next (by simp [eventCount]) (fun _ => rfl))
        (by
          intro readName cell source remaining
          cases source with
          | here =>
              change (embedding.event headIndex).val <
                (embedding.event (Fin.succ remaining)).val
              apply embedding.strictMono
              exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
          | there source => exact refsBefore source (Fin.succ remaining))
        (by
          intro remaining readOwner readPayload readName source field found
          cases source with
          | there source =>
              change FieldBefore (embedding.event (Fin.succ remaining)) field
              by_cases same : readName = name
              · subst readName
                have cellEq := HasVar.type_unique unique source selected
                cases cellEq
                have sameField : (embedding.ref headIndex).field = field := by
                  simpa [resolvePublications, PublicationRef.field?] using found
                subst field
                apply embedding.strictMono
                exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
              · exact publicationsBefore (Fin.succ remaining) source field (by
                  simpa [resolvePublications, same] using found))
        (offset + 1) tailAligned nextConfig nextPrefix
        (Env.cons acceptedResult resolved) nextRefs nextPublications
        (Function.update history owner
          (history owner ++ [OwnAction.reveal owner name disclose])) nextHistory

end Vegas.SourceProgram.EventLowering
