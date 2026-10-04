/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingBoundary
import Vegas.Game.SourceServiceSampleBoundary
import Vegas.Game.SourceServiceResolutionBoundary
import Vegas.Game.SourceServicePrefix
import Vegas.Game.SourceStateKernel
import Vegas.Source.DisclosureNormalization
import Vegas.Source.DisclosureSupport

/-! # Typed support of every retained full-source prefix

The actual service is folded through the existing source constructors. Policy
membership alone supplies the operational successor at each phase: private
bindings may occur at any permitted opportunity, public chance keeps its real
support, and guarded resolution records its effective disclosure. The decoded
source position and the dynamic operational boundary are derived together.
The residual-state inclusion also commutes with the existing source transition
and every later decoder offset.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Every actual retained service prefix has an existing typed source state
and a complete dynamic boundary. The arbitrary syntax profile supplies only
static compiler alignment; the physical policy need not be its compilation.
The residual inclusion is built from the source protocol's own sum constructors. -/
theorem run_sourceService_prefix_support
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    (wholeProfile : BehavioralProfile setup.program) (initial : State L setup.context) :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames) (profile : BehavioralProfile program)
      (source : Config Player L Γ) (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context)
        (outputLayout setup.program) program)
      (refsBefore : ContextRefsBefore refs embedding) (offset : Nat),
      CompiledPolicySuffix setup.program wholeProfile program profile refs source.revelations
        source.registry embedding refsBefore offset → count ≤ eventCount program →
      ∀ execution, ServiceBoundary setup leaks rosters initial source refs offset execution →
      ∀ final, final ∈ ((runtime setup).runInteractionPlan leaks players network
        (((List.finRange (eventCount program)).take count).flatMap fun index =>
          rosterBlock setup rosters (embedding.event index)) execution).support →
      ∃ state, SourcePrefixCheckpoint setup program refs source.registry source.revelations
        embedding.ref offset count state final.application.config ∧
        ∃ (Δ : SourceCtx Player L) (names : Finset VarId)
          (remaining : SourceProgram Player L Δ names)
          (remainingProfile : BehavioralProfile remaining)
          (current : Config Player L Δ) (currentRefs : ContextRefs (graph setup).layout Δ)
          (currentEmbedding : OutputEmbedding (inputLayout setup.context)
            (outputLayout setup.program) remaining)
          (currentBefore : ContextRefsBefore currentRefs currentEmbedding),
          CompiledPolicySuffix setup.program wholeProfile remaining remainingProfile currentRefs
            current.revelations current.registry currentEmbedding currentBefore (offset + count) ∧
          ((∀ who, (profile who).Admitted program (CommitmentInterface.values program)) →
            ∀ who, (remainingProfile who).Admitted remaining
              (CommitmentInterface.values remaining)) ∧
          ∃ lift : ProtocolState remaining → ProtocolState program,
            state = lift (ProtocolState.entry remaining current) ∧
            ((∀ tailState, ProtocolState.behavioralStateStep program profile (lift tailState) =
              (ProtocolState.behavioralStateStep remaining remainingProfile tailState).map lift) ∧
              (∀ tailState joint, ProtocolState.step program (lift tailState) joint =
                (ProtocolState.step remaining tailState joint).map lift) ∧
              Function.Injective lift) ∧
            (∀ more store history,
              decodeSourcePrefix? program refs source.registry source.revelations embedding.ref
                (count + more) store history =
              (decodeSourcePrefix? remaining currentRefs current.registry current.revelations
                currentEmbedding.ref more store history).map lift) ∧
            ((∀ who, (profile who).EffectiveDisclosures program source.registry
              source.revelations) → ∀ who, (remainingProfile who).EffectiveDisclosures remaining
                current.registry current.revelations) ∧
            ((∀ who, (profile who).SupportsEffectiveChoices program
              (CommitmentInterface.values program) source.registry source.revelations) →
                ∀ who, (remainingProfile who).SupportsEffectiveChoices remaining
                  (CommitmentInterface.values remaining) current.registry current.revelations) ∧
            ServiceBoundary setup leaks rosters initial current currentRefs
              (offset + count) final := by
  intro count
  induction count with
  | zero =>
      intro Γ openNames program profile source refs embedding refsBefore offset aligned bound
        execution boundary final reached
      simp only [List.take_zero, List.flatMap_nil, runInteractionPlan] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      refine ⟨ProtocolState.entry program source, ?_, Γ, openNames, program, profile,
        source, refs, embedding, refsBefore, ?_, ?_, id, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · cases program <;> exact ⟨source, rfl, rfl, rfl, boundary.toSourceCheckpoint⟩
      · simpa only [Nat.add_zero] using aligned
      · exact fun admitted => admitted
      · refine ⟨fun state => ?_, fun state joint => ?_, Function.injective_id⟩ <;>
          simp only [id_eq, PMF.map_id]
      · intro more store history
        simp only [Nat.zero_add, Option.map_id, id_eq]
      · exact fun effective => effective
      · exact fun supported => supported
      · simpa only [Nat.add_zero] using boundary
  | succ count ih =>
      intro Γ openNames program profile source refs embedding refsBefore offset aligned bound
        execution boundary final reached
      cases program with
      | ret payoffs => simp only [eventCount] at bound; omega
      | @sample Γ openNames name payload fresh distribution next =>
          let index : Fin (eventCount (.sample name fresh distribution next)) :=
            ⟨0, by simp [eventCount]⟩
          let event := embedding.event index
          have atRank : event.val = offset := by
            simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
          have outputEq : (graph setup).outputLayout event = .publicData payload := by
            change outputLayout setup.program event = _
            simpa [event, index, outputLayout, eventCount] using embedding.layout_eq index
          have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
              ((graph setup).nodes event) =
                .sample payload (compilePublicDist refs distribution) := by
            change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
              ((toEventGraph setup.program).nodes event) = _
            simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
          have node : nodeView (graph setup) event =
              .sample payload (compilePublicDist refs distribution) outputEq codeEq :=
            EventGraphRuntime.nodeView_eq_sample _ _
          have chance : (graph setup).actor? event = none := by
            change (toEventGraph setup.program).actor? event = none
            simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
          have decoded : decodeEventAction setup.program event
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit) = none := by
            have lookup := aligned.actionEq index
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
            simpa [event, index, outputEq, decodeEventAction] using lookup
          let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
          let tailRefs : ContextRefs (graphLayout setup.program)
              ((name, .publicData payload) :: Γ) := refs.cons ⟨.inr event, outputEq⟩
          have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
            intro readName cell ref remaining
            cases ref with
            | here =>
                change (embedding.event index).val < (embedding.event remaining.succ).val
                exact embedding.strictMono (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _))
            | there ref => exact refsBefore ref remaining.succ
          have planEq : (((List.finRange (eventCount (.sample name fresh distribution next))).take
              (count + 1)).flatMap fun entry =>
                rosterBlock setup rosters (embedding.event entry)) =
              rosterBlock setup rosters event ++
                (((List.finRange (eventCount next)).take count).flatMap fun entry =>
                  rosterBlock setup rosters (tailEmbedding.event entry)) := by
            simp only [eventCount, List.finRange_succ, List.take_succ_cons, ← List.map_take,
              List.flatMap_cons, List.flatMap_map]
            rfl
          rw [planEq, (runtime setup).runInteractionPlan_append] at reached
          obtain ⟨middle, first, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          obtain ⟨value, _, nextBoundary⟩ := boundary.sample_block bounds players lawful network
            event atRank name payload distribution outputEq codeEq node chance
              (fun ref => refsBefore ref index) decoded middle first
          have tailAligned : CompiledPolicySuffix setup.program wholeProfile next
              (afterSample profile) tailRefs (sampleSuccessor name source value).revelations
              (sampleSuccessor name source value).registry
              tailEmbedding tailBefore (offset + 1) := by
            simpa only [sampleSuccessor, tailRefs, tailEmbedding, OutputEmbedding.ref] using
              aligned.sampleTail setup.program wholeProfile (_openNames := openNames)
                fresh distribution next profile refs
                source.revelations source.registry embedding refsBefore offset
          obtain ⟨state, related, Δ, names, remaining, remainingProfile, current, currentRefs,
            currentEmbedding, currentBefore, currentAligned, currentAdmitted, lift, stateEq,
            stepEq, decodeEq, currentEffective, currentSupport, finalBoundary⟩ :=
            ih next (afterSample profile) (sampleSuccessor name source value) tailRefs
              tailEmbedding tailBefore (offset + 1) tailAligned
              (by simpa only [eventCount, Nat.succ_le_succ_iff] using bound)
              middle nextBoundary final rest
          refine ⟨Sum.inr state, related, Δ, names, remaining, remainingProfile, current,
            currentRefs, currentEmbedding, currentBefore, ?_, ?_, Sum.inr ∘ lift,
              congrArg Sum.inr stateEq, ?_, ?_, ?_, ?_, ?_⟩
          · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using currentAligned
          · intro admitted
            exact currentAdmitted (fun who => admitted who)
          · refine ⟨fun tailState => ?_, fun tailState joint => ?_,
              Sum.inr_injective.comp stepEq.2.2⟩
            · rw [Function.comp_apply, ProtocolState.behavioralStateStep_sample_tail, stepEq.1,
                PMF.map_comp]
            · change (ProtocolState.step _ (lift tailState) joint).map Sum.inr = _
              rw [stepEq.2.1, PMF.map_comp]
          · intro more store history
            rw [show count + 1 + more = (count + more) + 1 by omega,
              decodeSourcePrefix?_sample]
            change (decodeSourcePrefix? next tailRefs _ _ tailEmbedding.ref
              (count + more) store history).map Sum.inr = _
            simpa only [sampleSuccessor, Option.map_map] using
              congrArg (Option.map Sum.inr) (decodeEq more store history)
          · intro effective
            exact currentEffective (fun who => effective who)
          · intro supported
            exact currentSupport (fun who => supported who)
          · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalBoundary
      | @commit Γ openNames name owner payload fresh guard next =>
          let index : Fin (eventCount (.commit name owner fresh guard next)) :=
            ⟨0, by simp [eventCount]⟩
          let event := embedding.event index
          have atRank : event.val = offset := by
            simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
          have outputEq : (graph setup).outputLayout event = .binding owner payload := by
            change outputLayout setup.program event = _
            simpa [event, index, outputLayout, eventCount] using embedding.layout_eq index
          have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
              ((graph setup).nodes event) = .bind owner payload := by
            change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
              ((toEventGraph setup.program).nodes event) = _
            simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
          have node : nodeView (graph setup) event = .bind owner payload outputEq codeEq :=
            EventGraphRuntime.nodeView_eq_bind _ _
          have owned : (graph setup).actor? event = some owner := by
            change (toEventGraph setup.program).actor? event = some owner
            simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
          have decoded (value : L.Val payload) : decodeEventAction setup.program event
              (cast (congrArg EventGraph.EventField.Action outputEq.symm)
                (PublicationResult.success value)) =
                some (.commit owner name payload (.success value)) := by
            have lookup := aligned.actionEq index
              (cast (congrArg EventGraph.EventField.Action outputEq.symm)
                (PublicationResult.success value))
            simpa [event, index, outputEq, decodeEventAction] using lookup
          let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
          let tailRefs : ContextRefs (graphLayout setup.program)
              ((name, .commitment owner payload) :: Γ) := refs.cons ⟨.inr event, outputEq⟩
          have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
            intro readName cell ref remaining
            cases ref with
            | here =>
                change (embedding.event index).val < (embedding.event remaining.succ).val
                exact embedding.strictMono (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _))
            | there ref => exact refsBefore ref remaining.succ
          have planEq : (((List.finRange (eventCount (.commit name owner fresh guard next))).take
              (count + 1)).flatMap fun entry =>
                rosterBlock setup rosters (embedding.event entry)) =
              rosterBlock setup rosters event ++
                (((List.finRange (eventCount next)).take count).flatMap fun entry =>
                  rosterBlock setup rosters (tailEmbedding.event entry)) := by
            simp only [eventCount, List.finRange_succ, List.take_succ_cons, ← List.map_take,
              List.flatMap_cons, List.flatMap_map]
            rfl
          rw [planEq, (runtime setup).runInteractionPlan_append] at reached
          obtain ⟨middle, first, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          obtain ⟨value, _, nextBoundary⟩ := boundary.binding_block bounds values players lawful
            network event atRank name owner payload guard outputEq codeEq node owned
              (fun ref => refsBefore ref index) decoded
              (opportunities event owner (binding_actor setup event owner payload outputEq))
              (boundary.binding_capacity bounds capacity event atRank owner) middle first
          have tailAligned : CompiledPolicySuffix setup.program wholeProfile next
              (afterCommit profile) tailRefs
              (commitSuccessor name guard source (.success value)).revelations
              (commitSuccessor name guard source (.success value)).registry
              tailEmbedding tailBefore (offset + 1) := by
            simpa only [commitSuccessor, tailRefs, tailEmbedding, OutputEmbedding.ref] using
              aligned.commitTail setup.program wholeProfile fresh guard next profile refs
                source.revelations source.registry embedding refsBefore offset
          obtain ⟨state, related, Δ, names, remaining, remainingProfile, current, currentRefs,
            currentEmbedding, currentBefore, currentAligned, currentAdmitted, lift, stateEq,
            stepEq, decodeEq, currentEffective, currentSupport, finalBoundary⟩ :=
            ih next (afterCommit profile) (commitSuccessor name guard source (.success value))
              tailRefs tailEmbedding tailBefore (offset + 1) tailAligned
              (by simpa only [eventCount, Nat.succ_le_succ_iff] using bound)
              middle nextBoundary final rest
          refine ⟨Sum.inr state, related, Δ, names, remaining, remainingProfile, current,
            currentRefs, currentEmbedding, currentBefore, ?_, ?_, Sum.inr ∘ lift,
              congrArg Sum.inr stateEq, ?_, ?_, ?_, ?_, ?_⟩
          · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using currentAligned
          · intro admitted
            exact currentAdmitted (fun who => (admitted who).2)
          · refine ⟨fun tailState => ?_, fun tailState joint => ?_,
              Sum.inr_injective.comp stepEq.2.2⟩
            · rw [Function.comp_apply, ProtocolState.behavioralStateStep_commit_tail, stepEq.1,
                PMF.map_comp]
            · change (ProtocolState.step _ (lift tailState) joint).map Sum.inr = _
              rw [stepEq.2.1, PMF.map_comp]
          · intro more store history
            rw [show count + 1 + more = (count + more) + 1 by omega,
              decodeSourcePrefix?_commit]
            change (decodeSourcePrefix? next tailRefs _ _ tailEmbedding.ref
              (count + more) store history).map Sum.inr = _
            simpa only [commitSuccessor, Option.map_map] using
              congrArg (Option.map Sum.inr) (decodeEq more store history)
          · intro effective
            exact currentEffective (fun who => effective who)
          · intro supported
            exact currentSupport (fun who => (supported who).2)
          · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalBoundary
      | @reveal Γ openNames published owner name payload fresh selected unresolved next =>
          let index : Fin (eventCount
              (.reveal published owner name fresh selected unresolved next)) :=
            ⟨0, by simp [eventCount]⟩
          let event := embedding.event index
          have atRank : event.val = offset := by
            simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
          have outputEq : (graph setup).outputLayout event = .publication payload := by
            change outputLayout setup.program event = _
            simpa [event, index, outputLayout, eventCount] using embedding.layout_eq index
          let checks := compileChecks (published := published) refs
            source.registry source.revelations selected
          have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
              ((graph setup).nodes event) = .resolve owner payload (refs.get selected) checks := by
            change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
              ((toEventGraph setup.program).nodes event) = _
            simpa [event, index, compileRankedNodes, checks] using aligned.graphSuffix.nodeEq index
          have node : nodeView (graph setup) event =
              .resolve owner payload (refs.get selected) checks outputEq codeEq :=
            EventGraphRuntime.nodeView_eq_resolve _ _
          have owned : (graph setup).actor? event = some owner := by
            change (toEventGraph setup.program).actor? event = some owner
            simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
          have decoded (disclose : Bool) : decodeEventAction setup.program event
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
                some (.reveal owner name disclose) := by
            have lookup := aligned.actionEq index
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
            simpa [event, index, outputEq, decodeEventAction] using lookup
          let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
          let tailRefs : ContextRefs (graphLayout setup.program)
              ((published, .publication payload) :: Γ) := refs.cons ⟨.inr event, outputEq⟩
          have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
            intro readName cell ref remaining
            cases ref with
            | here =>
                change (embedding.event index).val < (embedding.event remaining.succ).val
                exact embedding.strictMono (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _))
            | there ref => exact refsBefore ref remaining.succ
          have planEq : (((List.finRange (eventCount
              (.reveal published owner name fresh selected unresolved next))).take
              (count + 1)).flatMap fun entry =>
                rosterBlock setup rosters (embedding.event entry)) =
              rosterBlock setup rosters event ++
                (((List.finRange (eventCount next)).take count).flatMap fun entry =>
                  rosterBlock setup rosters (tailEmbedding.event entry)) := by
            simp only [eventCount, List.finRange_succ, List.take_succ_cons, ← List.map_take,
              List.flatMap_cons, List.flatMap_map]
            rfl
          rw [planEq, (runtime setup).runInteractionPlan_append] at reached
          obtain ⟨middle, first, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          obtain ⟨disclose, _, nextBoundary⟩ := boundary.reveal_block bounds players lawful network
            event atRank published selected outputEq codeEq node owned
              (fun ref => refsBefore ref index) (opportunities event owner owned)
              decoded middle first
          have tailAligned : CompiledPolicySuffix setup.program wholeProfile next
              (afterReveal profile) tailRefs
              (revealSuccessor published selected source disclose).revelations
              (revealSuccessor published selected source disclose).registry
              tailEmbedding tailBefore (offset + 1) := by
            simpa only [revealSuccessor, tailRefs, tailEmbedding, OutputEmbedding.ref] using
              aligned.revealTail setup.program wholeProfile fresh selected unresolved next
                profile refs
                source.revelations source.registry embedding refsBefore offset
          obtain ⟨state, related, Δ, names, remaining, remainingProfile, current, currentRefs,
            currentEmbedding, currentBefore, currentAligned, currentAdmitted, lift, stateEq,
            stepEq, decodeEq, currentEffective, currentSupport, finalBoundary⟩ :=
            ih next (afterReveal profile) (revealSuccessor published selected source disclose)
              tailRefs tailEmbedding tailBefore (offset + 1) tailAligned
              (by simpa only [eventCount, Nat.succ_le_succ_iff] using bound)
              middle nextBoundary final rest
          refine ⟨Sum.inr state, related, Δ, names, remaining, remainingProfile, current,
            currentRefs, currentEmbedding, currentBefore, ?_, ?_, Sum.inr ∘ lift,
              congrArg Sum.inr stateEq, ?_, ?_, ?_, ?_, ?_⟩
          · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using currentAligned
          · intro admitted
            exact currentAdmitted (fun who => admitted who)
          · refine ⟨fun tailState => ?_, fun tailState joint => ?_,
              Sum.inr_injective.comp stepEq.2.2⟩
            · rw [Function.comp_apply, ProtocolState.behavioralStateStep_reveal_tail, stepEq.1,
                PMF.map_comp]
            · change (ProtocolState.step _ (lift tailState) joint).map Sum.inr = _
              rw [stepEq.2.1, PMF.map_comp]
          · intro more store history
            rw [show count + 1 + more = (count + more) + 1 by omega,
              decodeSourcePrefix?_reveal]
            change (decodeSourcePrefix? next tailRefs _ _ tailEmbedding.ref
              (count + more) store history).map Sum.inr = _
            simpa only [revealSuccessor, Option.map_map] using
              congrArg (Option.map Sum.inr) (decodeEq more store history)
          · intro effective
            exact currentEffective (fun who => (effective who).2)
          · intro supported
            exact currentSupport (fun who => (supported who).2)
          · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalBoundary

/-- Every initialized retained prefix has a genuine source-state decoder and
the exact residual compiler alignment. Initial private types may be correlated;
the physical players are arbitrary policies of the retained menu. -/
theorem initialized_sourceService_prefix_support
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (count : Nat) (within : count ≤ eventCount setup.program)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network
        (rosterPlanPrefix setup rosters count)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).support) :
    ∃ initial ∈ setup.initialLaw.support, ∃ state,
      SourcePrefixCheckpoint setup setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program)) []
        (Revelations.initial setup.context) (outputRef setup.program) 0 count state
        final.application.config ∧
      sourceServicePrefix? setup count final.application.config = some state ∧
      ∃ (Γ : SourceCtx Player L) (names : Finset VarId)
        (remaining : SourceProgram Player L Γ names)
        (remainingProfile : BehavioralProfile remaining)
        (current : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ)
        (embedding : OutputEmbedding (inputLayout setup.context)
          (outputLayout setup.program) remaining)
        (refsBefore : ContextRefsBefore refs embedding),
        CompiledPolicySuffix setup.program profile remaining remainingProfile refs
          current.revelations current.registry embedding refsBefore count ∧
        ((∀ who, (profile who).Admitted setup.program
          (CommitmentInterface.values setup.program)) →
            ∀ who, (remainingProfile who).Admitted remaining
              (CommitmentInterface.values remaining)) ∧
        ∃ lift : ProtocolState remaining → ProtocolState setup.program,
          state = lift (ProtocolState.entry remaining current) ∧
          ((∀ tailState, ProtocolState.behavioralStateStep setup.program profile
            (lift tailState) =
              (ProtocolState.behavioralStateStep remaining remainingProfile tailState).map lift) ∧
            (∀ tailState joint, ProtocolState.step setup.program (lift tailState) joint =
              (ProtocolState.step remaining tailState joint).map lift) ∧
            Function.Injective lift) ∧
          (∀ more store history,
            decodeSourcePrefix? setup.program
              (ContextRefs.initial setup.context (outputLayout setup.program)) []
              (Revelations.initial setup.context) (outputRef setup.program)
              (count + more) store history =
            (decodeSourcePrefix? remaining refs current.registry current.revelations
              embedding.ref more store history).map lift) ∧
          ((∀ who, (profile who).EffectiveDisclosures setup.program []
            (Revelations.initial setup.context)) →
              ∀ who, (remainingProfile who).EffectiveDisclosures remaining
                current.registry current.revelations) ∧
          ((∀ who, (profile who).SupportsEffectiveChoices setup.program
            (CommitmentInterface.values setup.program) [] (Revelations.initial setup.context)) →
              ∀ who, (remainingProfile who).SupportsEffectiveChoices remaining
                (CommitmentInterface.values remaining) current.registry current.revelations) ∧
          ServiceBoundary setup leaks rosters initial current refs count final := by
  rw [initialLaw, PMF.bind_map, PMF.support_bind] at reached
  obtain ⟨initial, initialSupport, continued⟩ := Set.mem_iUnion₂.mp reached
  obtain ⟨state, related, Γ, names, remaining, remainingProfile, current, refs,
      embedding, refsBefore, aligned, admitted, lift, stateEq, stepEq, decodeEq,
      effective, supported, boundary⟩ :=
    run_sourceService_prefix_support setup leaks bounds values capacity rosters opportunities
      players lawful network profile initial count setup.program profile
      (setup.initialConfig initial)
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program) (initialRefsBefore setup.program) 0
      (CompiledPolicySuffix.whole setup.program profile) within
      (ReactiveApplication.Execution.initial (application setup leaks)
        (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)))
      (serviceBoundary_initial setup leaks rosters initial) final continued
  refine ⟨initial, initialSupport, state, related, ?_, Γ, names, remaining, remainingProfile,
    current, refs, embedding, refsBefore, ?_, admitted, lift, stateEq, stepEq, decodeEq,
      effective, supported, ?_⟩
  · exact SourcePrefixCheckpoint.decode setup.program _ _ _ _ 0 count state _ related
  · simpa only [Nat.zero_add] using aligned
  · simpa only [Nat.zero_add] using boundary

end Vegas
