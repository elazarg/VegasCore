/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceCheckpoint
import Vegas.Game.RevealServiceCorrespondence
import Vegas.Game.RevealServiceBounds
import Vegas.Compile.EventGraphLaw

/-! # Exact source law of the restricted revelation service

The proof folds actual activation, response, inclusion, monitoring, and deadline
instructions along the existing source syntax. It allows arbitrary distributions
over published replay aliases, provided their Boolean projection is the source
choice kernel. This includes changing one player's private alias selector.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Every source-compatible physical policy has the exact decoded source
execution law. The bounds are extended once from the setup, not from a strategy
or its support. No continuation correspondence is a hypothesis. -/
theorem run_source_suffix_option_law
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (wholeProfile : BehavioralProfile setup.program)
    (players : Player → (application setup leaks).Policy)
    (watcherPolicy : players watcher = (application setup leaks).silentPolicy)
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
      (source : Config Player L Γ) (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding) (offset : Nat),
      CompiledPolicySuffix setup.program wholeProfile program profile refs source.revelations []
        embedding refsBefore offset →
      ∀ execution, Checkpoint setup leaks initial source refs offset execution →
      ((runtime setup).runInteractionPlan leaks players
        ((runtime setup).idleNetwork leaks)
        ((List.finRange (eventCount program)).flatMap fun index =>
          block setup watcher (embedding.event index)) execution).map
        (fun final => decodeState? (terminalRefsWith program refs embedding.ref)
          final.application.config.store) =
        (runFrom program profile source).map some := by
  intro Γ openNames program
  induction program with
  | ret payoffs =>
      intro _reveals profile source refs embedding refsBefore offset _aligned execution checkpoint
      simp only [eventCount, List.finRange_zero, List.flatMap_nil, runInteractionPlan,
        PMF.pure_map, terminalRefsWith, runFrom, runWith]
      exact congrArg PMF.pure (decodeState?_eq_some refs source.state
        execution.application.config.store checkpoint.agrees)
  | sample name fresh law next ih =>
      intro impossible
      exact impossible.elim
  | commit name owner fresh guard next ih =>
      intro impossible
      exact impossible.elim
  | @reveal Γ openNames published owner name payload fresh selected unresolved next ih =>
      intro reveals profile source refs embedding refsBefore offset aligned execution checkpoint
      let index : Fin (eventCount
        (.reveal published owner name fresh selected unresolved next)) := ⟨0, by simp [eventCount]⟩
      let event := embedding.event index
      have eventRank : event.val = offset := by
        simpa [event, index] using aligned.graphSuffix.rankEq index
      have actor : (graph setup).actor? event = some owner := by
        change (toEventGraph setup.program).actor? event = some owner
        simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
      have different : owner ≠ watcher := by
        intro same
        exact observer event (same ▸ actor)
      have outputEq : (graph setup).outputLayout event = .publication payload :=
        embedding.layout_eq index
      have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes event) = .resolve owner payload (refs.get selected) [] :=
        reveal_head_code setup fresh selected unresolved next refs source.revelations
          embedding refsBefore offset aligned.graphSuffix
      have node : nodeView (graph setup) event =
          .resolve owner payload (refs.get selected) [] outputEq codeEq :=
        EventGraphRuntime.nodeView_eq_resolve _ _
      obtain ⟨opportunity, activeCheckpoint, _sameApplication,
          opportunityLaw, _opportunityRecall⟩ :=
        checkpoint.owner_opportunity players ((runtime setup).idleNetwork leaks)
          owner
      have ready : opportunity.application.config.cut.Ready event := by
        have active : offset < (graph setup).order.eventCount := eventRank ▸ event.isLt
        have chosenEvent : (⟨offset, active⟩ : (graph setup).EventId) = event :=
          Fin.ext eventRank.symm
        rw [← chosenEvent]
        exact activeCheckpoint.ordered.ready active
      obtain ⟨value, bound⟩ := activeCheckpoint.openable selected
      obtain ⟨candidate, associated, owned, fixed, selectedOpening⟩ :=
        opening_at_checkpoint setup leaks selected source.state refs opportunity
          activeCheckpoint.agrees activeCheckpoint.binding event actor outputEq codeEq node
          (ownTurn?_of_ready setup opportunity.application ready actor) value bound
      have covered := opening_available_of_initial_tables setup leaks bounds initial initialSupport
        opportunity activeCheckpoint.accepted activeCheckpoint.candidates _ candidate associated
        owner owned ⟨payload, value⟩ fixed event
      have choiceLaw := projects owner different (opportunity.recall owner)
        (opportunity.observe (application setup leaks) owner) _ selectedOpening covered
      rw [sourceChoiceLaw_reveal setup leaks fresh selected unresolved next wholeProfile profile
        refs source embedding refsBefore offset aligned opportunity activeCheckpoint.agrees
        activeCheckpoint.history ready] at choiceLaw
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
      have tailAligned := aligned.revealTail (whole := setup.program)
        (wholeProfile := wholeProfile) fresh selected unresolved next profile refs
        source.revelations [] embedding refsBefore offset
      let suffix : List (ServiceInstruction (graph setup)) :=
        [.includeLatest event owner, .player watcher, .wire] ++
          List.replicate (event.val + 1) .tick ++ [.expire event]
      let remaining := (List.finRange (eventCount next)).flatMap fun tail =>
        block setup watcher (tailEmbedding.event tail)
      have planEq : ((List.finRange (eventCount
          (.reveal published owner name fresh selected unresolved next))).flatMap fun i =>
            block setup watcher (embedding.event i)) =
          [.player owner] ++ (suffix ++ remaining) := by
        simp only [eventCount, List.finRange_succ, List.flatMap_cons, List.flatMap_map]
        change block setup watcher event ++ remaining = _
        rw [block_of_owner setup watcher owner event actor]
        simp only [suffix, List.append_assoc, List.cons_append, List.nil_append]
      rw [planEq, runInteractionPlan_append, opportunityLaw, PMF.bind_map, PMF.map_bind]
      rw [runFrom_reveal, ← choiceLaw, PMF.bind_map, PMF.map_bind]
      apply bind_congr_on_support _
      intro response supported
      have member := ordinary owner different _ _ response supported
      have decoded (disclose : Bool) : decodeEventAction setup.program event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
          some (.reveal owner name disclose) := by
        have embedded := aligned.actionEq index
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
        simpa [event, index, outputEq, decodeEventAction] using embedded
      obtain ⟨after, afterLaw, afterCheckpoint, _afterRecall⟩ :=
        activeCheckpoint.reveal_response (bounds.withInitialValues (initialLaw setup)) players
          watcher watcherPolicy published selected event eventRank actor outputEq codeEq node
          (fun ref => refsBefore ref index) decoded response member
      simp only [Function.comp_apply]
      rw [runInteractionPlan_append, afterLaw, PMF.pure_bind]
      have nextAligned : CompiledPolicySuffix setup.program wholeProfile next
          (afterReveal profile) tailRefs
          (revealSuccessor published selected source
            (sourceChoice setup leaks response)).revelations
          [] tailEmbedding tailBefore (offset + 1) := by
        simpa only [Registry.weaken, List.map_nil, revealSuccessor, tailRefs, resultRef,
          tailEmbedding, OutputEmbedding.ref] using tailAligned
      exact ih reveals (afterReveal profile)
        (revealSuccessor published selected source (sourceChoice setup leaks response))
        tailRefs tailEmbedding tailBefore (offset + 1) nextAligned after afterCheckpoint

end Vegas
