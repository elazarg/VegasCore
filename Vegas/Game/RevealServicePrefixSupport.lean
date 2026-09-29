/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServicePrefix
import Vegas.Game.RevealServiceClock
import Vegas.Game.SourceInformation
import Vegas.Game.SourceStateKernel
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Operational coverage of every restricted service prefix

This induction uses only membership in the ordinary response menu. In
particular a policy may depend on its complete alias recall, and its Boolean
choices need not be the compilation of any one source behavioral policy.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Every supported restricted prefix has a typed source position and the full
operational checkpoint invariant. This is a support statement for arbitrary
restricted policies, independent of the source-choice projection theorem. -/
theorem run_source_prefix_support
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (wholeProfile : BehavioralProfile setup.program)
    (players : Player → (application setup leaks).Policy)
    (watcherPolicy : players watcher = (application setup leaks).reportFirstUnpublished)
    (ordinary : ∀ who, who ≠ watcher → ∀ past view response,
      response ∈ (players who past view).support → response ∈
        ordinaryActions setup leaks bounds who past view)
    (initial : State L setup.context) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames) (reveals : program.RevealOnly)
      (profile : BehavioralProfile program)
      (source : Config Player L Γ) (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding) (offset : Nat),
      CompiledPolicySuffix setup.program wholeProfile program profile refs source.revelations []
        embedding refsBefore offset →
      ∀ (count : Nat), count ≤ eventCount program →
      ∀ execution, Checkpoint setup leaks initial source refs offset execution →
      ∀ finished, finished ∈ ((runtime setup).runInteractionPlan leaks players
        ((runtime setup).reportNetwork leaks watcher)
        (((List.finRange (eventCount program)).take count).flatMap fun index =>
          block setup watcher (embedding.event index)) execution).support →
      ∃ state, PrefixCheckpoint setup leaks initial program refs source.revelations
        embedding.ref offset count state finished ∧
        (∀ who, ProtocolView.entryView who program (ProtocolState.observe who program state) =
          source.view who) ∧
        state ∈ ((fun law => law.bind (ProtocolState.behavioralStateStep program
          (fun who => RevealOnly.uniformPolicy who program reveals)))^[count]
            (PMF.pure (ProtocolState.entry program source))).support := by
  intro Γ openNames program
  induction program with
  | ret payoffs =>
      intro _reveals profile source refs embedding refsBefore offset _aligned count countBound
        execution checkpoint finished supported
      have zero : count = 0 := by simpa [eventCount] using countBound
      subst count
      simp only [List.take_zero, List.flatMap_nil, runInteractionPlan] at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact ⟨ProtocolState.entry _ source, ⟨source, rfl, rfl, checkpoint⟩,
        (fun who => ProtocolView.entryView_observe_entry who _ source),
        (PMF.mem_support_pure_iff _ _).mpr rfl⟩
  | sample name fresh law next ih =>
      intro impossible
      exact impossible.elim
  | commit name owner fresh guard next ih =>
      intro impossible
      exact impossible.elim
  | @reveal Γ openNames published owner name payload fresh selected unresolved next ih =>
      intro reveals profile source refs embedding refsBefore offset aligned count countBound
        execution checkpoint finished supported
      cases count with
      | zero =>
          simp only [List.take_zero, List.flatMap_nil, runInteractionPlan] at supported
          cases (PMF.mem_support_pure_iff _ _).mp supported
          exact ⟨ProtocolState.entry _ source, ⟨source, rfl, rfl, checkpoint⟩,
            (fun who => ProtocolView.entryView_observe_entry who _ source),
            (PMF.mem_support_pure_iff _ _).mpr rfl⟩
      | succ count =>
          let index : Fin (eventCount
            (.reveal published owner name fresh selected unresolved next)) :=
              ⟨0, by simp [eventCount]⟩
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
          obtain ⟨opportunity, activeCheckpoint, granted, _clock, _activation,
              opportunityLaw, _opportunityRecall⟩ :=
            checkpoint.owner_opportunity players ((runtime setup).reportNetwork leaks watcher)
              event owner
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
          let remaining := ((List.finRange (eventCount next)).take count).flatMap fun tail =>
            block setup watcher (tailEmbedding.event tail)
          have planEq : (((List.finRange (eventCount
              (.reveal published owner name fresh selected unresolved next))).take
                (count + 1)).flatMap fun i => block setup watcher (embedding.event i)) =
              [.grant event, .player owner] ++ (suffix ++ remaining) := by
            simp only [eventCount, List.finRange_succ, List.take_succ_cons, ← List.map_take,
              List.flatMap_cons, List.flatMap_map]
            change block setup watcher event ++ remaining = _
            rw [block_of_owner setup watcher owner event actor]
            simp only [suffix, List.append_assoc, List.cons_append, List.nil_append]
          rw [planEq, runInteractionPlan_append, opportunityLaw, PMF.bind_map] at supported
          obtain ⟨response, selectedResponse, continued⟩ :=
            Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
          have member := ordinary owner different _ _ response selectedResponse
          have decoded (disclose : Bool) : decodeEventAction setup.program event
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
              some (.reveal owner name disclose) := by
            have embedded := aligned.actionEq index
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
            simpa [event, index, outputEq, decodeEventAction] using embedded
          obtain ⟨after, afterLaw, afterCheckpoint, _afterRecall⟩ :=
            activeCheckpoint.reveal_response bounds players watcher watcherPolicy published
              selected event eventRank actor outputEq codeEq node
              (fun ref => refsBefore ref index) decoded granted response member
          simp only [Function.comp_apply] at continued
          rw [runInteractionPlan_append, afterLaw, PMF.pure_bind] at continued
          have nextAligned : CompiledPolicySuffix setup.program wholeProfile next
              (afterReveal profile) tailRefs
              (revealSuccessor published selected source
                (sourceChoice setup leaks response)).revelations
              [] tailEmbedding tailBefore (offset + 1) := by
            simpa only [Registry.weaken, List.map_nil, revealSuccessor, tailRefs, resultRef,
              tailEmbedding, OutputEmbedding.ref] using tailAligned
          have nextBound : count ≤ eventCount next := by simpa [eventCount] using countBound
          obtain ⟨state, related, priorView, sourceReach⟩ := ih reveals (afterReveal profile)
            (revealSuccessor published selected source (sourceChoice setup leaks response))
            tailRefs tailEmbedding tailBefore (offset + 1) nextAligned count nextBound after
            afterCheckpoint finished continued
          refine ⟨Sum.inr state, related, ?_, ?_⟩
          · intro who
            change (ProtocolView.entryView who next
              (ProtocolState.observe who next state)).back (decide (owner = who)) = _
            rw [priorView who, back_reveal_view]
          · rw [ProtocolState.behavioralStatePrefix_reveal, PMF.support_bind]
            apply Set.mem_iUnion₂.mpr
            refine ⟨sourceChoice setup leaks response, ?_, ?_⟩
            · exact PMF.mem_support_uniformOfFintype _
            · rw [PMF.support_map]
              exact ⟨state, sourceReach, rfl⟩

/-- Every initialized restricted prefix has a valid source-state readout and
an operational checkpoint witness. The reference profile is used only to read
the static compiled syntax; no restriction is placed on actual Boolean laws. -/
theorem initialized_prefix_support
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (players : Player → (application setup leaks).Policy)
    (watcherPolicy : players watcher = (application setup leaks).reportFirstUnpublished)
    (ordinary : ∀ who, who ≠ watcher → ∀ past view response,
      response ∈ (players who past view).support → response ∈
        ordinaryActions setup leaks bounds who past view)
    (count : Nat) (within : count ≤ eventCount setup.program)
    (finished : (application setup leaks).Execution)
    (supported : finished ∈ ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players ((runtime setup).reportNetwork leaks watcher)
        (planPrefix setup watcher count)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).support) :
    ∃ initial ∈ setup.initialLaw.support, ∃ state,
      PrefixCheckpoint setup leaks initial setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) (outputRef setup.program) 0 count state finished ∧
      sourcePrefix? setup count finished.application.config = some state ∧
      (∀ who, ProtocolView.entryView who setup.program
        (ProtocolState.observe who setup.program state) =
          (setup.initialConfig initial).view who) ∧
      state ∈ ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program
        (fun who => RevealOnly.uniformPolicy who setup.program reveals)))^[count]
          (PMF.pure (ProtocolState.entry setup.program
            (setup.initialConfig initial)))).support := by
  rw [initialLaw, PMF.bind_map, PMF.support_bind] at supported
  obtain ⟨initial, initialSupport, reached⟩ := Set.mem_iUnion₂.mp supported
  let profile : BehavioralProfile setup.program :=
    fun who => RevealOnly.uniformPolicy who setup.program reveals
  obtain ⟨state, related, priorView, sourceReach⟩ :=
    run_source_prefix_support setup leaks bounds watcher observer profile
    players watcherPolicy ordinary initial setup.program reveals profile
    (setup.initialConfig initial) (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program) (initialRefsBefore setup.program) 0
    (CompiledPolicySuffix.whole setup.program profile) count within
    (ReactiveApplication.Execution.initial (application setup leaks)
      (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)))
    (checkpoint_initial setup leaks reveals initial (openable initial initialSupport))
    finished reached
  exact ⟨initial, initialSupport, state, related,
    PrefixCheckpoint.decode setup.program _ _ _ 0 count state finished related, priorView,
    sourceReach⟩

end Vegas
