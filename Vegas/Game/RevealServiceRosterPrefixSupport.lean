/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServicePrefix
import Vegas.Game.RevealServiceRosterCheckpoint
import Vegas.Game.ServiceRosterCounts
import Vegas.Game.SourceStateKernel
import Vegas.Game.SourceInformation
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Every retained roster prefix represents a source prefix

The structural induction ranges over arbitrary retained policies. At each
actual block it derives a source successor, public checkpoint and clean pending
identifiers, while actual response counts supply the next owner's offset.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem run_roster_source_prefix_support
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (wholeProfile : BehavioralProfile setup.program)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ rosterActions setup leaks bounds rosters who past view)
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
      ∀ execution, PublicCheckpoint setup leaks initial source refs offset execution →
      (∀ who, (execution.recall who).length =
        (((List.finRange (graph setup).order.eventCount).take offset).flatMap rosters).count who) →
      execution.network.Satisfies (fun message =>
        message.id ∈ execution.network.ledger.map Message.id) →
      execution.network.SerialsBeforeNext →
      ∀ finished, finished ∈ ((runtime setup).runInteractionPlan leaks players
        network
        (((List.finRange (eventCount program)).take count).flatMap fun index =>
          rosterBlock setup rosters (embedding.event index)) execution).support →
      ∃ state, PublicPrefixCheckpoint setup leaks initial program refs source.revelations
        embedding.ref offset count state finished ∧
        (∀ who, ProtocolView.entryView who program (ProtocolState.observe who program state) =
          source.view who) ∧
        state ∈ ((fun law => law.bind (ProtocolState.behavioralStateStep program
          (fun who => RevealOnly.uniformPolicy who program reveals)))^[count]
            (PMF.pure (ProtocolState.entry program source))).support ∧
        finished.network.Satisfies (fun message =>
          message.id ∈ finished.network.ledger.map Message.id) := by
  intro Γ openNames program
  induction program with
  | ret payoffs =>
      intro _reveals profile source refs embedding refsBefore offset _aligned count countBound
        execution checkpoint counts clean serials finished supported
      have zero : count = 0 := by simpa [eventCount] using countBound
      subst count
      simp only [List.take_zero, List.flatMap_nil, runInteractionPlan] at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact ⟨ProtocolState.entry _ source, ⟨source, rfl, rfl, checkpoint⟩,
        (fun who => ProtocolView.entryView_observe_entry who _ source),
        (PMF.mem_support_pure_iff _ _).mpr rfl, clean⟩
  | sample name fresh law next ih =>
      intro impossible
      exact impossible.elim
  | commit name owner fresh guard next ih =>
      intro impossible
      exact impossible.elim
  | @reveal Γ openNames published owner name payload fresh selected unresolved next ih =>
      intro reveals profile source refs embedding refsBefore offset aligned count countBound
        execution checkpoint counts clean serials finished supported
      cases count with
      | zero =>
          simp only [List.take_zero, List.flatMap_nil, runInteractionPlan] at supported
          cases (PMF.mem_support_pure_iff _ _).mp supported
          exact ⟨ProtocolState.entry _ source, ⟨source, rfl, rfl, checkpoint⟩,
            (fun who => ProtocolView.entryView_observe_entry who _ source),
            (PMF.mem_support_pure_iff _ _).mpr rfl, clean⟩
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
          have outputEq : (graph setup).outputLayout event = .publication payload :=
            embedding.layout_eq index
          have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
              ((graph setup).nodes event) = .resolve owner payload (refs.get selected) [] :=
            reveal_head_code setup fresh selected unresolved next refs source.revelations
              embedding refsBefore offset aligned.graphSuffix
          have node : nodeView (graph setup) event =
              .resolve owner payload (refs.get selected) [] outputEq codeEq :=
            EventGraphRuntime.nodeView_eq_resolve _ _
          obtain ⟨opportunity, activeCheckpoint, granted, grantRecall, grantNetwork,
              grantLaw⟩ := checkpoint.grant players network event
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
          let remaining := ((List.finRange (eventCount next)).take count).flatMap fun tail =>
            rosterBlock setup rosters (tailEmbedding.event tail)
          have planEq : (((List.finRange (eventCount
              (.reveal published owner name fresh selected unresolved next))).take
                (count + 1)).flatMap fun i => rosterBlock setup rosters (embedding.event i)) =
              rosterBlock setup rosters event ++ remaining := by
            simp only [eventCount, List.finRange_succ, List.take_succ_cons, ← List.map_take,
              List.flatMap_cons, List.flatMap_map]
            rfl
          rw [planEq, runInteractionPlan_append] at supported
          obtain ⟨after, blockReached, continued⟩ :=
            Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
          have originalReached := blockReached
          rw [rosterBlock_of_owner setup rosters event owner actor,
            runInteractionPlan_append, grantLaw, PMF.pure_bind] at blockReached
          have ownerOffset : (opportunity.recall owner).length =
              rosterOffset setup rosters owner event := by
            rw [grantRecall, counts owner]
            simp only [rosterOffset, eventRank]
          have decoded (disclose : Bool) : decodeEventAction setup.program event
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
              some (.reveal owner name disclose) := by
            have embedded := aligned.actionEq index
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
            simpa [event, index, outputEq, decodeEventAction] using embedded
          obtain ⟨disclose, afterCheckpoint, afterClean⟩ :=
            activeCheckpoint.reveal_roster bounds rosters players covered network published
              selected
              event eventRank actor outputEq codeEq node (fun ref => refsBefore ref index) decoded
                ownerOffset (grantNetwork ▸ clean) (grantNetwork ▸ serials) after
                  blockReached
          have afterCounts (who : Player) : (after.recall who).length =
              (((List.finRange (graph setup).order.eventCount).take (offset + 1)).flatMap
                rosters).count who := by
            have advanced := fixed_plan_response_counts setup leaks network players
              (rosterBlock setup rosters event) (rosterBlock_no_wire setup rosters event)
                execution after originalReached who
            rw [rosterBlock_actors, counts who] at advanced
            have phases := congrArg (fun instructions : List (ServiceInstruction (graph setup)) =>
              (instructions.filterMap instructionActor).count who)
                (rosterPlanPrefix_succ setup rosters event)
            rw [List.filterMap_append, List.count_append, rosterPlanPrefix_actors,
              rosterPlanPrefix_actors, rosterBlock_actors, eventRank] at phases
            exact advanced.trans phases.symm
          have afterSerials := (runtime setup).runInteractionPlan_serials leaks players network
            (rosterBlock setup rosters event) execution after serials originalReached
          have nextAligned : CompiledPolicySuffix setup.program wholeProfile next
              (afterReveal profile) tailRefs
              (revealSuccessor published selected source
                disclose).revelations
              [] tailEmbedding tailBefore (offset + 1) := by
            simpa only [Registry.weaken, List.map_nil, revealSuccessor, tailRefs, resultRef,
              tailEmbedding, OutputEmbedding.ref] using tailAligned
          have nextBound : count ≤ eventCount next := by simpa [eventCount] using countBound
          obtain ⟨state, related, priorView, sourceReach, finalClean⟩ :=
            ih reveals (afterReveal profile)
            (revealSuccessor published selected source disclose)
            tailRefs tailEmbedding tailBefore (offset + 1) nextAligned count nextBound after
            afterCheckpoint afterCounts afterClean afterSerials finished continued
          refine ⟨Sum.inr state, related, ?_, ?_, finalClean⟩
          · intro who
            change (ProtocolView.entryView who next
              (ProtocolState.observe who next state)).back (decide (owner = who)) = _
            rw [priorView who, back_reveal_view]
          · rw [ProtocolState.behavioralStatePrefix_reveal, PMF.support_bind]
            apply Set.mem_iUnion₂.mpr
            refine ⟨disclose, ?_, ?_⟩
            · exact PMF.mem_support_uniformOfFintype _
            · rw [PMF.support_map]
              exact ⟨state, sourceReach, rfl⟩

/-- Initialized support, including source-impossible native histories only
when a response leaves the retained menu. No equilibrium support is assumed. -/
theorem initialized_roster_prefix_support
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ rosterActions setup leaks bounds rosters who past view)
    (count : Nat) (within : count ≤ eventCount setup.program)
    (finished : (application setup leaks).Execution)
    (supported : finished ∈ ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network
        (rosterPlanPrefix setup rosters count)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).support) :
    ∃ initial ∈ setup.initialLaw.support, ∃ state,
      PublicPrefixCheckpoint setup leaks initial setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) (outputRef setup.program) 0 count state finished ∧
      sourcePrefix? setup count finished.application.config = some state ∧
      (∀ who, ProtocolView.entryView who setup.program
        (ProtocolState.observe who setup.program state) = (setup.initialConfig initial).view who) ∧
      state ∈ ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program
        (fun who => RevealOnly.uniformPolicy who setup.program reveals)))^[count]
          (PMF.pure (ProtocolState.entry setup.program
            (setup.initialConfig initial)))).support ∧
      finished.network.Satisfies (fun message =>
        message.id ∈ finished.network.ledger.map Message.id) := by
  rw [initialLaw, PMF.bind_map, PMF.support_bind] at supported
  obtain ⟨initial, initialSupport, reached⟩ := Set.mem_iUnion₂.mp supported
  let profile : BehavioralProfile setup.program :=
    fun who => RevealOnly.uniformPolicy who setup.program reveals
  obtain ⟨state, related, priorView, sourceReach, clean⟩ :=
    run_roster_source_prefix_support setup leaks bounds rosters network profile players covered
      initial setup.program reveals profile (setup.initialConfig initial)
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (outputEmbedding setup.program) (initialRefsBefore setup.program) 0
        (CompiledPolicySuffix.whole setup.program profile) count within
        (ReactiveApplication.Execution.initial (application setup leaks)
          (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)))
        (checkpoint_initial setup leaks reveals initial
          (openable initial initialSupport)).toPublicCheckpoint
        (fun _ => rfl) MessageNetwork.Satisfies.empty MessageNetwork.SerialsBeforeNext.empty
        finished reached
  exact ⟨initial, initialSupport, state, related,
    PublicPrefixCheckpoint.decode setup.program _ _ _ 0 count state finished related,
    priorView, sourceReach, clean⟩

end Vegas
