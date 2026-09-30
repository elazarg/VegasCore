/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServicePrefixSupport
import Vegas.Game.RevealServicePrefixInformation
import Vegas.Game.RevealServiceSelector
import Vegas.Pending.ReactiveServiceRecall

/-! # Reconstructing focal replay aliases along actual service prefixes

The comparison run may use any ordinary response policy. When the selected
run reaches the same source observation, every focal response is forced to
the recorded comparison alias. The proof uses actual supported service
blocks, including their emitted envelopes and private before-views.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem reference_next {α : Type} (past reference : List α) (entry : α)
    (retained : past ++ [entry] <+: reference) :
    past = reference.take past.length ∧ reference[past.length]? = some entry := by
  obtain ⟨rest, rfl⟩ := retained
  simp only [List.append_assoc, List.take_append_of_le_length (le_refl past.length),
    List.take_length, List.getElem?_append_right (le_refl past.length), Nat.sub_self,
    List.singleton_append, List.getElem?_cons_zero, and_self]

/-- Source-view equality fixes the focal player's complete response recall
under the selector. The comparison run and its aliases need only be legal;
neither strategy support in a limiting equilibrium nor belief transport is a
premise. -/
theorem run_source_prefix_focal_recall
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (wholeProfile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (who : Player) (ordinaryWho : who ≠ watcher)
    (reference : List (application setup leaks).PlayerEntry)
    (leftPlayers rightPlayers : Player → (application setup leaks).Policy)
    (selectedPolicy : leftPlayers who =
      focalPolicy setup leaks bounds wholeProfile weight nonnegative atMostOne who reference)
    (leftWatcher : leftPlayers watcher = (application setup leaks).reportFirstUnpublished)
    (rightWatcher : rightPlayers watcher = (application setup leaks).reportFirstUnpublished)
    (leftOrdinary : ∀ player, player ≠ watcher → ∀ past view response,
      response ∈ (leftPlayers player past view).support → response ∈
        ordinaryActions setup leaks bounds player past view)
    (rightOrdinary : ∀ player, player ≠ watcher → ∀ past view response,
      response ∈ (rightPlayers player past view).support → response ∈
        ordinaryActions setup leaks bounds player past view)
    (leftInitial rightInitial : State L setup.context) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames) (_reveals : program.RevealOnly)
      (profile : BehavioralProfile program)
      (leftSource rightSource : Config Player L Γ)
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding) (offset : Nat),
      CompiledPolicySuffix setup.program wholeProfile program profile refs
        leftSource.revelations [] embedding refsBefore offset →
      CompiledPolicySuffix setup.program wholeProfile program profile refs
        rightSource.revelations [] embedding refsBefore offset →
      ∀ (count : Nat), count ≤ eventCount program →
      ∀ leftStart rightStart,
      Checkpoint setup leaks leftInitial leftSource refs offset leftStart →
      Checkpoint setup leaks rightInitial rightSource refs offset rightStart →
      leftStart.recall who = rightStart.recall who →
      ∀ leftEnd rightEnd,
      leftEnd ∈ ((runtime setup).runInteractionPlan leaks leftPlayers
        ((runtime setup).reportNetwork leaks watcher)
        (((List.finRange (eventCount program)).take count).flatMap fun index =>
          block setup watcher (embedding.event index)) leftStart).support →
      rightEnd ∈ ((runtime setup).runInteractionPlan leaks rightPlayers
        ((runtime setup).reportNetwork leaks watcher)
        (((List.finRange (eventCount program)).take count).flatMap fun index =>
          block setup watcher (embedding.event index)) rightStart).support →
      rightEnd.recall who = reference →
      ∀ leftState rightState,
      PrefixCheckpoint setup leaks leftInitial program refs leftSource.revelations
        embedding.ref offset count leftState leftEnd →
      PrefixCheckpoint setup leaks rightInitial program refs rightSource.revelations
        embedding.ref offset count rightState rightEnd →
      ProtocolState.observe who program leftState =
        ProtocolState.observe who program rightState →
      leftEnd.recall who = rightEnd.recall who := by
  intro Γ openNames program
  induction program with
  | ret payoffs =>
      intro _reveals profile leftSource rightSource refs embedding refsBefore offset
        _leftAligned _rightAligned count countBound leftStart rightStart leftCheckpoint
        rightCheckpoint earlier leftEnd rightEnd leftSupport rightSupport _reference
        _leftState _rightState _leftRelated _rightRelated _same
      have zero : count = 0 := by simpa [eventCount] using countBound
      subst count
      simp only [List.take_zero, List.flatMap_nil, runInteractionPlan] at leftSupport rightSupport
      cases (PMF.mem_support_pure_iff _ _).mp leftSupport
      cases (PMF.mem_support_pure_iff _ _).mp rightSupport
      exact earlier
  | sample name fresh law next ih =>
      intro impossible
      exact impossible.elim
  | commit name owner fresh guard next ih =>
      intro impossible
      exact impossible.elim
  | @reveal Γ openNames published owner name payload fresh selected unresolved next ih =>
      intro reveals profile leftSource rightSource refs embedding refsBefore offset
        leftAligned rightAligned count countBound leftStart rightStart leftCheckpoint
        rightCheckpoint earlier leftEnd rightEnd leftSupport rightSupport referenceEq
        leftState rightState leftRelated rightRelated same
      cases count with
      | zero =>
          simp only [List.take_zero, List.flatMap_nil, runInteractionPlan]
            at leftSupport rightSupport
          cases (PMF.mem_support_pure_iff _ _).mp leftSupport
          cases (PMF.mem_support_pure_iff _ _).mp rightSupport
          exact earlier
      | succ count =>
          cases leftState with
          | inl source => exact leftRelated.elim
          | inr leftState =>
            cases rightState with
            | inl source => exact rightRelated.elim
            | inr rightState =>
              simp only [ProtocolState.observe, Sum.elim_inr, Sum.inr.injEq] at same
              let index : Fin (eventCount
                (.reveal published owner name fresh selected unresolved next)) :=
                  ⟨0, by simp [eventCount]⟩
              let event := embedding.event index
              have eventRank : event.val = offset := by
                simpa [event, index] using leftAligned.graphSuffix.rankEq index
              have actor : (graph setup).actor? event = some owner := by
                change (toEventGraph setup.program).actor? event = some owner
                simpa [event, index, eventOwner?, eventCount] using leftAligned.actorEq index
              have different : owner ≠ watcher := by
                intro same
                exact observer event (same ▸ actor)
              have outputEq : (graph setup).outputLayout event = .publication payload :=
                embedding.layout_eq index
              have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
                  ((graph setup).nodes event) = .resolve owner payload (refs.get selected) [] :=
                reveal_head_code setup fresh selected unresolved next refs leftSource.revelations
                  embedding refsBefore offset leftAligned.graphSuffix
              have node : nodeView (graph setup) event =
                  .resolve owner payload (refs.get selected) [] outputEq codeEq :=
                EventGraphRuntime.nodeView_eq_resolve _ _
              obtain ⟨leftOpportunity, leftActive, leftGrant, _leftClock, _leftActivation,
                  leftOpportunityLaw, leftRecall⟩ :=
                leftCheckpoint.owner_opportunity leftPlayers
                  ((runtime setup).reportNetwork leaks watcher) event owner
              obtain ⟨rightOpportunity, rightActive, rightGrant, _rightClock, _rightActivation,
                  rightOpportunityLaw, rightRecall⟩ :=
                rightCheckpoint.owner_opportunity rightPlayers
                  ((runtime setup).reportNetwork leaks watcher) event owner
              let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
              let resultRef : EventGraph.FieldRef (graphLayout setup.program)
                (.publication payload) := ⟨.inr event, outputEq⟩
              let tailRefs := refs.cons (name := published) (cell := .publication payload) resultRef
              have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
                intro readName cell ref remaining
                cases ref with
                | here =>
                    change (embedding.event index).val < (embedding.event (Fin.succ remaining)).val
                    apply embedding.strictMono
                    exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
                | there ref => exact refsBefore ref (Fin.succ remaining)
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
              rw [planEq, runInteractionPlan_append, leftOpportunityLaw,
                PMF.bind_map] at leftSupport
              rw [planEq, runInteractionPlan_append, rightOpportunityLaw,
                PMF.bind_map] at rightSupport
              obtain ⟨leftResponse, leftChosen, leftContinued⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ leftSupport)
              obtain ⟨rightResponse, rightChosen, rightContinued⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ rightSupport)
              have leftMember := leftOrdinary owner different _ _ leftResponse leftChosen
              have rightMember := rightOrdinary owner different _ _ rightResponse rightChosen
              have decoded (disclose : Bool) : decodeEventAction setup.program event
                  (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
                  some (.reveal owner name disclose) := by
                have embedded := leftAligned.actionEq index
                  (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
                simpa [event, index, outputEq, decodeEventAction] using embedded
              obtain ⟨leftAfter, leftAfterLaw, leftAfterCheckpoint, leftAfterRecall⟩ :=
                leftActive.reveal_response bounds leftPlayers watcher leftWatcher published
                  selected event eventRank actor outputEq codeEq node
                  (fun ref => refsBefore ref index) decoded leftResponse leftMember
              obtain ⟨rightAfter, rightAfterLaw, rightAfterCheckpoint, rightAfterRecall⟩ :=
                rightActive.reveal_response bounds rightPlayers watcher rightWatcher published
                  selected event eventRank actor outputEq codeEq node
                  (fun ref => refsBefore ref index) decoded rightResponse rightMember
              rw [Function.comp_apply, runInteractionPlan_append, leftAfterLaw, PMF.pure_bind]
                at leftContinued
              rw [Function.comp_apply, runInteractionPlan_append, rightAfterLaw, PMF.pure_bind]
                at rightContinued
              have leftTailAligned : CompiledPolicySuffix setup.program wholeProfile next
                  (afterReveal profile) tailRefs
                  (revealSuccessor published selected leftSource
                    (sourceChoice setup leaks leftResponse)).revelations
                  [] tailEmbedding tailBefore (offset + 1) := by
                simpa only [Registry.weaken, List.map_nil, revealSuccessor, tailRefs, resultRef,
                  tailEmbedding, OutputEmbedding.ref] using leftAligned.revealTail
                    (whole := setup.program) (wholeProfile := wholeProfile) fresh selected
                    unresolved next profile refs leftSource.revelations [] embedding refsBefore
                    offset
              have rightTailAligned : CompiledPolicySuffix setup.program wholeProfile next
                  (afterReveal profile) tailRefs
                  (revealSuccessor published selected rightSource
                    (sourceChoice setup leaks rightResponse)).revelations
                  [] tailEmbedding tailBefore (offset + 1) := by
                simpa only [Registry.weaken, List.map_nil, revealSuccessor, tailRefs, resultRef,
                  tailEmbedding, OutputEmbedding.ref] using rightAligned.revealTail
                    (whole := setup.program) (wholeProfile := wholeProfile) fresh selected
                    unresolved next profile refs rightSource.revelations [] embedding refsBefore
                    offset
              have nextBound : count ≤ eventCount next := by simpa [eventCount] using countBound
              obtain ⟨leftWitness, leftWitnessRelated, leftPrior, _leftSourceReach⟩ :=
                run_source_prefix_support setup leaks bounds watcher observer wholeProfile
                  leftPlayers leftWatcher leftOrdinary leftInitial next reveals
                  (afterReveal profile) _ tailRefs tailEmbedding tailBefore (offset + 1)
                  leftTailAligned count nextBound leftAfter leftAfterCheckpoint leftEnd
                  leftContinued
              have leftUnique := PrefixCheckpoint.state_unique next tailRefs _ tailEmbedding.ref
                (offset + 1) count leftWitness leftState leftEnd leftWitnessRelated leftRelated
              subst leftWitness
              obtain ⟨rightWitness, rightWitnessRelated, rightPrior, _rightSourceReach⟩ :=
                run_source_prefix_support setup leaks bounds watcher observer wholeProfile
                  rightPlayers rightWatcher rightOrdinary rightInitial next reveals
                  (afterReveal profile) _ tailRefs tailEmbedding tailBefore (offset + 1)
                  rightTailAligned count nextBound rightAfter rightAfterCheckpoint rightEnd
                  rightContinued
              have rightUnique := PrefixCheckpoint.state_unique next tailRefs _ tailEmbedding.ref
                (offset + 1) count rightWitness rightState rightEnd rightWitnessRelated rightRelated
              subst rightWitness
              have nextView : (revealSuccessor published selected leftSource
                    (sourceChoice setup leaks leftResponse)).view who =
                  (revealSuccessor published selected rightSource
                    (sourceChoice setup leaks rightResponse)).view who := by
                rw [← leftPrior who, ← rightPrior who, same]
              have priorView := reveal_view_reflects who published selected leftSource rightSource
                _ _ nextView
              obtain ⟨leftValue, leftOpen⟩ := leftCheckpoint.openable selected
              obtain ⟨rightValue, rightOpen⟩ := rightCheckpoint.openable selected
              have choice := reveal_choice_eq_of_view_eq who published selected leftSource
                rightSource _ _ leftCheckpoint.emptyRegistry rightCheckpoint.emptyRegistry
                leftValue rightValue leftOpen rightOpen nextView
              have opportunityPast : leftOpportunity.recall who = rightOpportunity.recall who := by
                rw [leftRecall, rightRecall, earlier]
              have afterPast : leftAfter.recall who = rightAfter.recall who := by
                rw [leftAfterRecall who ordinaryWho, rightAfterRecall who ordinaryWho]
                by_cases owns : owner = who
                · subst owner
                  have input := leftActive.observe_eq rightActive who
                    (leftGrant.trans rightGrant.symm) priorView
                  obtain ⟨entry, appended, entryView, entryAction⟩ :=
                    (runtime setup).response_recall_entry leaks rightOpportunity who rightResponse
                  have retained := (runtime setup).runInteractionPlan_recall_prefix leaks
                    rightPlayers ((runtime setup).reportNetwork leaks watcher) remaining
                    rightAfter rightEnd rightContinued who
                  rw [rightAfterRecall who ordinaryWho, appended, referenceEq] at retained
                  obtain ⟨earlierReference, nextReference⟩ := reference_next _ _ entry retained
                  have played := leftChosen
                  rw [selectedPolicy] at played
                  have member : entry.action ∈ ordinaryActions setup leaks bounds who
                      (leftOpportunity.recall who)
                      (leftOpportunity.observe (application setup leaks) who) := by
                    rw [entryAction, opportunityPast, input]
                    exact rightMember
                  have chosen : leftResponse = rightResponse := by
                    have selected := focalPolicy_selects setup leaks bounds wholeProfile weight
                      nonnegative atMostOne who reference (leftOpportunity.recall who)
                      (leftOpportunity.observe (application setup leaks) who) entry
                      (by simpa only [opportunityPast] using nextReference)
                      (by simpa only [opportunityPast] using earlierReference)
                      (entryView.trans input.symm) member leftResponse played
                      (by simpa only [entryAction] using choice)
                    exact selected.trans entryAction
                  rw [chosen]
                  exact leftActive.respond_recall_eq rightActive who
                    (leftGrant.trans rightGrant.symm) priorView opportunityPast rightResponse
                · rw [(application setup leaks).respond_recall_other _ owner who
                    (Ne.symm owns), (application setup leaks).respond_recall_other _ owner who
                    (Ne.symm owns)]
                  exact opportunityPast
              exact ih reveals (afterReveal profile) _ _ tailRefs tailEmbedding tailBefore
                (offset + 1) leftTailAligned rightTailAligned count nextBound leftAfter rightAfter
                leftAfterCheckpoint rightAfterCheckpoint afterPast leftEnd rightEnd leftContinued
                rightContinued referenceEq leftState rightState leftRelated rightRelated same

/-- At initialized checkpoints, equality of the actual decoded source
observation is enough to reconstruct the complete selected alias recall.
The two initialized private states may be different and correlated with
other players' inputs. -/
theorem initialized_focal_recall
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (who : Player) (ordinaryWho : who ≠ watcher)
    (reference : List (application setup leaks).PlayerEntry)
    (leftPlayers rightPlayers : Player → (application setup leaks).Policy)
    (selectedPolicy : leftPlayers who =
      focalPolicy setup leaks bounds profile weight nonnegative atMostOne who reference)
    (leftWatcher : leftPlayers watcher = (application setup leaks).reportFirstUnpublished)
    (rightWatcher : rightPlayers watcher = (application setup leaks).reportFirstUnpublished)
    (leftOrdinary : ∀ player, player ≠ watcher → ∀ past view response,
      response ∈ (leftPlayers player past view).support → response ∈
        ordinaryActions setup leaks bounds player past view)
    (rightOrdinary : ∀ player, player ≠ watcher → ∀ past view response,
      response ∈ (rightPlayers player past view).support → response ∈
        ordinaryActions setup leaks bounds player past view)
    (count : Nat) (within : count ≤ eventCount setup.program)
    (leftEnd rightEnd : (application setup leaks).Execution)
    (leftSupport : leftEnd ∈ ((initialLaw setup).bind fun initial =>
      (runtime setup).runInteractionPlan leaks leftPlayers
        ((runtime setup).reportNetwork leaks watcher) (planPrefix setup watcher count)
        (ReactiveApplication.Execution.initial (application setup leaks) initial)).support)
    (rightSupport : rightEnd ∈ ((initialLaw setup).bind fun initial =>
      (runtime setup).runInteractionPlan leaks rightPlayers
        ((runtime setup).reportNetwork leaks watcher) (planPrefix setup watcher count)
        (ReactiveApplication.Execution.initial (application setup leaks) initial)).support)
    (referenceEq : rightEnd.recall who = reference)
    (same : setup.protocolObserve who (sourcePrefix? setup count leftEnd.application.config) =
      setup.protocolObserve who (sourcePrefix? setup count rightEnd.application.config)) :
    leftEnd.recall who = rightEnd.recall who := by
  rw [initialLaw, PMF.bind_map, PMF.support_bind] at leftSupport rightSupport
  obtain ⟨leftInitial, leftInitialSupport, leftRun⟩ := Set.mem_iUnion₂.mp leftSupport
  obtain ⟨rightInitial, rightInitialSupport, rightRun⟩ := Set.mem_iUnion₂.mp rightSupport
  let refs := ContextRefs.initial setup.context (outputLayout setup.program)
  let embedding := outputEmbedding setup.program
  let leftSource := setup.initialConfig leftInitial
  let rightSource := setup.initialConfig rightInitial
  let leftStart := ReactiveApplication.Execution.initial (application setup leaks)
    (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs leftInitial))
  let rightStart := ReactiveApplication.Execution.initial (application setup leaks)
    (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs rightInitial))
  have leftCheckpoint : Checkpoint setup leaks leftInitial leftSource refs 0 leftStart :=
    checkpoint_initial setup leaks reveals leftInitial (openable leftInitial leftInitialSupport)
  have rightCheckpoint : Checkpoint setup leaks rightInitial rightSource refs 0 rightStart :=
    checkpoint_initial setup leaks reveals rightInitial (openable rightInitial rightInitialSupport)
  obtain ⟨leftState, leftRelated, _leftPrior, _leftSourceReach⟩ :=
    run_source_prefix_support setup leaks bounds
    watcher observer profile leftPlayers leftWatcher leftOrdinary leftInitial setup.program
    reveals profile leftSource refs embedding (initialRefsBefore setup.program) 0
    (CompiledPolicySuffix.whole setup.program profile) count within leftStart leftCheckpoint
    leftEnd leftRun
  obtain ⟨rightState, rightRelated, _rightPrior, _rightSourceReach⟩ :=
    run_source_prefix_support setup leaks bounds
    watcher observer profile rightPlayers rightWatcher rightOrdinary rightInitial setup.program
    reveals profile rightSource refs embedding (initialRefsBefore setup.program) 0
    (CompiledPolicySuffix.whole setup.program profile) count within rightStart rightCheckpoint
    rightEnd rightRun
  have leftDecoded := PrefixCheckpoint.decode setup.program refs leftSource.revelations
    embedding.ref 0 count leftState leftEnd leftRelated
  have rightDecoded := PrefixCheckpoint.decode setup.program refs rightSource.revelations
    embedding.ref 0 count rightState rightEnd rightRelated
  change sourcePrefix? setup count leftEnd.application.config = some leftState at leftDecoded
  change sourcePrefix? setup count rightEnd.application.config = some rightState at rightDecoded
  rw [leftDecoded, rightDecoded] at same
  have observed := Option.some.inj same
  exact run_source_prefix_focal_recall setup leaks bounds watcher observer profile weight
    nonnegative atMostOne who ordinaryWho reference leftPlayers rightPlayers selectedPolicy
    leftWatcher rightWatcher leftOrdinary rightOrdinary leftInitial rightInitial setup.program
    reveals profile leftSource rightSource refs embedding (initialRefsBefore setup.program) 0
    (CompiledPolicySuffix.whole setup.program profile)
    (CompiledPolicySuffix.whole setup.program profile) count within leftStart rightStart
    leftCheckpoint rightCheckpoint rfl leftEnd rightEnd leftRun rightRun referenceEq leftState
    rightState leftRelated rightRelated observed

end Vegas
