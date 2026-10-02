/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterCheckpoint
import Vegas.Pending.ReactiveOpeningExpiryCoupling
import Vegas.Pending.EventCompletionObservation
import Vegas.Source.ObservationRecall

/-! # Conditional communication at matched source information

The result compares actual full revelation phases from typed source checkpoints.
Equal resulting focal source views account for the disclosed value, if any.
All sampling, replay multiplicities, message observations and focal recall are
retained; no observation-kernel independence assumption is introduced.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem no_opening_players
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (owner : Player) (event : (graph setup).EventId) (candidate : Handle (graph setup))
    (left right : Raw L) (offset : Nat) (slots : Nat) :
    (runtime setup).openingWindowPlayers leaks owner event candidate left offset
        (none : Option (Fin slots)) =
      (runtime setup).openingWindowPlayers leaks owner event candidate right offset
        (none : Option (Fin slots)) := by
  funext who past view
  by_cases same : who = owner
  · simp only [openingWindowPlayers, ite_eq_left same]
    simp only [ReactiveApplication.scheduledPolicy, Option.map_none, reduceCtorEq, ↓reduceIte]
  · simp only [openingWindowPlayers, ite_eq_right same]

/-- Conditional on the same source reveal choice, equal successor source
views imply equal complete auxiliary phase laws. The initial-message equality
is the induction variable: hidden application state itself may differ. -/
theorem PublicCheckpoint.reveal_scheduled_coupling
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {leftInitial rightInitial : State L setup.context} {Γ : SourceCtx Player L}
    {leftSource rightSource : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {left right : (application setup leaks).Execution}
    (leftCheckpoint : PublicCheckpoint setup leaks leftInitial leftSource refs rank left)
    (rightCheckpoint : PublicCheckpoint setup leaks rightInitial rightSource refs rank right)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (event : (graph setup).EventId) (eventRank : event.val = rank)
    (actor : (graph setup).actor? event = some owner)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding) [])
    (node : nodeView (graph setup) event =
      .resolve owner payload (refs.get binding) [] outputEq codeEq)
    (leftValue rightValue : L.Val payload)
    (leftOpen : leftSource.state.get binding = .success leftValue)
    (rightOpen : rightSource.state.get binding = .success rightValue)
    (candidate : Handle (graph setup)) (owned : candidate.1 = owner)
    (leftAssociated : left.application.accepted (refs.get binding).field = some candidate)
    (rightAssociated : right.application.accepted (refs.get binding).field = some candidate)
    (leftValid : left.application.candidates.lookup candidate = .openable ⟨payload, leftValue⟩)
    (rightValid : right.application.candidates.lookup candidate = .openable ⟨payload, rightValue⟩)
    (roster : List Player) (selected : Option (Fin (roster.count owner)))
    (network : (runtime setup).NetworkPolicy leaks) (focal : Player)
    (leftRecall : left.InputRecall (application setup leaks))
    (rightRecall : right.InputRecall (application setup leaks))
    (leftSerials : left.network.SerialsBeforeNext)
    (rightSerials : right.network.SerialsBeforeNext)
    (leftPublished : left.network.Satisfies fun message =>
      message.id ∈ left.network.ledger.map Message.id)
    (rightPublished : right.network.Satisfies fun message =>
      message.id ∈ right.network.ledger.map Message.id)
    (messages : (application setup leaks).messageView left =
      (application setup leaks).messageView right)
    (recall : left.recall focal = right.recall focal)
    (same : (revealSuccessor published binding leftSource selected.isSome).view focal =
      (revealSuccessor published binding rightSource selected.isSome).view focal) :
    let app := application setup leaks
    let phase := (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
      (List.replicate (event.val + 1) .tick ++ [.expire event])
    ((runtime setup).runInteractionPlan leaks
      ((runtime setup).openingWindowPlayers leaks owner event candidate ⟨payload, leftValue⟩
        (left.recall owner).length selected) network phase left).map
        (fun final => (app.messageView final, final.recall focal)) =
    ((runtime setup).runInteractionPlan leaks
      ((runtime setup).openingWindowPlayers leaks owner event candidate ⟨payload, rightValue⟩
        (right.recall owner).length selected) network phase right).map
        (fun final => (app.messageView final, final.recall focal)) := by
  dsimp only
  have sourceView := reveal_view_reflects focal published binding leftSource rightSource
    selected.isSome selected.isSome same
  have networks := congrArg Prod.fst messages
  have leaked : left.network.leaked focal = right.network.leaked focal :=
    congrArg (fun net => net.leaked focal) networks
  have observed := leftCheckpoint.observe_eq rightCheckpoint focal leaked sourceView
  have nativeView : (application setup leaks).observePlayer left.application focal =
      (application setup leaks).observePlayer right.application focal :=
    congrArg ReactiveApplication.PlayerView.application observed
  have publicView : left.application.publicView = right.application.publicView :=
    congrArg ReactivePlayerView.publicView nativeView
  have privateView : (application setup leaks).observePlayer left.application focal =
      (application setup leaks).observePlayer right.application focal := nativeView
  have leftReady : left.application.config.cut.Ready event := by
    have inside : rank < (graph setup).order.eventCount := eventRank ▸ event.isLt
    have index : (⟨rank, inside⟩ : (graph setup).EventId) = event := Fin.ext eventRank.symm
    rw [← index]
    exact leftCheckpoint.ordered.ready inside
  have rightReady : right.application.config.cut.Ready event := by
    have inside : rank < (graph setup).order.eventCount := eventRank ▸ event.isLt
    have index : (⟨rank, inside⟩ : (graph setup).EventId) = event := Fin.ext eventRank.symm
    rw [← index]
    exact rightCheckpoint.ordered.ready inside
  cases selected with
  | none =>
      rw [no_opening_players setup leaks owner event candidate
        ⟨payload, rightValue⟩ ⟨payload, leftValue⟩ (right.recall owner).length]
      exact (runtime setup).openingWindow_expiry_coupling leaks owner event candidate
        ⟨payload, leftValue⟩ roster none network focal (event.val + 1) left right
          leftRecall rightRecall leftSerials rightSerials leftPublished rightPublished messages
            recall publicView privateView owned (by simp) (by simp) publicView
  | some slot =>
      have values : leftValue = rightValue := by
        have result := congrArg
          (fun view : DecisionView focal ((published, .publication payload) :: Γ) =>
            view.1.cells.get (HasVar.here : HasVar ((published, CellTy.publication payload) :: Γ)
              published (.publication payload))) same
        change (revealSuccessor published binding leftSource true).state.get .here =
          (revealSuccessor published binding rightSource true).state.get .here at result
        rw [revealSuccessor_result_of_registry_empty published binding leftSource
          leftCheckpoint.emptyRegistry true,
          revealSuccessor_result_of_registry_empty published binding rightSource
            rightCheckpoint.emptyRegistry true, leftOpen, rightOpen] at result
        exact PublicationResult.success.inj result
      subst rightValue
      have strategic : ((graph setup).actor? event).isSome = true := by rw [actor]; rfl
      have leftStored : (refs.get binding).get? left.application.config.store =
          some (.success leftValue) := by
        simpa only [leftOpen, cellValue] using leftCheckpoint.agrees binding
      have rightStored : (refs.get binding).get? right.application.config.store =
          some (.success leftValue) := by
        simpa only [rightOpen, cellValue] using rightCheckpoint.agrees binding
      have leftResolved : EventGraph.EventCode.resolveOutput? (refs.get binding) [] true
          left.application.config.store = some (.success leftValue) := by
        simp only [EventGraph.EventCode.resolveOutput?, leftStored,
          EventGraph.GuardCheck.allAccepted?, ↓reduceIte]
        rfl
      have rightResolved : EventGraph.EventCode.resolveOutput? (refs.get binding) [] true
          right.application.config.store = some (.success leftValue) := by
        simp only [EventGraph.EventCode.resolveOutput?, rightStored,
          EventGraph.GuardCheck.allAccepted?, ↓reduceIte]
        rfl
      have leftAccepted : ((runtime setup).reactiveApplication leaks).handle left.application
          ((runtime setup).windowEnvelope leaks owner event candidate ⟨payload, leftValue⟩ left) =
            some (left.application.complete event leftReady
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
              (cast (congrArg EventGraph.EventField.Value outputEq.symm)
                (PublicationResult.success leftValue))) :=
        (reactiveApplication_handle_of_tokenValid (runtime setup) leaks _ _
          ((runtime setup).windowEnvelope_tokenValid leaks owner event candidate _ left
            leftReady)).trans
        (handle_opening_eq (runtime setup) left.application
        (owner, left.network.nextSerial owner) event candidate
        owner payload (refs.get binding) [] outputEq codeEq node leftReady
          (leftCheckpoint.timely event eventRank strategic) rfl owned leftAssociated leftValue
            leftValid leftStored (.success leftValue) leftResolved)
      have rightAccepted : ((runtime setup).reactiveApplication leaks).handle right.application
          ((runtime setup).windowEnvelope leaks owner event candidate ⟨payload, leftValue⟩ right) =
            some (right.application.complete event rightReady
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
              (cast (congrArg EventGraph.EventField.Value outputEq.symm)
                (PublicationResult.success leftValue))) :=
        (reactiveApplication_handle_of_tokenValid (runtime setup) leaks _ _
          ((runtime setup).windowEnvelope_tokenValid leaks owner event candidate _ right
            rightReady)).trans
        (handle_opening_eq (runtime setup) right.application
        (owner, right.network.nextSerial owner) event candidate
        owner payload (refs.get binding) [] outputEq codeEq node rightReady
          (rightCheckpoint.timely event eventRank strategic) rfl owned rightAssociated leftValue
            rightValid rightStored (.success leftValue) rightResolved)
      have observationEq : (graph setup).playerObserve focal left.application.config =
          (graph setup).playerObserve focal right.application.config := by
        have fields := congrArg (fun view : ReactivePlayerView (graph setup) =>
          (view.observation.completionOrder, view.observation.store, view.observation.ownActions))
            nativeView
        apply EventGraph.PlayerObservation.ext (graph setup)
        · exact congrArg Prod.fst fields
        · exact congrArg (fun fields => fields.2.1) fields
        · exact congrArg (fun fields => fields.2.2) fields
      have completed := EventGraphRuntime.State.complete_playerView_congr
        left.application right.application focal publicView observationEq
          (by rw [leftCheckpoint.remembered, rightCheckpoint.remembered])
          (congrArg ReactivePlayerView.candidates nativeView) event leftReady rightReady
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (PublicationResult.success leftValue))
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (PublicationResult.success leftValue)) (fun _ => rfl) (fun _ => rfl)
      apply (runtime setup).openingWindow_expiry_coupling leaks owner event candidate
        ⟨payload, leftValue⟩ roster (some slot) network focal (event.val + 1) left right
          leftRecall rightRecall leftSerials rightSerials leftPublished rightPublished messages
            recall publicView privateView owned (fun _ => ⟨leftValid, rightValid⟩)
      · intro _
        rw [leftAccepted, rightAccepted]
        exact ⟨rfl, rfl⟩
      · simp only [Option.isSome_some, ↓reduceIte, leftAccepted, rightAccepted, Option.getD_some]
        exact congrArg EventGraphRuntime.PlayerView.publicView completed

end Vegas
