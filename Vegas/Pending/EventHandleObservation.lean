/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventCompletionObservation

/-! # Focal observation of focal-authored packet handling -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

private def focalWithholdingAction (state : State graph) (event : graph.EventId)
    (focal : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding focal payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload) : Bool :=
  match state.remembered event with
  | none => false
  | some remembered =>
      match cast (congrArg EventField.Action outputEq) remembered with
      | false => false
      | true =>
          if EventCode.resolveOutput? binding checks true
                (graph.playerStore focal state.config.store) =
              EventCode.resolveOutput? binding checks false
                (graph.playerStore focal state.config.store) then true else false

private theorem focalWithholdingAction_output (state : State graph)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload) :
    EventCode.resolveOutput? binding checks
        (focalWithholdingAction state event owner payload binding checks outputEq)
        state.config.store =
      EventCode.resolveOutput? binding checks false state.config.store := by
  cases remembered : state.remembered event with
  | none => simp [focalWithholdingAction, remembered]
  | some action =>
      cases actionEq : cast (congrArg EventField.Action outputEq) action with
      | false => simp [focalWithholdingAction, remembered, actionEq]
      | true =>
          simp only [focalWithholdingAction, remembered, actionEq]
          split
          · rename_i localEq
            exact (EventCode.resolveOutput?_playerStore (graph := graph) binding checks
                state.config.store true).symm.trans
              (localEq.trans (EventCode.resolveOutput?_playerStore (graph := graph) binding checks
                state.config.store false))
          · rfl

omit [DecidableEq Player] in
private theorem focalReadFields_cast {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {left right : EventField Player L}
    (same : left = right) (code : EventCode layout left) :
    (cast (congrArg (EventCode layout) same) code).readFields = code.readFields := by
  cases same
  rfl

omit [DecidableEq Player] in
private theorem focalResolveFalse_of_ready (state : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks) :
    EventCode.resolveOutput? binding checks false state.config.store = some .failure := by
  apply EventCode.resolveOutput?_false_eq_failure binding checks state.config.store
  intro field read
  apply state.config.read_available ready
  have readsEq : (graph.nodes event).readFields =
      insert binding.field (GuardCheck.listReadFields checks) := by
    calc
      (graph.nodes event).readFields =
          (cast (congrArg (EventCode graph.layout) outputEq)
            (graph.nodes event)).readFields :=
        (focalReadFields_cast outputEq (graph.nodes event)).symm
      _ = (EventCode.resolve owner payload binding checks).readFields :=
        congrArg EventCode.readFields codeEq
      _ = insert binding.field (GuardCheck.listReadFields checks) := rfl
  rw [readsEq]
  exact read

private def focalAcceptResolution (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (focal : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding focal payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (disclose : Bool) : Option (State graph) := do
  let result ← EventCode.resolveOutput? binding checks disclose state.config.store
  pure (state.complete event ready
    (cast (congrArg EventField.Action outputEq.symm) disclose)
    (cast (congrArg EventField.Value outputEq.symm) result))

omit [IExpr.ResultTypes L] in
private theorem Raw.eq_mk_of_as?_eq_some (raw : Raw L) (payload : L.Ty)
    (value : L.Val payload) (decoded : raw.as? payload = some value) :
    raw = ⟨payload, value⟩ := by
  rcases raw with ⟨rawPayload, rawValue⟩
  unfold Raw.as? at decoded
  split at decoded
  · rename_i same
    cases same
    simp only [Option.some.injEq] at decoded
    cases decoded
    rfl
  · contradiction

/-- Handling the same focal-authored packet has the same focal observation in
two states with equal focal views. Foreign candidate meanings, remembered
actions, binding values, and supplied graph actions need not agree. -/
theorem handle_playerView_congr_of_sender
    (runtime : EventGraphRuntime graph) (left right : State graph) (focal : Player)
    (message : Message Player (Payload graph))
    (views : left.playerView focal = right.playerView focal)
    (sender : message.sender = focal) :
    Option.map (fun state => state.playerView focal) (handle runtime left message) =
      Option.map (fun state => state.playerView focal) (handle runtime right message) := by
  have publicEq : left.publicView = right.publicView :=
    congrArg PlayerView.publicView views
  have observationEq : graph.playerObserve focal left.config =
      graph.playerObserve focal right.config := by
    have observed := congrArg
      (fun view : PlayerView graph =>
        (view.observation.completionOrder, view.observation.store,
          view.observation.ownActions)) views
    apply PlayerObservation.ext graph
    · exact congrArg Prod.fst observed
    · exact congrArg (fun value => value.2.1) observed
    · exact congrArg (fun value => value.2.2) observed
  have rememberedEq : (fun event => if graph.actor? event = some focal then
      left.remembered event else none) =
    fun event => if graph.actor? event = some focal then right.remembered event else none :=
    congrArg PlayerView.remembered views
  have candidatesEq : (fun slot => left.candidates.lookup (focal, slot)) =
      fun slot => right.candidates.lookup (focal, slot) :=
    congrArg PlayerView.candidates views
  have acceptedEq : left.accepted = right.accepted :=
    congrArg PublicView.accepted publicEq
  have clockEq : left.clock = right.clock := congrArg PublicView.clock publicEq
  have activatedEq : left.activatedAt = right.activatedAt :=
    congrArg PublicView.activatedAt publicEq
  have orderEq : left.config.history.map Completion.event =
      right.config.history.map Completion.event :=
    congrArg PlayerObservation.completionOrder observationEq
  have cutEq : left.config.cut = right.config.cut :=
    cut_eq_of_completionOrder_eq left.config right.config orderEq
  have playerStoreEq : graph.playerStore focal left.config.store =
      graph.playerStore focal right.config.store :=
    congrArg PlayerObservation.store observationEq
  rcases message with ⟨id, packet⟩
  change id.1 = focal at sender
  cases packet with
  | malformed raw => simp [handle]
  | commitment event candidate =>
      by_cases leftReady : left.config.cut.Ready event
      · have rightReady : right.config.cut.Ready event := by simpa [← cutEq] using leftReady
        by_cases leftTimely : left.WithinDeadline runtime event
        · have rightTimely : right.WithinDeadline runtime event := by
            unfold State.WithinDeadline at leftTimely ⊢
            rw [← activatedEq, ← clockEq]
            exact leftTimely
          cases viewNode : nodeView graph event with
          | resolve owner payload binding checks outputEq codeEq =>
              simp [handle, leftReady, rightReady, leftTimely, rightTimely, viewNode]
          | sample payload law outputEq codeEq =>
              simp [handle, leftReady, rightReady, leftTimely, rightTimely, viewNode]
          | bind owner payload outputEq codeEq =>
              by_cases senderOwner : id.1 = owner
              · have ownerEq : owner = focal := senderOwner.symm.trans sender
                cases ownerEq
                by_cases handleOwner : candidate.1 = focal
                · rcases candidate with ⟨candidateOwner, slot⟩
                  change candidateOwner = focal at handleOwner
                  subst candidateOwner
                  by_cases vacant : left.accepted (.inr event) = none
                  · have rightVacant : right.accepted (.inr event) = none := by
                      rw [← acceptedEq]
                      exact vacant
                    by_cases unused : left.HandleUnused (focal, slot)
                    · have rightUnused : right.HandleUnused (focal, slot) := by
                        intro field
                        rw [← acceptedEq]
                        exact unused field
                      have resultEq : left.bindingResult (focal, slot) payload =
                          right.bindingResult (focal, slot) payload := by
                        unfold State.bindingResult
                        rw [congrFun candidatesEq slot]
                      let leftResult := left.bindingResult (focal, slot) payload
                      let rightResult := right.bindingResult (focal, slot) payload
                      let leftAction : graph.Action event :=
                        cast (congrArg EventField.Action outputEq.symm) leftResult
                      let rightAction : graph.Action event :=
                        cast (congrArg EventField.Action outputEq.symm) rightResult
                      let leftValue : (graph.outputLayout event).Value :=
                        cast (congrArg EventField.Value outputEq.symm) leftResult
                      let rightValue : (graph.outputLayout event).Value :=
                        cast (congrArg EventField.Value outputEq.symm) rightResult
                      have actionEq : leftAction = rightAction := by
                        dsimp only [leftAction, rightAction, leftResult, rightResult]
                        rw [resultEq]
                      have valueEq : leftValue = rightValue := by
                        dsimp only [leftValue, rightValue, leftResult, rightResult]
                        rw [resultEq]
                      have completed := State.complete_playerView_congr left right focal
                        publicEq observationEq rememberedEq candidatesEq event leftReady
                        rightReady leftAction rightAction leftValue rightValue
                        (fun _ => valueEq) (fun _ => actionEq)
                      have accepted := State.acceptHandle_playerView_congr
                        (left.complete event leftReady leftAction leftValue)
                        (right.complete event rightReady rightAction rightValue) focal completed
                        (.inr event) (focal, slot)
                      rw [handle_commitment_eq runtime left id event (focal, slot) focal payload
                          outputEq codeEq viewNode leftReady leftTimely senderOwner rfl vacant
                          unused,
                        handle_commitment_eq runtime right id event (focal, slot) focal payload
                          outputEq codeEq viewNode rightReady rightTimely senderOwner rfl
                          rightVacant rightUnused]
                      exact congrArg some accepted
                    · have rightUsed : ¬right.HandleUnused (focal, slot) := by
                        intro rightUnused
                        apply unused
                        intro field
                        rw [acceptedEq]
                        exact rightUnused field
                      simp [handle, Message.sender, leftReady, rightReady, leftTimely,
                        rightTimely, viewNode, senderOwner, vacant, rightVacant, unused, rightUsed]
                  · have rightOccupied : right.accepted (.inr event) ≠ none := by
                      rw [← acceptedEq]
                      exact vacant
                    simp [handle, Message.sender, leftReady, rightReady, leftTimely,
                      rightTimely, viewNode, senderOwner, vacant, rightOccupied]
                · simp [handle, Message.sender, leftReady, rightReady, leftTimely,
                    rightTimely, viewNode, senderOwner, handleOwner]
              · simp [handle, Message.sender, leftReady, rightReady, leftTimely,
                  rightTimely, viewNode, senderOwner]
        · have rightLate : ¬right.WithinDeadline runtime event := by
            intro rightTimely
            apply leftTimely
            unfold State.WithinDeadline at rightTimely ⊢
            rw [activatedEq, clockEq]
            exact rightTimely
          simp [handle, leftReady, rightReady, leftTimely, rightLate]
      · have rightNotReady : ¬right.config.cut.Ready event := by simpa [← cutEq] using leftReady
        simp [handle, leftReady, rightNotReady]
  | opening event candidate raw =>
      by_cases leftReady : left.config.cut.Ready event
      · have rightReady : right.config.cut.Ready event := by simpa [← cutEq] using leftReady
        by_cases leftTimely : left.WithinDeadline runtime event
        · have rightTimely : right.WithinDeadline runtime event := by
            unfold State.WithinDeadline at leftTimely ⊢
            rw [← activatedEq, ← clockEq]
            exact leftTimely
          cases viewNode : nodeView graph event with
          | bind owner payload outputEq codeEq =>
              simp [handle, leftReady, rightReady, leftTimely, rightTimely, viewNode]
          | sample payload law outputEq codeEq =>
              simp [handle, leftReady, rightReady, leftTimely, rightTimely, viewNode]
          | resolve owner payload binding checks outputEq codeEq =>
              by_cases senderOwner : id.1 = owner
              · have ownerEq : owner = focal := senderOwner.symm.trans sender
                cases ownerEq
                by_cases handleOwner : candidate.1 = focal
                · rcases candidate with ⟨candidateOwner, slot⟩
                  change candidateOwner = focal at handleOwner
                  subst candidateOwner
                  by_cases associated : left.accepted binding.field = some (focal, slot)
                  · have rightAssociated : right.accepted binding.field = some (focal, slot) := by
                      rw [← acceptedEq]
                      exact associated
                    have lookupEq : left.candidates.lookup (focal, slot) =
                        right.candidates.lookup (focal, slot) := congrFun candidatesEq slot
                    have verifyEq : left.candidates.verify (focal, slot) raw =
                        right.candidates.verify (focal, slot) raw := by
                      unfold CommitmentCandidates.verify
                      rw [lookupEq]
                    by_cases verified : left.candidates.verify (focal, slot) raw = true
                    · have rightVerified : right.candidates.verify (focal, slot) raw = true := by
                        rw [← verifyEq]
                        exact verified
                      cases typed : raw.as? payload with
                      | none =>
                          simp only [handle, dif_pos leftReady, dif_pos rightReady,
                            dif_pos leftTimely, dif_pos rightTimely, viewNode, Message.sender,
                            senderOwner, dif_pos, associated, rightAssociated, verified,
                            rightVerified]
                          rw [typed]
                      | some value =>
                          have rawEq := Raw.eq_mk_of_as?_eq_some raw payload value typed
                          subst raw
                          have storedEq : binding.get? left.config.store =
                              binding.get? right.config.store := by
                            calc
                              binding.get? left.config.store =
                                  binding.get? (graph.playerStore focal left.config.store) :=
                                (binding.get?_playerStore focal left.config.store rfl).symm
                              _ = binding.get? (graph.playerStore focal right.config.store) :=
                                congrArg binding.get? playerStoreEq
                              _ = binding.get? right.config.store :=
                                binding.get?_playerStore focal right.config.store rfl
                          by_cases stored : binding.get? left.config.store =
                              some (.success value)
                          · have rightStored : binding.get? right.config.store =
                                some (.success value) := by rw [← storedEq]; exact stored
                            have resolvedEq : EventCode.resolveOutput? binding checks true
                                left.config.store =
                              EventCode.resolveOutput? binding checks true
                                right.config.store := by
                              calc
                                _ = EventCode.resolveOutput? binding checks true
                                    (graph.playerStore focal left.config.store) :=
                                  (EventCode.resolveOutput?_playerStore binding checks
                                    left.config.store true).symm
                                _ = EventCode.resolveOutput? binding checks true
                                    (graph.playerStore focal right.config.store) := by
                                  rw [playerStoreEq]
                                _ = _ := EventCode.resolveOutput?_playerStore binding checks
                                  right.config.store true
                            cases leftResolved : EventCode.resolveOutput? binding checks true
                                left.config.store with
                            | none =>
                                have rightResolved : EventCode.resolveOutput? binding checks true
                                    right.config.store = none := by
                                  rw [← resolvedEq]
                                  exact leftResolved
                                simp only [handle, dif_pos leftReady, dif_pos rightReady,
                                  dif_pos leftTimely, dif_pos rightTimely, viewNode,
                                  Message.sender, senderOwner, dif_pos, associated,
                                  rightAssociated, verified, rightVerified, stored, rightStored]
                                rw [typed]
                                dsimp only
                                rw [dif_pos rfl]
                                rw [dif_pos rfl]
                                change Option.map (fun state => state.playerView focal)
                                    (focalAcceptResolution left event leftReady focal payload
                                      binding checks outputEq true) =
                                  Option.map (fun state => state.playerView focal)
                                    (focalAcceptResolution right event rightReady focal payload
                                      binding checks outputEq true)
                                simp [focalAcceptResolution, leftResolved, rightResolved]
                            | some result =>
                                have rightResolved : EventCode.resolveOutput? binding checks true
                                    right.config.store = some result := by
                                  rw [← resolvedEq]
                                  exact leftResolved
                                let action : graph.Action event :=
                                  cast (congrArg EventField.Action outputEq.symm) true
                                let resultValue : (graph.outputLayout event).Value :=
                                  cast (congrArg EventField.Value outputEq.symm) result
                                have completed := State.complete_playerView_congr left right focal
                                  publicEq observationEq rememberedEq candidatesEq event leftReady
                                  rightReady action action resultValue resultValue
                                  (fun _ => rfl) (fun _ => rfl)
                                rw [handle_opening_eq runtime left id event (focal, slot) focal
                                    payload binding checks outputEq codeEq viewNode leftReady
                                    leftTimely senderOwner rfl associated value
                                    ((CommitmentCandidates.verify_eq_true_iff _ _ _).mp verified)
                                    stored result leftResolved,
                                  handle_opening_eq runtime right id event (focal, slot) focal
                                    payload binding checks outputEq codeEq viewNode rightReady
                                    rightTimely senderOwner rfl rightAssociated value
                                    ((CommitmentCandidates.verify_eq_true_iff _ _ _).mp
                                      rightVerified) rightStored result rightResolved]
                                exact congrArg some completed
                          · have rightNotStored : binding.get? right.config.store ≠
                                some (.success value) := by
                              intro rightStored
                              apply stored
                              rw [storedEq]
                              exact rightStored
                            simp only [handle, dif_pos leftReady, dif_pos rightReady,
                              dif_pos leftTimely, dif_pos rightTimely, viewNode, Message.sender,
                              senderOwner, dif_pos, associated, rightAssociated, verified,
                              rightVerified]
                            rw [typed]
                            simp [stored, rightNotStored]
                    · have rightUnverified :
                          right.candidates.verify (focal, slot) raw ≠ true := by
                        intro rightVerified
                        apply verified
                        rw [verifyEq]
                        exact rightVerified
                      simp [handle, Message.sender, leftReady, rightReady, leftTimely,
                        rightTimely, viewNode, senderOwner, associated, rightAssociated, verified,
                        rightUnverified]
                  · have rightUnassociated :
                        right.accepted binding.field ≠ some (focal, slot) := by
                      intro rightAssociated
                      apply associated
                      rw [acceptedEq]
                      exact rightAssociated
                    simp [handle, Message.sender, leftReady, rightReady, leftTimely,
                      rightTimely, viewNode, senderOwner, associated, rightUnassociated]
                · simp [handle, Message.sender, leftReady, rightReady, leftTimely,
                    rightTimely, viewNode, senderOwner, handleOwner]
              · simp [handle, Message.sender, leftReady, rightReady, leftTimely,
                  rightTimely, viewNode, senderOwner]
        · have rightLate : ¬right.WithinDeadline runtime event := by
            intro rightTimely
            apply leftTimely
            unfold State.WithinDeadline at rightTimely ⊢
            rw [activatedEq, clockEq]
            exact rightTimely
          simp [handle, leftReady, rightReady, leftTimely, rightLate]
      · have rightNotReady : ¬right.config.cut.Ready event := by simpa [← cutEq] using leftReady
        simp [handle, leftReady, rightNotReady]
  | withhold event =>
      by_cases leftReady : left.config.cut.Ready event
      · have rightReady : right.config.cut.Ready event := by simpa [← cutEq] using leftReady
        by_cases leftTimely : left.WithinDeadline runtime event
        · have rightTimely : right.WithinDeadline runtime event := by
            unfold State.WithinDeadline at leftTimely ⊢
            rw [← activatedEq, ← clockEq]
            exact leftTimely
          cases viewNode : nodeView graph event with
          | bind owner payload outputEq codeEq =>
              simp [handle, leftReady, rightReady, leftTimely, rightTimely, viewNode]
          | sample payload law outputEq codeEq =>
              simp [handle, leftReady, rightReady, leftTimely, rightTimely, viewNode]
          | resolve owner payload binding checks outputEq codeEq =>
              by_cases senderOwner : id.1 = owner
              · have ownerEq : owner = focal := senderOwner.symm.trans sender
                cases ownerEq
                have actor : graph.actor? event = some focal := by
                  change EventCode.actor (graph.nodes event) = some focal
                  calc
                    EventCode.actor (graph.nodes event) = EventCode.actor
                        (cast (congrArg (EventCode graph.layout) outputEq)
                          (graph.nodes event)) :=
                      (EventCode.actor_cast outputEq (graph.nodes event)).symm
                    _ = some focal := by rw [codeEq]; rfl
                have memoryEq : left.remembered event = right.remembered event := by
                  have atEvent := congrFun rememberedEq event
                  simpa [actor] using atEvent
                have discloseEq :
                    focalWithholdingAction left event focal payload binding checks outputEq =
                      focalWithholdingAction right event focal payload binding checks outputEq := by
                  unfold focalWithholdingAction
                  rw [memoryEq, playerStoreEq]
                let disclose := focalWithholdingAction left event focal payload binding checks
                  outputEq
                have resolvedEq : EventCode.resolveOutput? binding checks disclose
                      left.config.store =
                    EventCode.resolveOutput? binding checks disclose right.config.store := by
                  calc
                    _ = EventCode.resolveOutput? binding checks disclose
                        (graph.playerStore focal left.config.store) :=
                      (EventCode.resolveOutput?_playerStore binding checks left.config.store
                        disclose).symm
                    _ = EventCode.resolveOutput? binding checks disclose
                        (graph.playerStore focal right.config.store) := by rw [playerStoreEq]
                    _ = _ := EventCode.resolveOutput?_playerStore binding checks
                      right.config.store disclose
                cases leftResolved : EventCode.resolveOutput? binding checks disclose
                    left.config.store with
                | none =>
                    have rightResolved : EventCode.resolveOutput? binding checks disclose
                        right.config.store = none := by rw [← resolvedEq]; exact leftResolved
                    simp only [handle, dif_pos leftReady, dif_pos rightReady,
                      dif_pos leftTimely, dif_pos rightTimely, viewNode, Message.sender,
                      senderOwner, dif_pos]
                    change Option.map (fun state => state.playerView focal)
                        (focalAcceptResolution left event leftReady focal payload binding checks
                          outputEq (focalWithholdingAction left event focal payload binding checks
                            outputEq)) =
                      Option.map (fun state => state.playerView focal)
                        (focalAcceptResolution right event rightReady focal payload binding checks
                          outputEq (focalWithholdingAction right event focal payload binding checks
                            outputEq))
                    rw [← discloseEq]
                    change Option.map (fun state => state.playerView focal)
                        (focalAcceptResolution left event leftReady focal payload binding checks
                          outputEq disclose) =
                      Option.map (fun state => state.playerView focal)
                        (focalAcceptResolution right event rightReady focal payload binding checks
                          outputEq disclose)
                    simp [focalAcceptResolution, leftResolved, rightResolved]
                | some result =>
                    have rightResolved : EventCode.resolveOutput? binding checks disclose
                        right.config.store = some result := by rw [← resolvedEq]; exact leftResolved
                    let action : graph.Action event :=
                      cast (congrArg EventField.Action outputEq.symm) disclose
                    let resultValue : (graph.outputLayout event).Value :=
                      cast (congrArg EventField.Value outputEq.symm) result
                    have completed := State.complete_playerView_congr left right focal publicEq
                      observationEq rememberedEq candidatesEq event leftReady rightReady action
                      action resultValue resultValue (fun _ => rfl) (fun _ => rfl)
                    simp only [handle, dif_pos leftReady, dif_pos rightReady,
                      dif_pos leftTimely, dif_pos rightTimely, viewNode, Message.sender,
                      senderOwner, dif_pos]
                    change Option.map (fun state => state.playerView focal)
                        (focalAcceptResolution left event leftReady focal payload binding checks
                          outputEq (focalWithholdingAction left event focal payload binding checks
                            outputEq)) =
                      Option.map (fun state => state.playerView focal)
                        (focalAcceptResolution right event rightReady focal payload binding checks
                          outputEq (focalWithholdingAction right event focal payload binding checks
                            outputEq))
                    rw [← discloseEq]
                    change Option.map (fun state => state.playerView focal)
                        (focalAcceptResolution left event leftReady focal payload binding checks
                          outputEq disclose) =
                      Option.map (fun state => state.playerView focal)
                        (focalAcceptResolution right event rightReady focal payload binding checks
                          outputEq disclose)
                    simp only [focalAcceptResolution, leftResolved, rightResolved, bind, pure,
                      Option.bind_some, Option.map_some]
                    exact congrArg some completed
              · simp [handle, Message.sender, leftReady, rightReady, leftTimely,
                  rightTimely, viewNode, senderOwner]
        · have rightLate : ¬right.WithinDeadline runtime event := by
            intro rightTimely
            apply leftTimely
            unfold State.WithinDeadline at rightTimely ⊢
            rw [activatedEq, clockEq]
            exact rightTimely
          simp [handle, leftReady, rightReady, leftTimely, rightLate]
      · have rightNotReady : ¬right.config.cut.Ready event := by simpa [← cutEq] using leftReady
        simp [handle, leftReady, rightNotReady]

/-- Commitment packets have the same acceptance status and focal result under
equal focal views, regardless of their sender.  A foreign binding result may
differ semantically, but both its value and its action are hidden from the
focal observer. -/
theorem handle_commitment_playerView_congr
    (runtime : EventGraphRuntime graph) (left right : State graph) (focal : Player)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (views : left.playerView focal = right.playerView focal) :
    Option.map (fun state => state.playerView focal)
        (handle runtime left ⟨id, .commitment event candidate⟩) =
      Option.map (fun state => state.playerView focal)
        (handle runtime right ⟨id, .commitment event candidate⟩) := by
  by_cases senderFocal : id.1 = focal
  · apply handle_playerView_congr_of_sender runtime left right focal
      ⟨id, .commitment event candidate⟩ views
    exact senderFocal
  have publicEq : left.publicView = right.publicView :=
    congrArg PlayerView.publicView views
  have observationEq : graph.playerObserve focal left.config =
      graph.playerObserve focal right.config := by
    have observed := congrArg
      (fun view : PlayerView graph =>
        (view.observation.completionOrder, view.observation.store,
          view.observation.ownActions)) views
    apply PlayerObservation.ext graph
    · exact congrArg Prod.fst observed
    · exact congrArg (fun value => value.2.1) observed
    · exact congrArg (fun value => value.2.2) observed
  have rememberedEq := congrArg PlayerView.remembered views
  have candidatesEq := congrArg PlayerView.candidates views
  have acceptedEq : left.accepted = right.accepted :=
    congrArg PublicView.accepted publicEq
  have clockEq : left.clock = right.clock := congrArg PublicView.clock publicEq
  have activatedEq : left.activatedAt = right.activatedAt :=
    congrArg PublicView.activatedAt publicEq
  have cutEq : left.config.cut = right.config.cut :=
    cut_eq_of_completionOrder_eq left.config right.config
      (congrArg PlayerObservation.completionOrder observationEq)
  by_cases leftReady : left.config.cut.Ready event
  · have rightReady : right.config.cut.Ready event := by simpa [← cutEq] using leftReady
    by_cases leftTimely : left.WithinDeadline runtime event
    · have rightTimely : right.WithinDeadline runtime event := by
        unfold State.WithinDeadline at leftTimely ⊢
        rw [← activatedEq, ← clockEq]
        exact leftTimely
      cases viewNode : nodeView graph event with
      | resolve owner payload binding checks outputEq codeEq =>
          simp [handle, leftReady, rightReady, leftTimely, rightTimely, viewNode]
      | sample payload law outputEq codeEq =>
          simp [handle, leftReady, rightReady, leftTimely, rightTimely, viewNode]
      | bind owner payload outputEq codeEq =>
          by_cases senderOwner : id.1 = owner
          · have ownerForeign : owner ≠ focal := by
              intro same
              apply senderFocal
              rw [senderOwner, same]
            by_cases handleOwner : candidate.1 = owner
            · by_cases vacant : left.accepted (.inr event) = none
              · have rightVacant : right.accepted (.inr event) = none := by
                  rw [← acceptedEq]
                  exact vacant
                by_cases unused : left.HandleUnused candidate
                · have rightUnused : right.HandleUnused candidate := by
                    intro field
                    rw [← acceptedEq]
                    exact unused field
                  let leftResult := left.bindingResult candidate payload
                  let rightResult := right.bindingResult candidate payload
                  let leftAction : graph.Action event :=
                    cast (congrArg EventField.Action outputEq.symm) leftResult
                  let rightAction : graph.Action event :=
                    cast (congrArg EventField.Action outputEq.symm) rightResult
                  let leftValue : (graph.outputLayout event).Value :=
                    cast (congrArg EventField.Value outputEq.symm) leftResult
                  let rightValue : (graph.outputLayout event).Value :=
                    cast (congrArg EventField.Value outputEq.symm) rightResult
                  have completed := State.complete_playerView_congr left right focal
                    publicEq observationEq rememberedEq candidatesEq event leftReady rightReady
                    leftAction rightAction leftValue rightValue (by
                      intro visible
                      exfalso
                      apply ownerForeign
                      unfold EventGraph.fieldVisibleTo at visible
                      change (graph.outputLayout event).VisibleTo focal at visible
                      rw [outputEq] at visible
                      simpa [EventField.VisibleTo] using visible) (by
                      intro focalActor
                      have ownerActor : graph.actor? event = some owner := by
                        change EventCode.actor (graph.nodes event) = some owner
                        calc
                          EventCode.actor (graph.nodes event) = EventCode.actor
                              (cast (congrArg (EventCode graph.layout) outputEq)
                                (graph.nodes event)) :=
                            (EventCode.actor_cast outputEq (graph.nodes event)).symm
                          _ = some owner := by rw [codeEq]; rfl
                      exact False.elim (ownerForeign
                        (Option.some.inj (ownerActor.symm.trans focalActor))))
                  have accepted := State.acceptHandle_playerView_congr
                    (left.complete event leftReady leftAction leftValue)
                    (right.complete event rightReady rightAction rightValue) focal completed
                    (.inr event) candidate
                  rw [handle_commitment_eq runtime left id event candidate owner payload
                        outputEq codeEq viewNode leftReady leftTimely senderOwner handleOwner
                        vacant unused,
                    handle_commitment_eq runtime right id event candidate owner payload
                        outputEq codeEq viewNode rightReady rightTimely senderOwner handleOwner
                        rightVacant rightUnused]
                  exact congrArg some accepted
                · have rightUsed : ¬right.HandleUnused candidate := by
                    intro rightUnused
                    apply unused
                    intro field
                    rw [acceptedEq]
                    exact rightUnused field
                  simp [handle, Message.sender, leftReady, rightReady, leftTimely,
                    rightTimely, viewNode, senderOwner, handleOwner, vacant, rightVacant,
                    unused, rightUsed]
              · have rightOccupied : right.accepted (.inr event) ≠ none := by
                  rw [← acceptedEq]
                  exact vacant
                simp [handle, Message.sender, leftReady, rightReady, leftTimely,
                  rightTimely, viewNode, senderOwner, handleOwner, vacant, rightOccupied]
            · simp [handle, Message.sender, leftReady, rightReady, leftTimely,
                rightTimely, viewNode, senderOwner, handleOwner]
          · simp [handle, Message.sender, leftReady, rightReady, leftTimely,
              rightTimely, viewNode, senderOwner]
    · have rightLate : ¬right.WithinDeadline runtime event := by
        intro rightTimely
        apply leftTimely
        unfold State.WithinDeadline at rightTimely ⊢
        rw [activatedEq, clockEq]
        exact rightTimely
      simp [handle, leftReady, rightReady, leftTimely, rightLate]
  · have rightNotReady : ¬right.config.cut.Ready event := by simpa [← cutEq] using leftReady
    simp [handle, leftReady, rightNotReady]

/-- A foreign-authored withholding packet has the same acceptance status and
focal result under equal focal views.  The private cached decisions may differ:
the withholding rule maps either decision to the canonical public failure,
while the foreign action itself is hidden from `focal`. -/
theorem handle_withhold_playerView_congr_of_sender_ne
    (runtime : EventGraphRuntime graph) (left right : State graph) (focal : Player)
    (id : MessageId Player) (event : graph.EventId)
    (views : left.playerView focal = right.playerView focal)
    (senderForeign : id.1 ≠ focal) :
    Option.map (fun state => state.playerView focal)
        (handle runtime left ⟨id, .withhold event⟩) =
      Option.map (fun state => state.playerView focal)
        (handle runtime right ⟨id, .withhold event⟩) := by
  have publicEq : left.publicView = right.publicView :=
    congrArg PlayerView.publicView views
  have observationEq : graph.playerObserve focal left.config =
      graph.playerObserve focal right.config := by
    have observed := congrArg
      (fun view : PlayerView graph =>
        (view.observation.completionOrder, view.observation.store,
          view.observation.ownActions)) views
    apply PlayerObservation.ext graph
    · exact congrArg Prod.fst observed
    · exact congrArg (fun value => value.2.1) observed
    · exact congrArg (fun value => value.2.2) observed
  have rememberedEq := congrArg PlayerView.remembered views
  have candidatesEq := congrArg PlayerView.candidates views
  have clockEq : left.clock = right.clock := congrArg PublicView.clock publicEq
  have activatedEq : left.activatedAt = right.activatedAt :=
    congrArg PublicView.activatedAt publicEq
  have cutEq : left.config.cut = right.config.cut :=
    cut_eq_of_completionOrder_eq left.config right.config
      (congrArg PlayerObservation.completionOrder observationEq)
  by_cases leftReady : left.config.cut.Ready event
  · have rightReady : right.config.cut.Ready event := by simpa [← cutEq] using leftReady
    by_cases leftTimely : left.WithinDeadline runtime event
    · have rightTimely : right.WithinDeadline runtime event := by
        unfold State.WithinDeadline at leftTimely ⊢
        rw [← activatedEq, ← clockEq]
        exact leftTimely
      cases viewNode : nodeView graph event with
      | bind owner payload outputEq codeEq =>
          simp [handle, leftReady, rightReady, leftTimely, rightTimely, viewNode]
      | sample payload law outputEq codeEq =>
          simp [handle, leftReady, rightReady, leftTimely, rightTimely, viewNode]
      | resolve owner payload binding checks outputEq codeEq =>
          by_cases senderOwner : id.1 = owner
          · have ownerForeign : owner ≠ focal := by
              intro same
              apply senderForeign
              rw [senderOwner, same]
            have ownerActor : graph.actor? event = some owner := by
              change EventCode.actor (graph.nodes event) = some owner
              calc
                EventCode.actor (graph.nodes event) = EventCode.actor
                    (cast (congrArg (EventCode graph.layout) outputEq)
                      (graph.nodes event)) :=
                  (EventCode.actor_cast outputEq (graph.nodes event)).symm
                _ = some owner := by rw [codeEq]; rfl
            let leftDisclose := focalWithholdingAction left event owner payload binding checks
              outputEq
            let rightDisclose := focalWithholdingAction right event owner payload binding checks
              outputEq
            have leftFalse := focalResolveFalse_of_ready left event leftReady
              owner payload binding checks outputEq codeEq
            have rightFalse := focalResolveFalse_of_ready right event rightReady
              owner payload binding checks outputEq codeEq
            have leftResolved : EventCode.resolveOutput? binding checks leftDisclose
                left.config.store = some .failure := by
              exact (focalWithholdingAction_output left event owner payload binding checks
                outputEq).trans leftFalse
            have rightResolved : EventCode.resolveOutput? binding checks rightDisclose
                right.config.store = some .failure := by
              exact (focalWithholdingAction_output right event owner payload binding checks
                outputEq).trans rightFalse
            let leftAction : graph.Action event :=
              cast (congrArg EventField.Action outputEq.symm) leftDisclose
            let rightAction : graph.Action event :=
              cast (congrArg EventField.Action outputEq.symm) rightDisclose
            let failedValue : (graph.outputLayout event).Value :=
              cast (congrArg EventField.Value outputEq.symm)
                (PublicationResult.failure : PublicationResult (L.Val payload))
            have completed := State.complete_playerView_congr left right focal publicEq
              observationEq rememberedEq candidatesEq event leftReady rightReady leftAction
              rightAction failedValue failedValue (fun _ => rfl) (by
                intro focalActor
                exact False.elim (ownerForeign
                  (Option.some.inj (ownerActor.symm.trans focalActor))))
            simp only [handle, dif_pos leftReady, dif_pos rightReady,
              dif_pos leftTimely, dif_pos rightTimely, viewNode, Message.sender,
              senderOwner, dif_pos]
            change Option.map (fun state => state.playerView focal)
                (focalAcceptResolution left event leftReady owner payload binding checks
                  outputEq leftDisclose) =
              Option.map (fun state => state.playerView focal)
                (focalAcceptResolution right event rightReady owner payload binding checks
                  outputEq rightDisclose)
            simp only [focalAcceptResolution, leftResolved, rightResolved, bind, pure,
              Option.bind_some, Option.map_some]
            exact congrArg some completed
          · simp [handle, Message.sender, leftReady, rightReady, leftTimely,
              rightTimely, viewNode, senderOwner]
    · have rightLate : ¬right.WithinDeadline runtime event := by
        intro rightTimely
        apply leftTimely
        unfold State.WithinDeadline at rightTimely ⊢
        rw [activatedEq, clockEq]
        exact rightTimely
      simp [handle, leftReady, rightReady, leftTimely, rightLate]
  · have rightNotReady : ¬right.config.cut.Ready event := by simpa [← cutEq] using leftReady
    simp [handle, leftReady, rightNotReady]

/-- Malformed traffic is rejected independently of all application state. -/
@[simp] theorem handle_malformed_playerView_congr
    (runtime : EventGraphRuntime graph) (left right : State graph) (focal : Player)
    (id : MessageId Player) (raw : Raw L) :
    Option.map (fun state => state.playerView focal)
        (handle runtime left ⟨id, .malformed raw⟩) =
      Option.map (fun state => state.playerView focal)
        (handle runtime right ⟨id, .malformed raw⟩) := by
  simp [handle]

end Vegas.EventGraphRuntime
