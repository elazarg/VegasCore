/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCheckpoint
import Vegas.Game.SourceServiceDisclosure
import Vegas.Pending.ReactiveDisclosure
import Vegas.Pending.ReactiveRevealResponse

/-! # Guarded source resolution through protected inclusion and expiry

The source choice is effective exactly when it can produce a successful
guarded opening. Withholding executes the actual inclusion wait and deadline
expiry. These equations permit dynamically allocated bindings and deferred
guards. They preserve the full source configuration checkpoint; they do not
identify original private intentions that disclosure normalization aggregates.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The existing service realizes an effective source choice, including its
private completed action, with no assumption that all source guards succeed. -/
theorem guarded_reveal_service
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (valid : execution.application.BindingInvariant)
    (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations binding))
    (node : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (entered ticks : Nat) (activated : execution.application.activatedAt event = some entered)
    (due : (runtime setup).deadline event ≤ execution.application.clock + ticks - entered)
    (pending : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (disclose : Bool)
    (effective : effectiveDisclosure published binding source disclose = disclose) :
    let response := (runtime setup).serviceDecision leaks owner (execution.recall owner)
      (execution.observe (application setup leaks) owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
    ((runtime setup).runInteractionPlan leaks players network
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
        (execution.respond (application setup leaks) owner response)).map
      (fun final => (final.application.config, final.receipts)) =
      FinDist.pure
        (execution.application.config.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (disclosureResult published binding source disclose)),
          if disclose then execution.receipts ++
            [((owner, execution.network.nextSerial owner), true)] else execution.receipts) := by
  intro response
  let app := application setup leaks
  cases disclose with
  | false =>
      have silent : response = ⟨none⟩ := by
        simp only [response, serviceDecision, reactiveDecision, node, reactiveResolutionPacket,
          cast_cast, cast_eq, Bool.false_eq_true, ↓reduceIte,
          disclosureSubmission_normalize_withhold]
        rfl
      let submitted := execution.respond app owner ⟨none⟩
      let waited : app.Execution := { submitted with
        environmentRecall := submitted.environmentRecall ++
          [⟨submitted.observeEnvironment app, .wait⟩] }
      have included : (runtime setup).interactionStep leaks players network
          (.includeLatest event owner) submitted = FinDist.pure waited := by
        rw [(runtime setup).interaction_includeLatest_of_pending_published leaks players network
          submitted owner event pending]
        simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
        rfl
      obtain ⟨final, law, state, _, receipt, _⟩ :=
        (runtime setup).canonical_silent_expiry leaks players network waited owner event payload
          (refs.get binding)
          (compileChecks (published := published) refs source.registry source.revelations binding)
          outputEq codeEq node ready entered ticks activated due
      rw [silent]
      change ((runtime setup).interactionStep leaks players network
        (.includeLatest event owner) submitted |>.bind _).map _ = _
      rw [included, FinDist.pure_bind]
      exact (congrArg (FinDist.map (fun final : (application setup leaks).Execution =>
        (final.application.config, final.receipts))) law).trans (by
        rw [FinDist.map_pure, state, receipt]
        simp only [disclosureResult_false, Bool.false_eq_true, ↓reduceIte]
        rfl)
  | true =>
      obtain ⟨value, success⟩ : ∃ value, disclosureResult published binding source true =
          PublicationResult.success value := by
        cases result : disclosureResult published binding source true with
        | failure => simp only [effectiveDisclosure, result, Bool.false_eq_true] at effective
        | success value => exact ⟨value, rfl⟩
      have resolved := compiled_disclosure_result published binding source refs
        execution.application.config.store agree true
      rw [success, EventGraph.EventCode.resolveOutput?_playerStore] at resolved
      have stored : (refs.get binding).get? execution.application.config.store =
          some (.success value) := by
        have bound := success
        simp only [disclosureResult, revealSuccessor, ite_true, Env.cons_get_here] at bound
        have originalValue : source.state.get binding = .success value := by
          split at bound
          · exact bound
          · cases bound
        simpa only [originalValue, cellValue] using agree binding
      obtain ⟨candidate, decision, accepted⟩ := (runtime setup).reactiveDecision_opening_law leaks
        execution.application valid (owner, execution.network.nextSerial owner) owner event payload
        (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations binding)
        outputEq codeEq node ready timely rfl
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
        (by simp only [cast_cast, cast_eq]) value stored resolved
      have original : (runtime setup).reactiveDecision leaks owner event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
          (execution.observe app owner).application =
        (runtime setup).canonicalRevealResponse leaks event candidate ⟨payload, value⟩ true := by
        exact congrArg ReactiveApplication.Action.mk decision
      have canonical : response = ((runtime setup).reactiveNormalization leaks).action owner
          (execution.recall owner) (execution.observe app owner)
          ((runtime setup).canonicalRevealResponse leaks event candidate
            ⟨payload, value⟩ true) := by
        dsimp only [response, serviceDecision]
        rw [original]
        rfl
      obtain ⟨evidence, shape⟩ := (runtime setup).normalized_reveal_response leaks owner
        (execution.recall owner) (execution.observe app owner) event candidate ⟨payload, value⟩
      have responseEq := canonical.trans shape
      obtain ⟨included, inclusion, state, _, receipts, _, _⟩ :=
        (runtime setup).opening_published_checkpoint leaks players network execution owner event
          candidate ⟨payload, value⟩ evidence _ pending (serials.next_unpublished owner) accepted
      have settled : ¬included.application.config.cut.Ready event := by
        rw [state]
        intro active
        exact active.1 (by simp [EventGraphRuntime.State.complete, EventOrder.Cut.complete])
      obtain ⟨final, law, finalState, _, finalReceipts, _⟩ :=
        (runtime setup).settled_reveal_expiry leaks players network included event settled ticks
      rw [responseEq]
      change ((runtime setup).interactionStep leaks players network
        (.includeLatest event owner) _ |>.bind _).map _ = _
      rw [inclusion, FinDist.pure_bind]
      exact (congrArg (FinDist.map (fun final : (application setup leaks).Execution =>
        (final.application.config, final.receipts))) law).trans (by
        rw [FinDist.map_pure, finalState, state, finalReceipts, receipts, success]
        rfl)

/-- The actual mixed compiler invocation preserves the complete distribution
of guarded publication results. Its completion action records the effective
choice; an ineffective private intention is retained by the source posterior
normalization, rather than reconstructed from silent network traffic. -/
theorem sourceServicePolicy_reveal_service
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.reveal published owner name fresh binding unresolved next) profile
      refs source.revelations source.registry embedding refsBefore offset)
    (execution : (application setup leaks).Execution)
    (checkpoint : SourceCheckpoint setup source refs offset execution.application.config)
    (valid : execution.application.BindingInvariant)
    (entered ticks : Nat)
    (pending : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event := embedding.event index
    let outputEq : (graph setup).outputLayout event = .publication payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    ∀ (_granted : execution.application.serviceGrant = some event)
      (ready : execution.application.config.cut.Ready event)
      (_timely : execution.application.WithinDeadline (runtime setup) event)
      (_activated : execution.application.activatedAt event = some entered)
      (_due : (runtime setup).deadline event ≤ execution.application.clock + ticks - entered),
    ((sourceServicePolicy setup leaks wholeProfile owner (execution.recall owner)
        (execution.observe (application setup leaks) owner)).bind fun response =>
      (runtime setup).runInteractionPlan leaks players network
        (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
        (execution.respond (application setup leaks) owner response)).map
      (fun final => (final.application.config, final.receipts)) =
      (revealKernel profile (source.view owner)).map fun disclose =>
        (execution.application.config.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm)
            (effectiveDisclosure published binding source disclose))
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (disclosureResult published binding source disclose)),
          if effectiveDisclosure published binding source disclose then execution.receipts ++
            [((owner, execution.network.nextSerial owner), true)] else execution.receipts) := by
  intro index event outputEq granted ready timely activated due
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry
          source.revelations binding) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
  have node : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq := by
    cases viewed : nodeView (graph setup) event with
    | sample otherPayload law kind code => cases kind.symm.trans outputEq
    | bind other otherPayload kind code => cases kind.symm.trans outputEq
    | resolve other otherPayload otherBinding otherChecks kind code =>
        have samePayload := EventGraph.EventField.publication.inj (kind.symm.trans outputEq)
        subst otherPayload
        have sameCode := code.symm.trans codeEq
        cases sameCode
        rfl
  rw [sourceServicePolicy_reveal setup leaks fresh binding unresolved next wholeProfile profile
    refs source embedding refsBefore offset aligned execution checkpoint.agrees checkpoint.history
    granted, FinDist.bind_map, FinDist.map_bind, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro disclose _
  rw [serviceDecision_effectiveDisclosure (runtime setup) leaks published binding source refs
    execution checkpoint.agrees event outputEq codeEq node disclose]
  have exactLaw := guarded_reveal_service setup leaks published binding source refs execution
    checkpoint.agrees valid event outputEq codeEq node ready timely entered ticks activated due
    pending serials players network (effectiveDisclosure published binding source disclose)
    (effectiveDisclosure_idempotent published binding source disclose)
  dsimp only at exactLaw
  simpa only [disclosureResult_effectiveDisclosure] using exactLaw

/-- Every supported execution of the actual guarded resolution suffix has a
supported source intention and the corresponding effective source checkpoint.
This statement includes both initial and dynamically committed bindings. -/
theorem sourceServicePolicy_reveal_checkpoint
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.reveal published owner name fresh binding unresolved next) profile
      refs source.revelations source.registry embedding refsBefore offset)
    (execution : (application setup leaks).Execution)
    (checkpoint : SourceCheckpoint setup source refs offset execution.application.config)
    (valid : execution.application.BindingInvariant)
    (entered ticks : Nat)
    (pending : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event := embedding.event index
    let outputEq : (graph setup).outputLayout event = .publication payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    ∀ (_granted : execution.application.serviceGrant = some event)
      (ready : execution.application.config.cut.Ready event)
      (_timely : execution.application.WithinDeadline (runtime setup) event)
      (_activated : execution.application.activatedAt event = some entered)
      (_due : (runtime setup).deadline event ≤ execution.application.clock + ticks - entered)
      (after : (application setup leaks).Execution),
    after ∈ ((sourceServicePolicy setup leaks wholeProfile owner (execution.recall owner)
        (execution.observe (application setup leaks) owner)).bind fun response =>
      (runtime setup).runInteractionPlan leaks players network
        (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
        (execution.respond (application setup leaks) owner response)).support →
      ∃ disclose ∈ (revealKernel profile (source.view owner)).support,
        SourceCheckpoint setup
          (revealSuccessor published binding source
            (effectiveDisclosure published binding source disclose))
          (refs.cons (name := published) ⟨.inr event, outputEq⟩) (offset + 1)
          after.application.config := by
  intro index event outputEq granted ready timely activated due after supported
  have law := sourceServicePolicy_reveal_service setup leaks fresh binding unresolved next
    wholeProfile profile refs source embedding refsBefore offset aligned execution checkpoint
    valid entered ticks pending serials players network granted ready timely activated due
  have mapped : (after.application.config, after.receipts) ∈
      (((sourceServicePolicy setup leaks wholeProfile owner (execution.recall owner)
        (execution.observe (application setup leaks) owner)).bind fun response =>
          (runtime setup).runInteractionPlan leaks players network
            (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
            (execution.respond (application setup leaks) owner response)).map
              (fun final => (final.application.config, final.receipts))).support := by
    rw [FinDist.support_map]
    exact ⟨after, supported, rfl⟩
  rw [law, FinDist.support_map] at mapped
  obtain ⟨disclose, chosen, same⟩ := mapped
  have stateEq := congrArg Prod.fst same
  dsimp only at stateEq
  have eventRank : event.val = offset := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have decoded : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (effectiveDisclosure published binding source disclose)) =
        some (.reveal owner name (effectiveDisclosure published binding source disclose)) := by
    have action := aligned.actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (effectiveDisclosure published binding source disclose))
    simpa [event, index, outputEq, decodeEventAction] using action
  have completed := checkpoint.reveal published binding event eventRank ready outputEq
    (fun ref => refsBefore ref index)
    (effectiveDisclosure published binding source disclose) decoded
  have resultEq := disclosureResult_effectiveDisclosure published binding source disclose
  rw [resultEq] at completed
  exact ⟨disclose, chosen, stateEq ▸ completed⟩

end Vegas.SourceProgram.RevealService
