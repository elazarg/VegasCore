/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceResolutionMemoryFactorization
import Vegas.Game.SourceServiceRecordedResolutionAlignment
import Vegas.Game.SourceServiceResponseCompletion

/-! # A real normalized resolution draw through delayed completion

An original intention sampled from the source normalizer determines a supported
effective packet at the actual protected input. The initialized physical response
records that same packet. Completion stopping accepts its exact identifier and
has the effective typed source successor; the restored original successor has
the same typed state and retains the intended private history.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

omit [Fintype Player] [IExpr.ResultTypes L] in
private theorem restored_disclosure_support {Γ : SourceCtx Player L} {name : VarId}
    {owner : Player} {payload : L.Ty} (published : VarId)
    (binding : HasVar Γ name (.commitment owner payload)) (source old : Config Player L Γ)
    (remember : DecisionView owner Γ → PMF (List (OwnAction Player L)))
    (choose : DecisionView owner Γ → PMF Bool)
    (restored : old ∈ (source.restoreMemory owner remember).support)
    (intended : Bool) (selected : intended ∈ (choose (old.view owner)).support) :
    effectiveDisclosure published binding source intended ∈
      ((disclosureMemoryLaw published binding source.registry source.revelations remember choose
        (source.view owner)).map Prod.fst).support := by
  obtain ⟨past, remembered, equal⟩ := PMF.support_map .. ▸ restored
  cases equal
  rw [PMF.support_map]
  refine ⟨(effectiveDisclosure published binding source intended,
    past ++ [.reveal owner name intended]), ?_, rfl⟩
  rw [disclosureMemoryLaw, PMF.support_bind]
  refine Set.mem_iUnion₂.mpr ⟨past, remembered, ?_⟩
  rw [PMF.support_map]
  refine ⟨intended, ?_, ?_⟩
  · simpa only [Config.view, Config.withOwnHistory, Function.update_self] using selected
  simp only [Config.view, effectiveDisclosureView_observe]

/-- A sampled original intention determines the exact protected packet and
every stopped effective source endpoint. Source support follows from the actual
normalizer and response law. Only the owner follows the prescribed policy;
foreign physical policies may be arbitrary. -/
theorem sourceServiceDecision_clear_resolution_intention_completion
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (profile : BehavioralProfile setup.program)
    (original : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (remember : DecisionView owner Γ → PMF (List (OwnAction Player L)))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (bounds : MessageBounds (graph setup)) (execution : (application setup leaks).Execution)
    (aligned : CompiledPolicySuffix setup.program profile
      (.reveal published owner name fresh binding unresolved next)
      (Function.update original owner ((original owner).normalizeDisclosureFrom
        (.reveal published owner name fresh binding unresolved next)
          source.registry source.revelations remember))
      refs source.revelations source.registry embedding refsBefore
        (embedding.event ⟨0, by simp [eventCount]⟩).val)
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some owner, execution⟩))
    (clear : ∀ player, (runtime setup).persistentServiceRisk leaks bound player
      (execution.recall player) (execution.observe (application setup leaks) player) = false)
    (ready : execution.application.config.cut.Ready
      (embedding.event ⟨0, by simp [eventCount]⟩))
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall owner)
      (embedding.event ⟨0, by simp [eventCount]⟩) = false)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound
      (embedding.event ⟨0, by simp [eventCount]⟩))
    (weight : ℝ) (positive : 0 < weight) (below : weight < 1)
    (players : Player → (application setup leaks).Policy)
    (follows : players owner = sourceServiceTurnPolicy setup leaks bound horizon
      (geometricTiming setup horizon weight positive.le below.le) profile owner)
    (initialized : (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler
      players (some ⟨remaining, some owner, execution⟩))
    (old : Config Player L Γ) (restored : old ∈ (source.restoreMemory owner remember).support)
    (intended : Bool) (selected : intended ∈ (revealKernel original (old.view owner)).support) :
    let program := SourceProgram.reveal published owner name fresh binding unresolved next
    let index : Fin (eventCount program) := ⟨0, by simp [program, eventCount]⟩
    let event := embedding.event index
    let outputEq : (graph setup).outputLayout event = .publication payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, program, outputLayout, eventCount] using embedding.layout_eq index
    let effective := effectiveDisclosure published binding source intended
    let response := resolutionIntentionResponse published binding source execution event
      outputEq (some intended)
    let submitted := execution.respond (application setup leaks) owner response
    response ∈ (players owner (execution.recall owner)
      (execution.observe (application setup leaks) owner)).support ∧
    ∃ entry ∈ submitted.recall owner, ∃ message,
      entry.action = response ∧ message.id = (owner, execution.network.nextSerial owner) ∧
      FreshCall setup leaks owner event bound entry message ∧
      ∀ stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon submitted).support,
        entry ∈ stopped.recall owner ∧ (message.id, true) ∈ stopped.receipts ∧
        event ∉ stopped.application.missedEvents ∧
        stopped.application.config = execution.application.config.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) effective)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (disclosureResult published binding source effective)) ∧
        (refs.cons (name := published) ⟨.inr event, outputEq⟩).Agrees
          (revealSuccessor published binding source effective).state
          stopped.application.config.store ∧
        (refs.cons (name := published) ⟨.inr event, outputEq⟩).Agrees
          (revealSuccessor published binding old intended).state stopped.application.config.store ∧
        decodeHistory setup.program (stopped.application.config.history.map
          (setup.eventGraph.fromModeCompletion .sequential)) =
            (revealSuccessor published binding source effective).history := by
  intro program index event outputEq effective response submitted
  let app := application setup leaks
  let timing := geometricTiming setup horizon weight positive.le below.le
  let normalized := Function.update original owner ((original owner).normalizeDisclosureFrom
    program source.registry source.revelations remember)
  have sampled : effective ∈ (revealKernel normalized (source.view owner)).support := by
    have kernel : revealKernel normalized (source.view owner) =
        (disclosureMemoryLaw published binding source.registry source.revelations
          remember (revealKernel original) (source.view owner)).map Prod.fst := by
      simp only [normalized, revealKernel, Function.update_self,
        BehavioralPolicy.normalizeDisclosureFrom, program]
    rw [kernel]
    exact restored_disclosure_support published binding source old remember (revealKernel original)
      restored intended selected
  have actor : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, program, eventOwner?, eventCount] using aligned.actorEq index
  have turn := ownTurn?_of_ready setup execution.application ready actor
  have physical := sourceServiceDecision_clear_geometric_response bounds bound profile owner
    execution trace clear event unrecorded turn weight positive below
  rw [sourceServiceCanonicalOpportunity_protected bound profile owner event (execution.recall owner)
      (execution.observe app owner) unrecorded fits,
    sourceServiceCanonicalPolicy_reveal setup leaks fresh binding unresolved next profile normalized
      refs source embedding refsBefore event.val aligned execution agree history ready] at physical
  have chosen : response ∈ (players owner (execution.recall owner)
      (execution.observe app owner)).support := by
    rw [follows, physical]
    apply mem_support_mix_right weight positive.le below.le below
    rw [PMF.support_map]
    exact ⟨effective, sampled, rfl⟩
  have supported := sourceResponse_roundSupported initialized response chosen
  have within : submitted.environmentRecall.length ≤ horizon := by
    have budget := supported.1
    change submitted.environmentRecall.length + remaining = horizon at budget
    omega
  have reached : submitted ∈ (app.roundsFrom (initialLaw setup) scheduler players
      submitted.environmentRecall.length).support := supported.2
  have configEq : submitted.application.config = execution.application.config :=
    ((runtime setup).reactive_respond_application leaks execution owner response).1
  have readyAfter : submitted.application.config.cut.Ready event := by rw [configEq]; exact ready
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations
          binding) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes _) = _
    simpa [event, index, program, outputLayout, compileRankedNodes] using
      aligned.graphSuffix.nodeEq index
  have node := nodeView_eq_resolve outputEq codeEq
  have notBinding who ty output code
      (impossible : nodeView (graph setup) event = .bind who ty output code) : False := by
    rw [node] at impossible
    cases impossible
  have rawTrace := (bounds.riskMenu (runtime setup) leaks bound).toRawTrace (initialLaw setup)
    horizon scheduler trace
  have facts := legalFacts setup leaks horizon scheduler _ rawTrace
  have emittable : effective = false ∨ ∃ value : L.Val payload,
      effective = true ∧ disclosureResult published binding source true = .success value := by
    cases intended with
    | false => exact Or.inl (effectiveDisclosure_false published binding source)
    | true =>
        cases result : disclosureResult published binding source true with
        | failure => exact Or.inl (by simp only [effective, effectiveDisclosure, result])
        | success value =>
            exact Or.inr ⟨value, by simp only [effective, effectiveDisclosure, result], rfl⟩
  obtain ⟨material, responseEq, packetShape⟩ :
      ∃ material, response = ⟨some material⟩ ∧
        ((effective = false ∧ material.call.packet = .withhold event) ∨
          (effective = true ∧ ∃ candidate value,
            material.call.packet = .opening event candidate ⟨payload, value⟩ ∧
            candidate.1 = owner ∧
            execution.application.accepted (refs.get binding).field = some candidate ∧
            execution.application.candidates.lookup candidate = .openable ⟨payload, value⟩ ∧
            (refs.get binding).get? execution.application.config.store = some (.success value) ∧
            EventGraph.EventCode.resolveOutput? (refs.get binding)
              (compileChecks (published := published) refs source.registry source.revelations
                binding) true execution.application.config.store = some (.success value))) := by
    rcases emittable with falseChoice | ⟨value, trueChoice, success⟩
    · refine ⟨disclosureSubmission (.withhold event), ?_, Or.inl ⟨falseChoice, rfl⟩⟩
      change (runtime setup).canonicalServiceDecision leaks owner (execution.recall owner)
        (execution.observe app owner) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) effective) = _
      rw [falseChoice]
      exact (runtime setup).canonicalServiceDecision_resolution_false leaks owner _ _ event
        owner payload (refs.get binding) _ outputEq codeEq node
    · obtain ⟨candidate, associated, owned, fixed, _⟩ := guarded_rosterOpening_success setup leaks
        published binding source refs execution agree facts.binding event outputEq codeEq node
        value success
      have resolved := compiled_disclosure_result (graph := graph setup) published binding source
        refs execution.application.config.store agree true
      rw [success] at resolved
      rw [EventGraph.EventCode.resolveOutput?_playerStore] at resolved
      have stored := facts.binding.opening_stored _ _ _ associated fixed
      let call : WitnessedSubmission (graph setup) :=
        disclosureSubmission (.opening event candidate ⟨payload, value⟩)
      let material : app.Submission := call.normalizeReactive owner
        (app.observePlayer execution.application owner)
        (execution.network.known owner)
      refine ⟨material, ?_, Or.inr ⟨trueChoice, candidate, value, ?_, owned, associated, fixed,
        stored, resolved⟩⟩
      · change (runtime setup).canonicalServiceDecision leaks owner (execution.recall owner)
          (execution.observe app owner) event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) effective) = _
        rw [trueChoice, (runtime setup).canonicalServiceDecision_eq_of_not_bind leaks owner
          _ _ event _ notBinding]
        exact (runtime setup).serviceDecision_successful_opening leaks execution facts.inputs
          owner event payload (refs.get binding) _ outputEq codeEq node candidate value
          associated owned fixed resolved
      · simp only [material, call, disclosureSubmission, WitnessedSubmission.normalizeReactive,
          Submission.normalizeReactive_none]
  have named : (runtime setup).submittedEvent? leaks response = some event := by
    rw [responseEq]
    rcases packetShape with ⟨_, packet⟩ | ⟨_, candidate, value, packet, _⟩ <;>
      simp only [EventGraphRuntime.submittedEvent?, packet, Payload.event?]
  have recorded := (runtime setup).eventRecorded_respond leaks execution owner response event named
  obtain ⟨entry, member, message, entryNamed, call, completion⟩ :=
    sourceServiceTurnPolicy_recorded_decision_completion contract players owner timing profile
      follows _ within submitted reached event actor recorded
  have originalMember := member
  dsimp only [submitted] at member
  rw [responseEq, respond_submit_recall, List.mem_append] at member
  have entryEq : entry = ⟨execution.observe app owner, ⟨some material⟩,
      some ⟨(owner, execution.network.nextSerial owner), app.packet
        (app.submit execution.application owner material) owner (execution.network.known owner)
          material⟩⟩ := by
    rcases member with before | last
    · have impossible := ((runtime setup).eventRecorded_iff leaks _ event).mpr
        ⟨entry, before, entryNamed⟩
      rw [unrecorded] at impossible
      cases impossible
    · exact List.mem_singleton.mp last
  have actualAction : entry.action = response := by rw [entryEq, responseEq]
  have identity : message.id = (owner, execution.network.nextSerial owner) := by
    have emitted := congrArg ReactiveApplication.PlayerEntry.emitted entryEq
    rw [call.emitted] at emitted
    exact congrArg Message.id (Option.some.inj emitted)
  have actualPacket : message.payload.call = material.call.packet := by
    have emitted := congrArg ReactiveApplication.PlayerEntry.emitted entryEq
    rw [call.emitted] at emitted
    cases Option.some.inj emitted
    rfl
  have realized : RealizesAt leaks submitted.application.config submitted.application event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) effective) entry message := by
    unfold RealizesAt
    rw [node]
    rcases packetShape with ⟨falseChoice, packet⟩ |
      ⟨trueChoice, candidate, value, packet, owned, associated, fixed, stored, resolved⟩
    · exact Or.inl ⟨by simpa only [cast_cast, cast_eq] using falseChoice,
        actualPacket.trans packet⟩
    · refine Or.inr ⟨by simpa only [cast_cast, cast_eq] using trueChoice, candidate, value,
        actualPacket.trans packet, owned, ?_, ?_, ?_, ⟨.success value, ?_⟩⟩
      · rw [entryEq]
        exact associated
      · have inert : submitted.application = execution.application :=
          (source_resolution_decision_include setup leaks published binding refs source execution
            horizon remaining scheduler rawTrace agree event ready fits.withinDeadline outputEq
              codeEq node effective emittable).1
        rw [inert]
        exact fixed
      · rw [configEq]
        exact stored
      · rw [configEq]
        exact resolved
  refine ⟨chosen, entry, originalMember, message, actualAction, identity, call, ?_⟩
  intro stopped stoppedSupported
  obtain ⟨retained, _, accepted, noMiss⟩ := completion stopped stoppedSupported
  have native := sourceServiceTurnPolicy_recorded_realization_completion contract players owner
    timing profile follows _ within submitted reached event actor readyAfter
    (cast (congrArg EventGraph.EventField.Action outputEq.symm) effective) entry originalMember
    message entryNamed call realized stopped stoppedSupported
  rw [submitted.application.config.step_eq_map_of_code event readyAfter outputEq _ codeEq effective
    (PMF.pure (disclosureResult published binding source effective))
    (compileResolve_eval? refs source.registry source.revelations source.state
      submitted.application.config.store (by rw [configEq]; exact agree) binding effective),
    PMF.pure_map, PMF.mem_support_pure_iff] at native
  have exactConfig : stopped.application.config = execution.application.config.complete event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) effective)
      (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (disclosureResult published binding source effective)) := by
    simpa only [configEq] using native
  have store : (refs.cons (name := published) ⟨.inr event, outputEq⟩).Agrees
      (revealSuccessor published binding source effective).state
      stopped.application.config.store := by
    rw [exactConfig]
    intro readName cell ref
    exact complete_guarded_reveal_agrees (graph := graph setup) published binding source refs
      execution.application agree event ready outputEq (by
        intro readName cell ref
        exact refsBefore ref index) effective ref
  have originalState : (revealSuccessor published binding old intended).state =
      (revealSuccessor published binding source effective).state := by
    obtain ⟨past, _remembered, equal⟩ := PMF.support_map .. ▸ restored
    cases equal
    rw [revealSuccessor_withOwnHistory]
    exact (congrArg Config.state (revealSuccessor_effective_withOwnHistory published binding source
      intended (past ++ [.reveal owner name intended]))).symm
  refine ⟨retained, accepted, noMiss, exactConfig, store, ?_, ?_⟩
  · rw [originalState]
    exact store
  · rw [exactConfig]
    have actionEq : decodeEventAction setup.program event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) effective) =
          some (.reveal owner name effective) := by
      have lookup := aligned.actionEq index
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) effective)
      have inverse : cast (congrArg EventGraph.EventField.Action (embedding.layout_eq index))
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) effective) = effective := by
        change cast (congrArg EventGraph.EventField.Action outputEq)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) effective) = effective
        simp only [cast_cast, cast_eq]
      change decodeEventAction setup.program event _ =
        some (.reveal owner name (cast (congrArg EventGraph.EventField.Action
          (embedding.layout_eq index)) _)) at lookup
      rw [inverse] at lookup
      exact lookup
    change decodeHistory setup.program ((execution.application.config.history ++
      [(⟨event, cast (congrArg EventGraph.EventField.Action outputEq.symm) effective⟩ :
        (graph setup).Completion)]).map (setup.eventGraph.fromModeCompletion .sequential)) = _
    have decoded := decodeHistory_append_completion setup.program
      (execution.application.config.history.map (setup.eventGraph.fromModeCompletion .sequential))
      event (cast (congrArg EventGraph.EventField.Action outputEq.symm) effective)
    rw [List.map_append, List.map_singleton]
    change decodeHistory setup.program
      ((execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) ++
        [⟨event, cast (congrArg EventGraph.EventField.Action outputEq.symm) effective⟩]) = _
    rw [decoded, history]
    rw [actionEq]
    rfl

end Vegas
