/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceSettlement
import Vegas.Game.SourceServiceBindingPhase
import Vegas.Game.RevealServiceRosterLaw

/-! # Guarded disclosure across an actual response roster

The selected source opportunity keeps its original Boolean lottery. Its silent
branch uses the actual replay policy, and later foreign visits retain passive
samples and replays before protected inclusion. The law records the effective
source action and the original guarded result. Original failed intentions are
retained separately by disclosure normalization's conditional memory law.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem opening_replay_inclusion
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (network : (runtime setup).NetworkPolicy leaks)
    (execution : (application setup leaks).Execution) (owner : Player)
    (event : (graph setup).EventId) (candidate : Handle (graph setup)) (raw : Raw L)
    (evidence : EvidenceRequest (graph setup))
    (published : execution.network.Satisfies fun packet =>
      packet.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext) (remaining : List Player) :
    let app := application setup leaks
    let players : Player → app.Policy := fun _ => app.replayPolicy
    let submitted := execution.respond app owner
      ⟨some (.submit ⟨⟨.opening event candidate raw, none⟩, evidence⟩)⟩
    ((runtime setup).runInteractionPlan leaks players network
      (remaining.map ServiceInstruction.player ++ [.includeLatest event owner]) submitted).map
        (fun final => (final.application, final.network.ledger,
          final.receipts, final.network.nextSerial)) =
      ((runtime setup).interactionStep leaks players network
        (.includeLatest event owner) submitted).map
          (fun final => (final.application, final.network.ledger,
            final.receipts, final.network.nextSerial)) := by
  dsimp only
  let app := application setup leaks
  let players : Player → app.Policy := fun _ => app.replayPolicy
  let submission : WitnessedSubmission (graph setup) :=
    ⟨⟨.opening event candidate raw, none⟩, evidence⟩
  let submitted := execution.respond app owner ⟨some (.submit submission)⟩
  let packet := app.packet execution.application owner (execution.network.known owner) submission
  let message : Message Player (WitnessedPacket (graph setup)) :=
    ⟨(owner, execution.network.nextSerial owner), packet⟩
  have responses := fun (current : app.Execution) who response
      (_ : current.application = submitted.application)
      (_ : submitted.recall owner ⊆ current.recall owner)
      (supported : response ∈ (players who (current.recall who)
        (current.observe app who)).support) =>
    app.replayPolicy_cases _ _ response supported
  have packets : submitted.network.Satisfies fun other =>
      other.id ∈ submitted.network.ledger.map Message.id ∨ other = message := by
    change (execution.network.submit owner packet).2.Satisfies _
    exact (published.mono (fun _ prior => Or.inl prior)).submit owner packet (Or.inr rfl)
  have pending : message ∈ submitted.network.pending :=
    List.mem_append_right _ (List.mem_singleton_self _)
  have delayed := (runtime setup).replay_window_settlement leaks players network owner submitted
    responses event message rfl rfl packets pending (serials.next_unpublished owner) remaining
  have immediate := (runtime setup).replay_window_settlement leaks players network owner submitted
    responses event message rfl rfl packets pending (serials.next_unpublished owner) []
  exact delayed.trans (by
    simpa only [List.map_nil, List.nil_append, runInteractionPlan, PMF.bind_pure]
      using immediate.symm)

/-- The actual replay lottery implementing an effective disclosure preserves
the typed source completion through all later passive activations and expiry. -/
theorem guarded_reveal_replay_service
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
    (packets : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (network : (runtime setup).NetworkPolicy leaks) (remaining : List Player)
    (disclose : Bool)
    (effective : effectiveDisclosure published binding source disclose = disclose) :
    let app := application setup leaks
    let players : Player → app.Policy := fun _ => app.replayPolicy
    let response := (runtime setup).serviceDecision leaks owner (execution.recall owner)
      (execution.observe app owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
    let law := if response.transmission = none then
      app.replayPolicy (execution.recall owner) (execution.observe app owner)
      else PMF.pure response
    (law.bind fun action => (runtime setup).runInteractionPlan leaks players network
      (remaining.map ServiceInstruction.player ++
        (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]))
      (execution.respond app owner action)).map
        (fun final => (final.application.config, final.receipts)) =
      PMF.pure
        (execution.application.config.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (disclosureResult published binding source disclose)),
          if disclose then execution.receipts ++
            [((owner, execution.network.nextSerial owner), true)] else execution.receipts) := by
  intro app players response law
  cases disclose with
  | false =>
      have silent : response = ⟨none⟩ := by
        simp only [response, serviceDecision, reactiveDecision, node, reactiveResolutionPacket,
          cast_cast, cast_eq, Bool.false_eq_true, ↓reduceIte,
          disclosureSubmission_normalize_withhold]
        rfl
      have lawEq : law = app.replayPolicy (execution.recall owner)
          (execution.observe app owner) := by
        simp only [law, silent, ↓reduceIte]
      let expected := (execution.application.config.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) false)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm)
          (disclosureResult published binding source false)), execution.receipts)
      rw [lawEq, PMF.map_bind]
      trans (app.replayPolicy (execution.recall owner) (execution.observe app owner)).bind
        (fun _ => PMF.pure expected)
      · apply bind_congr_on_support _
        intro action supported
        let submitted := execution.respond app owner action
        obtain ⟨same, ledger, receipt, _, safe, _⟩ :=
          (runtime setup).replay_response_preserves leaks _ execution packets owner action
            (app.replayPolicy_cases _ _ action supported)
        change submitted.application = execution.application at same
        change submitted.receipts = execution.receipts at receipt
        rw [(runtime setup).runInteractionPlan_append, PMF.map_bind]
        trans ((runtime setup).runInteractionPlan leaks players network
          (remaining.map ServiceInstruction.player) submitted).bind
            (fun _ => PMF.pure expected)
        · apply bind_congr_on_support _
          intro current reached
          obtain ⟨currentSame, currentLedger, currentReceipt, _, currentSafe, _⟩ :=
            (runtime setup).replay_window_preserves leaks players network owner submitted
              (fun value who response _ _ chosen => app.replayPolicy_cases _ _ response chosen)
              _ safe remaining current reached
          have currentReady : current.application.config.cut.Ready event := by
            rw [currentSame, same]; exact ready
          have currentPending : ∀ message ∈ current.network.pending,
              message.id ∈ current.network.ledger.map Message.id := by
            intro message member
            rw [currentLedger, ledger]
            exact currentSafe.pending message member
          let waited : app.Execution := { current with
            environmentRecall := current.environmentRecall ++
              [⟨current.observeEnvironment app, .wait⟩] }
          have included : (runtime setup).interactionStep leaks players network
              (.includeLatest event owner) current = PMF.pure waited := by
            rw [(runtime setup).interaction_includeLatest_of_pending_published leaks players
              network current owner event currentPending]
            simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
            rfl
          obtain ⟨final, tailLaw, state, _, receipts, _⟩ :=
            (runtime setup).canonical_silent_expiry leaks players network waited owner event
              payload (refs.get binding)
              (compileChecks (published := published) refs source.registry
                source.revelations binding)
              outputEq codeEq node currentReady entered ticks
              (by change current.application.activatedAt event = _
                  rw [currentSame, same]; exact activated)
              (by change _ ≤ current.application.clock + ticks - entered
                  rw [currentSame, same]; exact due)
          rw [List.cons_append, runInteractionPlan, included, PMF.pure_bind,
            tailLaw, PMF.pure_map,
            state, receipts]
          simp only [waited, currentSame, same, currentReceipt, receipt, expected,
            disclosureResult_false, EventGraphRuntime.State.complete]
        · exact PMF.bind_const _ _
      · exact PMF.bind_const _ _
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
        (runtime setup).canonicalRevealResponse leaks event candidate ⟨payload, value⟩ true :=
        congrArg ReactiveApplication.Action.mk decision
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
      have lawEq : law = PMF.pure response := by
        simp only [law, responseEq, reduceCtorEq, ↓reduceIte]
      obtain ⟨included, inclusion, state, _, receipts, _, _⟩ :=
        (runtime setup).opening_published_checkpoint leaks players network execution owner event
          candidate ⟨payload, value⟩ evidence _ packets.pending
          (serials.next_unpublished owner) accepted
      let submitted := execution.respond app owner response
      let delayed := (runtime setup).runInteractionPlan leaks players network
        (remaining.map ServiceInstruction.player ++ [.includeLatest event owner]) submitted
      have delayedLaw : delayed.map (fun final => (final.application, final.network.ledger,
          final.receipts, final.network.nextSerial)) =
          PMF.pure (included.application, included.network.ledger,
            included.receipts, included.network.nextSerial) := by
        dsimp only [delayed, submitted]
        rw [responseEq, opening_replay_inclusion setup leaks network execution owner event
          candidate ⟨payload, value⟩ evidence packets serials remaining,
          inclusion, PMF.pure_map]
      have settled : ∀ final ∈ delayed.support,
          ¬final.application.config.cut.Ready event := by
        intro final reached
        have member : (final.application, final.network.ledger, final.receipts,
            final.network.nextSerial) ∈ (delayed.map (fun next =>
              (next.application, next.network.ledger,
                next.receipts, next.network.nextSerial))).support :=
          PMF.support_map .. ▸ ⟨final, reached, rfl⟩
        rw [delayedLaw] at member
        have equal := congrArg Prod.fst ((PMF.mem_support_pure_iff _ _).mp member)
        change final.application = included.application at equal
        rw [equal, state]
        intro active
        exact active.1 (by simp [EventGraphRuntime.State.complete, EventOrder.Cut.complete])
      rw [lawEq, PMF.pure_bind]
      have splitPlan : remaining.map ServiceInstruction.player ++
          (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]) =
          (remaining.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
            (List.replicate ticks .tick ++ [.expire event]) := by simp only [List.append_assoc,
              List.cons_append, List.nil_append]
      rw [splitPlan, (runtime setup).runInteractionPlan_append]
      change (delayed.bind _).map _ = _
      rw [(runtime setup).settled_tail_config_receipts leaks players network delayed event ticks
        settled]
      have projected := congrArg (PMF.map (fun result : EventGraphRuntime.State (graph setup) ×
          List (Message Player (WitnessedPacket (graph setup))) ×
          List (MessageId Player × Bool) × (Player → Nat) =>
          (result.1.config, result.2.2.1))) delayedLaw
      simpa only [PMF.map_comp, PMF.pure_map, Function.comp_def, state, receipts,
        success, ↓reduceIte, EventGraphRuntime.State.complete] using projected

private theorem foreign_service_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (profile : BehavioralProfile setup.program)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (remaining : List Player) (absent : owner ∉ remaining) (ticks : Nat)
    (execution : (application setup leaks).Execution)
    (sole : execution.application.publicView.SoleReady event) :
    (runtime setup).runInteractionPlan leaks
      (sourceServiceLastPolicy setup leaks rosters profile) network
      (remaining.map ServiceInstruction.player ++
        (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])) execution =
      (runtime setup).runInteractionPlan leaks (fun _ => (application setup leaks).replayPolicy)
        network (remaining.map ServiceInstruction.player ++
          (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]))
          execution := by
  have splitPlan : remaining.map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]) =
      (remaining.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
        (List.replicate ticks .tick ++ [.expire event]) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [splitPlan]
  conv_lhs => rw [(runtime setup).runInteractionPlan_append]
  conv_rhs => rw [(runtime setup).runInteractionPlan_append]
  rw [sourceServiceLastPolicy_foreign_tail setup leaks rosters profile network event owner
    owned remaining absent execution sole]
  apply bind_congr_on_support _
  intro current _
  exact servicePlan_players_eq setup leaks _ _ network _ (by simp) (by intro who; simp) current

/-- The last owner visit draws the actual source kernel. Silent source choices
are implemented by real replay aliases; every later foreign visit remains. -/
theorem sourceServiceLastPolicy_reveal_opportunity
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
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
    (packets : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (network : (runtime setup).NetworkPolicy leaks)
    (remaining : List Player) (absent : owner ∉ remaining) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event := embedding.event index
    let outputEq : (graph setup).outputLayout event = .publication payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    ∀ (ready : execution.application.config.cut.Ready event)
      (_timely : execution.application.WithinDeadline (runtime setup) event)
      (_activated : execution.application.activatedAt event = some entered)
      (_due : (runtime setup).deadline event ≤ execution.application.clock + ticks - entered)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
      (_last : (execution.recall owner).length + 1 =
        rosterOffset setup rosters owner event + (rosters event).count owner),
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceLastPolicy setup leaks rosters wholeProfile) network
      (.player owner :: remaining.map ServiceInstruction.player ++
        (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]))
      execution).map (fun final => (final.application.config, final.receipts)) =
      (revealKernel profile (source.view owner)).map fun disclose =>
        (execution.application.config.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm)
            (effectiveDisclosure published binding source disclose))
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (disclosureResult published binding source disclose)),
          if effectiveDisclosure published binding source disclose then execution.receipts ++
            [((owner, execution.network.nextSerial owner), true)] else execution.receipts) := by
  intro index event outputEq ready timely activated due unsent last
  let app := application setup leaks
  let players := sourceServiceLastPolicy setup leaks rosters wholeProfile
  let transport : Player → app.Policy := fun _ => app.replayPolicy
  let observed : app.Execution := { execution with
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .activate owner⟩] }
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry
          source.revelations binding) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
  have node : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq :=
    EventGraphRuntime.nodeView_eq_resolve _ _
  rw [List.cons_append, runInteractionPlan,
    (runtime setup).player_instruction_published leaks players network execution owner
      packets.pending, PMF.bind_map, PMF.map_bind]
  change (players owner (execution.recall owner) (execution.observe app owner)).bind _ = _
  dsimp only [players]
  rw [sourceServiceLastPolicy_at_last setup leaks rosters wholeProfile owner _ _ event
    (ownTurn?_of_ready setup execution.application ready owned) owned unsent last,
    sourceServicePolicy_reveal setup leaks fresh binding unresolved next wholeProfile profile
      refs source embedding refsBefore offset aligned execution checkpoint.agrees checkpoint.history
        ready, PMF.bind_map, PMF.bind_bind, ← PMF.bind_pure_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro disclose _
  simp only [Function.comp_apply]
  rw [serviceDecision_effectiveDisclosure (runtime setup) leaks published binding source refs
    execution checkpoint.agrees event outputEq codeEq node disclose]
  let effective := effectiveDisclosure published binding source disclose
  let response := (runtime setup).serviceDecision leaks owner (execution.recall owner)
    (execution.observe app owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) effective)
  trans ((if response.transmission = none then
    app.replayPolicy (execution.recall owner) (execution.observe app owner)
    else PMF.pure response).bind fun action =>
      (runtime setup).runInteractionPlan leaks transport network
        (remaining.map ServiceInstruction.player ++
          (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]))
        (observed.respond app owner action)).map
          (fun final => (final.application.config, final.receipts))
  · rw [PMF.map_bind]
    apply bind_congr_on_support _
    intro action _
    apply congrArg (PMF.map (fun final : app.Execution =>
      (final.application.config, final.receipts)))
    apply foreign_service_law setup leaks rosters wholeProfile network event owner owned
      remaining absent ticks
    rw [((runtime setup).reactive_respond_application leaks observed owner action).2]
    exact soleReady_of_ready setup execution.application ready
  · have exactLaw := guarded_reveal_replay_service setup leaks published binding source refs
      observed checkpoint.agrees valid event outputEq codeEq node ready timely entered ticks
        activated due packets serials network remaining effective
        (effectiveDisclosure_idempotent published binding source disclose)
    dsimp only at exactLaw
    simpa only [effective, observed, response, app, transport,
      ReactiveApplication.Execution.observe, disclosureResult_effectiveDisclosure] using exactLaw

/-- Every activation in the complete fixed roster remains in the actual
execution. The unique last owner opportunity implements the source disclosure
kernel, including withholding and disclosure intentions defeated by guards. -/
theorem sourceServiceLastPolicy_reveal_roster
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
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
    (packets : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (network : (runtime setup).NetworkPolicy leaks)
    (visited remaining : List Player) (absent : owner ∉ remaining) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event := embedding.event index
    let outputEq : (graph setup).outputLayout event = .publication payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    ∀ (_position : rosters event = visited ++ owner :: remaining)
      (ready : execution.application.config.cut.Ready event)
      (_timely : execution.application.WithinDeadline (runtime setup) event)
      (_activated : execution.application.activatedAt event = some entered)
      (_due : (runtime setup).deadline event ≤ execution.application.clock + ticks - entered)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
      (_counted : (execution.recall owner).length = rosterOffset setup rosters owner event),
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceLastPolicy setup leaks rosters wholeProfile) network
      ((rosters event).map ServiceInstruction.player ++
        (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]))
      execution).map (fun final => (final.application.config, final.receipts)) =
      (revealKernel profile (source.view owner)).map fun disclose =>
        (execution.application.config.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm)
            (effectiveDisclosure published binding source disclose))
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (disclosureResult published binding source disclose)),
          if effectiveDisclosure published binding source disclose then execution.receipts ++
            [((owner, execution.network.nextSerial owner), true)] else execution.receipts) := by
  intro index event outputEq position ready timely activated due unsent counted
  let app := application setup leaks
  let players := sourceServiceLastPolicy setup leaks rosters wholeProfile
  let expected := (revealKernel profile (source.view owner)).map fun disclose =>
    (execution.application.config.complete event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (effectiveDisclosure published binding source disclose))
      (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (disclosureResult published binding source disclose)),
      if effectiveDisclosure published binding source disclose then execution.receipts ++
        [((owner, execution.network.nextSerial owner), true)] else execution.receipts)
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
  have total : (rosters event).count owner = visited.count owner + 1 := by
    rw [position, List.count_append, List.count_cons_self, List.count_eq_zero.mpr absent]
  have before : (execution.recall owner).length + visited.count owner <
      rosterOffset setup rosters owner event + (rosters event).count owner := by
    rw [counted, total]
    omega
  rw [position, List.map_append, List.map_cons, List.append_assoc,
    (runtime setup).runInteractionPlan_append, PMF.map_bind]
  trans ((runtime setup).runInteractionPlan leaks players network
    (visited.map ServiceInstruction.player) execution).bind (fun _ => expected)
  · apply bind_congr_on_support _
    intro current reached
    obtain ⟨same, ledger, receipts, counters, safe, _⟩ :=
      sourceServiceLastPolicy_waiting_data setup leaks rosters wholeProfile network event owner
        owned visited execution current (soleReady_of_ready setup execution.application ready)
        before _ packets reached
    have currentCheckpoint : SourceCheckpoint setup source refs offset
        current.application.config := by rw [same]; exact checkpoint
    have currentValid : current.application.BindingInvariant := by rw [same]; exact valid
    have currentReady : current.application.config.cut.Ready event := by rw [same]; exact ready
    have currentTimely : current.application.WithinDeadline (runtime setup) event := by
      rw [same]; exact timely
    have currentActivated : current.application.activatedAt event = some entered := by
      rw [same]; exact activated
    have currentDue : (runtime setup).deadline event ≤
        current.application.clock + ticks - entered := by
      rw [same]; exact due
    have currentSerials := (runtime setup).runInteractionPlan_serials leaks players network
      (visited.map ServiceInstruction.player) execution current serials reached
    have currentPublished : current.network.Satisfies fun message =>
        message.id ∈ current.network.ledger.map Message.id := by rwa [ledger]
    have pureReplay := reached
    rw [sourceServiceLastPolicy_waiting_law setup leaks rosters wholeProfile network event owner
      owned visited execution (soleReady_of_ready setup execution.application ready) before]
      at pureReplay
    have currentUnsent := (replay_window_eventRecorded setup leaks network visited execution current
      pureReplay owner event).trans unsent
    have fixed : (ServiceInstruction.wire : ServiceInstruction (graph setup)) ∉
        visited.map ServiceInstruction.player := by simp
    have currentCount := fixed_plan_response_counts setup leaks network players
      (visited.map ServiceInstruction.player) fixed execution current reached owner
    simp only [List.filterMap_map, Function.comp_def, instructionActor,
      List.filterMap_some] at currentCount
    have last : (current.recall owner).length + 1 =
        rosterOffset setup rosters owner event + (rosters event).count owner := by
      rw [currentCount, counted, total]
      omega
    have completed := sourceServiceLastPolicy_reveal_opportunity setup leaks rosters fresh binding
      unresolved next wholeProfile profile refs source embedding refsBefore offset aligned current
        currentCheckpoint currentValid entered ticks currentPublished currentSerials network
        remaining absent currentReady currentTimely currentActivated currentDue
          currentUnsent last
    simpa only [same, receipts, counters] using completed
  · exact PMF.bind_const _ expected

end Vegas
