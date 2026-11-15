module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceAcceptedContinuation
public import Vegas.Game.SourceServiceFirstTurnOpportunity
public import Vegas.Game.SourceServiceFirstTurnMixture
public import Vegas.Game.SourceServiceCanonicalAcceptance
public import Vegas.Game.SourceServiceTurnSubmissions
public import Vegas.EventGraph.PrefixRestriction
public import Vegas.Pending.ReactiveCompletion

@[expose] public section

/-! # Exact native records of fixed private-binding choices

A pure graph kernel at a binding fixes the recorded native action and output
whenever its owner remains active. The target need not be ready at the
starting boundary. Other clients and native service remain arbitrary.
Protected first callbacks also have their exact submitted record.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime EventGraph GameTheory.Protocol
  GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}

/-- Fixing an honest binding callback fixes the physical target record, without
constraining the callbacks of any other owner. -/
theorem decidedOpportunity_binding_response_record
    (timeouts : EventTimeouts (serviceGraph setup deps))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    {horizon remaining : Nat} (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (inclusion : ProtectedInclusion timeouts leaks
      (serviceInitialLaw setup deps) horizon scheduler bound)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (ownerSolitary : (serviceGraph setup deps).OwnerSolitary event)
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (payload : L.Ty)
    (binding : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (action : (serviceGraph setup deps).Action event)
    (result : PublicationResult (L.Val payload))
    (actionEq : action = cast (congrArg EventField.Action binding.symm) (some result))
    (execution : ((reactiveApplication timeouts) leaks).Execution)
    (trace : (((reactiveApplication timeouts) leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace
      (some ⟨remaining, some owner, execution⟩))
    (first : serviceTurn setup deps timeouts.duration leaks owner event
      (execution.logs owner) (execution.observe ((reactiveApplication timeouts) leaks) owner) =
        some 0)
    (fits : execution.application.publicView.InclusionFitsDeadline timeouts bound event)
    (truthful : OwnSubmissionsAtTurn setup leaks execution owner)
    (noRepeat : ∀ past view response,
      response ∈ (players owner past view).support →
      (eventRecorded timeouts) leaks past event = true →
      (submittedEvent? timeouts) leaks response ≠ some event)
    (response : ((reactiveApplication timeouts) leaks).Action)
    (selected : response ∈ (decidedOpportunity setup leaks bound owner event action
      (execution.logs owner)
        (execution.observe ((reactiveApplication timeouts) leaks) owner)).support) :
    ∀ stopped ∈ (((reactiveApplication timeouts) leaks).runUntil scheduler
      players
        (fun final => event ∈ final.application.config.cut.completed) remaining
        (execution.respond ((reactiveApplication timeouts) leaks) owner response)).support,
      event ∈ stopped.application.config.cut.completed →
      completionOf stopped.application.config event = some
          (EventGraph.completion (serviceGraph setup deps) event (some action)
            (cast (congrArg EventField.Value binding.symm) result)) ∧
        stopped.application.config.outputs event =
          some (cast (congrArg EventField.Value binding.symm) result) := by
  classical
  let app := (reactiveApplication timeouts) leaks
  have turn := (sourceServiceTurn_first first).1
  have never := (sourceServiceTurn_first first).2
  have ready := (execution.application.publicView_eventReady event).mp
    (execution.application.publicView.ownTurn?_spec owner event turn).1
  have codeEq : cast (congrArg (EventCode (serviceGraph setup deps).layout) binding)
      ((serviceGraph setup deps).nodes event) = .bind owner payload := by
    generalize cast (congrArg (EventCode (serviceGraph setup deps).layout) binding)
      ((serviceGraph setup deps).nodes event) = code
    cases code
    rfl
  have node := nodeView_eq_bind binding codeEq
  have effective : EffectiveAction execution.application.config event action := by
    simp only [EffectiveAction, node]
  have loudAction : ¬ SilentAction event action := by
    simp only [SilentAction, node, actionEq, cast_cast, cast_eq, reduceCtorEq, not_false_eq_true]
  obtain ⟨material, sends⟩ := canonicalServiceDecision_transmits_of_effective timeouts _ trace
    owner event turn action effective loudAction
  let canonical := (canonicalServiceDecision timeouts) leaks owner (execution.logs owner)
    (execution.observe app owner) event action
  have unsent : (eventRecorded timeouts) leaks (execution.logs owner) event = false := by
    cases recorded : (eventRecorded timeouts) leaks (execution.logs owner) event with
    | false => rfl
    | true =>
        obtain ⟨entry, remembered, submitted⟩ :=
          ((eventRecorded_iff timeouts) leaks _ event).mp recorded
        exact (never entry remembered (truthful entry remembered event submitted)).elim
  have loud : canonical.transmission ≠ none := by
    rw [sends]
    intro impossible
    cases impossible
  have chosen : response = canonical := by
    change response ∈ (if (eventRecorded timeouts) leaks (execution.logs owner) event then
      app.silentPolicy (execution.logs owner) (execution.observe app owner) else
      if execution.application.publicView.InclusionFitsDeadline timeouts bound event then
        if canonical.transmission = none then
          app.silentPolicy (execution.logs owner) (execution.observe app owner)
        else PMF.pure canonical else
          app.silentPolicy (execution.logs owner)
            (execution.observe app owner)).support at selected
    simpa only [unsent, Bool.false_eq_true, ↓reduceIte, ite_eq_left fits, ite_eq_right loud,
      PMF.mem_support_pure_iff] using selected
  subst response
  let after := execution.respond app owner canonical
  let entry := respondEntry setup timeouts leaks execution owner canonical
  let message := sentEnvelope setup timeouts leaks execution owner material
  have configEq : after.application.config = execution.application.config :=
    ((reactive_respond_application timeouts) leaks execution owner canonical).1
  have recalled : after.logs owner = execution.logs owner ++ [entry] := by
    rw [(respond_recall timeouts) leaks execution owner owner canonical, ite_eq_left rfl]
    rfl
  have recorded : entry ∈ after.logs owner := by
    rw [recalled]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have call : FreshCall setup leaks owner event bound entry message := by
    dsimp only [entry, message]
    rw [respondEntry_of_transmission execution owner canonical material sends]
    exact canonical_freshCall trace bound owner event turn fits action material sends
  have signed := signedCommitments_history timeouts leaks (serviceInitialLaw setup deps)
    (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨_, rfl⟩) horizon scheduler trace
  have sole : ∀ other ∈ after.logs owner,
      ¬ EmitsOtherFor timeouts leaks other event message.id := by
    intro other remembered emits
    rw [recalled] at remembered
    rcases List.mem_append.mp remembered with old | fresh
    · obtain ⟨packet, emitted, _sender, named, _different⟩ := emits
      obtain ⟨_sender, content, transmitted, packetEq⟩ :=
        signed.emissions owner other old packet emitted
      have submitted : (submittedEvent? timeouts) leaks other.action = some event := by
        simp only [EventGraphRuntime.submittedEvent?, transmitted]
        rw [← packetEq]
        exact named
      exact never other old (truthful other old event submitted)
    · obtain rfl := List.mem_singleton.mp fresh
      obtain ⟨packet, emitted, _sender, _named, different⟩ := emits
      have emittedEq : entry.emitted = some message := call.emitted
      have same : packet = message := Option.some.inj (emitted.symm.trans emittedEq)
      exact different (congrArg Message.id same)
  obtain ⟨output, witness⟩ := canonical_response_witness execution owner event turn action material
    sends
  have witnessAfter : AcceptanceWitness event message after.application.config action output
      after.application := by
    rw [configEq]
    have stateEq : after.application = app.submit execution.application owner material := by
      unfold after ReactiveApplication.Execution.respond
      rw [sends]
    rw [stateEq]
    exact witness
  obtain ⟨afterTrace⟩ := app.raw_trace_respond
    (serviceInitialLaw setup deps) horizon scheduler remaining
    execution owner canonical trace
  have certified := witnessAfter.binding_action_output binding
  rw [actionEq] at certified
  simp only [cast_cast, cast_eq, Option.some.injEq] at certified
  have valueEq : output = cast (congrArg EventField.Value binding.symm) result := by
    have reversed := congrArg (cast (congrArg EventField.Value binding.symm)) certified.symm
    simpa only [cast_cast, cast_eq] using reversed
  intro stopped reached completed
  have accounted : after.environmentRecall.length + remaining = horizon :=
    app.raw_trace_horizon (serviceInitialLaw setup deps) horizon scheduler afterTrace
  have countEq : horizon - after.environmentRecall.length = remaining := by omega
  have reachedHorizon : stopped ∈ (app.runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon after).support := by
    change stopped ∈ (app.runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed)
      (horizon - after.environmentRecall.length) after).support
    rw [countEq]
    exact reached
  have records := FreshCall.accepted_binding_record timeouts leaks scheduler players bound
    inclusion event ownerSolitary owner payload binding owned after afterTrace
    (configEq.symm ▸ ready) action output entry message recorded call sole witnessAfter noRepeat
    stopped reachedHorizon completed
  simpa only [valueEq] using records

/-- At the first actual binding callback, the service budget supplies the
protected packet and every completed member run retains the chosen binding.
No readiness assumption on this target at any earlier source boundary is needed. -/
theorem decidedOpportunity_first_binding_record
    (timeouts : EventTimeouts (serviceGraph setup deps))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    {horizon remaining : Nat} (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (delay bound : (serviceGraph setup deps).EventId → Nat)
    (contract : AsyncContract timeouts leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (ownerSolitary : (serviceGraph setup deps).OwnerSolitary event)
    (payload : L.Ty)
    (binding : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (result : PublicationResult (L.Val payload))
    (current middle : ((reactiveApplication timeouts) leaks).Execution)
    (trace : (((reactiveApplication timeouts) leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace
      (some ⟨remaining + 1, none, current⟩))
    (truthful : OwnSubmissionsAtTurn setup leaks current owner)
    (answered : ActivationsAnswered setup leaks current)
    (selected : (.activate owner : ((reactiveApplication timeouts) leaks).Command) ∈
      (scheduler current.environmentRecall
        (current.observeEnvironment ((reactiveApplication timeouts) leaks))).support)
    (moved : middle ∈ (current.environmentStep ((reactiveApplication timeouts) leaks)
      (.activate owner)).support)
    (first : serviceTurn setup deps timeouts.duration leaks owner event
      (middle.logs owner) (middle.observe ((reactiveApplication timeouts) leaks) owner) = some 0)
    (noRepeat : ∀ past view response,
      response ∈ (players owner past view).support →
      (eventRecorded timeouts) leaks past event = true →
      (submittedEvent? timeouts) leaks response ≠ some event)
    (response : ((reactiveApplication timeouts) leaks).Action)
    (responseSelected : response ∈ (decidedOpportunity setup leaks bound owner event
      (cast (congrArg EventField.Action binding.symm) (some result)) (middle.logs owner)
        (middle.observe ((reactiveApplication timeouts) leaks) owner)).support) :
    ∀ stopped ∈ (((reactiveApplication timeouts) leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) remaining
        (middle.respond ((reactiveApplication timeouts) leaks) owner response)).support,
      event ∈ stopped.application.config.cut.completed →
      completionOf stopped.application.config event = some
          (EventGraph.completion (serviceGraph setup deps) event
            (some (cast (congrArg EventField.Action binding.symm) (some result)))
            (cast (congrArg EventField.Value binding.symm) result)) ∧
        stopped.application.config.outputs event =
          some (cast (congrArg EventField.Value binding.symm) result) := by
  let app := (reactiveApplication timeouts) leaks
  have appEq := activation_application (setup := setup) leaks current middle owner moved
  have recallEq := app.environmentStep_recall current middle (.activate owner) moved
  have turn := (sourceServiceTurn_first first).1
  have owned := (middle.application.publicView.ownTurn?_spec owner event turn).2
  have readyMiddle := (middle.application.publicView_eventReady event).mp
    (middle.application.publicView.ownTurn?_spec owner event turn).1
  have ready : current.application.config.cut.Ready event := by
    rw [← appEq]
    exact readyMiddle
  have firstBefore : serviceTurn setup deps timeouts.duration leaks owner event
      (current.logs owner) (middle.observe app owner) = some 0 := by
    rw [← congrFun recallEq owner]
    exact first
  have fits := firstTurn_inclusionFits ownerSolitary contract timely trace answered owned ready
    firstBefore
  have fitsMiddle : middle.application.publicView.InclusionFitsDeadline timeouts bound event := by
    rw [appEq]
    exact fits
  have truthfulMiddle : OwnSubmissionsAtTurn setup leaks middle owner := by
    intro entry present
    rw [congrFun recallEq owner] at present
    exact truthful entry present
  obtain ⟨middleTrace⟩ := app.raw_trace_environment (serviceInitialLaw setup deps) horizon
    scheduler remaining current middle (.activate owner) trace selected moved
  exact decidedOpportunity_binding_response_record timeouts leaks scheduler bound
    contract.inclusion owner event ownerSolitary owned payload binding players
    (cast (congrArg EventField.Action binding.symm) (some result)) result rfl middle middleTrace
    first fitsMiddle truthfulMiddle noRepeat response responseSelected

private theorem fixed_reference_binding_response
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    {duration : (serviceGraph setup deps).EventId → Nat}
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (reference : (serviceGraph setup deps).BehavioralProfile)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (action : (serviceGraph setup deps).Action event)
    (fixed : ∀ view active, reference owner event owned view active = PMF.pure action)
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (response : (serviceApplication setup deps duration leaks).Action)
    (supported : response ∈ (serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps) reference owner (execution.logs owner)
        (execution.observe (serviceApplication setup deps duration leaks) owner)).support)
    (material : (serviceApplication setup deps duration leaks).Submission)
    (sends : response.transmission = some material)
    (named : material.call.packet.event? (serviceGraph setup deps) = some event) :
    response = (canonicalServiceDecision (serviceTimeouts setup deps duration)) leaks owner
      (execution.logs owner) (execution.observe (serviceApplication setup deps duration leaks)
        owner) event action := by
  let app := serviceApplication setup deps duration leaks
  have submitted : (submittedEvent? (serviceTimeouts setup deps duration)) leaks response =
      some event := by
    simp only [EventGraphRuntime.submittedEvent?, sends]
    exact named
  have turn := sourceServiceTurnPolicy_submitsAtTurn_reference setup leaks bound turns
    (firstTurnTiming setup turns deps) reference owner _ _ response supported event submitted
  have first : serviceTurn setup deps duration leaks owner event (execution.logs owner)
      (execution.observe app owner) = some 0 := by
    by_contra later
    rw [sourceServiceTurnPolicy_laterTurn_reference owned turn later,
      PMF.mem_support_pure_iff] at supported
    cases supported
    cases sends
  rw [sourceServiceTurnPolicy_firstTurn_reference owned first] at supported
  unfold serviceReferenceOpportunity at supported
  split at supported
  · cases (PMF.mem_support_pure_iff _ _).mp supported
    cases sends
  · split at supported
    · obtain ⟨chosen, kernel, selected⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      by_cases silent : chosen.transmission = none
      · rw [ite_eq_left silent, ReactiveApplication.silentPolicy_apply,
          PMF.mem_support_pure_iff] at selected
        subst response
        cases sends
      · rw [ite_eq_right silent, PMF.mem_support_pure_iff] at selected
        subst response
        rw [sourceServiceCanonicalPolicy_at_event_reference setup leaks reference owner execution
          event turn owned] at kernel
        split at kernel
        · cases (PMF.mem_support_pure_iff _ _).mp kernel
          cases sends
        · rw [fixed, PMF.pure_map, PMF.mem_support_pure_iff] at kernel
          exact kernel
    · cases (PMF.mem_support_pure_iff _ _).mp supported
      cases sends

section FixedCalls

variable {duration : (serviceGraph setup deps).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))

private def BindingCallsFixed (owner : Player) (event : (serviceGraph setup deps).EventId)
    (action : (serviceGraph setup deps).Action event)
    (output : ((serviceGraph setup deps).outputLayout event).Value)
    (execution : (serviceApplication setup deps duration leaks).Execution) : Prop :=
  ∀ message ∈ (serviceApplication setup deps duration leaks).outputs (execution.logs owner),
    message.payload.call.event? (serviceGraph setup deps) = some event →
      AcceptanceWitness event message execution.application.config action output
        execution.application

private theorem fixed_reference_binding_witness
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (reference : (serviceGraph setup deps).BehavioralProfile)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (payload : L.Ty)
    (binding : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (result : PublicationResult (L.Val payload))
    (action : (serviceGraph setup deps).Action event)
    (actionEq : action = cast (congrArg EventField.Action binding.symm) (some result))
    (fixed : ∀ view active, reference owner event owned view active = PMF.pure action)
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (response : (serviceApplication setup deps duration leaks).Action)
    (supported : response ∈ (serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps) reference owner (execution.logs owner)
        (execution.observe (serviceApplication setup deps duration leaks) owner)).support)
    (material : (serviceApplication setup deps duration leaks).Submission)
    (sends : response.transmission = some material)
    (named : material.call.packet.event? (serviceGraph setup deps) = some event) :
    AcceptanceWitness event
      (sentEnvelope setup (serviceTimeouts setup deps duration) leaks execution owner material)
      execution.application.config action (cast (congrArg EventField.Value binding.symm) result)
      (execution.respond (serviceApplication setup deps duration leaks) owner
        response).application := by
  let app := serviceApplication setup deps duration leaks
  have chosen := fixed_reference_binding_response leaks bound turns reference owner event owned
    action fixed execution response supported material sends named
  have submitted : (submittedEvent? (serviceTimeouts setup deps duration)) leaks response =
      some event := by simp only [EventGraphRuntime.submittedEvent?, sends]; exact named
  have turn := sourceServiceTurnPolicy_submitsAtTurn_reference setup leaks bound turns
    (firstTurnTiming setup turns deps) reference owner _ _ response supported event submitted
  obtain ⟨output, witness⟩ := canonical_response_witness execution owner event turn action material
    (chosen ▸ sends)
  have certified := witness.binding_action_output binding
  rw [actionEq] at certified
  simp only [cast_cast, cast_eq, Option.some.injEq] at certified
  have valueEq : output = cast (congrArg EventField.Value binding.symm) result := by
    have reversed := congrArg (cast (congrArg EventField.Value binding.symm)) certified.symm
    simpa only [cast_cast, cast_eq] using reversed
  have same : (execution.respond app owner response).application =
      app.submit execution.application owner material := by
    unfold ReactiveApplication.Execution.respond
    rw [sends]
  rw [same, ← valueEq]
  exact witness

private theorem BindingCallsFixed.respond
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (reference : (serviceGraph setup deps).BehavioralProfile)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (payload : L.Ty)
    (binding : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (result : PublicationResult (L.Val payload))
    (action : (serviceGraph setup deps).Action event)
    (actionEq : action = cast (congrArg EventField.Action binding.symm) (some result))
    (fixed : ∀ view active, reference owner event owned view active = PMF.pure action)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (follows : players owner = serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps) reference owner)
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (actor : Player) (response : (serviceApplication setup deps duration leaks).Action)
    (valid : BindingCallsFixed leaks owner event action
      (cast (congrArg EventField.Value binding.symm) result) execution)
    (supported : response ∈ (players actor (execution.logs actor)
      (execution.observe (serviceApplication setup deps duration leaks) actor)).support) :
    BindingCallsFixed leaks owner event action
      (cast (congrArg EventField.Value binding.symm) result)
      (execution.respond (serviceApplication setup deps duration leaks) actor response) := by
  let app := serviceApplication setup deps duration leaks
  have old (message) (member : message ∈ app.outputs (execution.logs owner))
      (named : message.payload.call.event? (serviceGraph setup deps) = some event) :
      AcceptanceWitness event message
        (execution.respond app actor response).application.config action
        (cast (congrArg EventField.Value binding.symm) result)
        (execution.respond app actor response).application :=
    ((valid message member named).keep
      (((keepsFixedCandidates_step (serviceTimeouts setup deps duration)) leaks).respond
        execution actor response)).binding_rebase binding
  intro message member named
  by_cases same : actor = owner
  · subst actor
    rw [follows] at supported
    rcases response with ⟨transmission⟩
    cases transmission with
    | none =>
        simp only [ReactiveApplication.Execution.respond, ↓reduceIte,
          ReactiveApplication.outputs, List.filterMap_append, List.filterMap_cons,
          List.filterMap_nil, List.append_nil] at member
        exact old message member named
    | some material =>
        simp only [ReactiveApplication.Execution.respond, ↓reduceIte,
          ReactiveApplication.outputs, List.filterMap_append, List.filterMap_cons,
          List.filterMap_nil] at member
        rcases List.mem_append.mp member with previous | fresh
        · exact old message previous named
        · obtain rfl := List.mem_singleton.mp fresh
          have witness := fixed_reference_binding_witness leaks bound turns reference owner event
            owned payload binding result action actionEq fixed execution ⟨some material⟩ supported
            material rfl named
          exact witness.binding_rebase binding
  · rw [app.respond_recall_other execution actor owner (Ne.symm same) response] at member
    exact old message member named

private def BindingRecordsFixed (owner : Player) (event : (serviceGraph setup deps).EventId)
    (action : (serviceGraph setup deps).Action event)
    (output : ((serviceGraph setup deps).outputLayout event).Value)
    (execution : (serviceApplication setup deps duration leaks).Execution) : Prop :=
  owner ∉ execution.application.config.defaulted →
    event ∈ execution.application.config.cut.completed →
      completionOf execution.application.config event =
          some (EventGraph.completion (serviceGraph setup deps) event (some action) output) ∧
        execution.application.config.outputs event = some output

private theorem BindingCallsFixed.environment
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (payload : L.Ty)
    (binding : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (action : (serviceGraph setup deps).Action event)
    (output : ((serviceGraph setup deps).outputLayout event).Value)
    (execution next : (serviceApplication setup deps duration leaks).Execution)
    (command : (serviceApplication setup deps duration leaks).Command)
    (valid : BindingCallsFixed leaks owner event action output execution)
    (reached : next ∈ (execution.environmentStep
      (serviceApplication setup deps duration leaks) command).support) :
    BindingCallsFixed leaks owner event action output next := by
  let app := serviceApplication setup deps duration leaks
  have recallEq := app.environmentStep_recall execution next command reached
  intro message member named
  rw [recallEq] at member
  exact ((valid message member named).keep
    (((keepsFixedCandidates_step (serviceTimeouts setup deps duration)) leaks).environmentStep
      execution next command reached)).binding_rebase binding

private theorem expired_binding_action {event : (serviceGraph setup deps).EventId}
    {action : (serviceGraph setup deps).Action event} (expired : ExpiredAction event action)
    (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup deps).outputLayout event = .binding owner payload) :
    action = cast (congrArg EventField.Action binding.symm)
      (none : Option (PublicationResult (L.Val payload))) := by
  cases expired with
  | binding actor ty other =>
      have same := EventField.binding.inj (other.symm.trans binding)
      rcases same with ⟨rfl, rfl⟩
      rfl
  | publication ty other => cases other.symm.trans binding

private theorem BindingRecordsFixed.environment
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (payload : L.Ty)
    (binding : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (action : (serviceGraph setup deps).Action event)
    (output : ((serviceGraph setup deps).outputLayout event).Value)
    (execution next : (serviceApplication setup deps duration leaks).Execution)
    (command : (serviceApplication setup deps duration leaks).Command)
    (provenance : execution.Provenance (serviceApplication setup deps duration leaks))
    (calls : BindingCallsFixed leaks owner event action output execution)
    (records : BindingRecordsFixed leaks owner event action output execution)
    (reached : next ∈ (execution.environmentStep
      (serviceApplication setup deps duration leaks) command).support) :
    BindingRecordsFixed leaks owner event action output next := by
  let app := serviceApplication setup deps duration leaks
  let timeouts := serviceTimeouts setup deps duration
  intro active completed
  have path := ((reactiveApplication_graphSteps timeouts) leaks).environmentStep execution next
    command reached
  have beforeActive : owner ∉ execution.application.config.defaulted :=
    fun inactive => active (Config.Step.path_defaulted_mono path inactive)
  by_cases previous : event ∈ execution.application.config.cut.completed
  · have saved := records beforeActive previous
    exact ⟨Config.Step.path_completionOf_of_some path event _ saved.1,
      Config.Step.path_store_of_some path (.inr event) output saved.2⟩
  · obtain ⟨record, found⟩ := Option.isSome_iff_exists.mp
      ((completionOf_isSome_iff next.application.config event).mpr completed)
    obtain ⟨present, eventEq⟩ :=
      (completionOf_eq_some_iff next.application.config event record).mp found
    subst event
    have fresh : record ∉ execution.application.config.history := by
      intro earlier
      exact previous ((execution.application.config.history_exact record.event).mp
        (List.mem_map.mpr ⟨record, earlier, rfl⟩))
    rcases reactive_new_completion_cases timeouts leaks execution next command reached record fresh
        present with accepted | expired | ownerless | automatic
    · obtain ⟨message, pending, native, _, _, named, sender, handled, drained, _⟩ := accepted
      have senderEq : message.sender = owner := Option.some.inj (sender.symm.trans owned)
      obtain ⟨entry, remembered, material, transmitted, emitted, _⟩ :=
        provenance.pending message pending
      rw [senderEq] at remembered
      have recalled : message ∈ app.outputs (execution.logs owner) :=
        List.mem_filterMap.mpr ⟨entry, remembered, emitted⟩
      have witness := calls message recalled named
      obtain ⟨ready, actual, nativeEq⟩ := witness.complete timeouts rfl handled
      have nativeRecord : completionOf native.config record.event =
          some (EventGraph.completion (serviceGraph setup deps) record.event (some action)
            output) := by
        rw [nativeEq, completionOf_complete, Function.update_self, actual]
      have stored : native.config.outputs record.event = some output := by
        rw [nativeEq, Config.complete_output_same]
      rw [← drained]
      exact ⟨Config.Step.path_completionOf_of_some native.drain_graph_steps _ _ nativeRecord,
        Config.Step.path_store_of_some native.drain_graph_steps (.inr record.event) output stored⟩
    · obtain ⟨_, _, _, _, expiredAction, value, expired, recordEq⟩ := expired
      have expiredEq := expired_binding_action expired owner payload binding
      have codeEq : cast (congrArg (EventCode (serviceGraph setup deps).layout) binding)
          ((serviceGraph setup deps).nodes record.event) = .bind owner payload := by
        generalize cast (congrArg (EventCode (serviceGraph setup deps).layout) binding)
          ((serviceGraph setup deps).nodes record.event) = code
        cases code
        rfl
      have defaultEq := congrArg EventCompletion.defaultEvent recordEq
      rw [expiredEq] at defaultEq
      have omitted := execution.application.config.completion_bind_none_defaultEvent
        record.event owner payload binding codeEq (cast (congrArg EventField.Value binding) value)
      simp only [cast_cast, cast_eq, ite_eq_right beforeActive] at omitted
      rw [omitted] at defaultEq
      exact (active ((mem_defaulted_iff_completionOf next.application.config owner).mpr
        ⟨record.event, by rw [found]; exact defaultEq⟩)).elim
    · rw [owned] at ownerless
      cases ownerless
    · obtain ⟨native, drained, _, _, _, _, actor, acting, inactive⟩ := automatic
      have same : actor = owner := Option.some.inj (acting.symm.trans owned)
      subst actor
      apply (active ?_).elim
      rw [← drained, native.drain_defaulted]
      exact inactive

private theorem fixed_binding_policyInvariant
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (reference : (serviceGraph setup deps).BehavioralProfile)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (payload : L.Ty)
    (binding : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (result : PublicationResult (L.Val payload))
    (action : (serviceGraph setup deps).Action event)
    (actionEq : action = cast (congrArg EventField.Action binding.symm) (some result))
    (fixed : ∀ view active, reference owner event owned view active = PMF.pure action)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (follows : players owner = serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps) reference owner) :
    (serviceApplication setup deps duration leaks).PolicyInvariant players (fun execution =>
      execution.Provenance (serviceApplication setup deps duration leaks) ∧
        BindingCallsFixed leaks owner event action
          (cast (congrArg EventField.Value binding.symm) result) execution ∧
        BindingRecordsFixed leaks owner event action
          (cast (congrArg EventField.Value binding.symm) result) execution) where
  respond execution actor response valid supported := by
    refine ⟨(serviceApplication setup deps duration leaks).respond_provenance execution actor
      response valid.1, BindingCallsFixed.respond leaks bound turns reference owner event owned
        payload binding result action actionEq fixed players follows execution actor response
          valid.2.1 supported, ?_⟩
    intro active completed
    have same := ((reactive_respond_application (serviceTimeouts setup deps duration)) leaks
      execution actor response).1
    rw [same] at active completed ⊢
    exact valid.2.2 active completed
  environment execution next command valid reached :=
    ⟨(serviceApplication setup deps duration leaks).environment_provenance execution next command
        valid.1 reached,
      BindingCallsFixed.environment leaks owner event payload binding action _ execution next
        command valid.2.1 reached,
      BindingRecordsFixed.environment leaks owner event owned payload binding action _ execution
        next command valid.1 valid.2.1 valid.2.2 reached⟩

/-- A fixed graph binding kernel fixes every later active physical binding record.
The event need not be ready initially, other clients remain arbitrary, and own
expiry is retained in the public-default alternative. -/
theorem fixed_reference_binding_record_runRounds
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (reference : (serviceGraph setup deps).BehavioralProfile)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (payload : L.Ty)
    (binding : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (result : PublicationResult (L.Val payload))
    (fixed : ∀ view active, reference owner event owned view active =
      PMF.pure (cast (congrArg EventField.Action binding.symm) (some result)))
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (follows : players owner = serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps) reference owner)
    {horizon remaining : Nat} {acting : Option Player}
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace
      (some ⟨remaining, acting, execution⟩))
    (truthful : OwnSubmissionsAtTurn setup leaks execution owner)
    (untouched : Untouched setup leaks event execution)
    (unfinished : event ∉ execution.application.config.cut.completed)
    (count : Nat) (next : (serviceApplication setup deps duration leaks).Execution)
    (reached : next ∈ ((serviceApplication setup deps duration leaks).runRounds scheduler players
      count execution).support)
    (completed : event ∈ next.application.config.cut.completed) :
    owner ∈ next.application.config.defaulted ∨
      (completionOf next.application.config event = some
          (EventGraph.completion (serviceGraph setup deps) event
            (some (cast (congrArg EventField.Action binding.symm) (some result)))
            (cast (congrArg EventField.Value binding.symm) result)) ∧
        next.application.config.outputs event =
          some (cast (congrArg EventField.Value binding.symm) result)) := by
  let app := serviceApplication setup deps duration leaks
  have signed := signedCommitments_history (serviceTimeouts setup deps duration) leaks
    (serviceInitialLaw setup deps) (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨_, rfl⟩) horizon scheduler trace
  have clean : BindingCallsFixed leaks owner event
      (cast (congrArg EventField.Action binding.symm) (some result))
      (cast (congrArg EventField.Value binding.symm) result) execution := by
    intro message member named
    obtain ⟨entry, remembered, emitted⟩ := List.mem_filterMap.mp member
    obtain ⟨_, material, transmission, packet⟩ := signed.emissions owner entry remembered message
      emitted
    have submitted : (submittedEvent? (serviceTimeouts setup deps duration)) leaks entry.action =
        some event := by
      simp only [EventGraphRuntime.submittedEvent?, transmission]
      rw [← packet]
      exact named
    have turn := truthful entry remembered event submitted
    exact (untouched owner entry remembered
      (entry.beforeView.application.publicView.ownTurn?_spec owner event turn).1).elim
  have initial : execution.Provenance app ∧
      BindingCallsFixed leaks owner event
        (cast (congrArg EventField.Action binding.symm) (some result))
        (cast (congrArg EventField.Value binding.symm) result) execution ∧
      BindingRecordsFixed leaks owner event
        (cast (congrArg EventField.Action binding.symm) (some result))
        (cast (congrArg EventField.Value binding.symm) result) execution :=
    ⟨signed.provenance, clean, fun _ completed => (unfinished completed).elim⟩
  have valid := (fixed_binding_policyInvariant leaks bound turns reference owner event owned
    payload binding result _ rfl fixed players follows).runRounds scheduler count execution next
      initial reached
  by_cases inactive : owner ∈ next.application.config.defaulted
  · exact Or.inl inactive
  · exact Or.inr (valid.2.2 inactive completed)

end FixedCalls

end Vegas
