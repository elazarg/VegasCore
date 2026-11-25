module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.AcceptedContinuation
public import Vegas.Pending.CanonicalAcceptance
public import Vegas.Pending.CanonicalTransmission
public import Vegas.Pending.FirstCallback
public import Vegas.Pending.FirstTurnSilence
public import Vegas.Pending.TurnClientSubmissions

@[expose] public section

/-! # Realization of a fixed graph action at its first ledger turn -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  {inputs : PMF graph.Inputs}

private theorem firstTurn_fixed_accepted_runUntil_bind_runPlan
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    {horizon remaining turns : Nat} (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (delay bound : graph.EventId → Nat)
    (client : graph.BehavioralProfile) {Result : Type*} (continuation :
      graph.Config → PMF Result)
    (drained : ∀ state : EventGraphRuntime.State graph,
      continuation state.drain.config = continuation state.config)
    (contract : AsyncContract timeouts leaks
      (inputs.map State.initial) horizon scheduler delay bound)
    (owner : Player) (event : graph.EventId)
    (owned : graph.actor? event = some owner) (solitary :
      graph.Solitary event)
    (background : Player → ((reactiveApplication timeouts) leaks).Policy)
    (action : graph.Action event)
    (execution : ((reactiveApplication timeouts) leaks).Execution)
    (trace : (((reactiveApplication timeouts) leaks).protocol
      (inputs.map State.initial) horizon scheduler).Trace
      (some ⟨remaining, some owner, execution⟩))
    (ready : execution.application.config.cut.Ready event)
    (turn : execution.application.publicView.ownTurn? owner = some event)
    (first : turnIndex timeouts leaks owner event
      (execution.logs owner) (execution.observe ((reactiveApplication timeouts) leaks) owner) =
        some 0)
    (fits : execution.application.publicView.InclusionFitsDeadline timeouts bound event)
    (truthful : OwnSubmissionsAtTurn timeouts leaks execution owner)
    (never : ∀ entry ∈ execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠ some event)
    (material : ((reactiveApplication timeouts) leaks).Submission)
    (sends : ((canonicalServiceDecision timeouts) leaks owner (execution.logs owner)
      (execution.observe ((reactiveApplication timeouts) leaks) owner) event action).transmission =
        some material)
    (response : ((reactiveApplication timeouts) leaks).Action)
    (selected : response ∈ (if turnIndex timeouts leaks owner event
        (execution.logs owner)
          (execution.observe ((reactiveApplication timeouts) leaks) owner) = some 0
      then fixedOpportunity timeouts leaks bound owner event action (execution.logs owner)
        (execution.observe ((reactiveApplication timeouts) leaks) owner)
      else turnPolicy timeouts leaks bound turns
        (EventGraphRuntime.firstTurnTiming graph turns) client owner (execution.logs owner)
          (execution.observe ((reactiveApplication timeouts) leaks) owner)).support) :
    let players := turnPolicy timeouts leaks bound turns
      (EventGraphRuntime.firstTurnTiming graph turns) client
    let member := fun past view =>
      if turnIndex timeouts leaks owner event past view = some 0 then
        fixedOpportunity timeouts leaks bound owner event action past view
      else players owner past view
    ((((reactiveApplication timeouts) leaks).runUntil scheduler
      (Function.update background owner member)
        (fun final => event ∈ final.application.config.cut.completed) remaining
        (execution.respond ((reactiveApplication timeouts) leaks) owner response)).bind fun
          stopped =>
      continuation stopped.application.config) =
      (execution.application.config.step event ready action).bind fun after =>
        continuation after := by
  classical
  let app := (reactiveApplication timeouts) leaks
  let players := turnPolicy timeouts leaks bound turns
    (EventGraphRuntime.firstTurnTiming graph turns) client
  let member := fun past view =>
    if turnIndex timeouts leaks owner event past view = some 0 then
      fixedOpportunity timeouts leaks bound owner event action past view
    else players owner past view
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
    rw [ite_eq_left first] at selected
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
  let entry := respondEntry timeouts leaks execution owner canonical
  let message := sentEnvelope timeouts leaks execution owner material
  have configEq : after.application.config = execution.application.config :=
    ((reactive_respond_application timeouts) leaks execution owner canonical).1
  have recalled : after.logs owner = execution.logs owner ++ [entry] := by
    rw [(respond_recall timeouts) leaks execution owner owner canonical, ite_eq_left rfl]
    rfl
  have recorded : entry ∈ after.logs owner := by
    rw [recalled]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have call : FreshCall timeouts leaks owner event bound entry message := by
    dsimp only [entry, message]
    rw [respondEntry_of_transmission execution owner canonical material sends]
    exact canonical_freshCall trace bound owner event turn fits action material sends
  have signed := signedCommitments_history timeouts leaks (inputs.map State.initial)
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
    (inputs.map State.initial) horizon scheduler remaining
    execution owner canonical trace
  have noRepeat : ∀ past view response,
      response ∈ ((Function.update background owner member) owner past view).support →
      (eventRecorded timeouts) leaks past event = true →
      (submittedEvent? timeouts) leaks response ≠ some event := by
    intro past view response supported recorded
    rw [Function.update_self] at supported
    exact fixedAction_noRepeatedEvent timeouts leaks bound turns
      (EventGraphRuntime.firstTurnTiming _ turns) client
      owner event action past view response supported recorded
  have accepted := FreshCall.accepted_continuation timeouts leaks continuation drained scheduler
    (Function.update background owner member) bound contract.inclusion contract.completes
      event solitary owner
      owned after afterTrace (configEq.symm ▸ ready) action output entry message recorded call sole
        witnessAfter noRepeat
  have accounted : execution.environmentRecall.length + remaining = horizon :=
    app.raw_trace_horizon (inputs.map State.initial) horizon scheduler trace
  have countEq : horizon - after.environmentRecall.length = remaining := by
    rw [ReactiveApplication.respond_environmentRecall]
    omega
  change (app.runUntil scheduler (Function.update background owner member)
    (fun final => event ∈ final.application.config.cut.completed)
    (horizon - after.environmentRecall.length) after).bind _ = _ at accepted
  rw [countEq] at accepted
  simpa only [configEq] using accepted

private theorem firstTurn_fixed_transmitting_runUntil_bind_runPlan
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    {horizon turns : Nat} (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (delay bound : graph.EventId → Nat)
    (client : graph.BehavioralProfile) {Result : Type*} (continuation :
      graph.Config → PMF Result)
    (drained : ∀ state : EventGraphRuntime.State graph,
      continuation state.drain.config = continuation state.config)
    (contract : AsyncContract timeouts leaks
      (inputs.map State.initial) horizon scheduler delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (owner : Player) (event : graph.EventId)
    (owned : graph.actor? event = some owner) (solitary :
      graph.Solitary event)
    (background : Player → ((reactiveApplication timeouts) leaks).Policy)
    (follows : background owner = turnPolicy timeouts leaks
      bound turns (EventGraphRuntime.firstTurnTiming graph turns) client owner)
    (action : graph.Action event)
    (execution : ((reactiveApplication timeouts) leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (supported : execution ∈ (((reactiveApplication timeouts) leaks).roundsFrom
      (inputs.map State.initial) scheduler background
        execution.environmentRecall.length).support)
    (untouched : ∀ who, ∀ entry ∈ execution.logs who,
      ¬ entry.beforeView.application.publicView.EventReady event)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (effective : EffectiveAction execution.application.config event action)
    (loud : ¬ SilentAction event action) :
    let players := turnPolicy timeouts leaks bound turns
      (EventGraphRuntime.firstTurnTiming graph turns) client
    let member := fun past view =>
      if turnIndex timeouts leaks owner event past view = some 0 then
        fixedOpportunity timeouts leaks bound owner event action past view
      else players owner past view
    ((((reactiveApplication timeouts) leaks).runUntilHorizon scheduler
        (Function.update background owner member)
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
      fun stopped =>
        continuation stopped.application.config) =
      (execution.application.config.step event ready action).bind
        fun after => continuation after := by
  classical
  let app := (reactiveApplication timeouts) leaks
  let players := turnPolicy timeouts leaks bound turns
    (EventGraphRuntime.firstTurnTiming graph turns) client
  let member := fun past view =>
    if turnIndex timeouts leaks owner event past view = some 0 then
      fixedOpportunity timeouts leaks bound owner event action past view
    else players owner past view
  have atTurn : SubmitsAtTurn timeouts leaks (background owner) owner := by
    rw [follows]
    exact turnPolicy_submitsAtTurn timeouts leaks bound turns
      (EventGraphRuntime.firstTurnTiming graph turns)
      client owner
  have truthful : OwnSubmissionsAtTurn timeouts leaks execution owner :=
    SubmitsAtTurn.roundsFrom timeouts leaks atTurn (inputs.map State.initial)
      execution.environmentRecall.length execution
      supported
  have never : ∀ entry ∈ execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠ some event := by
    intro entry remembered turn
    exact untouched owner entry remembered
      (entry.beforeView.application.publicView.ownTurn?_spec owner event turn).1
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (inputs.map State.initial) horizon scheduler
    background
    execution.environmentRecall.length bounded execution supported
  apply first_callback_runUntil timeouts leaks scheduler (Function.update background owner member)
    delay bound continuation contract timely owner event owned solitary action ?_
      (horizon - execution.environmentRecall.length) execution trace
      ready truthful never
      (roundsFrom_activationsAnswered _ execution supported) effective
  intro remaining current currentTrace ready first fits truthful never effective response selected
  rw [Function.update_self] at selected
  have turn := current.application.ownTurn?_of_ready solitary.ownerSolitary ready owned
  obtain ⟨material, sends⟩ := canonicalServiceDecision_transmits_of_effective timeouts _
    currentTrace
    owner event turn action effective loud
  exact firstTurn_fixed_accepted_runUntil_bind_runPlan timeouts leaks scheduler delay bound client
    continuation drained contract owner event owned solitary background action current
      currentTrace ready turn first
    fits truthful
      never material sends response selected

/-- Fixing one owner's first graph action preserves its full canonical
continuation against arbitrary other players, including automatic completion. -/
theorem firstTurn_fixedAction_continuation
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    {horizon turns : Nat} (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (delay bound : graph.EventId → Nat)
    (client : graph.BehavioralProfile) {Result : Type*} (continuation :
      graph.Config → PMF Result)
    (drained : ∀ state : EventGraphRuntime.State graph,
      continuation state.drain.config = continuation state.config)
    (contract : AsyncContract timeouts leaks
      (inputs.map State.initial) horizon scheduler delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (owner : Player) (event : graph.EventId)
    (owned : graph.actor? event = some owner) (solitary :
      graph.Solitary event)
    (background : Player → ((reactiveApplication timeouts) leaks).Policy)
    (follows : background owner = turnPolicy timeouts leaks
      bound turns (EventGraphRuntime.firstTurnTiming graph turns) client owner)
    (action : graph.Action event)
    (execution : ((reactiveApplication timeouts) leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (supported : execution ∈ (((reactiveApplication timeouts) leaks).roundsFrom
      (inputs.map State.initial) scheduler background
        execution.environmentRecall.length).support)
    (untouched : ∀ who, ∀ entry ∈ execution.logs who,
      ¬ entry.beforeView.application.publicView.EventReady event)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (effective : EffectiveAction execution.application.config event action) :
    let players := turnPolicy timeouts leaks bound turns
      (EventGraphRuntime.firstTurnTiming graph turns) client
    let member := fun past view =>
      if turnIndex timeouts leaks owner event past view = some 0 then
        fixedOpportunity timeouts leaks bound owner event action past view
      else players owner past view
    ((((reactiveApplication timeouts) leaks).runUntilHorizon scheduler
        (Function.update background owner member)
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
      fun stopped =>
        continuation stopped.application.config) =
      (execution.application.config.step event ready action).bind
        fun after => continuation after := by
  by_cases silent : SilentAction event action
  · exact firstTurn_fixed_silent_continuation timeouts leaks inputs scheduler delay bound
      client continuation drained contract owner event owned solitary background follows action
        silent execution
      ready supported untouched bounded
  · exact firstTurn_fixed_transmitting_runUntil_bind_runPlan timeouts leaks scheduler delay bound
      client continuation drained contract timely owner event owned solitary background follows
        action execution
      ready supported untouched bounded effective silent


end Vegas.EventGraphRuntime
