module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.TurnClientSubmissions
public import Vegas.Pending.ActivationRecall
public import Vegas.Pending.ExecutionFacts
public import Vegas.Pending.ReactiveCandidateBudget
public import Vegas.Pending.ReactiveCanonicalMenu
public import Interaction.ReactiveRawRoundTrace

@[expose] public section

/-! # Counted commitment slots for graph clients -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => (reactiveApplication timeouts) leaks

/-- Silence never makes a fresh submission. -/
theorem silentPolicy_not_transmit
    {past : List (app).PlayerEntry}
    {view : (app).PlayerView}
    {response : (app).Action}
    (chosen : response ∈
        ((app).silentPolicy past view).support)
    (material : (app).Submission) :
    response.transmission ≠ some material := by
  obtain rfl := (app).silentPolicy_cases past view
      response chosen
  simp

/-- A fresh submission of the canonical source policy is the canonical decision
at the player's own turn. -/
private theorem referencePolicy_canonical_transmission {reference :
    graph.BehavioralProfile}
    {who : Player} {past : List (app).PlayerEntry}
    {view : (app).PlayerView}
    {response : (app).Action}
    (chosen : response ∈
        (referencePolicy timeouts
          leaks reference who past view).support)
    {material : (app).Submission}
    (submits : response.transmission = some material) :
    ∃ event action, view.application.publicView.ownTurn? who = some event ∧
      response = (canonicalServiceDecision timeouts) leaks who past
        view
          event action := by
  unfold EventGraphRuntime.referencePolicy at chosen
  split at chosen
  · split at chosen
    · rw [PMF.mem_support_pure_iff] at chosen
      subst chosen
      cases submits
    · rename_i event turn
      split at chosen
      · dsimp only at chosen
        split at chosen
        · rw [PMF.mem_support_pure_iff] at chosen
          subst chosen
          cases submits
        · rw [PMF.support_map] at chosen
          obtain ⟨action, _, rfl⟩ := chosen
          exact ⟨event, action, turn, rfl⟩
      · rw [PMF.mem_support_pure_iff] at chosen
        subst chosen
        cases submits
  · rw [PMF.mem_support_pure_iff] at chosen
    subst chosen
    cases submits

/-- A fresh submission of a canonical opportunity is made before the event is
recorded and while a fresh call fits the deadline. -/
private theorem referenceOpportunity_canonical_transmission
    {bound : graph.EventId → Nat} {reference :
      graph.BehavioralProfile}
    {who : Player} {event : graph.EventId}
    {past : List (app).PlayerEntry}
    {view : (app).PlayerView}
    {response : (app).Action}
    (chosen : response ∈
        (referenceOpportunity timeouts leaks
          bound reference who event past
        view).support) {material : (app).Submission}
    (submits : response.transmission = some material) :
    (eventRecorded timeouts) leaks past event = false ∧
    view.application.publicView.InclusionFitsDeadline timeouts bound
    event ∧ ∃ turnEvent action, view.application.publicView.ownTurn? who = some turnEvent ∧
    response = (canonicalServiceDecision timeouts) leaks who past view
    turnEvent
          action := by
  unfold EventGraphRuntime.referenceOpportunity at chosen
  split at chosen
  · exact (silentPolicy_not_transmit timeouts leaks chosen material submits).elim
  · rename_i unrecorded
    split at chosen
    · rename_i fits
      rw [PMF.support_bind] at chosen
      obtain ⟨decided, decidedChosen, member⟩ := Set.mem_iUnion₂.mp chosen
      split at member
      · exact (silentPolicy_not_transmit timeouts leaks member material submits).elim
      · rw [PMF.mem_support_pure_iff] at member
        subst member
        exact ⟨by simpa using unrecorded, fits,
          referencePolicy_canonical_transmission timeouts leaks decidedChosen submits⟩
    · exact (silentPolicy_not_transmit timeouts leaks chosen material submits).elim

/-- **Fresh submissions of the turn-counted policy.** Every fresh submission on
its support, at any turn index, is the canonical decision at the player's own
turn, at an event not yet recorded in its recall, while a fresh call fits the
deadline within the inclusion bound. -/
theorem turnPolicy_canonical_transmission {bound :
    graph.EventId → Nat}
    {turns : Nat} {timing : EventGraphRuntime.TurnTiming graph turns} {reference :
      graph.BehavioralProfile}
    {who : Player} {past : List (app).PlayerEntry}
    {view : (app).PlayerView}
    {response : (app).Action}
    (chosen : response ∈
        (turnPolicy timeouts leaks
          bound turns timing reference who past
        view).support) {material : (app).Submission}
    (submits : response.transmission = some material) : ∃ event action,
    view.application.publicView.ownTurn? who = some event ∧
    (eventRecorded timeouts) leaks past event = false ∧
    view.application.publicView.InclusionFitsDeadline timeouts
    bound event ∧
      response = (canonicalServiceDecision timeouts) leaks who past
        view
          event action := by
  unfold EventGraphRuntime.turnPolicy at chosen
  split at chosen
  · exact (silentPolicy_not_transmit timeouts leaks chosen material submits).elim
  · rename_i event turn
    split at chosen
    · rw [ReactiveApplication.policyMixture_policy, PMF.support_bind] at chosen
      obtain ⟨slot, _, member⟩ := Set.mem_iUnion₂.mp chosen
      unfold EventGraphRuntime.turnFamily ReactiveApplication.turnScheduledPolicy at member
      dsimp only at member
      split at member
      · obtain ⟨unrecorded, fits, other, action, otherTurn, rfl⟩ :=
          referenceOpportunity_canonical_transmission timeouts leaks member submits
        have same : other = event := Option.some.inj (otherTurn.symm.trans turn)
        subst same
        exact ⟨other, action, turn, unrecorded, fits, rfl⟩
      · exact (silentPolicy_not_transmit timeouts leaks member material submits).elim
    · exact (silentPolicy_not_transmit timeouts leaks chosen material submits).elim

/-- Every transmitted response is the canonical decision at the player's own
turn for an event still unrecorded in that player's recall. -/
def SubmitsCanonically (policy : (app).Policy) (who : Player) : Prop :=
  ∀ past view response, response ∈ (policy past view).support →
    ∀ material : (app).Submission,
      response.transmission = some material → ∃ event action,
        view.application.publicView.ownTurn? who = some event ∧
        eventRecorded timeouts leaks past event = false ∧
        response = canonicalServiceDecision timeouts leaks who past view event action

/-- A timed client sends its canonical decision at an unrecorded own turn. -/
theorem turnPolicy_submitsCanonically (bound : graph.EventId → Nat) (turns : Nat)
    (timing : EventGraphRuntime.TurnTiming graph turns) (reference : graph.BehavioralProfile)
    (who : Player) :
    SubmitsCanonically timeouts leaks (turnPolicy timeouts leaks bound turns timing reference who)
      who := by
  intro past view response member material transmits
  obtain ⟨event, action, turn, unrecorded, _, rfl⟩ :=
    turnPolicy_canonical_transmission timeouts leaks member transmits
  exact ⟨event, action, turn, unrecorded, rfl⟩

/-- **The slot of a canonical decision.** When the canonical decision of the
owner of `event` uses a prepared slot, that slot is the one
`canonicalFreshSlot` selects, the event is a binding of the owner, and the
submission names the event. -/
theorem canonicalServiceDecision_candidateSlot (who : Player)
    (past : List (app).PlayerEntry)
    (view : (app).PlayerView)
    (event : graph.EventId)
    (owned : graph.actor? event = some who)
    (action : graph.Action event)
    (serial : Nat)
    (slot : (responseCandidateSlot timeouts) leaks
      ((canonicalServiceDecision timeouts) leaks who past view event
          action) = some serial) :
    canonicalFreshSlot who view.application = some serial ∧
      (∃ payload, graph.outputLayout event = .binding who payload) ∧
      (submittedEvent? timeouts) leaks
        ((canonicalServiceDecision timeouts) leaks who past view event
            action) =
          some event := by
  by_cases inactive : who ∈ view.application.publicView.observation.defaulted
  · rw [(canonicalServiceDecision_defaulted timeouts) leaks who past
      view event action inactive] at slot
    cases slot
  cases node : nodeView graph event with
  | sample payload law outputEq codeEq =>
      have none := nodeView_sample_actor outputEq codeEq
      rw [owned] at none
      cases none
  | bind actor payload outputEq codeEq =>
      have actorEq : actor = who :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst actorEq
      obtain ⟨choice, rfl⟩ : ∃ choice : Option (PublicationResult (L.Val payload)),
          action = cast (congrArg EventGraph.EventField.Action outputEq.symm) choice :=
        ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
      cases choice with
      | none =>
          rw [(canonicalServiceDecision_binding_none timeouts) leaks
            actor past view event actor payload outputEq codeEq node] at slot
          cases slot
      | some result =>
          cases selected : canonicalFreshSlot actor view.application with
          | none =>
              simp only [EventGraphRuntime.canonicalServiceDecision,
                EventGraphRuntime.canonicalReactiveDecision, ite_eq_right inactive, node,
                cast_cast, cast_eq, Option.bind_some, selected, Option.map_none] at slot
              cases slot
          | some chosen =>
              rw [(canonicalServiceDecision_binding timeouts) leaks
                actor
                past view event payload outputEq codeEq node inactive chosen selected result]
                  at slot ⊢
              cases Option.some.inj slot
              exact ⟨rfl, ⟨payload, outputEq⟩, rfl⟩
  | resolve actor payload binding checks outputEq codeEq =>
      exfalso
      rw [(canonicalServiceDecision_eq_of_not_bind timeouts) leaks who
        past view event action (fun _ _ _ _ bind => by rw [node] at bind; cases bind)] at slot
      unfold EventGraphRuntime.serviceDecision EventGraphRuntime.reactiveDecision at slot
      simp only [ite_eq_right inactive, node] at slot
      rcases reactiveResolutionPacket_shape who event payload binding checks outputEq action
          view.application with ⟨candidate, raw, packet⟩ | packet
      · rw [packet] at slot
        cases slot
      · rw [packet] at slot
        cases slot

/-- `who` has an unfinished binding of its own for which it has already
submitted. -/
def PendingBinding (execution : (app).Execution)
    (who : Player) : Prop := ∃ event payload, graph.outputLayout event =
    .binding who payload ∧ event ∉ execution.application.config.cut.completed ∧
    (eventRecorded timeouts) leaks (execution.logs who) event = true

/-- Every prepared slot `who` has used lies below its public binding count, or
at it while a binding of `who` it has submitted for is unfinished. -/
def CanonicalSlotsUsed (execution : (app).Execution)
    (who : Player) : Prop := ∀ serial ∈ (submittedCandidateSlots timeouts)
    leaks (execution.logs who), serial < execution.application.publicView.bindingCount who ∨
    (serial = execution.application.publicView.bindingCount who ∧ PendingBinding timeouts leaks
        execution who)


/-- At an owner-solitary turn at an event it has not submitted for, no binding
of `who` it has submitted for is unfinished: that binding would be ready too. -/
theorem not_pendingBinding_at_turn
    {inputs : PMF graph.Inputs}
    {horizon : Nat}
    {scheduler : (app).Scheduler}
    {control : (app).Control}
    (trace :
        ((app).protocol (inputs.map State.initial)
        horizon scheduler).Trace (some control))
    (who : Player) (atTurn : OwnSubmissionsAtTurn
      timeouts leaks control.execution who)
    (event : graph.EventId)
    (ownerSolitary : graph.OwnerSolitary event)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (eventRecorded timeouts) leaks
        (control.execution.logs who) event = false) :
    ¬ PendingBinding timeouts leaks control.execution who := by
  rintro ⟨other, payload, _, unfinished, recorded⟩
  have facts := legalFacts timeouts leaks inputs horizon scheduler control trace
  have otherRecorded := recorded
  unfold EventGraphRuntime.eventRecorded at recorded
  obtain ⟨entry, member, submitted⟩ := List.any_eq_true.mp recorded
  have entryTurn := atTurn entry member other (of_decide_eq_true submitted)
  have entryReady := (PublicView.ownTurn?_spec _ who other entryTurn).1
  have readyOther : control.execution.application.config.cut.Ready other := by
    obtain ⟨extra, order, _, _, _⟩ := facts.eventStable who entry member other entryReady
      unfinished
    exact ready_of_eventReady_extends order entryReady unfinished
  have readyEvent := (PublicView.ownTurn?_spec _ who event turn).1
  have same : other = event :=
    ownerSolitary.ready_actor_unique
      control.execution.application.config.cut
      ((control.execution.application.publicView_eventReady event).mp readyEvent) readyOther
      (PublicView.ownTurn?_spec _ who event turn).2
      (PublicView.ownTurn?_spec _ who other entryTurn).2
  subst same
  rw [unrecorded] at otherRecorded
  cases otherRecorded

/-- At `who`'s turn at an event it has not submitted for, the counted slot is
unused and therefore fresh. -/
theorem canonicalSlot_fresh_of_used
    {inputs : PMF graph.Inputs}
    {horizon : Nat}
    {scheduler : (app).Scheduler}
    {control : (app).Control}
    (trace :
        ((app).protocol (inputs.map State.initial)
        horizon scheduler).Trace (some control))
    (who : Player) (atTurn : OwnSubmissionsAtTurn
      timeouts leaks control.execution who)
    (valid : CanonicalSlotsUsed timeouts leaks control.execution who)
    (event : graph.EventId)
    (ownerSolitary : graph.OwnerSolitary event)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (eventRecorded timeouts) leaks
        (control.execution.logs who) event = false) :
    control.execution.application.candidates.lookup
      (who, .prepared (control.execution.application.publicView.bindingCount who)) = .fresh := by
  have noPending := not_pendingBinding_at_turn timeouts leaks trace who atTurn event
    ownerSolitary turn unrecorded
  have unused : control.execution.application.publicView.bindingCount who ∉
      (submittedCandidateSlots timeouts) leaks
      (control.execution.logs who) := by
    intro member
    rcases valid _ member with lower | ⟨_, pending⟩
    · exact Nat.lt_irrefl _ lower
    · exact noPending pending
  have candidates : (CandidateRecall timeouts) leaks
    control.execution :=
    candidateRecall_history timeouts leaks inputs horizon scheduler
      trace
  exact candidates who _ unused

/-- A scheduler command keeps the used slots below the count. -/
theorem canonicalSlotsUsed_environment
    {execution next : (app).Execution}
    {command : (app).Command}
    (reached : next ∈
        (execution.environmentStep (app) command).support)
    (who : Player) (valid : CanonicalSlotsUsed timeouts leaks execution who) :
    CanonicalSlotsUsed timeouts leaks next who := by
  have recallEq := (app).environmentStep_recall execution next command reached
  have path := (reactiveApplication_graphSteps timeouts leaks).environmentStep execution next
    command reached
  obtain ⟨extra, appended⟩ := EventGraph.Config.Step.path_history_prefix path
  have historyEq : next.application.config.history = execution.application.config.history ++
      extra := appended.symm
  have countEq : next.application.publicView.bindingCount who =
      execution.application.publicView.bindingCount who +
        ((extra.map EventCompletion.event).countP fun event =>
          match graph.outputLayout event with
          | .binding owner _ => decide (owner = who)
          | .publicData _ | .privateInput _ _ | .publication _ => false) := by
    unfold PublicView.bindingCount
    change List.countP _ (next.application.config.history.map EventCompletion.event) = _
    rw [historyEq, List.map_append, List.countP_append]
    rfl
  intro serial used
  rw [recallEq] at used
  rcases valid serial used with lower | ⟨equal, other, payload, layout, unfinished, recorded⟩
  · left
    rw [countEq]
    omega
  · by_cases sameCount : execution.application.publicView.bindingCount who =
        next.application.publicView.bindingCount who
    · refine Or.inr ⟨equal.trans sameCount, other, payload, layout, ?_, ?_⟩
      · intro completed
        have listed := (next.application.config.history_exact other).mpr completed
        rw [historyEq, List.map_append, List.mem_append] at listed
        rcases listed with old | fresh
        · exact unfinished ((execution.application.config.history_exact other).mp old)
        · have zero : ((extra.map EventCompletion.event).countP fun event =>
              match graph.outputLayout event with
              | .binding owner _ => decide (owner = who)
              | .publicData _ | .privateInput _ _ | .publication _ => false) = 0 := by omega
          have absent := List.countP_eq_zero.mp zero other fresh
          apply absent
          simp only [layout, decide_true]
      · rw [recallEq]
        exact recorded
    · left
      rw [countEq] at sameCount ⊢
      omega

/-- Another player's response leaves `who`'s used slots and their count. -/
theorem canonicalSlotsUsed_respond_other
    (execution : (app).Execution) {who responder : Player}
    (different : who ≠ responder)
    (response : (app).Action)
    (valid : CanonicalSlotsUsed timeouts leaks execution who) : CanonicalSlotsUsed timeouts leaks
      (execution.respond (app) responder response)
      who := by
  have recallEq := (app).respond_recall_other execution
      responder who different response
  have appEq := (reactive_respond_application timeouts) leaks execution
      responder response
  unfold CanonicalSlotsUsed PendingBinding at valid ⊢
  rw [recallEq, appEq.1, appEq.2]
  exact valid

/-- **One response of the turn-counted policy.** A fresh commitment of `who`
on the policy's support uses exactly the counted slot, and its binding stays
pending until it completes. -/
theorem canonicalSlotsUsed_respond
    {inputs : PMF graph.Inputs}
    (serial : graph.ActorSerial) {horizon remaining : Nat}
    {scheduler : (app).Scheduler}
    {middle : (app).Execution} {who : Player}
    (trace :
        ((app).protocol (inputs.map State.initial)
        horizon scheduler).Trace (some ⟨remaining, some who, middle⟩))
    {policy : (app).Policy}
    (canonical : SubmitsCanonically timeouts leaks policy who)
    {response : (app).Action}
    (chosen : response ∈ (policy (middle.logs who) (middle.observe app who)).support)
    (atTurn : OwnSubmissionsAtTurn timeouts leaks middle who)
    (valid : CanonicalSlotsUsed timeouts leaks middle who) :
    CanonicalSlotsUsed timeouts leaks
        (middle.respond (app) who response)
      who := by
  have appEq := (reactive_respond_application timeouts) leaks middle
      who response
  obtain ⟨emitted, recalled, _⟩ := respond_recall_self timeouts leaks middle who response
  have recordedMono : ∀ event,
      (eventRecorded timeouts) leaks (middle.logs who) event = true →
        (eventRecorded timeouts) leaks
        ((middle.respond app who response).logs who)
          event = true := by
    intro event recorded
    rw [recalled]
    unfold EventGraphRuntime.eventRecorded at recorded ⊢
    rw [List.any_append, recorded, Bool.true_or]
  intro slotIndex used
  rw [(submittedCandidateSlots_respond timeouts) leaks middle who
          response] at used
  rw [appEq.2]
  rcases List.mem_append.mp used with old | new
  · rcases valid slotIndex old with lower | ⟨equal, other, payload, layout, unfinished, recorded⟩
    · exact Or.inl lower
    · refine Or.inr ⟨equal, other, payload, layout, ?_, recordedMono other recorded⟩
      rw [appEq.1]
      exact unfinished
  · have slot : (responseCandidateSlot timeouts) leaks response = some
        slotIndex := Option.mem_toList.mp new
    obtain ⟨material, submits⟩ : ∃ material, response.transmission = some material := by
      unfold EventGraphRuntime.responseCandidateSlot at slot
      split at slot
      · exact ⟨_, ‹_›⟩
      · cases slot
    obtain ⟨event, action, turn, unrecorded, rfl⟩ :=
      canonical _ _ response chosen material submits
    have owned := (PublicView.ownTurn?_spec _ who event turn).2
    have fresh := canonicalSlot_fresh_of_used timeouts leaks trace who atTurn valid event
      (serial event) turn unrecorded
    have canonical := canonicalFreshSlot_canonical who (middle.observe app who).application fresh
    obtain ⟨selected, ⟨payload, layout⟩, named⟩ :=
      canonicalServiceDecision_candidateSlot timeouts leaks who (middle.logs who)
        (middle.observe app who) event owned action slotIndex slot
    rw [canonical] at selected
    cases Option.some.inj selected
    have ready := (middle.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1
    refine Or.inr ⟨rfl, event, payload, layout, ?_, ?_⟩
    · rw [appEq.1]
      exact ready.1
    · rw [recalled]
      unfold EventGraphRuntime.eventRecorded
      rw [List.any_append]
      simp only [List.any_cons, List.any_nil, Bool.or_false]
      rw [named]
      simp

/-- One round keeps `who`'s submissions at its turns and its used slots below
the count, when `who` submits canonically and only at its turns. -/
theorem canonicalSlots_round
    {inputs : PMF graph.Inputs}
    (serial : graph.ActorSerial) {horizon remaining : Nat}
    {scheduler : (app).Scheduler}
    {players : Player → (app).Policy} {who : Player}
    (canonical : SubmitsCanonically timeouts leaks (players who) who)
    (submitsAtTurn : SubmitsAtTurn timeouts leaks (players who) who)
    {execution next : (app).Execution}
    (trace :
        ((app).protocol (inputs.map State.initial)
        horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩))
    (atTurn : OwnSubmissionsAtTurn timeouts leaks execution who)
    (valid : CanonicalSlotsUsed timeouts leaks execution who)
    (reached : next ∈
        ((app).round scheduler players
        execution).support) :
    OwnSubmissionsAtTurn
      timeouts leaks next who ∧
        CanonicalSlotsUsed timeouts leaks next who := by
  obtain ⟨command, selected, middle, moved, cases⟩ := round_cases timeouts leaks reached
  have recallEq := (app).environmentStep_recall execution middle command moved
  have atMiddle : OwnSubmissionsAtTurn timeouts leaks middle who := by
    unfold EventGraphRuntime.OwnSubmissionsAtTurn
    rw [recallEq]
    exact atTurn
  have validMiddle := canonicalSlotsUsed_environment timeouts leaks moved who valid
  rcases cases with ⟨_, rfl⟩ | ⟨responder, active, response, chosen, rfl⟩
  · exact ⟨atMiddle, validMiddle⟩
  · obtain ⟨middleTrace⟩ := (app).raw_trace_environment (inputs.map State.initial) horizon
        scheduler remaining execution middle command trace selected moved
    rw [active] at middleTrace
    by_cases same : responder = who
    · subst responder
      refine ⟨?_, canonicalSlotsUsed_respond timeouts leaks serial middleTrace canonical
        chosen atMiddle validMiddle⟩
      obtain ⟨emitted, recalled, _⟩ :=
        respond_recall_self timeouts leaks middle who response
      intro entry member event submitted
      rw [recalled] at member
      rcases List.mem_append.mp member with old | new
      · exact atMiddle entry old event submitted
      · rw [List.mem_singleton] at new
        subst new
        exact submitsAtTurn _ _ response chosen event submitted
    · have different : who ≠ responder := fun equal => same equal.symm
      refine ⟨?_, canonicalSlotsUsed_respond_other timeouts leaks middle different response
        validMiddle⟩
      unfold EventGraphRuntime.OwnSubmissionsAtTurn
      rw [(app).respond_recall_other middle responder who different response]
      exact atMiddle

/-- On the support of rounds in which `who` follows the turn-counted policy,
`who`'s submissions are at its turns and its used slots lie below the count. -/
theorem canonicalSlots_roundsFrom
    (inputs : PMF graph.Inputs)
    (serial : graph.ActorSerial)
    (scheduler : (app).Scheduler)
    (players : Player → (app).Policy) (who : Player)
    {bound : graph.EventId → Nat} {turns : Nat}
    (timing : EventGraphRuntime.TurnTiming graph turns) (reference : graph.BehavioralProfile)
    (follows : players who = turnPolicy timeouts leaks bound turns
      timing reference
        who) (count : Nat) (execution : (app).Execution)
    (reached : execution ∈
        ((app).roundsFrom (inputs.map State.initial)
        scheduler players count).support) : OwnSubmissionsAtTurn
          timeouts leaks execution who ∧
      CanonicalSlotsUsed timeouts leaks execution who := by
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      cases (PMF.mem_support_pure_iff _ _).mp supported
      refine ⟨fun entry member => ?_, fun serial used => ?_⟩
      · cases member
      · cases used
  | succ count ih =>
      rw [(app).roundsFrom_succ] at reached
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨atTurn, valid⟩ := ih prior priorMem
      obtain ⟨trace⟩ := (app).raw_trace_roundsFrom (inputs.map State.initial) (count + 1)
          scheduler players count (Nat.le_succ count) prior priorMem
      rw [show count + 1 - count = 0 + 1 by omega] at trace
      exact canonicalSlots_round timeouts leaks serial
        (follows ▸ turnPolicy_submitsCanonically timeouts leaks bound turns timing reference who)
        (follows ▸ turnPolicy_submitsAtTurn timeouts leaks bound turns timing reference who)
        trace atTurn valid moved

end Vegas.EventGraphRuntime
