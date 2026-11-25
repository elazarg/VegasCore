module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ForeignTraffic
public import Vegas.Pending.CanonicalSlots
public import Vegas.Pending.SilentAction
public import Vegas.Pending.ForeignBindingObservation
public import Vegas.Pending.FixedOpportunity
public import Vegas.Pending.PrefixBoundary
public import Interaction.ReactiveRawRoundTrace
public import Vegas.Pending.FirstTurnMixture
public import Vegas.Pending.TurnClientActionLaw

@[expose] public section

/-! # Native traffic stopped at a foreign binding -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {timeouts : EventTimeouts graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {inputs : PMF graph.Inputs}

local notation "app" => reactiveApplication timeouts leaks

/-- Decide `action` at the first turn at `event`, and stay silent at every other
input. -/
def decidedTurnPolicy (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (bound : graph.EventId → Nat) (owner : Player)
    (event : graph.EventId) (action : graph.Action event) :
    (reactiveApplication timeouts leaks).Policy :=
  let currentApp := reactiveApplication timeouts leaks
  currentApp.turnScheduledPolicy
    (turnIndex timeouts leaks owner event) (some (0 : Fin 1))
    (fixedOpportunity timeouts leaks bound owner event action)
    currentApp.silentPolicy

/-- A fixed silent graph action stays silent at every input of its turn policy. -/
theorem decidedTurnPolicy_silent {bound : graph.EventId → Nat}
    {owner : Player} {event : graph.EventId}
    (action : graph.Action event) (silent : SilentAction event action)
    (past : List (app).PlayerEntry)
    (view : (app).PlayerView) :
    decidedTurnPolicy timeouts leaks bound owner event action past view = PMF.pure ⟨none⟩ := by
  unfold decidedTurnPolicy ReactiveApplication.turnScheduledPolicy
  dsimp only
  split
  · exact fixedOpportunity_silent action past view
      (canonicalServiceDecision_silent owner past view event action silent)
  · rfl

private theorem silentPolicy_no_transmission
    {past : List (app).PlayerEntry} {view : (app).PlayerView} {response : (app).Action}
    (chosen : response ∈ ((app).silentPolicy past view).support)
    (material : (app).Submission) :
    response.transmission ≠ some material := by
  obtain rfl := (app).silentPolicy_cases past view response chosen
  simp

/-- Deciding a fixed action at the first turn submits only for that event,
and only at an input where it is the owner's turn. -/
theorem decidedTurnPolicy_submitsAtTurn (bound : graph.EventId → Nat)
    (owner : Player) (event : graph.EventId)
    (action : graph.Action event) :
    SubmitsAtTurn timeouts leaks
        (decidedTurnPolicy timeouts leaks bound owner event
      action) owner := by
  intro past view response chosen other submitted
  have silentAt := silentPolicy_submitsAtTurn timeouts leaks owner
  unfold decidedTurnPolicy ReactiveApplication.turnScheduledPolicy at chosen
  dsimp only at chosen
  split at chosen
  · rename_i first
    have turn : view.application.publicView.ownTurn? owner = some event := by
      unfold EventGraphRuntime.turnIndex at first
      split at first
      · assumption
      · cases first
    let decision := canonicalServiceDecision timeouts leaks owner past view event action
    have fromDecision (equal : response = decision) : other = event := by
      subst response
      exact submittedEvent_canonicalServiceDecision timeouts leaks owner past view event action
        other submitted
    by_cases prior : eventRecorded timeouts leaks past event
    · rw [fixedOpportunity, ite_eq_left prior] at chosen
      exact silentAt past view response chosen other submitted
    · rw [fixedOpportunity, ite_eq_right prior] at chosen
      by_cases fits : view.application.publicView.InclusionFitsDeadline timeouts bound event
      · rw [ite_eq_left fits] at chosen
        by_cases silent : decision.transmission = none
        · rw [ite_eq_left silent] at chosen
          exact silentAt past view response chosen other submitted
        · rw [ite_eq_right silent, PMF.mem_support_pure_iff] at chosen
          exact (fromDecision chosen).symm ▸ turn
      · rw [ite_eq_right fits] at chosen
        exact silentAt past view response chosen other submitted
  · exact silentAt past view response chosen other submitted

private theorem decided_policy_canonical
    (bound : graph.EventId → Nat) (owner : Player)
    (event : graph.EventId) (action : graph.Action event) :
    SubmitsCanonically timeouts leaks
      (decidedTurnPolicy timeouts leaks bound owner event action) owner := by
  intro past view response chosen material sends
  unfold decidedTurnPolicy ReactiveApplication.turnScheduledPolicy at chosen
  dsimp only at chosen
  split at chosen
  · rename_i first
    have turn := (turnIndex_first (timeouts := timeouts) (leaks := leaks) first).1
    unfold fixedOpportunity at chosen
    split at chosen
    · exact (silentPolicy_no_transmission (timeouts := timeouts) (leaks := leaks)
          chosen material sends).elim
    · rename_i unrecorded
      split at chosen
      · split at chosen
        · exact (silentPolicy_no_transmission (timeouts := timeouts) (leaks := leaks)
          chosen material sends).elim
        · rw [PMF.mem_support_pure_iff] at chosen
          subst response
          exact ⟨event, action, turn, by simpa using unrecorded, rfl⟩
      · exact (silentPolicy_no_transmission (timeouts := timeouts) (leaks := leaks)
          chosen material sends).elim
  · exact (silentPolicy_no_transmission (timeouts := timeouts) (leaks := leaks)
          chosen material sends).elim

private theorem binding_ready_handler
    {event : graph.EventId} {owner : Player} {payload : L.Ty}
    {outputEq : graph.outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload}
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (left right : EventGraphRuntime.State graph) (focal : Player)
    (views : left.playerView focal = right.playerView focal)
    (leftReady : left.config.cut.Ready event) (rightReady : right.config.cut.Ready event)
    (alone : ∀ (cut : graph.order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (message : Message Player (Payload graph)) :
    (handle timeouts left message).map
        (fun state => state.playerView focal) =
      (handle timeouts right message).map
        (fun state => state.playerView focal) := by
  classical
  obtain ⟨id, packet⟩ := message
  cases packet with
  | malformed raw => simp [handle]
  | commitment named candidate =>
      exact handle_commitment_playerView_congr _ left right focal id named candidate views
  | opening named candidate raw =>
      by_cases namedReady : left.config.cut.Ready named
      · have namedEq := alone _ named leftReady namedReady
        subst named
        simp [handle, leftReady, rightReady, node]
      · have cuts := cut_eq_of_publicView_eq (congrArg PlayerView.publicView views)
        have rightNot : ¬right.config.cut.Ready named := by simpa only [← cuts] using namedReady
        simp [handle, namedReady, rightNot]

/-- Away from an unrecorded first turn that still fits the deadline, the
decided policy is silent. -/
theorem decidedTurnPolicy_closed {bound : graph.EventId → Nat}
    {owner : Player} {event : graph.EventId}
    (action : graph.Action event)
    (execution : (app).Execution)
    (selected : execution.application.publicView.ownTurn? owner = some event)
    (closed : ¬ (ownerTurns owner event execution = 0 ∧
      (eventRecorded timeouts) leaks (execution.logs owner) event =
        false ∧
      execution.application.publicView.InclusionFitsDeadline timeouts
        bound event)) :
    decidedTurnPolicy timeouts leaks bound owner event action (execution.logs owner)
        (execution.observe (app) owner) =
      PMF.pure ⟨none⟩ := by
  have turn := serviceTurn_of_turn execution selected
  unfold decidedTurnPolicy
  by_cases first : ownerTurns owner event execution = 0
  · rw [(app).turnScheduledPolicy_selected _ (0 : Fin 1)
      _ _ _ _ (by rw [turn, first]; rfl)]
    unfold fixedOpportunity
    by_cases recorded : (eventRecorded timeouts) leaks
        (execution.logs owner) event = true
    · simp only [recorded, ↓reduceIte, ReactiveApplication.silentPolicy_apply]
    · have unrecorded : (eventRecorded timeouts) leaks
          (execution.logs owner) event = false := by simpa using recorded
      have late : ¬ execution.application.publicView.InclusionFitsDeadline
          timeouts bound event := fun fits =>
        closed ⟨first, unrecorded, fits⟩
      have lateView : ¬ (execution.observe (app)
          owner).application.publicView.InclusionFitsDeadline
            timeouts bound event := late
      simp only [unrecorded, Bool.false_eq_true, ↓reduceIte, lateView,
        ReactiveApplication.silentPolicy_apply]
  · rw [(app).turnScheduledPolicy_unselected _ _ _ _ _ _
      (by
        intro slot chosen
        rw [turn]
        intro equal
        exact first ((Option.some.inj equal).trans
          ((Fin.val_eq_zero slot).trans (by rfl))))]
    rfl

/-- At an unrecorded first turn, the decided policy is its opportunity. -/
theorem decidedTurnPolicy_open {bound : graph.EventId → Nat}
    {owner : Player} {event : graph.EventId}
    (action : graph.Action event)
    (execution : (app).Execution)
    (selected : execution.application.publicView.ownTurn? owner = some event)
    (first : ownerTurns owner event execution = 0) :
    decidedTurnPolicy timeouts leaks bound owner event action (execution.logs owner)
        (execution.observe (app) owner) =
      fixedOpportunity timeouts leaks
        bound owner event action (execution.logs owner)
        (execution.observe (app) owner) := by
  have turn := serviceTurn_of_turn execution selected
  unfold decidedTurnPolicy
  rw [(app).turnScheduledPolicy_selected _ (0 : Fin 1)
    _ _ _ _ (by rw [turn, first]; rfl)]

/-- An opportunity that transmits a given decision. -/
theorem decidedOpportunity_transmits {bound : graph.EventId → Nat}
    {owner : Player} {event : graph.EventId}
    (action : graph.Action event)
    (execution : (app).Execution)
    (unrecorded : (eventRecorded timeouts) leaks
      (execution.logs owner) event = false)
    (fits : execution.application.publicView.InclusionFitsDeadline
      timeouts bound event)
    (material : (app).Submission)
    (decision : (canonicalServiceDecision timeouts) leaks owner
      (execution.logs owner) (execution.observe (app)
        owner) event action = ⟨some material⟩) :
    fixedOpportunity timeouts leaks
      bound owner event action (execution.logs owner)
        (execution.observe (app) owner) =
      PMF.pure ⟨some material⟩ := by
  have fitsView : (execution.observe (app)
      owner).application.publicView.InclusionFitsDeadline timeouts
        bound event := fits
  unfold fixedOpportunity
  simp only [unrecorded, Bool.false_eq_true, ↓reduceIte, fitsView, decision, reduceCtorEq]



private theorem decided_binding_response
    {horizon remaining : Nat}
    {scheduler : (app).Scheduler}
    {bound : graph.EventId → Nat}
    {event : graph.EventId} {owner : Player} {payload : L.Ty}
    (ownerSolitary : graph.OwnerSolitary event)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (result : PublicationResult (L.Val payload))
    {current : (app).Execution}
    (trace : ((app).protocol
      (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨remaining + 1, none, current⟩))
    (own : OwnSubmissionsAtTurn timeouts leaks current owner)
    (slots : CanonicalSlotsUsed timeouts leaks current owner)
    (ready : current.application.config.cut.Ready event)
    (selected : (.activate owner : (app).Command) ∈
      (scheduler current.environmentRecall
        (current.observeEnvironment (app))).support)
    (sample : Finset (MessageId Player))
    (sampled : sample ∈ ((app).observePending owner
      current.network.pending).support)
    (first : ownerTurns owner event current = 0)
    (unrecorded : (eventRecorded timeouts) leaks
      (current.logs owner) event = false)
    (fits : current.application.publicView.InclusionFitsDeadline
      timeouts bound event) :
    let active := current.sampledActivation (app) owner
      sample
    decidedTurnPolicy timeouts leaks bound owner event
        (cast (congrArg EventField.Action outputEq.symm) (some result))
        (active.logs owner) (active.observe (app)
          owner) =
      PMF.pure ((reactiveBinding timeouts) leaks owner event payload
        result (current.application.publicView.bindingCount owner)) := by
  intro active
  have owned : graph.actor? event = some owner :=
    nodeView_bind_actor outputEq codeEq
  have moved : active ∈ (current.environmentStep app (.activate owner)).support := by
    rw [ReactiveApplication.Execution.activation_samples, PMF.support_map]
    exact ⟨sample, sampled, rfl⟩
  obtain ⟨activeTrace⟩ := (app).raw_trace_environment (inputs.map State.initial) horizon
    scheduler remaining current active (.activate owner) trace selected moved
  have turn : active.application.publicView.ownTurn? owner = some event :=
    active.application.ownTurn?_of_ready ownerSolitary ready owned
  have fresh := canonicalSlot_fresh_of_used timeouts leaks activeTrace owner own slots event
    ownerSolitary turn unrecorded
  have canonical := canonicalFreshSlot_canonical owner (active.observe app owner).application fresh
  have activeOwner : owner ∉ active.application.config.defaulted :=
    active.application.active_of_ready_owned
      (legalFacts timeouts leaks inputs horizon scheduler _ activeTrace).quiescent ready owned
  have decision := (canonicalServiceDecision_binding timeouts) leaks
    owner (active.logs owner) (active.observe app owner) event payload outputEq codeEq node
      activeOwner _ canonical result
  rw [decidedTurnPolicy_open _ active turn first,
    decidedOpportunity_transmits _ active unrecorded fits _ decision]
  rfl

theorem binding_response_matched
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (app).Scheduler}
    {bound : graph.EventId → Nat}
    {event : graph.EventId} {owner focal : Player} {payload : L.Ty}
    (ownerSolitary : graph.OwnerSolitary event)
    (foreign : owner ≠ focal)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (leftChoice rightChoice : Option (PublicationResult (L.Val payload)))
    (admitted : leftChoice.isSome = rightChoice.isSome)
    {left right : (app).Execution}
    (same : foreignReadout (leaks := leaks) focal owner event left =
      foreignReadout (leaks := leaks) focal owner event right)
    (leftTrace : ((app).protocol
      (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨leftRemaining + 1, none, left⟩))
    (rightTrace : ((app).protocol
      (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨rightRemaining + 1, none, right⟩))
    (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (leftOwn : OwnSubmissionsAtTurn timeouts leaks left owner)
    (leftSlots : CanonicalSlotsUsed timeouts leaks left owner)
    (rightOwn : OwnSubmissionsAtTurn timeouts leaks right owner)
    (rightSlots : CanonicalSlotsUsed timeouts leaks right owner)
    (selected : (.activate owner : (app).Command) ∈
      (scheduler left.environmentRecall
        (left.observeEnvironment (app))).support)
    (sample : Finset (MessageId Player))
    (sampled : sample ∈ ((app).observePending owner
      left.network.pending).support) :
    let leftActive := left.sampledActivation (app)
      owner sample
    let rightActive := right.sampledActivation (app)
      owner sample
    ∃ leftResponse rightResponse,
      decidedTurnPolicy timeouts leaks bound owner event
        (cast (congrArg EventField.Action outputEq.symm) leftChoice)
        (leftActive.logs owner) (leftActive.observe
          (app) owner) = PMF.pure leftResponse ∧
      decidedTurnPolicy timeouts leaks bound owner event
        (cast (congrArg EventField.Action outputEq.symm) rightChoice)
        (rightActive.logs owner) (rightActive.observe
          (app) owner) = PMF.pure rightResponse ∧
      (submittedEvent? timeouts) leaks leftResponse =
        (submittedEvent? timeouts) leaks rightResponse ∧
      (bindingTraffic timeouts) leaks focal
        (leftActive.respond (app) owner leftResponse) =
      (bindingTraffic timeouts) leaks focal
        (rightActive.respond (app) owner
          rightResponse) := by
  intro leftActive rightActive
  have sameTraffic : (bindingTraffic timeouts) leaks focal left =
      (bindingTraffic timeouts) leaks focal right := congrArg
        Prod.fst same
  have sameTurns : ownerTurns owner event left = ownerTurns owner event right :=
    congrArg (fun value => value.2.1) same
  have sameRecorded : (eventRecorded timeouts) leaks
      (left.logs owner) event =
      (eventRecorded timeouts) leaks (right.logs owner) event :=
    congrArg (fun value => value.2.2) same
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) sameTraffic
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) sameTraffic
  have networks : left.network = right.network := congrArg Prod.fst sameTraffic
  have activated := bindingTraffic_activation timeouts leaks left
    right focal owner sameTraffic sample
  have owned : graph.actor? event = some owner :=
    nodeView_bind_actor outputEq codeEq
  cases leftChoice with
  | none =>
      cases rightChoice with
      | some result => cases admitted
      | none =>
          have silent : SilentAction event
              (cast (congrArg EventField.Action outputEq.symm)
                (none : Option (PublicationResult (L.Val payload)))) := by
            unfold SilentAction
            rw [node]
            simp only [cast_cast, cast_eq]
          exact ⟨⟨none⟩, ⟨none⟩, decidedTurnPolicy_silent _ silent _ _,
            decidedTurnPolicy_silent _ silent _ _, rfl,
            bindingTraffic_respond_other foreign.symm activated _ _ (Or.inl ⟨rfl, rfl⟩)⟩
  | some leftResult =>
      cases rightChoice with
      | none => cases admitted
      | some rightResult =>
          by_cases opened : ownerTurns owner event left = 0 ∧
              (eventRecorded timeouts) leaks (left.logs owner) event =
                false ∧ left.application.publicView.InclusionFitsDeadline
                  timeouts bound event
          · obtain ⟨first, unrecorded, fits⟩ := opened
            have rightFirst : ownerTurns owner event right = 0 := sameTurns ▸ first
            have rightUnrecorded : (eventRecorded timeouts) leaks
                (right.logs owner) event = false := sameRecorded ▸ unrecorded
            have rightFits : right.application.publicView.InclusionFitsDeadline
                timeouts bound event := publics ▸ fits
            have counts : left.application.publicView.bindingCount owner =
                right.application.publicView.bindingCount owner := by rw [publics]
            refine ⟨(reactiveBinding timeouts) leaks owner event
              payload
                leftResult (left.application.publicView.bindingCount owner),
              (reactiveBinding timeouts) leaks owner event payload
                rightResult (right.application.publicView.bindingCount owner), ?_, ?_, rfl, ?_⟩
            · exact decided_binding_response ownerSolitary outputEq codeEq node leftResult
                leftTrace leftOwn leftSlots leftReady selected sample sampled first unrecorded fits
            · exact decided_binding_response ownerSolitary outputEq codeEq node rightResult
                rightTrace rightOwn rightSlots rightReady (by
                  rw [← environments, ← observeEnvironment_eq_of_bindingTraffic focal sameTraffic]
                  exact selected) sample (by rw [← networks]; exact sampled) rightFirst
                  rightUnrecorded rightFits
            · apply bindingTraffic_respond_other foreign.symm activated
              refine Or.inr ⟨_, _, rfl, rfl, ?_⟩
              have activePublics : leftActive.application.publicView =
                  rightActive.application.publicView := publics
              rw [reactiveApplication_packet_none, reactiveApplication_packet_none, counts,
                activePublics]
          · have rightClosed : ¬ (ownerTurns owner event right = 0 ∧
                (eventRecorded timeouts) leaks (right.logs owner)
                  event = false ∧ right.application.publicView.InclusionFitsDeadline
                    timeouts bound event) := by
              rw [← sameTurns, ← sameRecorded, ← publics]
              exact opened
            exact ⟨⟨none⟩, ⟨none⟩,
              decidedTurnPolicy_closed _ leftActive
                (leftActive.application.ownTurn?_of_ready ownerSolitary leftReady owned) opened,
              decidedTurnPolicy_closed _ rightActive
                (rightActive.application.ownTurn?_of_ready ownerSolitary rightReady owned)
                  rightClosed, rfl,
              bindingTraffic_respond_other foreign.symm activated _ _ (Or.inl ⟨rfl, rfl⟩)⟩


/-- Decided foreign bindings of equal admission, run until the binding completes from
equal starting readouts, give equal stopped readout laws. -/
theorem binding_stopped_readout_congr
    (serial : graph.ActorSerial)
    {horizon count leftRemaining rightRemaining : Nat}
    (scheduler : (app).Scheduler)
    (focal : Player) (deviation : (app).Policy)
    (bound : graph.EventId → Nat)
    {event : graph.EventId} {owner : Player} {payload : L.Ty}
    (foreign : owner ≠ focal)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (leftChoice rightChoice : Option (PublicationResult (L.Val payload)))
    (admitted : leftChoice.isSome = rightChoice.isSome)
    (alone : ∀ (cut : graph.order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (leftStart rightStart : (app).Execution)
    (leftTrace : ((app).protocol
      (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨leftRemaining + count, none, leftStart⟩))
    (rightTrace : ((app).protocol
      (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨rightRemaining + count, none, rightStart⟩))
    (leftReady : leftStart.application.config.cut.Ready event)
    (rightReady : rightStart.application.config.cut.Ready event)
    (leftOwn : OwnSubmissionsAtTurn timeouts leaks leftStart owner)
    (leftSlots : CanonicalSlotsUsed timeouts leaks leftStart owner)
    (rightOwn : OwnSubmissionsAtTurn timeouts leaks rightStart owner)
    (rightSlots : CanonicalSlotsUsed timeouts leaks rightStart owner)
    (same : foreignReadout (leaks := leaks) focal owner event leftStart =
      foreignReadout (leaks := leaks) focal owner event rightStart) :
    ((app).runUntil scheduler
      (Function.update
        (focalPlayers timeouts leaks focal deviation) owner
        (decidedTurnPolicy timeouts leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) leftChoice)))
      (fun final => event ∈ final.application.config.cut.completed) count leftStart).map
        (foreignReadout (leaks := leaks) focal owner event) =
    ((app).runUntil scheduler
      (Function.update
        (focalPlayers timeouts leaks focal deviation) owner
        (decidedTurnPolicy timeouts leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) rightChoice)))
      (fun final => event ∈ final.application.config.cut.completed) count rightStart).map
        (foreignReadout (leaks := leaks) focal owner event) := by
  let players := fun choice => Function.update
    (focalPlayers timeouts leaks focal deviation) owner
    (decidedTurnPolicy timeouts leaks bound owner event
      (cast (congrArg EventField.Action outputEq.symm) choice))
  let invariant := fun (start : (app).Execution) (count : Nat) (current : (app).Execution) =>
    (∃ remaining, Nonempty (((app).protocol (inputs.map State.initial) horizon scheduler).Trace
      (some ⟨remaining + count, none, current⟩))) ∧
    (event ∉ current.application.config.cut.completed →
      current.application.config = start.application.config) ∧
    OwnSubmissionsAtTurn
      timeouts leaks current owner ∧
        CanonicalSlotsUsed timeouts leaks current owner
  have owned : graph.actor? event = some owner :=
    nodeView_bind_actor outputEq codeEq
  have advance (start : (app).Execution) (startReady : start.application.config.cut.Ready event)
      (choice : Option (PublicationResult (L.Val payload))) (n : Nat) (current : (app).Execution)
      (valid : invariant start (n + 1) current)
      (running : event ∉ current.application.config.cut.completed)
      (next : (app).Execution)
      (reached : next ∈ ((app).round scheduler (players choice) current).support) :
      invariant start n next := by
    obtain ⟨⟨remaining, ⟨trace⟩⟩, framed, own, slots⟩ := valid
    have before : ((app).protocol (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨(remaining + n) + 1, none, current⟩) := by
      simpa only [Nat.add_assoc] using trace
    obtain ⟨nextTrace⟩ := (app).raw_trace_round (inputs.map State.initial) horizon scheduler
      (players choice) (remaining + n) current next before reached
    obtain ⟨nextOwn, nextSlots⟩ := canonicalSlots_round timeouts leaks
      (players := players choice) (who := owner) serial
      (by
        simpa only [players, Function.update_self] using
          (decided_policy_canonical bound owner event
            (cast (congrArg EventField.Action outputEq.symm) choice)))
      (by
        simpa only [players, Function.update_self] using
          (decidedTurnPolicy_submitsAtTurn bound owner event
            (cast (congrArg EventField.Action outputEq.symm) choice))) before own slots reached
    refine ⟨⟨remaining, ⟨nextTrace⟩⟩, ?_, nextOwn, nextSlots⟩
    intro unfinished
    have currentReady : current.application.config.cut.Ready event :=
      (framed running).symm ▸ startReady
    exact (reactive_round_config_eq_of_pending timeouts leaks
      scheduler (players choice) event current next
      (fun query queryReady => alone _ query currentReady queryReady) unfinished reached).trans
        (framed running)
  apply ReactiveApplication.runUntil_map_congr_of_rounds app scheduler (players leftChoice)
    (players rightChoice)
    (fun final => event ∈ final.application.config.cut.completed)
    (foreignReadout (leaks := leaks) focal owner event)
    (invariant leftStart) (invariant rightStart)
  · intro n left right _leftValid _rightValid equal
    have traffic := congrArg Prod.fst equal
    have publics : left.application.publicView = right.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) traffic
    rw [cut_eq_of_publicView_eq publics]
  · intro n left right leftValid rightValid equal running
    obtain ⟨⟨leftRest, ⟨leftCurrentTrace⟩⟩, leftFrame, currentLeftOwn, currentLeftSlots⟩ :=
      leftValid
    obtain ⟨⟨rightRest, ⟨rightCurrentTrace⟩⟩, rightFrame, currentRightOwn, currentRightSlots⟩ :=
      rightValid
    have traffic := congrArg Prod.fst equal
    have publics : left.application.publicView = right.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) traffic
    have rightRunning : event ∉ right.application.config.cut.completed := by
      rw [← cut_eq_of_publicView_eq publics]
      exact running
    have currentLeftReady : left.application.config.cut.Ready event :=
      (leftFrame running).symm ▸ leftReady
    have currentRightReady : right.application.config.cut.Ready event :=
      (rightFrame rightRunning).symm ▸ rightReady
    have leftBefore : ((app).protocol (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨(leftRest + n) + 1, none, left⟩) := by
      simpa only [Nat.add_assoc] using leftCurrentTrace
    have rightBefore : ((app).protocol (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨(rightRest + n) + 1, none, right⟩) := by
      simpa only [Nat.add_assoc] using rightCurrentTrace
    apply foreignRound_readout_congr scheduler focal deviation owned foreign alone _ _
      currentLeftReady currentRightReady equal
    · intro selected sample sampled
      exact binding_response_matched (serial event) foreign outputEq codeEq node leftChoice
        rightChoice admitted
        equal leftBefore rightBefore currentLeftReady currentRightReady
        currentLeftOwn currentLeftSlots currentRightOwn currentRightSlots selected sample sampled
    · intro id message _found _sender
      exact binding_ready_handler node left.application right.application focal
        (congrArg (fun value => value.2.2.2.2.1) traffic) currentLeftReady currentRightReady alone
        ⟨message.id, message.payload.call⟩
  · exact advance leftStart leftReady leftChoice
  · exact advance rightStart rightReady rightChoice
  · exact ⟨⟨leftRemaining, ⟨leftTrace⟩⟩, fun _ => rfl, leftOwn, leftSlots⟩
  · exact ⟨⟨rightRemaining, ⟨rightTrace⟩⟩, fun _ => rfl, rightOwn, rightSlots⟩
  · exact same


/-- Fixed decisions of equal admission at a solitary foreign binding have the
same stopped focal traffic law. The starting prefixes come from the actual
first-turn reference with an arbitrary focal deviation. -/
theorem foreign_binding_fixed_traffic_congr
    (serial : graph.ActorSerial)
    {horizon turns : Nat} (scheduler : (app).Scheduler)
    (bound : graph.EventId → Nat) (reference : graph.BehavioralProfile)
    (focal owner : Player) (deviation : (app).Policy) (foreign : owner ≠ focal)
    (event : graph.EventId) (solitary : graph.Solitary event) {payload : L.Ty}
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (leftChoice rightChoice : Option (PublicationResult (L.Val payload)))
    (admitted : leftChoice.isSome = rightChoice.isSome)
    (left right : (app).Execution) :
    let honest := turnPolicy timeouts leaks bound turns
      (EventGraphRuntime.firstTurnTiming graph turns) reference
    let players := Function.update honest focal deviation
    PrefixBoundary (inputs.map State.initial) scheduler players event.val left →
    PrefixBoundary (inputs.map State.initial) scheduler players event.val right →
    left.environmentRecall.length ≤ horizon →
    right.environmentRecall.length ≤ horizon →
    bindingTraffic timeouts leaks focal left = bindingTraffic timeouts leaks focal right →
    let fixed := fun choice => Function.update (focalPlayers timeouts leaks focal deviation) owner
      (decidedTurnPolicy timeouts leaks bound owner event
        (cast (congrArg EventField.Action outputEq.symm) choice))
    let stop := fun final : (app).Execution => event ∈ final.application.config.cut.completed
    ((app).runUntilHorizon scheduler (fixed leftChoice) stop horizon left).map
        (bindingTraffic timeouts leaks focal) =
      ((app).runUntilHorizon scheduler (fixed rightChoice) stop horizon right).map
        (bindingTraffic timeouts leaks focal) := by
  intro honest players leftBoundary rightBoundary leftBounded rightBounded same fixed stop
  have follows : players owner = honest owner := Function.update_of_ne foreign _ _
  have facts (current : (app).Execution)
      (boundary : PrefixBoundary (inputs.map State.initial) scheduler players event.val current)
      (bounded : current.environmentRecall.length ≤ horizon) :
      Nonempty (((app).protocol (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨horizon - current.environmentRecall.length, none, current⟩)) ∧
      OwnSubmissionsAtTurn timeouts leaks current owner ∧
      CanonicalSlotsUsed timeouts leaks current owner ∧
      ownerTurns owner event current = 0 ∧
      eventRecorded timeouts leaks (current.logs owner) event = false := by
    obtain ⟨own, slots⟩ := canonicalSlots_roundsFrom timeouts leaks inputs serial scheduler
      players owner (EventGraphRuntime.firstTurnTiming graph turns) reference follows
      current.environmentRecall.length current boundary.supported
    have never : ∀ entry ∈ current.logs owner,
        entry.beforeView.application.publicView.ownTurn? owner ≠ some event := by
      intro entry member turn
      exact boundary.untouched event le_rfl owner entry member
        (entry.beforeView.application.publicView.ownTurn?_spec owner event turn).1
    refine ⟨(app).raw_trace_roundsFrom (inputs.map State.initial) horizon scheduler players
      current.environmentRecall.length bounded current boundary.supported, own, slots, ?_, ?_⟩
    · apply List.countP_eq_zero.mpr
      intro entry member
      exact fun equal => never entry member (of_decide_eq_true equal)
    · apply Bool.eq_false_iff.mpr
      intro recorded
      obtain ⟨entry, member, submitted⟩ := (eventRecorded_iff timeouts leaks _ event).mp recorded
      exact never entry member (own entry member event submitted)
  obtain ⟨⟨leftTrace⟩, leftOwn, leftSlots, leftTurns, leftRecorded⟩ :=
    facts left leftBoundary leftBounded
  obtain ⟨⟨rightTrace⟩, rightOwn, rightSlots, rightTurns, rightRecorded⟩ :=
    facts right rightBoundary rightBounded
  have equal : foreignReadout focal owner event left = foreignReadout focal owner event right :=
    Prod.ext same (Prod.ext (leftTurns.trans rightTurns.symm)
      (leftRecorded.trans rightRecorded.symm))
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun traffic => traffic.2.2.1) same
  rw [environments] at leftTrace
  have coupled := binding_stopped_readout_congr serial scheduler focal deviation bound foreign
    outputEq codeEq node leftChoice rightChoice admitted
    (fun cut _ ready otherReady => solitary cut otherReady ready) left right
    (leftRemaining := 0) (rightRemaining := 0)
    (by simpa only [Nat.zero_add] using leftTrace)
    (by simpa only [Nat.zero_add] using rightTrace)
    (leftBoundary.ordered.ready event.isLt) (rightBoundary.ordered.ready event.isLt)
    leftOwn leftSlots rightOwn rightSlots equal
  have projected := congrArg (PMF.map Prod.fst) coupled
  simpa only [ReactiveApplication.runUntilHorizon, environments, PMF.map_comp,
    foreignReadout, Function.comp_def] using projected

/-- At an event ready alone, fixing its owner's first-turn action agrees until
completion with the decided client, while only the deviator and owner respond. -/
theorem foreign_firstTurn_fixedRun
    {horizon : Nat} (scheduler : (app).Scheduler)
    (bound : graph.EventId → Nat) (turns : Nat)
    (reference : graph.BehavioralProfile) (focal : Player)
    (deviation : (app).Policy)
    (owner : Player) (event : graph.EventId)
    (owned : graph.actor? event = some owner)
    (solitary : graph.Solitary event) (action : graph.Action event)
    (execution : (app).Execution)
    (ready : execution.application.config.cut.Ready event) :
    let players := Function.update
      (turnPolicy timeouts leaks bound turns
        (EventGraphRuntime.firstTurnTiming graph turns) reference) focal deviation
    let baseline := turnPolicy timeouts leaks bound turns
      (EventGraphRuntime.firstTurnTiming graph turns) reference
    let member := fun past view =>
      if turnIndex timeouts leaks owner event past
        view = some 0 then
        fixedOpportunity timeouts leaks bound owner event action past view
      else baseline owner past view
    ((app).runUntilHorizon scheduler
      (Function.update players owner member)
      (fun final => event ∈ final.application.config.cut.completed) horizon execution) =
    (app).runUntilHorizon scheduler
      (Function.update
        (focalPlayers timeouts leaks focal deviation) owner
        (decidedTurnPolicy timeouts leaks bound owner event action))
      (fun final => event ∈ final.application.config.cut.completed) horizon execution := by
  intro players baseline _member
  unfold ReactiveApplication.runUntilHorizon
  let first := fun past view =>
    turnIndex timeouts leaks owner event past view =
      some 0
  let member := fun past view =>
    if first past view then fixedOpportunity timeouts leaks bound owner event action past view
    else baseline owner past view
  apply (app).runUntil_congr_of_agree scheduler (Function.update players owner member)
    (Function.update (focalPlayers timeouts leaks focal deviation) owner
      (decidedTurnPolicy timeouts leaks bound owner event action))
    (fun final => event ∈ final.application.config.cut.completed)
    (fun current => event ∉ current.application.config.cut.completed →
      current.application.config.cut.Ready event)
  · intro current holds running command _ middle moved actor active
    have activateIs : command = .activate actor := by
      cases command <;> simp_all [ReactiveApplication.Command.actor?]
    subst command
    have unchanged := activation_application timeouts leaks current middle actor moved
    have ready : middle.application.config.cut.Ready event := by
      rw [unchanged]
      exact holds running
    by_cases isOwner : actor = owner
    · subst actor
      simp only [Function.update_self]
      have serving := middle.application.ownTurn?_of_ready solitary.ownerSolitary ready owned
      dsimp only [member, first, decidedTurnPolicy, ReactiveApplication.turnScheduledPolicy]
      simp only [Fin.val_zero]
      by_cases selected : turnIndex timeouts leaks
        owner event
          (middle.logs owner) (middle.observe app owner) = some 0
      · simp only [selected, ite_true]
      · simp only [selected, ite_false]
        exact turnPolicy_later (timeouts := timeouts) (leaks := leaks) owned serving selected
    · simp only [Function.update_of_ne isOwner]
      by_cases isFocal : actor = focal
      · subst actor
        simp only [players, focalPlayers, Function.update_self]
      · simp only [players, focalPlayers, Function.update_of_ne isFocal]
        have idle : (middle.observe app actor).application.publicView.ownTurn? actor = none := by
          change middle.application.publicView.ownTurn? actor = none
          cases turn : middle.application.publicView.ownTurn? actor with
          | none => rfl
          | some other =>
              obtain ⟨visible, actorEq⟩ := PublicView.ownTurn?_spec _ actor other turn
              have same := solitary _ ((middle.application.publicView_eventReady _).mp visible)
                ready
              subst other
              exact (isOwner (Option.some.inj (actorEq.symm.trans owned))).elim
        simp only [EventGraphRuntime.turnPolicy, idle, ReactiveApplication.silentPolicy_apply]
  · intro current holds running next reached nextPending
    rw [reactive_round_config_eq_of_pending timeouts leaks scheduler _ event current next
      (fun _ other => solitary _ other (holds running)) nextPending reached]
    exact holds running
  · exact fun _ => ready



/-- The honest foreign first-turn phase is the native mixture of fixed
canonical decisions, with the same arbitrary focal policy in every branch. -/
theorem foreign_firstTurn_mixture
    {horizon turns : Nat} (scheduler : (app).Scheduler)
    (bound : graph.EventId → Nat) (reference : graph.BehavioralProfile) (focal : Player)
    (deviation : (app).Policy) (owner : Player) (event : graph.EventId)
    (owned : graph.actor? event = some owner) (foreign : owner ≠ focal)
    (solitary : graph.Solitary event) (execution : (app).Execution) :
    let honest := turnPolicy timeouts leaks bound turns
      (EventGraphRuntime.firstTurnTiming graph turns) reference
    let players := Function.update honest focal deviation
    PrefixBoundary (inputs.map State.initial) scheduler players event.val execution →
      execution.environmentRecall.length ≤ horizon →
      let law := actionLaw reference execution.application.config event
      let stop := fun final : (app).Execution => event ∈ final.application.config.cut.completed
      (app).runUntilHorizon scheduler players stop horizon execution =
      law.bind fun action => (app).runUntilHorizon scheduler
        (Function.update (focalPlayers timeouts leaks focal deviation) owner
          (decidedTurnPolicy timeouts leaks bound owner event action))
        stop horizon execution := by
  intro honest players boundary bounded law stop
  have ready := boundary.ordered.ready event.isLt
  have follows : players owner = honest owner := Function.update_of_ne foreign _ _
  have mixed := firstTurn_mixture timeouts leaks scheduler bound reference owner event owned
    players follows execution (fun _ other => solitary _ other ready) boundary.supported
    (boundary.untouched event le_rfl owner) bounded law (fun current same selected => by
      simpa only [law, same] using
        referencePolicy_actionLaw timeouts leaks reference owner current event selected owned)
  rw [mixed]
  apply bind_congr_on_support _
  intro action _
  exact foreign_firstTurn_fixedRun scheduler bound turns reference focal deviation owner event
    owned solitary action execution ready


end Vegas.EventGraphRuntime
