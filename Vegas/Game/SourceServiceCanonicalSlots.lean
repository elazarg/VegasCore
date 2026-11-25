module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceTurnSubmissions
public import Vegas.Pending.CanonicalSlots
public import Vegas.Pending.ReactiveCanonicalMenu
public import Interaction.ReactiveRawRoundTrace

@[expose] public section

/-! # Counted slots and timely submissions of compiled source clients -/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))

section CompiledClients

variable {setup leaks}

/-- A fresh transmission from a compiled source client is its timely, unrecorded own turn. -/
theorem sourceServiceTurnPolicy_submission {bound : (serviceGraph setup deps).EventId → Nat}
    {turns : Nat} {timing : TurnTiming setup turns deps} {profile : BehavioralProfile setup.program}
    {who : Player} {past : List (serviceApplication setup deps duration leaks).PlayerEntry}
    {view : (serviceApplication setup deps duration leaks).PlayerView}
    {response : (serviceApplication setup deps duration leaks).Action}
    (chosen : response ∈
        (serviceTurnPolicy setup deps duration leaks bound turns timing profile who past
        view).support) {material : (serviceApplication setup deps duration leaks).Submission}
    (submits : response.transmission = some material) : ∃ event action,
    view.application.publicView.ownTurn? who = some event ∧
    (eventRecorded (serviceTimeouts setup deps duration)) leaks past event = false ∧
    view.application.publicView.InclusionFitsDeadline (serviceTimeouts setup deps duration)
    bound event ∧
      response = (canonicalServiceDecision (serviceTimeouts setup deps duration)) leaks who past
        view
          event action := by
  exact turnPolicy_canonical_transmission (serviceTimeouts setup deps duration) leaks
    chosen submits

/-- Compiled source clients use the canonical decision at each unrecorded own turn. -/
theorem serviceTurnPolicy_submitsCanonically (bound : (serviceGraph setup deps).EventId → Nat)
    (turns : Nat) (timing : TurnTiming setup turns deps) (profile : BehavioralProfile setup.program)
    (who : Player) :
    EventGraphRuntime.SubmitsCanonically (serviceTimeouts setup deps duration) leaks
      (serviceTurnPolicy setup deps duration leaks bound turns timing profile who)
      who :=
  turnPolicy_submitsCanonically (serviceTimeouts setup deps duration) leaks bound turns timing
    (compileEventProfile setup.program profile) who

end CompiledClients

section Initialized

variable {setup leaks}

/-- The initialized source trace supplies freshness at an unrecorded own turn. -/
theorem canonicalSlot_fresh_of_used
    {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {control : (serviceApplication setup deps duration leaks).Control}
    (trace :
        ((serviceApplication setup deps duration leaks).protocol (serviceInitialLaw setup deps)
        horizon scheduler).Trace (some control))
    (who : Player) (atTurn : OwnSubmissionsAtTurn
      (serviceTimeouts setup deps duration) leaks control.execution who)
    (valid : EventGraphRuntime.CanonicalSlotsUsed (serviceTimeouts setup deps duration)
      leaks control.execution who)
    (event : (serviceGraph setup deps).EventId)
    (ownerSolitary : (serviceGraph setup deps).OwnerSolitary event)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (eventRecorded (serviceTimeouts setup deps duration)) leaks
        (control.execution.logs who) event = false) :
    control.execution.application.candidates.lookup
      (who, .prepared (control.execution.application.publicView.bindingCount who)) = .fresh := by
  rw [serviceInitialLaw_eq_inputs setup] at trace
  exact EventGraphRuntime.canonicalSlot_fresh_of_used (serviceTimeouts setup deps duration) leaks
    trace who atTurn valid event ownerSolitary turn unrecorded

/-- A response on an initialized source history preserves the used-slot invariant. -/
theorem canonicalSlotsUsed_respond
    (serial : (serviceGraph setup deps).ActorSerial) {horizon remaining : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {middle : (serviceApplication setup deps duration leaks).Execution} {who : Player}
    (trace :
        ((serviceApplication setup deps duration leaks).protocol (serviceInitialLaw setup deps)
        horizon scheduler).Trace (some ⟨remaining, some who, middle⟩))
    {policy : (serviceApplication setup deps duration leaks).Policy}
    (canonical : EventGraphRuntime.SubmitsCanonically (serviceTimeouts setup deps duration)
      leaks policy who)
    {response : (serviceApplication setup deps duration leaks).Action}
    (chosen : response ∈ (policy (middle.logs who)
      (middle.observe (serviceApplication setup deps duration leaks) who)).support)
    (atTurn : OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks middle who)
    (valid : EventGraphRuntime.CanonicalSlotsUsed (serviceTimeouts setup deps duration)
      leaks middle who) :
    EventGraphRuntime.CanonicalSlotsUsed (serviceTimeouts setup deps duration) leaks
        (middle.respond (serviceApplication setup deps duration leaks) who response)
      who := by
  rw [serviceInitialLaw_eq_inputs setup] at trace
  exact EventGraphRuntime.canonicalSlotsUsed_respond (serviceTimeouts setup deps duration) leaks
    serial trace canonical chosen atTurn valid

/-- Each round of initialized source service preserves the canonical-slot invariant. -/
theorem canonicalSlots_round
    (serial : (serviceGraph setup deps).ActorSerial) {horizon remaining : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {players : Player → (serviceApplication setup deps duration leaks).Policy} {who : Player}
    (canonical : EventGraphRuntime.SubmitsCanonically (serviceTimeouts setup deps duration)
      leaks (players who) who)
    (submitsAtTurn : SubmitsAtTurn setup leaks (players who) who)
    {execution next : (serviceApplication setup deps duration leaks).Execution}
    (trace :
        ((serviceApplication setup deps duration leaks).protocol (serviceInitialLaw setup deps)
        horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩))
    (atTurn : OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks execution who)
    (valid : EventGraphRuntime.CanonicalSlotsUsed (serviceTimeouts setup deps duration)
      leaks execution who)
    (reached : next ∈
        ((serviceApplication setup deps duration leaks).round scheduler players
        execution).support) :
    OwnSubmissionsAtTurn
      (serviceTimeouts setup deps duration) leaks next who ∧
        EventGraphRuntime.CanonicalSlotsUsed (serviceTimeouts setup deps duration)
          leaks next who := by
  rw [serviceInitialLaw_eq_inputs setup] at trace
  exact EventGraphRuntime.canonicalSlots_round (serviceTimeouts setup deps duration) leaks
    serial canonical submitsAtTurn trace atTurn valid reached

/-- Graph clients on the initialized source law obey the used-slot invariant under arbitrary
other policies. -/
theorem canonicalSlots_roundsFrom_reference
    (serial : (serviceGraph setup deps).ActorSerial)
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (players : Player → (serviceApplication setup deps duration leaks).Policy) (who : Player)
    {bound : (serviceGraph setup deps).EventId → Nat} {turns : Nat}
    (timing : TurnTiming setup turns deps) (reference : (serviceGraph setup deps).BehavioralProfile)
    (follows : players who = turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      timing reference
        who) (count : Nat) (execution : (serviceApplication setup deps duration leaks).Execution)
    (reached : execution ∈
        ((serviceApplication setup deps duration leaks).roundsFrom (serviceInitialLaw setup deps)
        scheduler players count).support) : OwnSubmissionsAtTurn
          (serviceTimeouts setup deps duration) leaks execution who ∧
      EventGraphRuntime.CanonicalSlotsUsed (serviceTimeouts setup deps duration)
        leaks execution who := by
  rw [serviceInitialLaw_eq_inputs setup] at reached
  exact EventGraphRuntime.canonicalSlots_roundsFrom (serviceTimeouts setup deps duration) leaks
    (setup.initialLaw.map setup.eventInputs) serial scheduler players who timing reference follows
    count execution reached

/-- Compiled source clients preserve canonical slots along all supported initialized rounds. -/
theorem canonicalSlots_roundsFrom
    (serial : (serviceGraph setup deps).ActorSerial)
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (players : Player → (serviceApplication setup deps duration leaks).Policy) (who : Player)
    {bound : (serviceGraph setup deps).EventId → Nat} {turns : Nat}
    (timing : TurnTiming setup turns deps) (profile : BehavioralProfile setup.program)
    (follows : players who = serviceTurnPolicy setup deps duration leaks bound turns timing profile
        who) (count : Nat) (execution : (serviceApplication setup deps duration leaks).Execution)
    (reached : execution ∈
        ((serviceApplication setup deps duration leaks).roundsFrom (serviceInitialLaw setup deps)
        scheduler players count).support) : OwnSubmissionsAtTurn
          (serviceTimeouts setup deps duration) leaks execution who ∧
      EventGraphRuntime.CanonicalSlotsUsed (serviceTimeouts setup deps duration)
        leaks execution who := by
  exact canonicalSlots_roundsFrom_reference serial scheduler players who timing
    (compileEventProfile setup.program profile) follows count execution reached

/-- **The counted slot supplies an unrecorded own decision.** On every legal
history where the owner's submissions were made at its own turns and its used
prepared slots stay canonical, the counted slot at an unrecorded own turn is
fresh, below the candidate count, and selected by the canonical decision. -/
theorem canonicalSlot_resources_of_used
    (bounds : MessageBounds (serviceGraph setup deps)) {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    (capacity : (serviceGraph setup deps).order.eventCount ≤ bounds.candidateCount)
    {control : (serviceApplication setup deps duration leaks).Control}
    (trace :
        ((serviceApplication setup deps duration leaks).protocol (serviceInitialLaw setup deps)
        horizon scheduler).Trace (some control))
    (who : Player) (atTurn : OwnSubmissionsAtTurn
      (serviceTimeouts setup deps duration) leaks control.execution who)
    (valid : EventGraphRuntime.CanonicalSlotsUsed (serviceTimeouts setup deps duration)
      leaks control.execution who)
    (event : (serviceGraph setup deps).EventId)
    (ownerSolitary : (serviceGraph setup deps).OwnerSolitary event)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (eventRecorded (serviceTimeouts setup deps duration)) leaks
        (control.execution.logs who) event = false) :
    control.execution.application.publicView.bindingCount who < bounds.candidateCount ∧
      control.execution.application.candidates.lookup
        (who, .prepared (control.execution.application.publicView.bindingCount who)) = .fresh ∧
      canonicalFreshSlot who
        (control.execution.observe (serviceApplication setup deps duration leaks) who).application =
          some (control.execution.application.publicView.bindingCount who) := by
  classical
  have fresh := canonicalSlot_fresh_of_used trace who atTurn valid event ownerSolitary turn
    unrecorded
  refine ⟨?_, fresh, canonicalFreshSlot_canonical who _ fresh⟩
  let history := control.execution.application.config.history.map EventCompletion.event
  have ready := (control.execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have absent : event ∉ history := fun present => ready.1
    ((control.execution.application.config.history_exact event).mp present)
  have distinct : (event :: history).Nodup :=
    List.nodup_cons.mpr ⟨absent, control.execution.application.config.history_nodup⟩
  have lengthBound := distinct.length_le_card
  change history.countP _ < bounds.candidateCount
  apply lt_of_le_of_lt List.countP_le_length
  simp only [List.length_cons, Fintype.card_fin] at lengthBound
  omega

end Initialized

/-- Every fresh call of `who` emitted its own packet addressed to the event it
submitted for, early enough to be included before the deadline within
`bound`. -/
def OwnFreshCalls (bound : (serviceGraph setup deps).EventId → Nat)
    (execution : (serviceApplication setup deps duration leaks).Execution) (who : Player) : Prop :=
  ∀ entry ∈ execution.logs who, ∀ material,
    entry.action.transmission = some material →
    ∃ event message, entry.emitted = some message ∧ message.sender = who ∧
      message.payload.call.event? (serviceGraph setup deps) = some event ∧
      (submittedEvent? (serviceTimeouts setup deps duration)) leaks entry.action = some event ∧
      entry.beforeView.application.publicView.InclusionFitsDeadline
          (serviceTimeouts setup deps duration) bound event

/-- Two fresh calls of `who` for one event emitted the same identifier. -/
def OneCallPerEvent (execution : (serviceApplication setup deps duration leaks).Execution)
    (who : Player) : Prop := ∀ first ∈ execution.logs who, ∀ second ∈ execution.logs who,
    ∀ event
      (firstMessage secondMessage : Message Player (WitnessedPacket (serviceGraph setup deps))),
    (submittedEvent? (serviceTimeouts setup deps duration)) leaks first.action = some event →
    (submittedEvent? (serviceTimeouts setup deps duration)) leaks second.action = some event →
    first.emitted = some firstMessage → second.emitted = some secondMessage → firstMessage.id =
    secondMessage.id


variable {setup leaks}

/-- A recorded fresh call is the owner's only identifier for its event when the
owner calls once per event. -/
theorem FreshCall.sole {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {bound : (serviceGraph setup deps).EventId → Nat}
    {control : (serviceApplication setup deps duration leaks).Control}
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace (some control))
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (once : OneCallPerEvent setup leaks control.execution owner)
    (earlier : List (serviceApplication setup deps duration leaks).PlayerEntry)
    (entry : (serviceApplication setup deps duration leaks).PlayerEntry)
    (later : List (serviceApplication setup deps duration leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup deps)))
    (split : control.execution.logs owner = earlier ++ entry :: later)
    (call : FreshCall (serviceTimeouts setup deps duration) leaks owner event bound entry message) :
    ∀ other ∈ earlier ++ later, ¬ EmitsOtherFor (serviceTimeouts setup deps duration) leaks
      other event message.id := by
  have signed := signedCommitments_history (serviceTimeouts setup deps duration) leaks
    (serviceInitialLaw setup deps) (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨_, rfl⟩) horizon scheduler trace
  have submitted (current : (serviceApplication setup deps duration leaks).PlayerEntry)
      (recorded : current ∈ control.execution.logs owner)
      (sent : Message Player (WitnessedPacket (serviceGraph setup deps)))
      (emitted : current.emitted = some sent)
      (named : sent.payload.call.event? (serviceGraph setup deps) = some event) :
      (submittedEvent? (serviceTimeouts setup deps duration)) leaks current.action = some event
        := by
    obtain ⟨_sender, material, transmitted, packet⟩ :=
      signed.emissions owner current recorded sent emitted
    simp only [EventGraphRuntime.submittedEvent?, transmitted]
    rw [← packet]
    exact named
  have entryMember : entry ∈ control.execution.logs owner := by rw [split]; simp
  intro other otherMember ⟨second, emittedOther, _, secondAddressed, differentId⟩
  have otherRecall : other ∈ control.execution.logs owner := by
    rw [split]
    rcases List.mem_append.mp otherMember with inside | inside
    · exact List.mem_append_left _ inside
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ inside)
  exact differentId (once other otherRecall entry entryMember event second message
    (submitted other otherRecall second emittedOther secondAddressed)
    (submitted entry entryMember message call.emitted call.addressed) emittedOther call.emitted)

/-- A completed round preserves the owner's timely once-per-event calls. -/
theorem round_freshCalls_reference
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {players : Player → (serviceApplication setup deps duration leaks).Policy} {who : Player}
    {bound : (serviceGraph setup deps).EventId → Nat} {turns : Nat}
    (timing : TurnTiming setup turns deps) (reference : (serviceGraph setup deps).BehavioralProfile)
    (follows : players who = turnPolicy (serviceTimeouts setup deps duration) leaks
      bound turns timing
      reference who)
    {execution next : (serviceApplication setup deps duration leaks).Execution}
    (calls : OwnFreshCalls setup leaks bound execution who)
    (once : OneCallPerEvent setup leaks execution who)
    (reached : next ∈ ((serviceApplication setup deps duration leaks).round scheduler players
      execution).support) :
    OwnFreshCalls setup leaks bound next who ∧ OneCallPerEvent setup leaks next who := by
  let app := serviceApplication setup deps duration leaks
  let timeouts := serviceTimeouts setup deps duration
  obtain ⟨command, _, middle, moved, cases⟩ := round_cases setup leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  have callsMiddle : OwnFreshCalls setup leaks bound middle who := by
    unfold OwnFreshCalls
    rw [recallEq]
    exact calls
  have onceMiddle : OneCallPerEvent setup leaks middle who := by
    unfold OneCallPerEvent
    rw [recallEq]
    exact once
  rcases cases with ⟨_, rfl⟩ | ⟨responder, _, response, chosen, rfl⟩
  · exact ⟨callsMiddle, onceMiddle⟩
  · by_cases same : responder = who
    · subst responder
      rw [follows] at chosen
      rcases response with ⟨transmission⟩
      cases transmission with
      | none =>
          obtain ⟨emitted, recalled, _⟩ :=
            respond_recall_self _ leaks middle who ⟨none⟩
          refine ⟨?_, ?_⟩
          · intro entry member material submitted
            rw [recalled] at member
            rcases List.mem_append.mp member with old | fresh
            · exact callsMiddle entry old material submitted
            · obtain rfl := List.mem_singleton.mp fresh
              cases submitted
          · intro first firstMember second secondMember event firstMessage secondMessage
              firstEvent secondEvent firstEmitted secondEmitted
            rw [recalled] at firstMember secondMember
            rcases List.mem_append.mp firstMember with firstOld | firstNew
            · rcases List.mem_append.mp secondMember with secondOld | secondNew
              · exact onceMiddle first firstOld second secondOld event _ _ firstEvent secondEvent
                  firstEmitted secondEmitted
              · obtain rfl := List.mem_singleton.mp secondNew
                cases secondEvent
            · obtain rfl := List.mem_singleton.mp firstNew
              cases firstEvent
      | some material =>
          obtain ⟨event, action, _turn, unrecorded, fits, decided⟩ :=
            turnPolicy_canonical_transmission timeouts leaks chosen rfl
          have canonical := (canonicalServiceDecision_cases timeouts) leaks who (middle.logs who)
            (middle.observe app who) event action
          rw [← decided] at canonical
          have named : (submittedEvent? timeouts) leaks (⟨some material⟩ : app.Action) =
              some event := by
            rcases canonical with silent | named
            · have impossible := congrArg
                (fun response : app.Action => response.transmission) silent
              cases impossible
            · exact named
          let message : Message Player (WitnessedPacket (serviceGraph setup deps)) :=
            ⟨(who, middle.network.nextSerial who), app.packet
              (app.submit middle.application who material) who (middle.network.known who)
              material⟩
          let entry : app.PlayerEntry :=
            ⟨middle.observe app who, ⟨some material⟩, some message⟩
          have recalled : (middle.respond app who ⟨some material⟩).logs who =
              middle.logs who ++ [entry] := by
            simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
            rfl
          have absent : ∀ old ∈ middle.logs who,
              (submittedEvent? timeouts) leaks old.action ≠ some event := by
            intro old present submitted
            have recorded := ((eventRecorded_iff timeouts) leaks _ event).mpr ⟨old, present,
              submitted⟩
            rw [unrecorded] at recorded
            cases recorded
          refine ⟨?_, ?_⟩
          · intro current member content submitted
            rw [recalled] at member
            rcases List.mem_append.mp member with old | fresh
            · exact callsMiddle current old content submitted
            · obtain rfl := List.mem_singleton.mp fresh
              exact ⟨event, message, rfl, rfl, named, named, fits⟩
          · intro first firstMember second secondMember shared firstMessage secondMessage
              firstEvent secondEvent firstEmitted secondEmitted
            rw [recalled] at firstMember secondMember
            rcases List.mem_append.mp firstMember with firstOld | firstNew <;>
              rcases List.mem_append.mp secondMember with secondOld | secondNew
            · exact onceMiddle first firstOld second secondOld shared _ _ firstEvent secondEvent
                firstEmitted secondEmitted
            · obtain rfl := List.mem_singleton.mp secondNew
              rw [named] at secondEvent
              cases Option.some.inj secondEvent
              exact (absent first firstOld firstEvent).elim
            · obtain rfl := List.mem_singleton.mp firstNew
              rw [named] at firstEvent
              cases Option.some.inj firstEvent
              exact (absent second secondOld secondEvent).elim
            · obtain rfl := List.mem_singleton.mp firstNew
              obtain rfl := List.mem_singleton.mp secondNew
              exact congrArg Message.id (Option.some.inj (firstEmitted.symm.trans secondEmitted))
    · have different : who ≠ responder := fun equal => same equal.symm
      have recallSame := app.respond_recall_other middle responder who different response
      refine ⟨?_, ?_⟩
      · unfold OwnFreshCalls
        rw [recallSame]
        exact callsMiddle
      · unfold OneCallPerEvent
        rw [recallSame]
        exact onceMiddle

/-- Every prescribed player's transmitted calls are timely and use one identifier
per event, under arbitrary other policies and scheduler, for every turn timing. -/
theorem sourceServiceTurnPolicy_freshCalls_reference
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (players : Player → (serviceApplication setup deps duration leaks).Policy) (who : Player)
    {bound : (serviceGraph setup deps).EventId → Nat} {turns : Nat}
    (timing : TurnTiming setup turns deps) (reference : (serviceGraph setup deps).BehavioralProfile)
    (follows : players who = turnPolicy (serviceTimeouts setup deps duration) leaks
      bound turns timing
      reference who) (count : Nat)
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (reached : execution ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialLaw setup deps) scheduler players count).support) :
    OwnFreshCalls setup leaks bound execution who ∧
      OneCallPerEvent setup leaks execution who := by
  let app := serviceApplication setup deps duration leaks
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      cases (PMF.mem_support_pure_iff _ _).mp supported
      constructor
      · intro entry member
        cases member
      · intro entry member
        cases member
  | succ count ih =>
      rw [app.roundsFrom_succ] at reached
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨calls, once⟩ := ih prior priorMem
      exact round_freshCalls_reference timing reference follows calls once moved

/-- Every prescribed player's transmitted calls are timely and use one identifier
per event, under arbitrary other policies and scheduler, for every turn timing. -/
theorem sourceServiceTurnPolicy_freshCalls
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (players : Player → (serviceApplication setup deps duration leaks).Policy) (who : Player)
    {bound : (serviceGraph setup deps).EventId → Nat} {turns : Nat}
    (timing : TurnTiming setup turns deps) (profile : BehavioralProfile setup.program)
    (follows : players who = serviceTurnPolicy setup deps duration leaks bound turns timing
      profile who) (count : Nat)
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (reached : execution ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialLaw setup deps) scheduler players count).support) :
    OwnFreshCalls setup leaks bound execution who ∧
      OneCallPerEvent setup leaks execution who := by
  apply sourceServiceTurnPolicy_freshCalls_reference (deps := deps) (duration := duration)
    (reference := compileEventProfile setup.program profile) <;> assumption

end Vegas
