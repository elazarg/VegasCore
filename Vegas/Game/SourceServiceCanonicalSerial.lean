/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCanonicalConformance

/-! # Prescribed fresh calls carry the audit's serial

A fresh call carries its author's next serial, and the audit expects the
number of distinct identifiers of that author already on the ledger
(`Interaction.Message.distinctAuthoredCount`). Under the asynchronous contract,
on the support of the turn-counted policy, deferral trembles included and
whatever everyone else does, the two agree at every fresh call
(`Vegas.sourceServiceTurnPolicy_serial`), so every prescribed fresh call is
permitted by the audit (`Vegas.sourceServiceTurnPolicy_permittedServiceEnvelope`).

Each earlier fresh call of the owner was for an event that has completed by
the time of the next one: on the sequentialized graph the turn's event is the
only ready event. Such a call fits its deadline within the inclusion bound and
is the owner's only identifier for its event, so protected inclusion settles
it, and an event completes only together with its acceptance. Its identifier is
then on the ledger, and copies on the ledger do not count twice.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

section Invariant

/-- Every fresh call of `who` emitted its own packet addressed to the event it
submitted for, early enough to be included before the deadline within
`bound`. -/
def OwnFreshCalls (bound : (graph setup).EventId → Nat)
    (execution : (application setup leaks).Execution) (who : Player) : Prop :=
  ∀ entry ∈ execution.recall who, ∀ material,
    entry.action.transmission = some material →
    ∃ event message, entry.emitted = some message ∧ message.sender = who ∧
      message.payload.call.event? (graph setup) = some event ∧
      (runtime setup).submittedEvent? leaks entry.action = some event ∧
      entry.beforeView.application.publicView.InclusionFitsDeadline (runtime setup) bound event

/-- Two fresh calls of `who` for one event emitted the same identifier. -/
def OneCallPerEvent (execution : (application setup leaks).Execution) (who : Player) : Prop :=
  ∀ first ∈ execution.recall who, ∀ second ∈ execution.recall who,
    ∀ event (firstMessage secondMessage : Message Player (WitnessedPacket (graph setup))),
      (runtime setup).submittedEvent? leaks first.action = some event →
      (runtime setup).submittedEvent? leaks second.action = some event →
      first.emitted = some firstMessage → second.emitted = some secondMessage →
      firstMessage.id = secondMessage.id

/-- Every fresh call of `who` carried the audit's serial: the number of
distinct identifiers of `who` on the ledger it saw. -/
def FreshCallsCounted (execution : (application setup leaks).Execution) (who : Player) :
    Prop :=
  ∀ entry ∈ execution.recall who, ∀ material message,
    entry.action.transmission = some material → entry.emitted = some message →
      message.id.2 = Message.distinctAuthoredCount entry.beforeView.messages.ledger
        message.sender

variable {setup leaks}

/-- A receipt names an identifier on the ledger. -/
private theorem receipt_published {execution : (application setup leaks).Execution}
    (sound : execution.ReceiptsSound (application setup leaks) (fun _ => True))
    {id : MessageId Player} {accepted : Bool} (receipt : (id, accepted) ∈ execution.receipts) :
    id ∈ execution.network.ledger.map Message.id := by
  unfold ReactiveApplication.Execution.ReceiptsSound at sound
  generalize execution.network.ledger = ledger at sound ⊢
  generalize execution.receipts = receipts at sound receipt
  induction sound with
  | nil => cases receipt
  | cons head _ ih =>
      rw [List.map_cons]
      rcases List.mem_cons.mp receipt with same | inside
      · subst same
        exact List.mem_cons.mpr (Or.inl head.1)
      · exact List.mem_cons_of_mem _ (ih inside)

/-- A submission names the event its emitted packet addresses. -/
private theorem issued_submittedEvent {entry : (application setup leaks).PlayerEntry}
    {material : (application setup leaks).Submission}
    (transmission : entry.action.transmission = some material)
    {state : EventGraphRuntime.State (graph setup)} {who : Player}
    {known : List (Message Player (WitnessedPacket (graph setup)))}
    {message : Message Player (WitnessedPacket (graph setup))}
    (packet : (application setup leaks).packet state who known material = message.payload) :
    (runtime setup).submittedEvent? leaks entry.action =
      message.payload.call.event? (graph setup) := by
  unfold EventGraphRuntime.submittedEvent?
  rw [transmission, ← packet]
  rfl

/-- **The serial at a turn.** Under the asynchronous contract, when `event` is
`who`'s turn and `who` has not yet submitted for it, `who`'s next serial is the
number of its distinct identifiers on the ledger. -/
theorem nextSerial_eq_distinctAuthoredCount {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    {actor : Option Player} {who : Player} {middle : (application setup leaks).Execution}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, actor, middle⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks middle who)
    (calls : OwnFreshCalls setup leaks bound middle who)
    (once : OneCallPerEvent setup leaks middle who)
    (conform : FreshCallsConform setup leaks middle who)
    (event : (graph setup).EventId)
    (turn : middle.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime setup).eventRecorded leaks (middle.recall who) event = false) :
    middle.network.nextSerial who = Message.distinctAuthoredCount middle.network.ledger who := by
  let app := application setup leaks
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have issuedAll : middle.SerialsIssued app :=
    app.serialsIssued_history scheduler (initialLaw setup) horizon trace
  symm
  apply Message.distinctAuthoredCount_eq_of_serials
  · intro message member authored
    have below := facts.serials.ledger message member
    change message.id.2 < middle.network.nextSerial message.sender at below
    rw [authored] at below
    exact below
  · intro serial lower
    obtain ⟨entry, member, submitted, message, emitted, identified⟩ := issuedAll who serial lower
    obtain ⟨material, transmission⟩ :
        ∃ material, entry.action.transmission = some material := by
      rcases entry with ⟨view, ⟨transmission⟩, emittedOption⟩
      rcases transmission with _ | material
      · cases submitted
      · exact ⟨material, rfl⟩
    obtain ⟨other, packet, emittedPacket, authored, addressed, submittedOther, fits⟩ :=
      calls entry member material transmission
    rw [emitted] at emittedPacket
    cases Option.some.inj emittedPacket
    have otherTurn := atTurn entry member other submittedOther
    have readyThen := (PublicView.ownTurn?_spec _ who other otherTurn).1
    have owned := (PublicView.ownTurn?_spec _ who other otherTurn).2
    have different : other ≠ event := by
      rintro rfl
      have recorded : (runtime setup).eventRecorded leaks (middle.recall who) other = true :=
        List.any_eq_true.mpr ⟨entry, member, decide_eq_true submittedOther⟩
      rw [unrecorded] at recorded
      cases recorded
    have completed : other ∈ middle.application.config.cut.completed := by
      by_contra unfinished
      have current := (entry_view_current setup leaks middle facts.stable who entry member other
        readyThen unfinished).1
      have readyOther : middle.application.publicView.EventReady other := by
        unfold PublicView.EventReady at readyThen ⊢
        rw [← current]
        exact readyThen
      have readyEvent := (PublicView.ownTurn?_spec _ who event turn).1
      have sole := soleReady_of_ready setup middle.application
        ((middle.application.publicView_eventReady event).mp readyEvent)
      exact different (sole.2 other readyOther)
    obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp member
    have call : FreshCall setup leaks who other bound entry message :=
      { fresh := ⟨material, transmission⟩
        emitted := emitted
        authored := authored
        addressed := addressed
        ready := readyThen
        fits := fits
        conforming := EventGraphRuntime.freshServiceEnvelope.acceptable (runtime setup)
          (conform entry member material message transmission emitted) }
    have sole : ∀ other' ∈ earlier ++ later,
        ¬ EmitsOtherFor (runtime setup) leaks other' other message.id := by
      intro other' otherMember ⟨otherEnvelope, emittedOther, otherAuthor, otherAddressed,
        differentId⟩
      have otherRecall : other' ∈ middle.recall who := by
        rw [split]
        rcases List.mem_append.mp otherMember with inside | inside
        · exact List.mem_append_left _ inside
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ inside)
      have output : otherEnvelope ∈ app.outputs (middle.recall who) :=
        List.mem_filterMap.mpr ⟨other', otherRecall, emittedOther⟩
      rw [← facts.inputs who] at output
      have inputMember := (List.mem_filter.mp output).1
      obtain ⟨issuer, issuerMember, issuerMaterial, issuerTransmission, issuerEmitted, _, _,
        issuerPacket⟩ := facts.provenance.inputs otherEnvelope inputMember
      have senderWho : otherEnvelope.sender = who := by
        rw [otherAuthor, identified]
      rw [senderWho] at issuerMember
      have issuerEvent : (runtime setup).submittedEvent? leaks issuer.action = some other := by
        rw [issued_submittedEvent issuerTransmission issuerPacket]
        exact otherAddressed
      exact differentId (once issuer issuerMember entry member other _ _ issuerEvent
        submittedOther issuerEmitted emitted)
    have settles : SettlesFreshCalls setup leaks who other bound middle :=
      settlesFreshCalls_history setup leaks contract.inclusion who other owned trace
    have receipt := (settles earlier entry later message split call sole).1 completed
    have published := receipt_published facts.receipts receipt
    rw [identified] at published
    exact published

/-- One round keeps `who`'s fresh calls addressed, timely, one per event and
counted, when `who` follows the turn-counted policy. -/
theorem serialFacts_round {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    {players : Player → (application setup leaks).Policy} {who : Player}
    {turns : Nat} {timing : TurnTiming setup turns} {profile : BehavioralProfile setup.program}
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns timing profile who)
    {execution next : (application setup leaks).Execution}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks execution who)
    (valid : CanonicalSlotsUsed setup leaks execution who)
    (conform : FreshCallsConform setup leaks execution who)
    (calls : OwnFreshCalls setup leaks bound execution who)
    (once : OneCallPerEvent setup leaks execution who)
    (counted : FreshCallsCounted setup leaks execution who)
    (reached : next ∈ ((application setup leaks).round scheduler players execution).support) :
    OwnFreshCalls setup leaks bound next who ∧ OneCallPerEvent setup leaks next who ∧
      FreshCallsCounted setup leaks next who := by
  let app := application setup leaks
  have conformNext := freshCallsConform_round follows trace atTurn valid conform reached
  obtain ⟨command, selected, middle, moved, cases⟩ := round_cases setup leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  have atMiddle : OwnSubmissionsAtTurn setup leaks middle who := by
    unfold OwnSubmissionsAtTurn
    rw [recallEq]
    exact atTurn
  have conformMiddle : FreshCallsConform setup leaks middle who := by
    unfold FreshCallsConform
    rw [recallEq]
    exact conform
  have callsMiddle : OwnFreshCalls setup leaks bound middle who := by
    unfold OwnFreshCalls
    rw [recallEq]
    exact calls
  have onceMiddle : OneCallPerEvent setup leaks middle who := by
    unfold OneCallPerEvent
    rw [recallEq]
    exact once
  have countedMiddle : FreshCallsCounted setup leaks middle who := by
    unfold FreshCallsCounted
    rw [recallEq]
    exact counted
  rcases cases with ⟨_, rfl⟩ | ⟨responder, active, response, chosen, rfl⟩
  · exact ⟨callsMiddle, onceMiddle, countedMiddle⟩
  · obtain ⟨middleTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler
      remaining execution middle command trace selected moved
    rw [active] at middleTrace
    by_cases same : responder = who
    · subst responder
      rw [follows] at chosen
      rcases response with ⟨transmission⟩
      rcases transmission with _ | material
      · -- Silence appends an entry that is not a submission.
        obtain ⟨emittedOption, recalled, _⟩ := respond_recall_self setup leaks middle who ⟨none⟩
        refine ⟨?_, ?_, ?_⟩
        · intro entry member material submits
          rw [recalled] at member
          rcases List.mem_append.mp member with old | new
          · exact callsMiddle entry old material submits
          · rw [List.mem_singleton] at new
            subst new
            cases submits
        · intro first firstMember second secondMember event firstMessage secondMessage
            firstEvent secondEvent firstEmitted secondEmitted
          rw [recalled] at firstMember secondMember
          rcases List.mem_append.mp firstMember with firstOld | firstNew
          · rcases List.mem_append.mp secondMember with secondOld | secondNew
            · exact onceMiddle first firstOld second secondOld event _ _ firstEvent secondEvent
                firstEmitted secondEmitted
            · rw [List.mem_singleton] at secondNew
              subst secondNew
              cases secondEvent
          · rw [List.mem_singleton] at firstNew
            subst firstNew
            cases firstEvent
        · intro entry member material message submits
          rw [recalled] at member
          rcases List.mem_append.mp member with old | new
          · exact countedMiddle entry old material message submits
          · rw [List.mem_singleton] at new
            subst new
            cases submits
      · -- A fresh submission at the owner's turn.
        obtain ⟨event, action, turn, unrecorded, fits, _⟩ :=
          sourceServiceTurnPolicy_submission chosen rfl
        have recalled := respond_submit_recall middle who material
        let message : Message Player (WitnessedPacket (graph setup)) :=
          ⟨(who, middle.network.nextSerial who), app.packet
            (app.submit middle.application who material) who (middle.network.known who)
            material⟩
        let entry : app.PlayerEntry :=
          ⟨middle.observe app who, ⟨some material⟩, some message⟩
        have entryMember :
            entry ∈ (middle.respond app who ⟨some material⟩).recall who := by
          rw [recalled]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have entryConform := conformNext entry entryMember material message rfl rfl
        obtain ⟨named, namedAddressed, namedReady, namedActor⟩ :=
          (runtime setup).freshServiceEnvelope_owned _ message entryConform
        have namedTurn : middle.application.publicView.ownTurn? who = some named :=
          ownTurn?_of_ready setup middle.application
            ((middle.application.publicView_eventReady named).mp namedReady) namedActor
        have namedIs : named = event := Option.some.inj (namedTurn.symm.trans turn)
        subst namedIs
        have entryEvent : (runtime setup).submittedEvent? leaks entry.action = some named :=
          namedAddressed
        refine ⟨?_, ?_, ?_⟩
        · intro current member currentMaterial submits
          rw [recalled] at member
          rcases List.mem_append.mp member with old | new
          · exact callsMiddle current old currentMaterial submits
          · rw [List.mem_singleton] at new
            subst new
            exact ⟨named, message, rfl, rfl, namedAddressed, entryEvent, fits⟩
        · intro first firstMember second secondMember shared firstMessage secondMessage
            firstEvent secondEvent firstEmitted secondEmitted
          have absent : ∀ old ∈ middle.recall who,
              (runtime setup).submittedEvent? leaks old.action ≠ some named := by
            intro old oldMember oldEvent
            have recorded : (runtime setup).eventRecorded leaks (middle.recall who) named =
                true := List.any_eq_true.mpr ⟨old, oldMember, decide_eq_true oldEvent⟩
            rw [unrecorded] at recorded
            cases recorded
          rw [recalled] at firstMember secondMember
          rcases List.mem_append.mp firstMember with firstOld | firstNew <;>
            rcases List.mem_append.mp secondMember with secondOld | secondNew
          · exact onceMiddle first firstOld second secondOld shared _ _ firstEvent secondEvent
              firstEmitted secondEmitted
          · rw [List.mem_singleton] at secondNew
            subst secondNew
            rw [entryEvent] at secondEvent
            cases Option.some.inj secondEvent
            exact (absent first firstOld firstEvent).elim
          · rw [List.mem_singleton] at firstNew
            subst firstNew
            rw [entryEvent] at firstEvent
            cases Option.some.inj firstEvent
            exact (absent second secondOld secondEvent).elim
          · rw [List.mem_singleton] at firstNew secondNew
            subst firstNew secondNew
            rw [firstEmitted] at secondEmitted
            rw [Option.some.inj secondEmitted]
        · intro current member currentMaterial currentMessage submits currentEmitted
          rw [recalled] at member
          rcases List.mem_append.mp member with old | new
          · exact countedMiddle current old currentMaterial currentMessage submits currentEmitted
          · rw [List.mem_singleton] at new
            subst new
            cases Option.some.inj currentEmitted
            exact nextSerial_eq_distinctAuthoredCount contract middleTrace atMiddle callsMiddle
              onceMiddle conformMiddle named turn unrecorded
    · have different : who ≠ responder := fun equal => same equal.symm
      have recallSame := app.respond_recall_other middle responder who different response
      refine ⟨?_, ?_, ?_⟩
      · unfold OwnFreshCalls
        rw [recallSame]
        exact callsMiddle
      · unfold OneCallPerEvent
        rw [recallSame]
        exact onceMiddle
      · unfold FreshCallsCounted
        rw [recallSame]
        exact countedMiddle

end Invariant

section Support

variable {setup leaks}

/-- The serial facts hold on the support of every profile in which `who`
follows the turn-counted policy, for every count of rounds within the
horizon. -/
theorem serialFacts_roundsFrom {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    {turns : Nat} (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns timing profile who)
    (count : Nat) (bounded : count ≤ horizon) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support) :
    OwnFreshCalls setup leaks bound execution who ∧ OneCallPerEvent setup leaks execution who ∧
      FreshCallsCounted setup leaks execution who := by
  let app := application setup leaks
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      cases (PMF.mem_support_pure_iff _ _).mp supported
      refine ⟨fun entry member => ?_, fun entry member => ?_, fun entry member => ?_⟩ <;>
        cases member
  | succ count ih =>
      rw [app.roundsFrom_succ] at reached
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨calls, once, counted⟩ := ih (by omega) prior priorMem
      obtain ⟨atTurn, valid⟩ := canonicalSlots_roundsFrom scheduler players who timing profile
        follows count prior priorMem
      have conform : FreshCallsConform setup leaks prior who :=
        fun entry member material message fresh emitted =>
          sourceServiceTurnPolicy_freshServiceEnvelope scheduler players who timing profile
            follows count prior priorMem entry member material fresh message emitted
      obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
        count (by omega) prior priorMem
      rw [show horizon - count = (horizon - (count + 1)) + 1 by omega] at trace
      exact serialFacts_round contract follows trace atTurn valid conform calls once counted moved

/-- **Prescribed fresh calls carry the audit's serial.** Under the asynchronous
contract, in every profile in which `who` follows the turn-counted policy,
deferral trembles included and whatever everyone else does, every fresh
submission of `who` within the horizon carries the number of distinct
identifiers of `who` on the ledger it saw. -/
theorem sourceServiceTurnPolicy_serial {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    {turns : Nat} (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns timing profile who)
    (count : Nat) (bounded : count ≤ horizon) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support)
    (entry : (application setup leaks).PlayerEntry) (member : entry ∈ execution.recall who)
    (material : (application setup leaks).Submission)
    (fresh : entry.action.transmission = some material)
    (message : Message Player (WitnessedPacket (graph setup)))
    (emitted : entry.emitted = some message) :
    message.id.2 = Message.distinctAuthoredCount entry.beforeView.messages.ledger
      message.sender :=
  (serialFacts_roundsFrom contract players who timing profile follows count bounded execution
    reached).2.2 entry member material message fresh emitted

/-- **Prescribed fresh calls are permitted by the audit.** Under the
asynchronous contract, in every profile in which `who` follows the
turn-counted policy, deferral trembles included and whatever everyone else
does, every fresh submission of `who` within the horizon passes the audit's
per-packet rule on the view and ledger it was made from. -/
theorem sourceServiceTurnPolicy_permittedServiceEnvelope {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    {turns : Nat} (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns timing profile who)
    (count : Nat) (bounded : count ≤ horizon) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support)
    (entry : (application setup leaks).PlayerEntry) (member : entry ∈ execution.recall who)
    (material : (application setup leaks).Submission)
    (fresh : entry.action.transmission = some material)
    (message : Message Player (WitnessedPacket (graph setup)))
    (emitted : entry.emitted = some message) :
    (runtime setup).permittedServiceEnvelope entry.beforeView.application.publicView
      entry.beforeView.messages.ledger message = true :=
  ((runtime setup).permittedServiceEnvelope_iff _ _ _).mpr (Or.inr
    ⟨sourceServiceTurnPolicy_serial contract players who timing profile follows count bounded
        execution reached entry member material fresh message emitted,
      sourceServiceTurnPolicy_freshServiceEnvelope scheduler players who timing profile follows
        count execution reached entry member material fresh message emitted⟩)

end Support

end Vegas
