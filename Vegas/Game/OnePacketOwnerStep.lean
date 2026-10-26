/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLumpingInstance

/-! # The owner's step of the one-packet game at a pending publication

A response changes the operational state only through the envelope it emits:
the actor clears, the envelope joins the network, and the responder's recall
gains its current operational view with the envelope
(`Vegas.operationalState_respond`). A menu opening emits the responder's next
envelope with the opening, its own certificate and the event's token
(`Vegas.emittedEnvelope_of_opening`), so an opening of the bound value of a
ready publication event leads to an image read off the operational state: the
handle is public and the owner's key carries the value
(`Vegas.opensBinding_image_congr`).

Hence, if the owner's decoded response keeps silence with mass near a keyed
weight and leaves little mass outside silence and openings of the bound value
(`Vegas.OwnerOpeningLaw`), the owner's step is close to a two-point kernel of
the key, the option and the operational state
(`Vegas.ownerStepClose_of_openingLaw`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The envelope a response emits. -/
def emittedEnvelope (execution : (application setup runtime leaks).Execution) (who : Player)
    (action : (application setup runtime leaks).Action) :
    Option (Message Player (application setup runtime leaks).Payload) :=
  match action.transmission with
  | none => none
  | some submission => some ⟨(who, execution.network.nextSerial who),
      (application setup runtime leaks).packet
        ((application setup runtime leaks).submit execution.application who submission) who
        (execution.network.known who) submission⟩

/-- A response on the operational state: the actor clears, the emitted envelope
joins the network, and the responder's recall gains its current operational
view with the envelope. -/
def OperationalState.respond (responder : Player)
    (emitted : Option (Message Player (application setup runtime leaks).Payload))
    (state : OperationalState setup runtime leaks) : OperationalState setup runtime leaks :=
  { state with
    actor := none
    environment := { state.environment with
      network := match emitted with
        | none => state.environment.network
        | some envelope => (state.network.submit responder
          envelope.payload).2.publicView }
    keys := fun who => if who = responder then (state.keys who).map fun key =>
      { key with recalled := key.recalled ++
        [(key.current, emitted)] } else state.keys who }

/-- A response leaves every player's operational view and delivered value
unchanged. -/
theorem respond_observe_operational (execution : (application setup runtime leaks).Execution)
    (responder : Player) (action : (application setup runtime leaks).Action) (who : Player) :
    operationalView setup runtime leaks ((execution.respond (application setup runtime leaks)
      responder
        action).observe (application setup runtime leaks) who) =
      operationalView setup runtime leaks (execution.observe (application setup runtime leaks)
        who) ∧
    deliveredValue setup runtime leaks who ((execution.respond (application setup runtime leaks)
      responder
        action).observe (application setup runtime leaks) who) =
      deliveredValue setup runtime leaks who (execution.observe (application setup runtime leaks)
        who) := by
  have contract := runtime.reactive_respond_application leaks execution responder action
  constructor
  · change ((execution.respond (application setup runtime leaks) responder
      action).application.publicView,
        (execution.respond (application setup runtime leaks) responder action).network.observe who,
        (execution.respond (application setup runtime leaks) responder action).receipts) =
      (execution.application.publicView, execution.network.observe who, execution.receipts)
    rw [contract.2]
    rcases action with ⟨_ | _⟩ <;> rfl
  · apply deliveredValue_congr (runtime := runtime)
    · change (execution.respond (application setup runtime leaks) responder
        action).application.publicView.ownTurn? who = execution.application.publicView.ownTurn? who
      rw [contract.2]
    · change ((graph setup).playerObserve who
          (execution.respond (application setup runtime leaks) responder
            action).application.config).store =
        ((graph setup).playerObserve who execution.application.config).store
      rw [contract.1]

/-- **A response on the operational state.** -/
theorem operationalState_respond (control : (application setup runtime leaks).Control)
    (responder : Player) (action : (application setup runtime leaks).Action) :
    operationalState setup runtime leaks (some { control with
      actor := none
      execution := control.execution.respond (application setup runtime leaks) responder action }) =
      (operationalState setup runtime leaks (some control)).map
        (OperationalState.respond (runtime := runtime) responder
          (emittedEnvelope (runtime := runtime) control.execution responder action)) := by
  have contract := runtime.reactive_respond_application leaks control.execution
    responder action
  rcases control with ⟨remaining, actor, execution⟩
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      simp only [operationalState, Option.map_some, OperationalState.respond, emittedEnvelope,
        Option.some.injEq, OperationalState.mk.injEq]
      refine ⟨trivial, trivial, rfl, rfl, rfl, ?_⟩
      funext who
      by_cases same : who = responder
      · subst same
        simp only [↓reduceIte, Option.map_some, lateKey, ReactiveApplication.Execution.respond,
          List.map_append, List.map_cons, List.map_nil]
        rfl
      · simp only [same, ↓reduceIte]
        rw [(application setup runtime leaks).respond_recall_other execution responder who same]
        rfl
  | some submission =>
      simp only [operationalState, Option.map_some, OperationalState.respond, emittedEnvelope,
        Option.some.injEq, OperationalState.mk.injEq]
      refine ⟨trivial, trivial, rfl, ?_, rfl, ?_⟩
      · unfold ReactiveApplication.Execution.observeEnvironment
        congr 1
        exact contract.2
      · funext who
        obtain ⟨current, delivered⟩ := respond_observe_operational (runtime := runtime) execution
          responder
          ⟨some submission⟩ who
        by_cases same : who = responder
        · subst same
          simp only [↓reduceIte, Option.map_some, lateKey, Option.some.injEq, LateKey.mk.injEq]
          refine ⟨trivial, current, ?_, delivered⟩
          simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.map_append,
            List.map_cons, List.map_nil]
          rfl
        · simp only [same, ↓reduceIte, lateKey, Option.some.injEq, LateKey.mk.injEq]
          rw [(application setup runtime leaks).respond_recall_other execution responder who same]
          exact ⟨trivial, current, rfl, delivered⟩

/-- **An opening of a bound value.** The response opens the event with the
handle accepted at the binding, carrying the binding's successful value. -/
def OpensBinding (execution : (application setup runtime leaks).Execution) (event : (graph
  setup).EventId)
    {owner : Player} {payload : L.Ty}
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (action : (application setup runtime leaks).Action) : Prop :=
  ∃ submission candidate value, action.transmission = some submission ∧
    submission.call.packet = .opening event candidate ⟨payload, value⟩ ∧
    execution.application.accepted binding.field = some candidate ∧
    binding.get? execution.application.config.store = some (.success value)

variable [Fintype Player] (bounds : MessageBounds (graph setup))

/-- **The envelope of a menu opening.** At a state of a one-packet history, a
one-packet response opening an event emits the next envelope of the responder
carrying that opening, its own certificate, and the event's token. -/
theorem emittedEnvelope_of_opening {horizon : Nat} {scheduler : (application setup runtime
  leaks).Scheduler}
    (history : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History)
    {control : (application setup runtime leaks).Control} (current : history.state = some control)
    (who : Player) (action : (application setup runtime leaks).Action)
    (member : action ∈ bounds.onePacketActions runtime leaks who
      (control.execution.recall who) (control.execution.observe (application setup runtime leaks)
        who))
    {submission : (application setup runtime leaks).Submission}
    (sent : action.transmission = some submission)
    {event : (graph setup).EventId} {candidate : Handle (graph setup)} {raw : Raw L}
    (call : submission.call.packet = .opening event candidate raw) :
    emittedEnvelope (runtime := runtime) control.execution who action =
      some ⟨(who, control.execution.network.nextSerial who),
        ⟨.opening event candidate raw, some ⟨candidate, raw⟩, some ⟨event⟩⟩⟩ := by
  rcases ((bounds.mem_onePacketActions runtime leaks who _ _ action).mp member).2 with
    silent | ⟨material, sentMaterial, permitted⟩
  · rw [sent] at silent
    cases silent
  rw [sent] at sentMaterial
  cases sentMaterial
  have trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    current ▸ (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon
      scheduler history.trace
  obtain ⟨inputRecall, serialRecall, _⟩ := runtime.countRecall_history leaks trace
  have local_ := runtime.localEnvelope_eq_of_recall leaks control.execution inputRecall
    serialRecall who submission
  obtain ⟨tokenValid, correct, _⟩ := (countPermits_eq_true_iff _ _).mp permitted
  rw [local_] at tokenValid correct
  unfold emittedEnvelope
  rw [sent]
  simp only [Option.some.injEq, Message.mk.injEq, true_and]
  set packet := (application setup runtime leaks).packet ((application setup runtime leaks).submit
    control.execution.application who submission) who (control.execution.network.known who)
    submission with packetEq
  have packetCall : packet.call = .opening event candidate raw := call
  have certified : certifiedOpening packet = true := by
    unfold CountCallCorrect at correct
    simp only [packetCall] at correct
    exact correct.1
  obtain ⟨tokenEvent, tokenNamed, tokenEq⟩ := (WitnessedPacket.tokenValid_iff packet).mp tokenValid
  rw [packetCall] at tokenNamed
  cases tokenNamed
  obtain ⟨shapeEvent, shapeCandidate, shapeRaw, shapeToken, shape⟩ :=
    (certifiedOpening_iff packet).mp certified
  have shapeCall := congrArg WitnessedPacket.call shape
  rw [packetCall] at shapeCall
  cases shapeCall
  rw [shape] at tokenEq ⊢
  cases tokenEq
  rfl

omit [Fintype Player] in
/-- A key decides at most one publication event. -/
theorem turnEvent_of_publicationTurn {key : LateKey setup runtime leaks} {event : (graph
  setup).EventId}
    (turn : PublicationTurn (runtime := runtime) key event) : turnEvent (runtime := runtime) key =
      some event := by
  have exists_ : ∃ event, PublicationTurn (runtime := runtime) key event := ⟨event, turn⟩
  unfold turnEvent
  rw [dite_eq_left exists_]
  have chosen := exists_.choose_spec.1
  rw [turn.1] at chosen
  exact congrArg some (Option.some.inj chosen).symm

omit [Fintype Player] in
/-- **The image of a response while the event is pending.** It is the
operational state after the response's emitted envelope. -/
theorem pendingImage_respond {remaining : Nat} {who : Player}
    {execution : (application setup runtime leaks).Execution} {event : (graph setup).EventId}
    (pending : event ∉ execution.application.config.cut.completed)
    (action : (application setup runtime leaks).Action) :
    pendingImage (runtime := runtime) event (some ⟨remaining, none, execution.respond (application
      setup runtime leaks) who
        action⟩) =
      .inl ((operationalState setup runtime leaks (some ⟨remaining, some who, execution⟩)).map
        (OperationalState.respond (runtime := runtime) who (emittedEnvelope (runtime := runtime)
          execution who action))) := by
  rw [pendingImage_of_pending (runtime := runtime) _ (by
    change event ∉ (execution.respond (application setup runtime leaks) who
      action).application.config.cut.completed
    rw [(runtime.reactive_respond_application leaks execution who action).1]
    exact pending)]
  exact congrArg Sum.inl (operationalState_respond (runtime := runtime) ⟨remaining, some who,
    execution⟩ who action)

/-- **Openings of the bound value are read off the operational state.** At
states of one-packet histories with the same operational state, while a
publication event is ready, menu openings of its binding's value lead to the
same image. -/
theorem opensBinding_image_congr {horizon : Nat} {scheduler : (application setup runtime
  leaks).Scheduler}
    {remaining : Nat} {owner : Player}
    (firstHistory secondHistory : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).History)
    {first second : (application setup runtime leaks).Execution}
    (firstCurrent : firstHistory.state = some ⟨remaining, some owner, first⟩)
    (secondCurrent : secondHistory.state = some ⟨remaining, some owner, second⟩)
    (same : operationalState setup runtime leaks (some ⟨remaining, some owner, first⟩) =
      operationalState setup runtime leaks (some ⟨remaining, some owner, second⟩))
    {event : (graph setup).EventId} (ready : first.application.config.cut.Ready event)
    {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (view : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (firstAction secondAction : (application setup runtime leaks).Action)
    (firstMember : firstAction ∈ bounds.onePacketActions runtime leaks owner
      (first.recall owner) (first.observe (application setup runtime leaks) owner))
    (secondMember : secondAction ∈ bounds.onePacketActions runtime leaks owner
      (second.recall owner) (second.observe (application setup runtime leaks) owner))
    (firstOpens : OpensBinding (runtime := runtime) first event binding firstAction)
    (secondOpens : OpensBinding (runtime := runtime) second event binding secondAction) :
    pendingImage (runtime := runtime) event (some ⟨remaining, none, first.respond (application
      setup runtime leaks) owner
        firstAction⟩) =
      pendingImage (runtime := runtime) event (some ⟨remaining, none, second.respond (application
        setup runtime leaks) owner
        secondAction⟩) := by
  have ready' : second.application.config.cut.Ready event :=
    (SameOperational.ready (runtime := runtime) same event).mp ready
  obtain ⟨firstSubmission, firstCandidate, firstValue, firstSent, firstCall, firstAccepted,
    firstStored⟩ := firstOpens
  obtain ⟨secondSubmission, secondCandidate, secondValue, secondSent, secondCall, secondAccepted,
    secondStored⟩ := secondOpens
  have accepted : first.application.accepted = second.application.accepted :=
    congrArg PublicView.accepted (SameOperational.publicView same)
  rw [accepted, secondAccepted] at firstAccepted
  cases Option.some.inj firstAccepted
  have bindings := SameOperational.binding (runtime := runtime) same ready view
  rw [firstStored, secondStored] at bindings
  cases (PublicationResult.success.inj (Option.some.inj bindings))
  have networks : first.network = second.network := SameOperational.network same
  have emitted : emittedEnvelope (runtime := runtime) first owner firstAction =
      emittedEnvelope (runtime := runtime) second owner secondAction := by
    rw [emittedEnvelope_of_opening (runtime := runtime) bounds firstHistory firstCurrent owner
      firstAction firstMember
        firstSent firstCall,
      emittedEnvelope_of_opening (runtime := runtime) bounds secondHistory secondCurrent owner
        secondAction
        secondMember secondSent secondCall, networks]
  rw [pendingImage_respond (runtime := runtime) ready.1, pendingImage_respond (runtime := runtime)
    ready'.1, same, emitted]

omit [Fintype Player] in
/-- An opening of a publication event by its owner of the binding's value. -/
def OpensTurn (event : (graph setup).EventId) (owner : Player)
    (execution : (application setup runtime leaks).Execution) (action : (application setup runtime
      leaks).Action) :
    Prop :=
  ∃ (payload : L.Ty) (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks),
    nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq ∧
      OpensBinding (runtime := runtime) execution event binding action

variable (horizon : Nat) (scheduler : (application setup runtime leaks).Scheduler)

open Classical in
/-- The image after the owner opens the decided event from an operational
state, read off a representative forced state with the event ready; nothing
when there is none. -/
def openedImage (key : LateKey setup runtime leaks) (state : Option (OperationalState setup
  runtime leaks)) :
    PendingImage (runtime := runtime) (setup := setup) (leaks := leaks) :=
  match turnEvent (runtime := runtime) key with
  | none => .inl none
  | some event =>
      if represented : ∃ witness : (onePacketProtocol setup runtime leaks bounds horizon
          scheduler).History × Nat × (application setup runtime leaks).Execution ×
            (application setup runtime leaks).Action,
          witness.1.state = some ⟨witness.2.1, some key.owner, witness.2.2.1⟩ ∧
          ForcedState setup runtime leaks key.owner witness.1.state ∧
          witness.2.2.1.application.config.cut.Ready event ∧
          operationalState setup runtime leaks (some ⟨witness.2.1, some key.owner, witness.2.2.1⟩) =
            state ∧
          witness.2.2.2 ∈ bounds.onePacketActions runtime leaks key.owner
            (witness.2.2.1.recall key.owner)
            (witness.2.2.1.observe (application setup runtime leaks) key.owner) ∧
          OpensTurn (runtime := runtime) event key.owner witness.2.2.1
            witness.2.2.2 then
        pendingImage (runtime := runtime) event (some ⟨represented.choose.2.1, none,
          represented.choose.2.2.1.respond (application setup runtime leaks) key.owner
            represented.choose.2.2.2⟩)
      else .inl none

/-- **The owner's opening kernel.** With the weight a Boolean law gives
silence, the owner keeps silence; otherwise it opens the decided event. -/
def openingKernel {LateOption : Type}
    (silence : LateKey setup runtime leaks → LateOption → Option (OperationalState setup runtime
      leaks) →
      PMF Bool)
    (key : LateKey setup runtime leaks) (option : LateOption)
    (state : Option (OperationalState setup runtime leaks)) :
    PMF (PendingImage (runtime := runtime) (setup := setup) (leaks := leaks)) :=
  (silence key option state).map fun silent =>
    if silent then .inl (state.map (OperationalState.respond (runtime := runtime) key.owner none))
    else openedImage (runtime := runtime) bounds horizon scheduler key state

open Classical in
/-- **The owner's opening law at a key.** At every forced state with the
decided publication event ready and the owner acting, the owner's decoded
response keeps silence with mass within `δ₁` of the key's silence weight, and
leaves at most `δ₂` outside silence and openings of the bound value. -/
def OwnerOpeningLaw {LateOption : Type}
    (silence : LateKey setup runtime leaks → LateOption → Option (OperationalState setup runtime
      leaks) →
      PMF Bool)
    (key : LateKey setup runtime leaks) (option : LateOption)
    (profile : ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player)
    (δ₁ δ₂ : ℝ) (allowed : (application setup runtime leaks).ProtocolState → Prop := fun _ =>
      True) :
    Prop :=
  ∀ event, PublicationTurn (runtime := runtime) key event →
    ∀ (history : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History)
      (control : (application setup runtime leaks).Control), history.state = some control →
      allowed (some control) →
      ForcedState setup runtime leaks key.owner (some control) →
      control.execution.application.config.cut.Ready event →
      control.actor = some key.owner →
      |expect ((bounds.onePacketMenu runtime leaks).decodeProfile (initialLaw setup)
          horizon scheduler profile key.owner (control.execution.recall
            key.owner)
          (control.execution.observe (application setup runtime leaks) key.owner))
          (fun action => if action.transmission = none then 1 else 0) -
        expect (silence key option (operationalState setup runtime leaks (some control)))
          (fun silent => if silent then 1 else 0)| ≤ δ₁ ∧
      expect ((bounds.onePacketMenu runtime leaks).decodeProfile (initialLaw setup)
          horizon scheduler profile key.owner (control.execution.recall
            key.owner)
          (control.execution.observe (application setup runtime leaks) key.owner))
          (fun action => if action.transmission = none ∨
            OpensTurn (runtime := runtime) event key.owner control.execution
              action then 0 else 1) ≤ δ₂

variable {horizon scheduler}

omit [Fintype Player] in
/-- The control step at the owner's activation is the owner's decoded response
followed by the response transition. -/
theorem controlStep_owner (players : Player → (application setup runtime leaks).Policy)
    (remaining : Nat) (owner : Player) (execution : (application setup runtime leaks).Execution) :
    (application setup runtime leaks).controlStep (initialLaw setup) horizon scheduler players
        (some ⟨remaining, some owner, execution⟩) =
      (players owner (execution.recall owner) (execution.observe (application setup runtime leaks)
        owner)).map fun action =>
          some ⟨remaining, none, execution.respond (application setup runtime leaks) owner action⟩
            := by
  unfold ReactiveApplication.controlStep
  simp only [ReactiveApplication.actor, Option.bind_some]
  rw [← PMF.bind_pure_comp]
  congr 1
  funext action
  rw [transition_respond (runtime := runtime) (horizon := horizon) (scheduler := scheduler)
    ⟨remaining, some owner, execution⟩ rfl]
  simp only [↓reduceIte, Option.getD_some, Function.comp]

open Classical in
/-- **The owner's step from its opening law.** -/
theorem ownerStepClose_of_openingLaw {LateOption : Type}
    (silence : LateKey setup runtime leaks → LateOption → Option (OperationalState setup runtime
      leaks) →
      PMF Bool)
    (key : LateKey setup runtime leaks) (option : LateOption)
    (profile : ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player)
    {δ₁ δ₂ : ℝ} {allowed : (application setup runtime leaks).ProtocolState → Prop}
    (law : OwnerOpeningLaw (runtime := runtime) bounds horizon scheduler silence key option
      profile δ₁ δ₂ allowed) :
    OwnerStepClose (runtime := runtime) (openingKernel (runtime := runtime) bounds horizon
      scheduler silence) key option profile
      (δ₁ + δ₂) allowed := by
  intro event turn history control current allowedState forced ready acting
  have turnEq := turnEvent_of_publicationTurn (runtime := runtime) turn
  obtain ⟨silentMass, remainder⟩ := law event turn history control current allowedState forced
    ready acting
  rcases control with ⟨remaining, actor, execution⟩
  change actor = some key.owner at acting
  subst acting
  obtain ⟨_, payload, binding, checks, outputEq, codeEq, view⟩ := turn
  rw [controlStep_owner, PMF.map_comp]
  apply withinTV_map_of_two_outcomes _ _ (fun action => action.transmission = none)
    (fun action => OpensTurn (runtime := runtime) event key.owner execution
      action) _ _ _ δ₁ δ₂ _ _ silentMass
    remainder
  · intro action _ silent
    simp only [Function.comp]
    rw [pendingImage_respond (runtime := runtime) ready.1]
    simp only [emittedEnvelope, silent]
  · intro action supported _ opens
    have member := (bounds.onePacketMenu runtime leaks).decodeProfile_support
      (initialLaw setup) horizon scheduler profile key.owner _ _ action
        supported
    have represented : ∃ witness : (onePacketProtocol setup runtime leaks bounds horizon
        scheduler).History × Nat × (application setup runtime leaks).Execution ×
          (application setup runtime leaks).Action,
        witness.1.state = some ⟨witness.2.1, some key.owner, witness.2.2.1⟩ ∧
        ForcedState setup runtime leaks key.owner witness.1.state ∧
        witness.2.2.1.application.config.cut.Ready event ∧
        operationalState setup runtime leaks (some ⟨witness.2.1, some key.owner, witness.2.2.1⟩) =
          operationalState setup runtime leaks (some ⟨remaining, some key.owner, execution⟩) ∧
        witness.2.2.2 ∈ bounds.onePacketActions runtime leaks key.owner
          (witness.2.2.1.recall key.owner)
          (witness.2.2.1.observe (application setup runtime leaks) key.owner) ∧
        OpensTurn (runtime := runtime) event key.owner witness.2.2.1
          witness.2.2.2 :=
      ⟨(history, remaining, execution, action), current, by rw [current]; exact forced, ready,
        rfl, member, opens⟩
    simp only [Function.comp]
    unfold openedImage
    rw [turnEq]
    simp only
    rw [dite_eq_left represented]
    have spec := represented.choose_spec
    generalize represented.choose = witness at spec ⊢
    obtain ⟨chosenHistory, chosenRemaining, chosenExecution, chosenAction⟩ := witness
    obtain ⟨chosenCurrent, _, _, chosenSame, chosenMember, chosenOpens⟩ := spec
    have remainingEq : chosenRemaining = remaining := SameOperational.remaining chosenSame
    subst remainingEq
    obtain ⟨_, _, _, _, _, ourView, ourOpens⟩ := opens
    obtain ⟨_, _, _, _, _, chosenView, chosenOpens⟩ := chosenOpens
    cases ourView.symm.trans view
    cases chosenView.symm.trans view
    exact opensBinding_image_congr (runtime := runtime) bounds history chosenHistory current
      chosenCurrent
      chosenSame.symm ready view action chosenAction member chosenMember ourOpens
      chosenOpens

end Vegas
