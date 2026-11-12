module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealService
public import Vegas.Pending.ReactiveSettledStability
public import Vegas.Pending.ReactiveGraphSteps
public import Interaction.ReactiveReceipts
public import Vegas.Pending.ReactiveServiceAudit
public import Interaction.ReactiveMessageIdentity
public import Vegas.Pending.ReactiveEventStability

@[expose] public section

/-! # Traffic facts for settled native executions

The traffic certificate relates emitted packets, input recall, receipts,
readiness tokens and completed content at arbitrary native histories.
Packet content along finite graph paths is handled by the native settled
stability API; accepted-message origins use the generic receipt accessor.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]


section Facts

variable (setup : Setup (Player := Player) (L := L))
  {mode : EventGraph.ExecutionMode}
  {duration : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- An envelope the network has carried as an input. -/
def Emitted (execution : (serviceApplication setup mode duration leaks).Execution)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode))) : Prop :=
  message ∈ execution.network.inputs

/-- One scheduler command keeps the inputs and the next serials. It either keeps
the ledger and receipts and lets the network only learn, or includes one pending
envelope with its receipt. -/
theorem environmentStep_shape
    (execution next : (serviceApplication setup mode duration leaks).Execution)
    (command : (serviceApplication setup mode duration leaks).Command)
    (reached : next ∈
        (execution.environmentStep (serviceApplication setup mode duration leaks)
        command).support) : next.network.inputs = execution.network.inputs ∧
    next.network.nextSerial = execution.network.nextSerial ∧
    ((next.receipts = execution.receipts ∧ next.network.ledger = execution.network.ledger ∧ ∀ safe :
        Message Player (WitnessedPacket (serviceGraph setup mode)) → Prop,
        execution.network.Satisfies safe → next.network.Satisfies safe) ∨ ∃ id message,
        execution.network.lookup id = some message ∧ next.network =
        (execution.network.includePending id).2 ∧ next.receipts = execution.receipts ++
        [(id, ((serviceApplication setup mode duration leaks).handle execution.application
        message).isSome)] ∧ next.application =
        ((serviceApplication setup mode duration leaks).handle execution.application
            message).getD execution.application) := by
  unfold ReactiveApplication.Execution.environmentStep at reached
  rw [PMF.support_map] at reached
  obtain ⟨updated, supported, rfl⟩ := reached
  cases command with
  | activate who =>
      rw [PMF.support_map] at supported
      obtain ⟨selected, _, rfl⟩ := supported
      exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl, fun _ valid => valid.learn who selected⟩⟩
  | wait =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl, fun _ valid => valid⟩⟩
  | application command =>
      rw [PMF.support_map] at supported
      obtain ⟨_, _, rfl⟩ := supported
      exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl, fun _ valid => valid⟩⟩
  | «include» id =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      change
          (execution.includePending (serviceApplication setup mode duration leaks)
              id).network.inputs = _ ∧
          (execution.includePending (serviceApplication setup mode duration leaks)
              id).network.nextSerial = _ ∧
          (((execution.includePending (serviceApplication setup mode duration leaks) id).receipts =
              _ ∧ (execution.includePending (serviceApplication setup mode duration leaks)
              id).network.ledger = _ ∧ _) ∨ _)
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl, fun _ valid => valid⟩⟩
      | some message =>
          refine ⟨rfl, rfl, Or.inr ⟨id, message, found, ?_, rfl, rfl⟩⟩
          simp only [found]

/-- The facts every legal history keeps, for every scheduler and arbitrary
responses, that tie the receipts and tokens to the traffic. -/
structure SettledFacts (execution : (serviceApplication setup mode duration leaks).Execution) :
    Prop where
  serials : execution.network.SerialsBeforeNext
  unique : execution.network.UniqueIds
  receipts : execution.ReceiptsSound (serviceApplication setup mode duration leaks) (fun _ => True)
  /-- Every envelope the network holds was an input. -/
  carried : execution.network.Satisfies (Emitted setup leaks execution)
  /-- Every allocated identifier was emitted. -/
  allocated : ∀ who serial, serial < execution.network.nextSerial who →
    ∃ message, Emitted setup leaks execution message ∧ message.id = (who, serial)
  /-- A readiness token names an event whose prerequisites have completed. -/
  issued : ∀ message, Emitted setup leaks execution message → ∀ token,
    message.payload.token = some token →
    ∀ predecessor ∈ (serviceGraph setup mode).order.predecessors token.event,
      predecessor ∈ execution.application.config.cut.completed
  /-- An accepting receipt names a ledger envelope with a valid token, whose
  event has completed and whose sender is that event's actor. -/
  accepted : ∀ id, (id, true) ∈ execution.receipts →
    ∃ message ∈ execution.network.ledger, message.id = id ∧
      message.payload.tokenValid = true ∧
      ∃ event, message.payload.call.event? (serviceGraph setup mode) = some event ∧
        event ∈ execution.application.config.cut.completed ∧
        (serviceGraph setup mode).actor? event = some message.sender
  /-- The contract accepts at most one identifier per event. -/
  single : ∀ first ∈ execution.network.ledger, ∀ second ∈ execution.network.ledger,
    (first.id, true) ∈ execution.receipts → (second.id, true) ∈ execution.receipts →
    ∀ event, first.payload.call.event? (serviceGraph setup mode) = some event →
      second.payload.call.event? (serviceGraph setup mode) = some event → first.id = second.id
  /-- Once a later identifier of an author is accepted, the event of each of the
  author's earlier identifiers with a valid token for an event the author acts
  at has completed. -/
  ordered : ∀ earlier later, Emitted setup leaks execution earlier →
    Emitted setup leaks execution later → earlier.sender = later.sender →
    earlier.id.2 < later.id.2 → (later.id, true) ∈ execution.receipts →
    earlier.payload.tokenValid = true →
    ∀ event, earlier.payload.call.event? (serviceGraph setup mode) = some event →
      (serviceGraph setup mode).actor? event = some earlier.sender →
      event ∈ execution.application.config.cut.completed

variable {setup leaks}

/-- A receipt names an identifier on the ledger. -/
theorem SettledFacts.receipt_published
    {execution : (serviceApplication setup mode duration leaks).Execution}
    (facts : SettledFacts setup leaks execution) {id : MessageId Player} {accepted : Bool}
    (receipt : (id, accepted) ∈ execution.receipts) :
    id ∈ execution.network.ledger.map Message.id := by
  have sound := facts.receipts
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

/-- Two emitted envelopes with one identifier are equal. -/
theorem SettledFacts.emitted_unique
    {execution : (serviceApplication setup mode duration leaks).Execution}
    (facts : SettledFacts setup leaks execution)
    {first second : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (firstEmitted : Emitted setup leaks execution first)
    (secondEmitted : Emitted setup leaks execution second) (same : first.id = second.id) :
    first = second := by
  exact ((facts.unique.inputs first firstEmitted).inputs second secondEmitted
    same.symm).symm

/-- An emitted envelope's serial is below its author's next serial. -/
theorem SettledFacts.emitted_serial
    {execution : (serviceApplication setup mode duration leaks).Execution}
    (facts : SettledFacts setup leaks execution)
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (emitted : Emitted setup leaks execution message) :
    message.id.2 < execution.network.nextSerial message.id.1 := by
  exact facts.serials.inputs message emitted

theorem settledFacts_initial (state : (serviceApplication setup mode duration leaks).State) :
    SettledFacts setup leaks
        (ReactiveApplication.Execution.initial (serviceApplication setup mode duration leaks)
      state) where
  serials := MessageNetwork.SerialsBeforeNext.empty
  unique := MessageNetwork.UniqueIds.empty
  receipts := (serviceApplication setup mode duration leaks).receiptsSound_initial _ state
  carried := MessageNetwork.Satisfies.empty
  allocated := by
    intro who serial lower
    exact absurd lower (Nat.not_lt_zero _)
  issued := by
    intro message emitted
    simp [Emitted, ReactiveApplication.Execution.initial, MessageNetwork.empty] at emitted
  accepted := by
    intro id member
    simp [ReactiveApplication.Execution.initial] at member
  single := by
    intro first member
    simp [ReactiveApplication.Execution.initial, MessageNetwork.empty] at member
  ordered := by
    intro earlier later emitted
    simp [Emitted, ReactiveApplication.Execution.initial, MessageNetwork.empty] at emitted

/-- A response only appends inputs. -/
theorem respond_emitted_mono (execution : (serviceApplication setup mode duration leaks).Execution)
    (who : Player) (action : (serviceApplication setup mode duration leaks).Action)
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (emitted : Emitted setup leaks execution message) :
    Emitted setup leaks
        (execution.respond (serviceApplication setup mode duration leaks) who action) message := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact emitted
  | some material =>
      unfold Emitted at emitted ⊢
      simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit,
        List.mem_append]
      exact Or.inl emitted

/-- A response emits fresh at most the responder's next identifier; any other new
input is an envelope the network already carried. -/
theorem respond_emitted {execution : (serviceApplication setup mode duration leaks).Execution}
    (_facts : SettledFacts setup leaks execution) (who : Player)
    (action : (serviceApplication setup mode duration leaks).Action)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (emitted : Emitted setup leaks
        (execution.respond (serviceApplication setup mode duration leaks) who action) message) :
    Emitted setup leaks execution message ∨
      ∃ material, action.transmission = some material ∧
        message = ⟨(who, execution.network.nextSerial who),
          (serviceApplication setup mode duration leaks).packet
          ((serviceApplication setup mode duration leaks).submit
            execution.application who material) who (execution.network.known who) material⟩ := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact Or.inl emitted
  | some material =>
      unfold Emitted at emitted
      simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit,
        List.mem_append, List.mem_singleton] at emitted
      rcases emitted with prior | fresh
      · exact Or.inl prior
      · exact Or.inr ⟨material, rfl, fresh⟩

/-- A response advances only the responder's next serial, and only by a fresh
submission. -/
theorem respond_nextSerial (execution : (serviceApplication setup mode duration leaks).Execution)
    (who : Player) (action : (serviceApplication setup mode duration leaks).Action)
    (observer : Player) :
    (execution.respond (serviceApplication setup mode duration leaks) who action).network.nextSerial
    observer = execution.network.nextSerial observer ∨
    ((∃ material, action.transmission = some material) ∧ observer = who ∧
        (execution.respond (serviceApplication setup mode duration leaks) who
        action).network.nextSerial observer =
          execution.network.nextSerial who + 1) := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact Or.inl rfl
  | some material =>
      by_cases same : observer = who
      · subst observer
        right
        refine ⟨⟨material, rfl⟩, rfl, ?_⟩
        simp [ReactiveApplication.Execution.respond, MessageNetwork.submit]
      · left
        simp [ReactiveApplication.Execution.respond, MessageNetwork.submit, same]

/-- The token a submission's emission carries names an event whose
prerequisites have completed. -/
theorem packet_token_issued (state : (serviceApplication setup mode duration leaks).State)
    (who : Player) (known : List (Message Player (WitnessedPacket (serviceGraph setup mode))))
    (material : (serviceApplication setup mode duration leaks).Submission)
    (token : ReadinessToken (serviceGraph setup mode))
    (carried :
        ((serviceApplication setup mode duration leaks).packet
        ((serviceApplication setup mode duration leaks).submit state who material) who known
        material).token = some token) : ∀ predecessor ∈ (serviceGraph setup mode).order.predecessors
    token.event,
      predecessor ∈ state.config.cut.completed := by
  rw [reactiveApplication_packet_token] at carried
  unfold PublicView.tokenFor at carried
  obtain ⟨event, _, issued⟩ := Option.bind_eq_some_iff.mp carried
  obtain ⟨rfl, settled⟩ := (state.publicView.readinessToken?_eq_some_iff event token).mp issued
  intro predecessor member
  exact (state.config.history_exact predecessor).mp (settled predecessor member)

theorem settledFacts_respond (execution : (serviceApplication setup mode duration leaks).Execution)
    (facts : SettledFacts setup leaks execution) (who : Player)
    (action : (serviceApplication setup mode duration leaks).Action) :
    SettledFacts setup leaks
        (execution.respond (serviceApplication setup mode duration leaks) who action) := by
  let app := serviceApplication setup mode duration leaks
  have configEq :=
      ((reactive_respond_application (serviceTimeouts setup mode duration)) leaks execution who
          action).1
  have receiptsEq := app.respond_receipts execution who action
  have ledgerEq := app.respond_ledger execution who action
  have identity := (app.messageIdentityInvariant (fun _ _ => PMF.pure .wait)).respond execution
    who action ⟨facts.serials, facts.unique⟩
  have fresh : ∀ material (token : ReadinessToken (serviceGraph setup mode)),
      (app.packet (app.submit execution.application who material) who
        (execution.network.known who) material).token = some token →
      ∀ predecessor ∈ (serviceGraph setup mode).order.predecessors token.event,
        predecessor ∈ execution.application.config.cut.completed :=
    fun material token carried =>
      packet_token_issued execution.application who _ material token carried
  refine
    { serials := identity.1
      unique := identity.2
      receipts := app.receiptsSound_respond _ execution who action facts.receipts
      carried := ?_
      allocated := ?_
      issued := ?_
      accepted := ?_
      single := ?_
      ordered := ?_ }
  · rcases action with ⟨transmission⟩
    cases transmission with
    | none => exact facts.carried
    | some material =>
        apply (facts.carried.mono fun message emitted =>
          respond_emitted_mono execution who _ emitted).submit
        unfold Emitted
        simp [ReactiveApplication.Execution.respond, MessageNetwork.submit]
  · intro observer serial lower
    rcases respond_nextSerial execution who action observer with same | ⟨⟨material, submitted⟩,
        rfl, advanced⟩
    · rw [same] at lower
      obtain ⟨message, emitted, identified⟩ := facts.allocated observer serial lower
      exact ⟨message, respond_emitted_mono execution who action emitted, identified⟩
    · rw [advanced] at lower
      rcases Nat.lt_succ_iff_lt_or_eq.mp lower with below | equal
      · obtain ⟨message, emitted, identified⟩ := facts.allocated observer serial below
        exact ⟨message, respond_emitted_mono execution observer action emitted, identified⟩
      · subst equal
        refine ⟨⟨(observer, execution.network.nextSerial observer),
          app.packet (app.submit execution.application observer material) observer
            (execution.network.known observer) material⟩, ?_, rfl⟩
        rcases action with ⟨transmission⟩
        cases submitted
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  · intro message emitted token carried
    rw [configEq]
    rcases respond_emitted facts who action message emitted with prior | ⟨material, _, rfl⟩
    · exact facts.issued message prior token carried
    · exact fresh material token carried
  · intro id member
    rw [receiptsEq] at member
    rw [ledgerEq, configEq]
    exact facts.accepted id member
  · intro first firstMember second secondMember firstAccepted secondAccepted
    rw [ledgerEq] at firstMember secondMember
    rw [receiptsEq] at firstAccepted secondAccepted
    exact facts.single first firstMember second secondMember firstAccepted secondAccepted
  · intro earlier later earlierEmitted laterEmitted sameSender lower accepted
    rw [receiptsEq] at accepted
    rw [configEq]
    rcases respond_emitted facts who action later laterEmitted with laterPrior |
        ⟨material, _, rfl⟩
    · rcases respond_emitted facts who action earlier earlierEmitted with earlierPrior |
          ⟨material, _, rfl⟩
      · exact facts.ordered earlier later earlierPrior laterPrior sameSender lower accepted
      · have bound := facts.emitted_serial laterPrior
        change who = later.id.1 at sameSender
        rw [← sameSender] at bound
        exact absurd lower (Nat.not_lt.mpr (Nat.le_of_lt bound))
    · have published := facts.receipt_published accepted
      obtain ⟨message, member, identified⟩ := List.mem_map.mp published
      have bound := facts.serials.ledger message member
      rw [identified] at bound
      exact absurd bound (Nat.lt_irrefl _)

/-- An included envelope carries its lookup identifier and lands on the ledger. -/
theorem includePending_found
    (network : MessageNetwork Player (WitnessedPacket (serviceGraph setup mode)))
    (id : MessageId Player) (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (found : network.lookup id = some message) : message.id = id ∧ message ∈ network.pending ∧
      (network.includePending id).2.ledger = network.ledger ++ [message] := by
  refine ⟨?_, List.mem_of_find?_eq_some found, ?_⟩
  · have identified := (List.find?_eq_some_iff_append.mp found).1
    simpa only [decide_eq_true_eq] using identified
  · simp only [MessageNetwork.includePending, found]

/-- What an accepting inclusion establishes: the envelope's token is valid, its
event was ready and has completed, and its sender is the event's actor. -/
theorem accepted_inclusion (state next : (serviceApplication setup mode duration leaks).State)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (handled : (serviceApplication setup mode duration leaks).handle state message = some next) :
    message.payload.tokenValid = true ∧
      ∃ event, message.payload.call.event? (serviceGraph setup mode) = some event ∧
        state.config.cut.Ready event ∧ event ∈ next.config.cut.completed ∧
        (serviceGraph setup mode).actor? event = some message.sender := by
  obtain ⟨valid, native, call, drained⟩ := reactiveApplication_handle_eq_some
    (serviceTimeouts setup mode duration) leaks state next message handled
  obtain ⟨event, named, ready, action, member⟩ :=
    handle_config_mem_step (serviceTimeouts setup mode duration) state native _ call
  refine ⟨valid, event, named, ready, ?_, handle_sender_actor
    (serviceTimeouts setup mode duration) state native _ call event named⟩
  rw [← drained]
  apply native.drainFuel_completed_subset native.config.remaining
  rw [state.config.step_cut event ready action native.config member]
  exact Finset.mem_insert_self _ _

theorem settledFacts_environment
    (execution next : (serviceApplication setup mode duration leaks).Execution)
    (command : (serviceApplication setup mode duration leaks).Command)
    (facts : SettledFacts setup leaks execution)
    (reached : next ∈
        (execution.environmentStep (serviceApplication setup mode duration leaks)
        command).support) :
    SettledFacts setup leaks next := by
  let app := serviceApplication setup mode duration leaks
  obtain ⟨inputsEq, serialEq, effect⟩ :=
    environmentStep_shape setup leaks execution next command reached
  have path := (reactiveApplication_graphSteps (serviceTimeouts setup mode duration)
    leaks).environmentStep execution next command reached
  have identity := (app.messageIdentityInvariant (fun _ _ => PMF.pure command)).environment
    execution next command ⟨facts.serials, facts.unique⟩ (by simp) reached
  have sound := app.receiptsSound_environmentStep _ execution next command facts.receipts
    (fun _ _ _ => trivial) reached
  have emittedEq : ∀ message, Emitted setup leaks next message ↔
      Emitted setup leaks execution message := by
    intro message
    unfold Emitted
    rw [inputsEq]
  have completedMono : ∀ event, event ∈ execution.application.config.cut.completed →
      event ∈ next.application.config.cut.completed :=
    fun _ completed => EventGraph.Config.Step.path_completed_mono path completed
  refine
    { serials := identity.1
      unique := identity.2
      receipts := sound
      carried := ?_
      allocated := ?_
      issued := ?_
      accepted := ?_
      single := ?_
      ordered := ?_ }
  · rcases effect with ⟨_, _, keep⟩ | ⟨id, message, found, networkEq, _, _⟩
    · exact keep _ (facts.carried.mono fun message emitted => (emittedEq message).mpr emitted)
    · rw [networkEq]
      exact (facts.carried.mono fun message emitted =>
        (emittedEq message).mpr emitted).includePending id
  · intro who serial lower
    rw [serialEq] at lower
    obtain ⟨message, emitted, identified⟩ := facts.allocated who serial lower
    exact ⟨message, (emittedEq message).mpr emitted, identified⟩
  · intro message emitted token carried predecessor member
    exact completedMono _ (facts.issued message ((emittedEq message).mp emitted) token carried
      predecessor member)
  · rcases effect with ⟨receiptsEq, ledgerEq, _⟩ |
        ⟨id, message, found, networkEq, receiptsEq, applicationEq⟩
    · intro id' member
      rw [receiptsEq] at member
      obtain ⟨accepted, onLedger, identified, valid, event, named, completed, owned⟩ :=
        facts.accepted id' member
      rw [ledgerEq]
      exact ⟨accepted, onLedger, identified, valid, event, named, completedMono event completed,
        owned⟩
    · obtain ⟨addressed, _, ledgerEq⟩ := includePending_found execution.network id message found
      intro id' member
      rw [receiptsEq] at member
      rw [networkEq, ledgerEq]
      rcases List.mem_append.mp member with prior | fresh
      · obtain ⟨accepted, onLedger, identified, valid, event, named, completed, owned⟩ :=
          facts.accepted id' prior
        exact ⟨accepted, List.mem_append_left _ onLedger, identified, valid, event, named,
          completedMono event completed, owned⟩
      · obtain ⟨idEq, isSome⟩ := Prod.mk.inj (List.mem_singleton.mp fresh)
        subst idEq
        obtain ⟨after, handled⟩ := Option.isSome_iff_exists.mp isSome.symm
        obtain ⟨valid, event, named, _, completed, owned⟩ :=
          accepted_inclusion execution.application after message handled
        refine ⟨message, List.mem_append_right _ (List.mem_singleton.mpr rfl), addressed, valid,
          event, named, ?_, owned⟩
        rw [applicationEq, handled]
        exact completed
  · rcases effect with ⟨receiptsEq, ledgerEq, _⟩ |
        ⟨id, message, found, networkEq, receiptsEq, applicationEq⟩
    · rw [receiptsEq, ledgerEq]
      exact facts.single
    · obtain ⟨addressed, pending, ledgerEq⟩ :=
        includePending_found execution.network id message found
      -- Every accepted ledger envelope is an old accepted one or the newly accepted one.
      have classify : ∀ candidate ∈ next.network.ledger,
          (candidate.id, true) ∈ next.receipts →
          (candidate ∈ execution.network.ledger ∧
              (candidate.id, true) ∈ execution.receipts) ∨
            (candidate = message ∧
              (app.handle execution.application message).isSome = true) := by
        intro candidate onLedger accepted
        rw [networkEq, ledgerEq] at onLedger
        rw [receiptsEq] at accepted
        rcases List.mem_append.mp accepted with prior | fresh
        · left
          refine ⟨?_, prior⟩
          rcases List.mem_append.mp onLedger with old | new
          · exact old
          · cases List.mem_singleton.mp new
            obtain ⟨other, otherMember, identified, _⟩ := facts.accepted _ prior
            have same := (facts.unique.ledger other otherMember).pending message pending
              identified.symm
            rw [same]
            exact otherMember
        · obtain ⟨idEq, isSome⟩ := Prod.mk.inj (List.mem_singleton.mp fresh)
          right
          refine ⟨?_, isSome.symm⟩
          rcases List.mem_append.mp onLedger with old | new
          · exact (facts.unique.pending message pending).ledger candidate old
              (idEq.trans addressed.symm)
          · exact List.mem_singleton.mp new
      intro first firstMember second secondMember firstAccepted secondAccepted event
        firstNamed secondNamed
      have readyFresh : ∀ (other : Message Player (WitnessedPacket (serviceGraph setup mode))),
          other ∈ execution.network.ledger → (other.id, true) ∈ execution.receipts →
          other.payload.call.event? (serviceGraph setup mode) = some event →
          (app.handle execution.application message).isSome = true →
          message.payload.call.event? (serviceGraph setup mode) = some event → False := by
        intro other otherMember otherAccepted otherNamed isSome messageNamed
        obtain ⟨after, handled⟩ := Option.isSome_iff_exists.mp isSome
        obtain ⟨_, readyEvent, named, ready, _, _⟩ :=
          accepted_inclusion execution.application after message handled
        rw [messageNamed] at named
        cases Option.some.inj named
        obtain ⟨witness, witnessMember, identified, _, completedEvent, completedNamed,
          completed, _⟩ := facts.accepted other.id otherAccepted
        have same := (facts.unique.ledger witness witnessMember).ledger other otherMember
          identified.symm
        rw [← same, otherNamed] at completedNamed
        cases Option.some.inj completedNamed
        exact ready.1 completed
      rcases classify first firstMember firstAccepted with ⟨firstOld, firstPrior⟩ |
          ⟨firstNew, firstSome⟩ <;>
        rcases classify second secondMember secondAccepted with ⟨secondOld, secondPrior⟩ |
          ⟨secondNew, secondSome⟩
      · exact facts.single first firstOld second secondOld firstPrior secondPrior event
          firstNamed secondNamed
      · subst secondNew
        exact (readyFresh first firstOld firstPrior firstNamed secondSome secondNamed).elim
      · subst firstNew
        exact (readyFresh second secondOld secondPrior secondNamed firstSome firstNamed).elim
      · rw [firstNew, secondNew]
  · intro earlier later earlierEmitted laterEmitted sameSender lower accepted valid event
      named owned
    rcases effect with ⟨receiptsEq, _, _⟩ |
        ⟨id, message, found, networkEq, receiptsEq, applicationEq⟩
    · rw [receiptsEq] at accepted
      exact completedMono event (facts.ordered earlier later ((emittedEq earlier).mp
        earlierEmitted) ((emittedEq later).mp laterEmitted) sameSender lower accepted valid
          event named owned)
    · rw [receiptsEq] at accepted
      rcases List.mem_append.mp accepted with prior | fresh
      · exact completedMono event (facts.ordered earlier later ((emittedEq earlier).mp
          earlierEmitted) ((emittedEq later).mp laterEmitted) sameSender lower prior valid
            event named owned)
      · obtain ⟨identified, isSome⟩ := Prod.mk.inj (List.mem_singleton.mp fresh)
        obtain ⟨after, handled⟩ := Option.isSome_iff_exists.mp isSome.symm
        obtain ⟨_, accepted', _, ready, completed, actor⟩ :=
          accepted_inclusion execution.application after message handled
        obtain ⟨tokenEvent, tokenNamed, tokenEq⟩ :=
          (WitnessedPacket.tokenValid_iff earlier.payload).mp valid
        rw [named] at tokenNamed
        cases Option.some.inj tokenNamed
        have settled := facts.issued earlier ((emittedEq earlier).mp earlierEmitted) ⟨event⟩
          tokenEq
        by_cases done : event ∈ execution.application.config.cut.completed
        · exact completedMono event done
        · have readyEarlier : execution.application.config.cut.Ready event :=
            ⟨done, fun predecessor member => settled predecessor member⟩
          have senders : message.sender = earlier.sender := by
            obtain ⟨messageId, _, _⟩ := includePending_found execution.network id message found
            change message.id.1 = earlier.id.1
            rw [messageId, ← identified]
            exact sameSender.symm
          cases (serviceGraph_revealRelaxedOrdered setup mode).ready_actor_unique
            execution.application.config.cut readyEarlier ready owned (actor.trans
              (congrArg some senders))
          rw [applicationEq, handled]
          exact completed

theorem settledFacts_serviceInvariant
    (scheduler : (serviceApplication setup mode duration leaks).Scheduler) :
    (serviceApplication setup mode duration leaks).ServiceInvariant scheduler
    (SettledFacts setup leaks) where
  respond execution who action facts := settledFacts_respond execution facts who action
  environment execution next command facts _ reached :=
    settledFacts_environment execution next command facts reached

/-- The settled facts hold at every legal history, for every scheduler and
arbitrary responses. -/
theorem settledFacts_history (initial : PMF (serviceApplication setup mode duration leaks).State)
    (horizon : Nat) (scheduler : (serviceApplication setup mode duration leaks).Scheduler)
    {control : (serviceApplication setup mode duration leaks).Control}
    (trace :
        ((serviceApplication setup mode duration leaks).protocol initial horizon scheduler).Trace
        (some control)) : SettledFacts setup leaks control.execution :=
    (settledFacts_serviceInvariant scheduler).history initial horizon
    (fun state _ => settledFacts_initial state) trace

end Facts



end Vegas
