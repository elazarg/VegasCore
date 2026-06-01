import Vegas.Machine.Refinement

/-!
# Message-in-flight machine wrapper

`Machine.messageInFlight` adds an implementation-level message buffer to an
existing machine. Sends enqueue public messages, delivery moves one pending
message to the delivered log, and both pending and delivered messages are
visible in public and player observations. Wrapped source events may run while
messages are pending only when every supported source successor is nonterminal;
terminal-producing source events must wait until the pending queue has drained.
The refinement back to the source machine erases send/deliver events and
forgets the message buffers.
-/

namespace Vegas

namespace Machine

variable {Player : Type}

/-- State for a message-in-flight wrapper. -/
structure MessageInFlightState
    (M : Machine Player) (Message : Player → Type) where
  source : M.State
  pending : List (Sigma Message)
  delivered : List (Sigma Message)

/-- Player actions in a message-in-flight wrapper: send a message or execute an
underlying source-machine action. -/
inductive MessageInFlightAction
    (M : Machine Player) (Message : Player → Type) (player : Player) where
  | send (message : Message player)
  | spec (action : M.Action player)

/-- Internal events in a message-in-flight wrapper: deliver a pending message
or execute an underlying source-machine internal event. -/
inductive MessageInFlightInternal
    (M : Machine Player) (Message : Player → Type) where
  | deliver
  | spec (event : M.Internal)

/-- Add public pending/delivered message buffers to a machine. -/
noncomputable def messageInFlight
    (M : Machine Player) (Message : Player → Type) : Machine Player where
  State := MessageInFlightState M Message
  Action := MessageInFlightAction M Message
  Internal := MessageInFlightInternal M Message
  Public := M.Public × List (Sigma Message) × List (Sigma Message)
  Obs := fun player => M.Obs player × List (Sigma Message) ×
    List (Sigma Message)
  Outcome := M.Outcome
  init :=
    { source := M.init, pending := [], delivered := [] }
  available := fun state player action =>
    match action with
    | .send _ => ¬ M.terminal state.source
    | .spec sourceAction =>
        sourceAction ∈ M.available state.source player ∧
          (state.pending = [] ∨
            ∀ target,
              target ∈ (M.stepPlay player sourceAction state.source).support →
                ¬ M.terminal target)
  availableInternal := fun state event =>
    match event with
    | .deliver => state.pending ≠ [] ∧ ¬ M.terminal state.source
    | .spec sourceEvent =>
        sourceEvent ∈ M.availableInternal state.source ∧
          (state.pending = [] ∨
            ∀ target,
              target ∈ (M.stepInternal sourceEvent state.source).support →
                ¬ M.terminal target)
  stepPlay := fun player action state =>
    match action with
    | .send message =>
        PMF.pure
          { source := state.source,
            pending := state.pending ++ [⟨player, message⟩],
            delivered := state.delivered }
    | .spec sourceAction =>
        PMF.map
          (fun dst =>
            { source := dst,
              pending := state.pending,
              delivered := state.delivered })
          (M.stepPlay player sourceAction state.source)
  stepInternal := fun event state =>
    match event with
    | .deliver =>
        match state.pending with
        | [] => PMF.pure state
        | message :: rest =>
            PMF.pure
              { source := state.source,
                pending := rest,
                delivered := state.delivered ++ [message] }
    | .spec sourceEvent =>
        PMF.map
          (fun dst =>
            { source := dst,
              pending := state.pending,
              delivered := state.delivered })
          (M.stepInternal sourceEvent state.source)
  terminal := fun state => M.terminal state.source
  publicView := fun state =>
    (M.publicView state.source, state.pending, state.delivered)
  observe := fun player state =>
    (M.observe player state.source, state.pending, state.delivered)
  outcome := fun state => M.outcome state.source
  utility := M.utility

namespace messageInFlight

variable (M : Machine Player) (Message : Player → Type)

@[simp] theorem init_source :
    (messageInFlight M Message).init.source = M.init := rfl

@[simp] theorem init_pending :
    (messageInFlight M Message).init.pending = [] := rfl

@[simp] theorem init_delivered :
    (messageInFlight M Message).init.delivered = [] := rfl

@[simp] theorem terminal_iff (state : (messageInFlight M Message).State) :
    (messageInFlight M Message).terminal state ↔
      M.terminal state.source := by
  change M.terminal state.source ↔ M.terminal state.source
  rfl

/-- Lift an underlying source event to the message-in-flight machine. -/
def liftEvent : M.Event → (messageInFlight M Message).Event
  | .play player action => .play player (.spec action)
  | .internal event => .internal (.spec event)

/-- Project message-in-flight events, erasing sends and deliveries. -/
def projectEvent? :
    (messageInFlight M Message).Event → Option M.Event
  | .play _ (.send _) => none
  | .play player (.spec action) => some (.play player action)
  | .internal .deliver => none
  | .internal (.spec event) => some (.internal event)

/-- Project a message-in-flight batch by erasing sends and deliveries. -/
def projectEventBatch
    (batch : List (messageInFlight M Message).Event) : List M.Event :=
  batch.filterMap (projectEvent? M Message)

@[simp] theorem projectEvent?_liftEvent (event : M.Event) :
    projectEvent? M Message (liftEvent M Message event) = some event := by
  cases event <;> rfl

@[simp] theorem projectEventBatch_map_liftEvent (batch : List M.Event) :
    projectEventBatch M Message (batch.map (liftEvent M Message)) =
      batch := by
  rw [projectEventBatch, List.filterMap_map]
  simp

/-- Event batch that drains the current pending queue. -/
def deliverAllEvents
    (pending : List (Sigma Message)) :
    List (messageInFlight M Message).Event :=
  pending.map fun _ => .internal .deliver

/-- Drain the pending queue, then run a suffix batch. This is definitionally
convenient for concrete trace computations. -/
def deliverAllThenEvents
    (pending : List (Sigma Message))
    (suffix : List (messageInFlight M Message).Event) :
    List (messageInFlight M Message).Event :=
  match pending with
  | [] => suffix
  | _ :: rest => .internal .deliver :: deliverAllThenEvents rest suffix

@[simp] theorem deliverAllEvents_nil :
    deliverAllEvents M Message [] = [] := rfl

@[simp] theorem deliverAllEvents_cons
    (message : Sigma Message) (rest : List (Sigma Message)) :
    deliverAllEvents M Message (message :: rest) =
      .internal .deliver :: deliverAllEvents M Message rest := rfl

@[simp] theorem deliverAllThenEvents_nil
    (suffix : List (messageInFlight M Message).Event) :
    deliverAllThenEvents M Message [] suffix = suffix := rfl

@[simp] theorem deliverAllThenEvents_cons
    (message : Sigma Message) (rest : List (Sigma Message))
    (suffix : List (messageInFlight M Message).Event) :
    deliverAllThenEvents M Message (message :: rest) suffix =
      .internal .deliver :: deliverAllThenEvents M Message rest suffix := rfl

theorem deliverAllThenEvents_eq
    (pending : List (Sigma Message))
    (suffix : List (messageInFlight M Message).Event) :
    deliverAllThenEvents M Message pending suffix =
      deliverAllEvents M Message pending ++ suffix := by
  induction pending with
  | nil => rfl
  | cons message rest ih =>
      simp [deliverAllThenEvents, deliverAllEvents, ih]

@[simp] theorem projectEventBatch_deliverAllEvents
    (pending : List (Sigma Message)) :
    projectEventBatch M Message (deliverAllEvents M Message pending) = [] := by
  induction pending with
  | nil => rfl
  | cons message rest ih =>
      simp [deliverAllEvents, projectEventBatch, projectEvent?]

@[simp] theorem projectEventBatch_deliverAllThenEvents
    (pending : List (Sigma Message))
    (suffix : List (messageInFlight M Message).Event) :
    projectEventBatch M Message
        (deliverAllThenEvents M Message pending suffix) =
      projectEventBatch M Message suffix := by
  induction pending with
  | nil => rfl
  | cons message rest ih =>
      change
        List.filterMap (projectEvent? M Message)
            (deliverAllThenEvents M Message rest suffix) =
          List.filterMap (projectEvent? M Message) suffix
      simpa [projectEventBatch] using ih

/-- Sending one message is a semantically available implementation step while
the source machine is nonterminal. -/
theorem sendAvailableStep
    (state : (messageInFlight M Message).State)
    (player : Player) (message : Message player)
    (hnonterminal : ¬ M.terminal state.source) :
    (messageInFlight M Message).AvailableStep state
      (.play player (.send message))
      { source := state.source,
        pending := state.pending ++ [⟨player, message⟩],
        delivered := state.delivered } := by
  constructor
  · exact hnonterminal
  · change
      ({ source := state.source,
         pending := state.pending ++ [⟨player, message⟩],
         delivered := state.delivered } :
        (messageInFlight M Message).State) ∈
        (PMF.pure
          ({ source := state.source,
             pending := state.pending ++ [⟨player, message⟩],
             delivered := state.delivered } :
            (messageInFlight M Message).State)).support
    rw [PMF.support_pure]
    exact Set.mem_singleton _

/-- Sending one message as a singleton available run. -/
theorem sendAvailableRunFrom
    (state : (messageInFlight M Message).State)
    (player : Player) (message : Message player)
    (hnonterminal : ¬ M.terminal state.source) :
    (messageInFlight M Message).AvailableRunFrom state
      [.play player (.send message)]
      { source := state.source,
        pending := state.pending ++ [⟨player, message⟩],
        delivered := state.delivered } :=
  (sendAvailableStep M Message state player message hnonterminal)
    |>.availableRunFrom_singleton

/-- Delivering the head pending message is a semantically available
implementation step while the source machine is nonterminal. -/
theorem deliverAvailableStep
    (source : M.State) (message : Sigma Message)
    (rest delivered : List (Sigma Message))
    (hnonterminal : ¬ M.terminal source) :
    (messageInFlight M Message).AvailableStep
      { source := source,
        pending := message :: rest,
        delivered := delivered }
      (.internal .deliver)
      { source := source,
        pending := rest,
        delivered := delivered ++ [message] } := by
  constructor
  · constructor
    · intro hnil
      cases hnil
    · exact hnonterminal
  · change
      ({ source := source,
         pending := rest,
         delivered := delivered ++ [message] } :
        (messageInFlight M Message).State) ∈
        (PMF.pure
          ({ source := source,
             pending := rest,
             delivered := delivered ++ [message] } :
            (messageInFlight M Message).State)).support
    rw [PMF.support_pure]
    exact Set.mem_singleton _

/-- Delivering the head pending message as a singleton available run. -/
theorem deliverAvailableRunFrom
    (source : M.State) (message : Sigma Message)
    (rest delivered : List (Sigma Message))
    (hnonterminal : ¬ M.terminal source) :
    (messageInFlight M Message).AvailableRunFrom
      { source := source,
        pending := message :: rest,
        delivered := delivered }
      [.internal .deliver]
      { source := source,
        pending := rest,
        delivered := delivered ++ [message] } :=
  (deliverAvailableStep M Message source message rest delivered hnonterminal)
    |>.availableRunFrom_singleton

/-- Lifting one available source step preserves the message buffers. -/
theorem liftAvailableStep
    {source target : M.State} {event : M.Event}
    (pending delivered : List (Sigma Message))
    (hqueue :
      pending = [] ∨
        ∀ target, target ∈ (M.step event source).support →
          ¬ M.terminal target)
    (hstep : M.AvailableStep source event target) :
    (messageInFlight M Message).AvailableStep
      { source := source,
        pending := pending,
        delivered := delivered }
      (liftEvent M Message event)
      { source := target,
        pending := pending,
        delivered := delivered } := by
  constructor
  · cases event with
    | play player action =>
        change action ∈ M.available source player ∧
          (pending = [] ∨
            ∀ target,
              target ∈ (M.stepPlay player action source).support →
                ¬ M.terminal target)
        exact ⟨hstep.available, by
          simpa [Machine.step_play] using hqueue⟩
    | internal event =>
        change event ∈ M.availableInternal source ∧
          (pending = [] ∨
            ∀ target,
              target ∈ (M.stepInternal event source).support →
                ¬ M.terminal target)
        exact ⟨hstep.available, by
          simpa [Machine.step_internal] using hqueue⟩
  · cases event with
    | play player action =>
        change
          ({ source := target,
             pending := pending,
             delivered := delivered } :
            (messageInFlight M Message).State) ∈
            (PMF.map
              (fun dst =>
                ({ source := dst,
                   pending := pending,
                   delivered := delivered } :
                  (messageInFlight M Message).State))
              (M.stepPlay player action source)).support
        exact (PMF.mem_support_map_iff _ _ _).mpr
          ⟨target, hstep.support, rfl⟩
    | internal event =>
        change
          ({ source := target,
             pending := pending,
             delivered := delivered } :
            (messageInFlight M Message).State) ∈
            (PMF.map
              (fun dst =>
                ({ source := dst,
                   pending := pending,
                   delivered := delivered } :
                  (messageInFlight M Message).State))
              (M.stepInternal event source)).support
        exact (PMF.mem_support_map_iff _ _ _).mpr
          ⟨target, hstep.support, rfl⟩

/-- Lifting an available source run from an empty pending queue preserves the
delivered log and keeps the queue empty. -/
theorem liftAvailableRunFrom
    {source target : M.State} {events : List M.Event}
    (delivered : List (Sigma Message))
    (hrun : M.AvailableRunFrom source events target) :
    (messageInFlight M Message).AvailableRunFrom
      { source := source,
        pending := [],
        delivered := delivered }
      (events.map (liftEvent M Message))
      { source := target,
        pending := [],
        delivered := delivered } := by
  induction hrun with
  | nil state =>
      exact Machine.AvailableRunFrom.nil _
  | cons havailable hsupport _ ih =>
      exact Machine.AvailableRunFrom.cons
        (Machine.AvailableStep.available
          (liftAvailableStep M Message [] delivered
            (Or.inl rfl)
            ⟨havailable, hsupport⟩))
        (Machine.AvailableStep.support
          (liftAvailableStep M Message [] delivered
            (Or.inl rfl)
            ⟨havailable, hsupport⟩))
        ih

/-- Running lifted source events from an empty message queue maps exactly over
the source-machine event run and preserves the delivered log. -/
theorem runEventsFrom_liftEvent
    (events : List M.Event) (source : M.State)
    (delivered : List (Sigma Message)) :
    (messageInFlight M Message).runEventsFrom
        (events.map (liftEvent M Message))
        { source := source, pending := [], delivered := delivered } =
      PMF.map
        (fun dst =>
          ({ source := dst,
             pending := [],
             delivered := delivered } :
            (messageInFlight M Message).State))
        (M.runEventsFrom events source) := by
  induction events generalizing source with
  | nil =>
      change PMF.pure
          ({ source := source, pending := [], delivered := delivered } :
            (messageInFlight M Message).State) =
        PMF.map
          (fun dst =>
            ({ source := dst, pending := [], delivered := delivered } :
              (messageInFlight M Message).State))
          (PMF.pure source)
      rw [PMF.pure_map]
  | cons event events ih =>
      simp only [List.map_cons]
      rw [Machine.runEventsFrom_cons_bind]
      rw [Machine.runEventsFrom_cons_bind]
      cases event with
      | play player action =>
          change
            (PMF.map
                (fun dst =>
                  ({ source := dst,
                     pending := [],
                     delivered := delivered } :
                    (messageInFlight M Message).State))
                (M.stepPlay player action source)).bind
                (fun current =>
                  (messageInFlight M Message).runEventsFrom
                    (events.map (liftEvent M Message)) current) =
              PMF.map
                (fun dst =>
                  ({ source := dst,
                     pending := [],
                     delivered := delivered } :
                    (messageInFlight M Message).State))
                ((M.stepPlay player action source).bind
                  fun current => M.runEventsFrom events current)
          rw [PMF.bind_map]
          rw [PMF.map_bind]
          congr
          funext current
          exact ih current
      | internal event =>
          change
            (PMF.map
                (fun dst =>
                  ({ source := dst,
                     pending := [],
                     delivered := delivered } :
                    (messageInFlight M Message).State))
                (M.stepInternal event source)).bind
                (fun current =>
                  (messageInFlight M Message).runEventsFrom
                    (events.map (liftEvent M Message)) current) =
              PMF.map
                (fun dst =>
                  ({ source := dst,
                     pending := [],
                     delivered := delivered } :
                    (messageInFlight M Message).State))
                ((M.stepInternal event source).bind
                  fun current => M.runEventsFrom events current)
          rw [PMF.bind_map]
          rw [PMF.map_bind]
          congr
          funext current
          exact ih current

/-- Lifting a support-wide available source batch from an empty message queue
gives a support-wide available message-in-flight batch. -/
theorem liftAvailableBatchFrom
    {source : M.State} {events : List M.Event}
    (delivered : List (Sigma Message))
    (hbatch : M.AvailableBatchFrom source events) :
    (messageInFlight M Message).AvailableBatchFrom
      { source := source,
        pending := [],
        delivered := delivered }
      (events.map (liftEvent M Message)) := by
  induction events generalizing source with
  | nil =>
      exact Machine.AvailableBatchFrom.nil _
  | cons event events ih =>
      refine Machine.AvailableBatchFrom.cons ?_ ?_
      · cases event with
        | play player action =>
            change action ∈ M.available source player ∧
              (([] : List (Sigma Message)) = [] ∨
                ∀ target,
                  target ∈ (M.stepPlay player action source).support →
                    ¬ M.terminal target)
            exact ⟨hbatch.1, Or.inl rfl⟩
        | internal event =>
            change event ∈ M.availableInternal source ∧
              (([] : List (Sigma Message)) = [] ∨
                ∀ target,
                  target ∈ (M.stepInternal event source).support →
                    ¬ M.terminal target)
            exact ⟨hbatch.1, Or.inl rfl⟩
      · intro mid hmid
        cases event with
        | play player action =>
            rcases (PMF.mem_support_map_iff _ _ _).mp hmid with
              ⟨sourceMid, hsourceMid, hmidEq⟩
            subst hmidEq
            exact ih (hbatch.2 sourceMid hsourceMid)
        | internal event =>
            rcases (PMF.mem_support_map_iff _ _ _).mp hmid with
              ⟨sourceMid, hsourceMid, hmidEq⟩
            subst hmidEq
            exact ih (hbatch.2 sourceMid hsourceMid)

/-- Draining every pending message is available while the source machine is
nonterminal. -/
theorem deliverAllAvailableRunFrom
    (source : M.State) (pending delivered : List (Sigma Message))
    (hnonterminal : ¬ M.terminal source) :
    (messageInFlight M Message).AvailableRunFrom
      { source := source,
        pending := pending,
        delivered := delivered }
      (deliverAllEvents M Message pending)
      { source := source,
        pending := [],
        delivered := delivered ++ pending } := by
  induction pending generalizing delivered with
  | nil =>
      simpa using
        (Machine.AvailableRunFrom.nil (M := messageInFlight M Message)
          ({ source := source,
             pending := [],
             delivered := delivered } :
            (messageInFlight M Message).State))
  | cons message rest ih =>
      let src : (messageInFlight M Message).State :=
        { source := source,
          pending := message :: rest,
          delivered := delivered }
      let afterDeliver : (messageInFlight M Message).State :=
        { source := source,
          pending := rest,
          delivered := delivered ++ [message] }
      change
        (messageInFlight M Message).AvailableRunFrom src
          (.internal .deliver :: deliverAllEvents M Message rest)
          { source := source,
            pending := [],
            delivered := delivered ++ (message :: rest) }
      refine Machine.AvailableRunFrom.cons (mid := afterDeliver) ?_ ?_ ?_
      · change src.pending ≠ [] ∧ ¬ M.terminal src.source
        constructor
        · intro hnil
          cases hnil
        · exact hnonterminal
      · change afterDeliver ∈ (PMF.pure afterDeliver).support
        rw [PMF.support_pure]
        exact Set.mem_singleton _
      · simpa [afterDeliver, List.append_assoc] using
          ih (delivered ++ [message])

/-- Drain pending messages, then run a lifted source event list from the empty
queue. -/
theorem deliverAllThenLiftAvailableRunFrom
    {source target : M.State} {events : List M.Event}
    (pending delivered : List (Sigma Message))
    (hnonterminal : ¬ M.terminal source)
    (hrun : M.AvailableRunFrom source events target) :
    (messageInFlight M Message).AvailableRunFrom
      { source := source,
        pending := pending,
        delivered := delivered }
      (deliverAllThenEvents M Message pending
        (events.map (liftEvent M Message)))
      { source := target,
        pending := [],
        delivered := delivered ++ pending } := by
  simpa [deliverAllThenEvents_eq] using
    (deliverAllAvailableRunFrom M Message source pending delivered
        hnonterminal).append
      (liftAvailableRunFrom M Message (delivered ++ pending) hrun)

/-- Drain pending messages, then run a lifted support-wide source event batch
from the empty queue. -/
theorem deliverAllThenLiftAvailableBatchFrom
    {source : M.State} {events : List M.Event}
    (pending delivered : List (Sigma Message))
    (hnonterminal : ¬ M.terminal source)
    (hbatch : M.AvailableBatchFrom source events) :
    (messageInFlight M Message).AvailableBatchFrom
      { source := source,
        pending := pending,
        delivered := delivered }
      (deliverAllThenEvents M Message pending
        (events.map (liftEvent M Message))) := by
  induction pending generalizing delivered with
  | nil =>
      exact liftAvailableBatchFrom M Message delivered hbatch
  | cons message rest ih =>
      let src : (messageInFlight M Message).State :=
        { source := source,
          pending := message :: rest,
          delivered := delivered }
      let afterDeliver : (messageInFlight M Message).State :=
        { source := source,
          pending := rest,
          delivered := delivered ++ [message] }
      change
        (messageInFlight M Message).AvailableBatchFrom src
          (.internal .deliver ::
            deliverAllThenEvents M Message rest
              (events.map (liftEvent M Message)))
      refine Machine.AvailableBatchFrom.cons ?_ ?_
      · change src.pending ≠ [] ∧ ¬ M.terminal src.source
        constructor
        · intro hnil
          cases hnil
        · exact hnonterminal
      · intro mid hmid
        change mid ∈ (PMF.pure afterDeliver).support at hmid
        rw [PMF.support_pure] at hmid
        subst mid
        simpa [afterDeliver, List.append_assoc] using
          ih (delivered ++ [message])

/-- Sending a message from an empty buffer and immediately delivering it is
available while the source machine is nonterminal. -/
theorem sendDeliverAvailableRunFrom
    (source : M.State) (delivered : List (Sigma Message))
    (player : Player) (message : Message player)
    (hnonterminal : ¬ M.terminal source) :
    (messageInFlight M Message).AvailableRunFrom
      { source := source,
        pending := [],
        delivered := delivered }
      [.play player (.send message), .internal .deliver]
      { source := source,
        pending := [],
        delivered := delivered ++ [⟨player, message⟩] } := by
  let sent : Sigma Message := ⟨player, message⟩
  change
    (messageInFlight M Message).AvailableRunFrom
      { source := source,
        pending := [],
        delivered := delivered }
      ([.play player (.send message)] ++ [.internal .deliver])
      { source := source,
        pending := [],
        delivered := delivered ++ [sent] }
  exact
    (sendAvailableRunFrom M Message
      { source := source, pending := [], delivered := delivered }
      player message hnonterminal).append
      (deliverAvailableRunFrom M Message source sent [] delivered
        hnonterminal)

/-- Send, deliver, then execute a lifted support-wide source batch from an
empty message queue. -/
theorem sendDeliverThenLiftAvailableBatchFrom
    {source : M.State} {events : List M.Event}
    (delivered : List (Sigma Message))
    (player : Player) (message : Message player)
    (hnonterminal : ¬ M.terminal source)
    (hbatch : M.AvailableBatchFrom source events) :
    (messageInFlight M Message).AvailableBatchFrom
      { source := source,
        pending := [],
        delivered := delivered }
      (.play player (.send message) :: .internal .deliver ::
        events.map (liftEvent M Message)) := by
  let sent : Sigma Message := ⟨player, message⟩
  let afterSend : (messageInFlight M Message).State :=
    { source := source,
      pending := [sent],
      delivered := delivered }
  let afterDeliver : (messageInFlight M Message).State :=
    { source := source,
      pending := [],
      delivered := delivered ++ [sent] }
  refine Machine.AvailableBatchFrom.cons ?_ ?_
  · change ¬ M.terminal source
    exact hnonterminal
  · intro mid hmid
    change mid ∈ (PMF.pure afterSend).support at hmid
    rw [PMF.support_pure] at hmid
    subst mid
    refine Machine.AvailableBatchFrom.cons ?_ ?_
    · change [sent] ≠ [] ∧ ¬ M.terminal source
      constructor
      · intro hnil
        cases hnil
      · exact hnonterminal
    · intro mid hmid
      change mid ∈ (PMF.pure afterDeliver).support at hmid
      rw [PMF.support_pure] at hmid
      subst mid
      exact liftAvailableBatchFrom M Message (delivered ++ [sent])
        hbatch

/-- Drain pending messages, then send/deliver one message and execute a lifted
support-wide source batch. -/
theorem deliverAllThenSendDeliverLiftAvailableBatchFrom
    {source : M.State} {events : List M.Event}
    (pending delivered : List (Sigma Message))
    (player : Player) (message : Message player)
    (hnonterminal : ¬ M.terminal source)
    (hbatch : M.AvailableBatchFrom source events) :
    (messageInFlight M Message).AvailableBatchFrom
      { source := source,
        pending := pending,
        delivered := delivered }
      (deliverAllThenEvents M Message pending
        (.play player (.send message) :: .internal .deliver ::
          events.map (liftEvent M Message))) := by
  induction pending generalizing delivered with
  | nil =>
      exact sendDeliverThenLiftAvailableBatchFrom M Message delivered
        player message hnonterminal hbatch
  | cons pendingMessage rest ih =>
      let src : (messageInFlight M Message).State :=
        { source := source,
          pending := pendingMessage :: rest,
          delivered := delivered }
      let afterDeliver : (messageInFlight M Message).State :=
        { source := source,
          pending := rest,
          delivered := delivered ++ [pendingMessage] }
      change
        (messageInFlight M Message).AvailableBatchFrom src
          (.internal .deliver ::
            deliverAllThenEvents M Message rest
              (.play player (.send message) :: .internal .deliver ::
                events.map (liftEvent M Message)))
      refine Machine.AvailableBatchFrom.cons ?_ ?_
      · change src.pending ≠ [] ∧ ¬ M.terminal src.source
        constructor
        · intro hnil
          cases hnil
        · exact hnonterminal
      · intro mid hmid
        change mid ∈ (PMF.pure afterDeliver).support at hmid
        rw [PMF.support_pure] at hmid
        subst mid
        simpa [afterDeliver, List.append_assoc] using
          ih (delivered ++ [pendingMessage])

/-- One available message-in-flight step cannot produce a terminal state with
messages still pending. -/
theorem availableStep_pending_nil_or_nonterminal
    {state target : (messageInFlight M Message).State}
    {event : (messageInFlight M Message).Event}
    (hstep : (messageInFlight M Message).AvailableStep state event target) :
    target.pending = [] ∨ ¬ (messageInFlight M Message).terminal target := by
  rcases hstep with ⟨havailable, hsupport⟩
  cases event with
  | play player action =>
      cases action with
      | send message =>
          right
          change ¬ M.terminal target.source
          have htarget :
              target =
                { source := state.source,
                  pending := state.pending ++ [⟨player, message⟩],
                  delivered := state.delivered } := by
            change target ∈
              (PMF.pure
                ({ source := state.source,
                   pending := state.pending ++ [⟨player, message⟩],
                   delivered := state.delivered } :
                  (messageInFlight M Message).State)).support at hsupport
            rw [PMF.support_pure] at hsupport
            exact hsupport
          subst target
          exact havailable
      | spec action =>
          change action ∈ M.available state.source player ∧
            (state.pending = [] ∨
              ∀ target,
                target ∈ (M.stepPlay player action state.source).support →
                  ¬ M.terminal target) at havailable
          rcases
              (PMF.mem_support_map_iff _ _ _).mp hsupport with
            ⟨sourceTarget, hsourceSupport, htarget⟩
          subst target
          cases havailable.2 with
          | inl hpending =>
              left
              exact hpending
          | inr hnonterminal =>
              right
              change ¬ M.terminal sourceTarget
              exact hnonterminal sourceTarget hsourceSupport
  | internal event =>
      cases event with
      | deliver =>
          right
          change ¬ M.terminal target.source
          cases hpending : state.pending with
          | nil =>
              exact False.elim (havailable.1 hpending)
          | cons message rest =>
            have htarget :
                target =
                  { source := state.source,
                    pending := rest,
                    delivered := state.delivered ++ [message] } := by
              simpa [Machine.step_internal, messageInFlight, hpending] using
                hsupport
            subst target
            exact havailable.2
      | spec event =>
          change event ∈ M.availableInternal state.source ∧
            (state.pending = [] ∨
              ∀ target,
                target ∈ (M.stepInternal event state.source).support →
                  ¬ M.terminal target) at havailable
          rcases
              (PMF.mem_support_map_iff _ _ _).mp hsupport with
            ⟨sourceTarget, hsourceSupport, htarget⟩
          subst target
          cases havailable.2 with
          | inl hpending =>
              left
              exact hpending
          | inr hnonterminal =>
              right
              change ¬ M.terminal sourceTarget
              exact hnonterminal sourceTarget hsourceSupport

/-- Runs of the message-in-flight wrapper preserve the invariant that either
no messages are pending or the wrapped source state is nonterminal. -/
theorem availableRunFrom_pending_nil_or_nonterminal
    {source target : (messageInFlight M Message).State}
    {events : List (messageInFlight M Message).Event}
    (hrun : (messageInFlight M Message).AvailableRunFrom source events target)
    (hsource :
      source.pending = [] ∨ ¬ (messageInFlight M Message).terminal source) :
    target.pending = [] ∨ ¬ (messageInFlight M Message).terminal target := by
  induction hrun with
  | nil state =>
      exact hsource
  | cons havailable hsupport _ ih =>
      exact ih
        (availableStep_pending_nil_or_nonterminal M Message
          ⟨havailable, hsupport⟩)

/-- Any terminal state reachable from the wrapper initial state has drained
all pending messages. -/
theorem initAvailableRunFrom_terminal_pending_nil
    {target : (messageInFlight M Message).State}
    {events : List (messageInFlight M Message).Event}
    (hrun :
      (messageInFlight M Message).AvailableRunFrom
        (messageInFlight M Message).init events target)
    (hterminal : (messageInFlight M Message).terminal target) :
    target.pending = [] := by
  have hinvariant :
      target.pending = [] ∨
        ¬ (messageInFlight M Message).terminal target :=
    availableRunFrom_pending_nil_or_nonterminal M Message hrun
      (Or.inl rfl)
  cases hinvariant with
  | inl hpending =>
      exact hpending
  | inr hnonterminal =>
      exact False.elim (hnonterminal hterminal)

section MapRefinement

variable {Impl Spec : Machine Player}

/-- Lift a source-machine state projection through the message-in-flight
wrapper, preserving the runtime message buffers. -/
def mapProjectState
    (R : StochasticRefinement Impl Spec) :
    (messageInFlight Impl Message).State →
      (messageInFlight Spec Message).State :=
  fun state =>
    { source := R.projectState state.source,
      pending := state.pending,
      delivered := state.delivered }

/-- Lift a source-machine event projection through the message-in-flight
wrapper. Protocol send/deliver events survive; wrapped source events are
projected by the underlying refinement. -/
def mapProjectEvent?
    (R : StochasticRefinement Impl Spec) :
    (messageInFlight Impl Message).Event →
      Option (messageInFlight Spec Message).Event
  | .play player (.send message) =>
      some (.play player (.send message))
  | .play player (.spec action) =>
      (R.projectEvent? (.play player action)).map
        (liftEvent Spec Message)
  | .internal .deliver =>
      some (.internal .deliver)
  | .internal (.spec event) =>
      (R.projectEvent? (.internal event)).map
        (liftEvent Spec Message)

/-- Batch projection for a lifted source-machine refinement. -/
def mapProjectEventBatch
    (R : StochasticRefinement Impl Spec)
    (batch : List (messageInFlight Impl Message).Event) :
    List (messageInFlight Spec Message).Event :=
  batch.filterMap (mapProjectEvent? Message R)

@[simp] theorem mapProjectEventBatch_nil
    (R : StochasticRefinement Impl Spec) :
    mapProjectEventBatch Message R [] = [] := rfl

theorem mapRefinement_step_project
    (R : StochasticRefinement Impl Spec)
    (event : (messageInFlight Impl Message).Event)
    (state : (messageInFlight Impl Message).State) :
    PMF.map (mapProjectState Message R)
        ((messageInFlight Impl Message).step event state) =
      match mapProjectEvent? Message R event with
      | some specEvent =>
          (messageInFlight Spec Message).step specEvent
            (mapProjectState Message R state)
      | none =>
          PMF.pure (mapProjectState Message R state) := by
  rcases state with ⟨source, pending, delivered⟩
  cases event with
  | play player action =>
      cases action with
      | send message =>
          change
            PMF.map (mapProjectState Message R)
                (PMF.pure
                  ({ source := source,
                     pending := pending ++ [⟨player, message⟩],
                     delivered := delivered } :
                    (messageInFlight Impl Message).State)) =
              PMF.pure
                ({ source := R.projectState source,
                   pending := pending ++ [⟨player, message⟩],
                   delivered := delivered } :
                  (messageInFlight Spec Message).State)
          rw [PMF.pure_map]
          rfl
      | spec action =>
          simp only [Machine.step_play, messageInFlight, mapProjectEvent?]
          let restoreSpec (sourceValue : Spec.State) :
              (messageInFlight Spec Message).State :=
            { source := sourceValue,
              pending := pending,
              delivered := delivered }
          have hstep := R.step_project (.play player action) source
          simp only [Machine.step_play] at hstep
          rw [PMF.map_comp]
          change
            PMF.map (restoreSpec ∘ R.projectState)
                (Impl.stepPlay player action source) =
              match Option.map (liftEvent Spec Message)
                  (R.projectEvent? (.play player action)) with
              | some specEvent =>
                  (messageInFlight Spec Message).step
                    specEvent
                    (restoreSpec (R.projectState source))
              | none => PMF.pure (restoreSpec (R.projectState source))
          rw [← PMF.map_comp]
          rw [hstep]
          cases hproject : R.projectEvent? (.play player action) with
          | none =>
              rw [PMF.pure_map]
              rfl
          | some specEvent =>
              cases specEvent with
              | play specPlayer specAction =>
                  change
                    PMF.map restoreSpec
                        (Spec.stepPlay specPlayer specAction
                          (R.projectState source)) =
                      PMF.map restoreSpec
                        (Spec.stepPlay specPlayer specAction
                          (R.projectState source))
                  rfl
              | internal specEvent =>
                  change
                    PMF.map restoreSpec
                        (Spec.stepInternal specEvent
                          (R.projectState source)) =
                      PMF.map restoreSpec
                        (Spec.stepInternal specEvent
                          (R.projectState source))
                  rfl
  | internal event =>
      cases event with
      | deliver =>
          cases pending with
          | nil =>
              change
                PMF.map (mapProjectState Message R)
                    (PMF.pure
                      ({ source := source,
                         pending := [],
                         delivered := delivered } :
                        (messageInFlight Impl Message).State)) =
                  PMF.pure
                    ({ source := R.projectState source,
                       pending := [],
                       delivered := delivered } :
                      (messageInFlight Spec Message).State)
              rw [PMF.pure_map]
              rfl
          | cons message rest =>
              change
                PMF.map (mapProjectState Message R)
                    (PMF.pure
                      ({ source := source,
                         pending := rest,
                         delivered := delivered ++ [message] } :
                        (messageInFlight Impl Message).State)) =
                  PMF.pure
                    ({ source := R.projectState source,
                       pending := rest,
                       delivered := delivered ++ [message] } :
                      (messageInFlight Spec Message).State)
              rw [PMF.pure_map]
              rfl
      | spec event =>
          simp only [Machine.step_internal, messageInFlight, mapProjectEvent?]
          let restoreSpec (sourceValue : Spec.State) :
              (messageInFlight Spec Message).State :=
            { source := sourceValue,
              pending := pending,
              delivered := delivered }
          have hstep := R.step_project (.internal event) source
          simp only [Machine.step_internal] at hstep
          rw [PMF.map_comp]
          change
            PMF.map (restoreSpec ∘ R.projectState)
                (Impl.stepInternal event source) =
              match Option.map (liftEvent Spec Message)
                  (R.projectEvent? (.internal event)) with
              | some specEvent =>
                  (messageInFlight Spec Message).step
                    specEvent
                    (restoreSpec (R.projectState source))
              | none => PMF.pure (restoreSpec (R.projectState source))
          rw [← PMF.map_comp]
          rw [hstep]
          cases hproject : R.projectEvent? (.internal event) with
          | none =>
              rw [PMF.pure_map]
              rfl
          | some specEvent =>
              cases specEvent with
              | play specPlayer specAction =>
                  change
                    PMF.map restoreSpec
                        (Spec.stepPlay specPlayer specAction
                          (R.projectState source)) =
                      PMF.map restoreSpec
                        (Spec.stepPlay specPlayer specAction
                          (R.projectState source))
                  rfl
              | internal specEvent =>
                  change
                    PMF.map restoreSpec
                        (Spec.stepInternal specEvent
                          (R.projectState source)) =
                      PMF.map restoreSpec
                        (Spec.stepInternal specEvent
                          (R.projectState source))
                  rfl

theorem mapRefinement_runEventsFrom_project_eq
    (R : StochasticRefinement Impl Spec)
    (events : List (messageInFlight Impl Message).Event)
    (state : (messageInFlight Impl Message).State) :
    PMF.map (mapProjectState Message R)
        ((messageInFlight Impl Message).runEventsFrom events state) =
      (messageInFlight Spec Message).runEventsFrom
        (mapProjectEventBatch Message R events)
        (mapProjectState Message R state) := by
  induction events generalizing state with
  | nil =>
      change
        PMF.map (mapProjectState Message R) (PMF.pure state) =
          PMF.pure (mapProjectState Message R state)
      rw [PMF.pure_map]
  | cons event events ih =>
      rw [Machine.runEventsFrom_cons_bind]
      rw [PMF.map_bind]
      simp_rw [ih]
      change
        ((messageInFlight Impl Message).step event state).bind
            ((fun specState =>
                (messageInFlight Spec Message).runEventsFrom
                  (mapProjectEventBatch Message R events)
                  specState) ∘
              mapProjectState Message R) =
          (messageInFlight Spec Message).runEventsFrom
            (mapProjectEventBatch Message R (event :: events))
            (mapProjectState Message R state)
      rw [← PMF.bind_map
        (p := (messageInFlight Impl Message).step event state)
        (f := mapProjectState Message R)
        (q := fun specState =>
          (messageInFlight Spec Message).runEventsFrom
            (mapProjectEventBatch Message R events) specState)]
      rw [mapRefinement_step_project Message R event state]
      cases hproject : mapProjectEvent? Message R event with
      | none =>
          simp [mapProjectEventBatch, hproject, PMF.pure_bind]
      | some specEvent =>
          simp [mapProjectEventBatch, hproject,
            Machine.runEventsFrom_cons_bind]

/-- Lift a source-machine refinement through identical message-in-flight
wrappers. The lifted refinement preserves protocol send/deliver events and
projects only the wrapped source-machine events. -/
noncomputable def mapRefinement
    (R : StochasticRefinement Impl Spec) :
    StochasticRefinement
      (messageInFlight Impl Message) (messageInFlight Spec Message) where
  projectState := mapProjectState Message R
  projectEvent? := mapProjectEvent? Message R
  projectEventBatch := mapProjectEventBatch Message R
  projectPublic := fun view =>
    (R.projectPublic view.1, view.2.1, view.2.2)
  projectObs := fun player view =>
    (R.projectObs player view.1, view.2.1, view.2.2)
  projectOutcome := R.projectOutcome
  init_project := by
    change
      ({ source := R.projectState Impl.init,
         pending := [],
         delivered := [] } :
        (messageInFlight Spec Message).State) =
      { source := Spec.init, pending := [], delivered := [] }
    rw [R.init_project]
  available_project := by
    intro state event specEvent havailable hproject
    rcases state with ⟨source, pending, delivered⟩
    cases event with
    | play player action =>
        cases action with
        | send message =>
            cases hproject
            change ¬ Spec.terminal (R.projectState source)
            intro hterminal
            exact havailable (R.terminal_reflect hterminal)
        | spec action =>
            rcases havailable with ⟨havailableSource, hqueue⟩
            change
              Option.map (liftEvent Spec Message)
                  (R.projectEvent? (.play player action)) =
                some specEvent at hproject
            cases hsource : R.projectEvent? (.play player action) with
            | none =>
                simp only [hsource, Option.map_none] at hproject
                cases hproject
            | some sourceSpecEvent =>
                simp only [hsource, Option.map_some] at hproject
                cases hproject
                cases sourceSpecEvent with
                | play specPlayer specAction =>
                    change specAction ∈
                        Spec.available (R.projectState source) specPlayer ∧
                      (pending = [] ∨
                        ∀ target,
                          target ∈
                            (Spec.stepPlay specPlayer specAction
                              (R.projectState source)).support →
                            ¬ Spec.terminal target)
                    constructor
                    · exact R.available_project
                        (event := .play player action)
                        havailableSource hsource
                    · cases hqueue with
                      | inl hpending =>
                          exact Or.inl hpending
                      | inr hnonterminal =>
                          exact Or.inr (by
                            simpa [Machine.step_play] using
                              R.step_support_nonterminal_project
                                (event := .play player action)
                                (source := source)
                                hsource
                                (by
                                  simpa [Machine.step_play] using
                                    hnonterminal))
                | internal specEvent =>
                    change specEvent ∈
                        Spec.availableInternal (R.projectState source) ∧
                      (pending = [] ∨
                        ∀ target,
                          target ∈
                            (Spec.stepInternal specEvent
                              (R.projectState source)).support →
                            ¬ Spec.terminal target)
                    constructor
                    · exact R.available_project
                        (event := .play player action)
                        havailableSource hsource
                    · cases hqueue with
                      | inl hpending =>
                          exact Or.inl hpending
                      | inr hnonterminal =>
                          exact Or.inr (by
                            simpa [Machine.step_internal] using
                              R.step_support_nonterminal_project
                                (event := .play player action)
                                (source := source)
                                hsource
                                (by
                                  simpa [Machine.step_play] using
                                    hnonterminal))
    | internal event =>
        cases event with
        | deliver =>
            cases hproject
            rcases havailable with ⟨hpending, hnonterminal⟩
            constructor
            · exact hpending
            · intro hterminal
              exact hnonterminal (R.terminal_reflect hterminal)
        | spec event =>
            rcases havailable with ⟨havailableSource, hqueue⟩
            change
              Option.map (liftEvent Spec Message)
                  (R.projectEvent? (.internal event)) =
                some specEvent at hproject
            cases hsource : R.projectEvent? (.internal event) with
            | none =>
                simp only [hsource, Option.map_none] at hproject
                cases hproject
            | some sourceSpecEvent =>
                simp only [hsource, Option.map_some] at hproject
                cases hproject
                cases sourceSpecEvent with
                | play specPlayer specAction =>
                    change specAction ∈
                        Spec.available (R.projectState source) specPlayer ∧
                      (pending = [] ∨
                        ∀ target,
                          target ∈
                            (Spec.stepPlay specPlayer specAction
                              (R.projectState source)).support →
                            ¬ Spec.terminal target)
                    constructor
                    · exact R.available_project
                        (event := .internal event)
                        havailableSource hsource
                    · cases hqueue with
                      | inl hpending =>
                          exact Or.inl hpending
                      | inr hnonterminal =>
                          exact Or.inr (by
                            simpa [Machine.step_play] using
                              R.step_support_nonterminal_project
                                (event := .internal event)
                                (source := source)
                                hsource
                                (by
                                  simpa [Machine.step_internal] using
                                    hnonterminal))
                | internal specEvent =>
                    change specEvent ∈
                        Spec.availableInternal (R.projectState source) ∧
                      (pending = [] ∨
                        ∀ target,
                          target ∈
                            (Spec.stepInternal specEvent
                              (R.projectState source)).support →
                            ¬ Spec.terminal target)
                    constructor
                    · exact R.available_project
                        (event := .internal event)
                        havailableSource hsource
                    · cases hqueue with
                      | inl hpending =>
                          exact Or.inl hpending
                      | inr hnonterminal =>
                          exact Or.inr (by
                            simpa [Machine.step_internal] using
                              R.step_support_nonterminal_project
                                (event := .internal event)
                                (source := source)
                                hsource
                                (by
                                  simpa [Machine.step_internal] using
                                    hnonterminal))
  step_project := by
    intro event state
    convert
      (@mapRefinement_step_project Player Message Impl Spec R event state)
      using 1
    cases hproject : mapProjectEvent? Message R event <;> rfl
  eventBatch_project := by
    intro events state
    show
      PMF.map (mapProjectState Message R)
          ((messageInFlight Impl Message).runEventsFrom events state) =
        (messageInFlight Spec Message).runEventsFrom
          (mapProjectEventBatch Message R events)
          (mapProjectState Message R state)
    exact
      @mapRefinement_runEventsFrom_project_eq Player Message Impl Spec R
        events state
  publicView_project := by
    intro state
    rcases state with ⟨source, pending, delivered⟩
    simp [mapProjectState, messageInFlight, R.publicView_project]
  observe_project := by
    intro player state
    rcases state with ⟨source, pending, delivered⟩
    simp [mapProjectState, messageInFlight, R.observe_project]
  terminal_project := by
    intro state hterminal
    exact R.terminal_project hterminal
  terminal_reflect := by
    intro state hterminal
    exact R.terminal_reflect hterminal
  outcome_project := by
    intro state
    change
      Option.map R.projectOutcome (Impl.outcome state.source) =
        Spec.outcome (R.projectState state.source)
    exact R.outcome_project state.source
  utility_project := by
    intro outcome player
    exact R.utility_project outcome player

end MapRefinement

theorem runEventsFrom_project_eq
    (events : List (messageInFlight M Message).Event)
    (state : (messageInFlight M Message).State) :
    PMF.map MessageInFlightState.source
        ((messageInFlight M Message).runEventsFrom events state) =
      M.runEventsFrom (projectEventBatch M Message events)
        state.source := by
  induction events generalizing state with
  | nil =>
      change
        PMF.map MessageInFlightState.source (PMF.pure state) =
          PMF.pure state.source
      rw [PMF.pure_map]
  | cons event events ih =>
      cases event with
      | play player action =>
          cases action with
          | send message =>
              simpa [Machine.runEventsFrom_cons_bind, Machine.step,
                messageInFlight, projectEventBatch, projectEvent?,
                PMF.map_bind] using
                ih
                  { source := state.source,
                    pending := state.pending ++ [⟨player, message⟩],
                    delivered := state.delivered }
          | spec action =>
              rw [Machine.runEventsFrom_cons_bind]
              simp only [Machine.step_play, messageInFlight,
                projectEventBatch, projectEvent?, List.filterMap_cons,
                PMF.map_bind]
              rw [PMF.bind_map]
              rw [Machine.runEventsFrom_cons_bind]
              congr
              funext current
              exact ih
                { source := current,
                  pending := state.pending,
                  delivered := state.delivered }
      | internal event =>
          cases event with
          | deliver =>
              rw [Machine.runEventsFrom_cons_bind]
              simp only [Machine.step_internal, messageInFlight,
                projectEventBatch, projectEvent?, List.filterMap_cons,
                PMF.map_bind]
              cases hpending : state.pending with
              | nil =>
                  simp only [PMF.pure_bind]
                  exact ih state
              | cons message rest =>
                  simp only [PMF.pure_bind]
                  exact
                    ih
                      { source := state.source,
                        pending := rest,
                        delivered := state.delivered ++ [message] }
          | spec event =>
              rw [Machine.runEventsFrom_cons_bind]
              simp only [Machine.step_internal, messageInFlight,
                projectEventBatch, projectEvent?, List.filterMap_cons,
                PMF.map_bind]
              rw [PMF.bind_map]
              rw [Machine.runEventsFrom_cons_bind]
              congr
              funext current
              exact ih
                { source := current,
                  pending := state.pending,
                  delivered := state.delivered }

/-- Message-in-flight machines refine their source machine by forgetting
message buffers and erasing send/deliver events. -/
noncomputable def refinement :
    StochasticRefinement (messageInFlight M Message) M where
  projectState := MessageInFlightState.source
  projectEvent? := projectEvent? M Message
  projectEventBatch := projectEventBatch M Message
  projectPublic := fun view => view.1
  projectObs := fun _ view => view.1
  projectOutcome := id
  init_project := rfl
  available_project := by
    intro state event specEvent havailable hproject
    cases event with
    | play player action =>
        cases action with
        | send message =>
            simp [projectEvent?] at hproject
        | spec action =>
            cases hproject
            exact havailable.1
    | internal event =>
        cases event with
        | deliver =>
            simp [projectEvent?] at hproject
        | spec event =>
            cases hproject
            exact havailable.1
  step_project := by
    intro event source
    cases event with
    | play player action =>
        cases action with
        | send message =>
            change
              PMF.map MessageInFlightState.source
                  (PMF.pure
                    { source := source.source,
                      pending := source.pending ++ [⟨player, message⟩],
                      delivered := source.delivered }) =
                PMF.pure source.source
            rw [PMF.pure_map]
        | spec action =>
            change
              PMF.map MessageInFlightState.source
                  (PMF.map
                    (fun dst =>
                      { source := dst,
                        pending := source.pending,
                        delivered := source.delivered })
                    (M.stepPlay player action source.source)) =
                M.stepPlay player action source.source
            exact
              (PMF.map_comp (p := M.stepPlay player action source.source)
                (f := fun dst =>
                  { source := dst,
                    pending := source.pending,
                    delivered := source.delivered })
                MessageInFlightState.source).trans
                (by
                  change PMF.map id
                      (M.stepPlay player action source.source) =
                    M.stepPlay player action source.source
                  rw [PMF.map_id])
    | internal event =>
        cases event with
        | deliver =>
            simp only [Machine.step_internal, messageInFlight, projectEvent?]
            cases hpending : source.pending with
            | nil =>
                rw [PMF.pure_map]
            | cons message rest =>
                rw [PMF.pure_map]
        | spec event =>
            change
              PMF.map MessageInFlightState.source
                  (PMF.map
                    (fun dst =>
                      { source := dst,
                        pending := source.pending,
                        delivered := source.delivered })
                    (M.stepInternal event source.source)) =
                M.stepInternal event source.source
            exact
              (PMF.map_comp (p := M.stepInternal event source.source)
                (f := fun dst =>
                  { source := dst,
                    pending := source.pending,
                    delivered := source.delivered })
                MessageInFlightState.source).trans
                (by
                  change PMF.map id
                      (M.stepInternal event source.source) =
                    M.stepInternal event source.source
                  rw [PMF.map_id])
  eventBatch_project := by
    intro events source
    exact runEventsFrom_project_eq M Message events source
  publicView_project := by
    intro state
    rfl
  observe_project := by
    intro player state
    rfl
  terminal_project := by
    intro state hterminal
    exact hterminal
  terminal_reflect := by
    intro state hterminal
    exact hterminal
  outcome_project := by
    intro state
    change Option.map id (M.outcome state.source) =
      M.outcome state.source
    cases M.outcome state.source <;> rfl
  utility_project := by
    intro outcome player
    rfl

end messageInFlight

end Machine
end Vegas
