import Vegas.Machine.Refinement

/-!
# Message-in-flight machine wrapper

`Machine.messageInFlight` adds an implementation-level message buffer to an
existing machine. Sends enqueue public messages, delivery moves one pending
message to the delivered log, and both pending and delivered messages are
visible in public and player observations. The refinement back to the source
machine erases send/deliver events and forgets the message buffers.
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
    | .spec sourceAction => sourceAction ∈ M.available state.source player
  availableInternal := fun state event =>
    match event with
    | .deliver => state.pending ≠ [] ∧ ¬ M.terminal state.source
    | .spec sourceEvent => sourceEvent ∈ M.availableInternal state.source
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
            exact havailable
    | internal event =>
        cases event with
        | deliver =>
            simp [projectEvent?] at hproject
        | spec event =>
            cases hproject
            exact havailable
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
