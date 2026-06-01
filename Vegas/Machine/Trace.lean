import Vegas.Machine.Basic

/-!
# Machine trace semantics

Bounded event/state traces produced by running a `Machine` under a scheduling
`EventLaw`.

`traceDist M law n` is the distribution over `(events, states)` lists obtained
by stepping the machine `n` primitive events from the initial state, where each
step samples an event from `law` and then samples a successor from
`Machine.step`. `traceDistFrom` is the same starting from a given state.

`outcomeKernelFrom` is the same outcome marginal, written as a state-recursive
kernel from an arbitrary starting state. The result is partial because a
bounded run can stop before a terminal outcome exists. `outcomeKernel`
specializes it to `M.init`.
-/

namespace Vegas

namespace Machine

variable {Player : Type}

/-- Execute a fixed primitive event list from a given state, returning only the
final state. This is the state marginal of a scheduled finite trace with the
schedule stored outside the machine. -/
noncomputable def runEventsFrom
    (M : Machine Player) (events : List M.Event) (state : M.State) :
    PMF M.State :=
  events.foldl
    (fun acc event => acc.bind fun current => M.step event current)
    (PMF.pure state)

@[simp] theorem runEventsFrom_nil
    (M : Machine Player) (state : M.State) :
    M.runEventsFrom [] state = PMF.pure state := rfl

theorem runEventsFrom_cons
    (M : Machine Player) (event : M.Event)
    (events : List M.Event) (state : M.State) :
    M.runEventsFrom (event :: events) state =
      events.foldl
        (fun acc nextEvent => acc.bind fun current =>
          M.step nextEvent current)
        (M.step event state) := by
  simp [runEventsFrom]

/-- Folding a primitive event list over an arbitrary input distribution is the
same as binding that distribution into `runEventsFrom`. -/
private theorem runEventsFrom_foldl_eq_bind
    (M : Machine Player) (events : List M.Event) (acc : PMF M.State) :
    events.foldl
        (fun acc event => acc.bind fun current => M.step event current)
        acc =
      acc.bind fun current => M.runEventsFrom events current := by
  induction events generalizing acc with
  | nil =>
      change acc = acc.bind PMF.pure
      exact (PMF.bind_pure acc).symm
  | cons event events ih =>
      change
        events.foldl
            (fun acc event => acc.bind fun current => M.step event current)
            (acc.bind fun current => M.step event current) =
          acc.bind fun current => M.runEventsFrom (event :: events) current
      rw [ih, PMF.bind_bind]
      congr
      funext current
      rw [runEventsFrom_cons]
      exact (ih (M.step event current)).symm

/-- Executing a nonempty event list is the first primitive step followed by the
remaining fixed event list. -/
theorem runEventsFrom_cons_bind
    (M : Machine Player) (event : M.Event)
    (events : List M.Event) (state : M.State) :
    M.runEventsFrom (event :: events) state =
      (M.step event state).bind fun current =>
        M.runEventsFrom events current := by
  rw [runEventsFrom_cons]
  rw [runEventsFrom_foldl_eq_bind]

/-- Executing appended event lists is Kleisli composition of the two runs. -/
theorem runEventsFrom_append
    (M : Machine Player) (events₁ events₂ : List M.Event)
    (state : M.State) :
    M.runEventsFrom (events₁ ++ events₂) state =
      (M.runEventsFrom events₁ state).bind fun current =>
        M.runEventsFrom events₂ current := by
  rw [runEventsFrom]
  rw [List.foldl_append]
  rw [runEventsFrom_foldl_eq_bind]
  rfl

/-- A fixed primitive event list is semantically available along one supported
machine execution from a source state to a destination state. -/
inductive AvailableRunFrom (M : Machine Player) :
    M.State → List M.Event → M.State → Prop where
  | nil (state : M.State) :
      AvailableRunFrom M state [] state
  | cons {source mid dst : M.State} {event : M.Event}
      {events : List M.Event} :
      M.EventAvailable source event →
      mid ∈ (M.step event source).support →
      AvailableRunFrom M mid events dst →
      AvailableRunFrom M source (event :: events) dst

namespace AvailableRunFrom

theorem append
    {M : Machine Player} {source mid dst : M.State}
    {events₁ events₂ : List M.Event}
    (left : M.AvailableRunFrom source events₁ mid)
    (right : M.AvailableRunFrom mid events₂ dst) :
    M.AvailableRunFrom source (events₁ ++ events₂) dst := by
  induction left with
  | nil state =>
      simpa using right
  | cons havailable hstep _ ih =>
      exact .cons havailable hstep (ih right)

theorem cons_inv
    {M : Machine Player} {source dst : M.State}
    {event : M.Event} {events : List M.Event}
    (hrun : M.AvailableRunFrom source (event :: events) dst) :
    ∃ mid, M.EventAvailable source event ∧
      mid ∈ (M.step event source).support ∧
      M.AvailableRunFrom mid events dst := by
  cases hrun with
  | cons havailable hstep htail =>
      exact ⟨_, havailable, hstep, htail⟩

theorem mem_runEventsFrom_support
    {M : Machine Player} {source dst : M.State}
    {events : List M.Event}
    (hrun : M.AvailableRunFrom source events dst) :
    dst ∈ (M.runEventsFrom events source).support := by
  induction hrun with
  | nil state =>
      simp
  | cons havailable hstep _ ih =>
      rw [Machine.runEventsFrom_cons_bind]
      rw [PMF.mem_support_bind_iff]
      exact ⟨_, hstep, ih⟩

end AvailableRunFrom

/-- One semantically available primitive machine step with positive support.

This is the labeled-transition-system view of `Machine`: total unavailable
steps may exist at the raw transition surface, but refinement and trace
theorems should use this relation. -/
def AvailableStep (M : Machine Player)
    (source : M.State) (event : M.Event) (target : M.State) : Prop :=
  M.EventAvailable source event ∧
    target ∈ (M.step event source).support

/-- Reachability by semantically available primitive steps. -/
def Reaches (M : Machine Player) (source target : M.State) : Prop :=
  ∃ events, M.AvailableRunFrom source events target

namespace AvailableStep

theorem available {M : Machine Player} {source target : M.State}
    {event : M.Event}
    (hstep : M.AvailableStep source event target) :
    M.EventAvailable source event :=
  hstep.1

theorem support {M : Machine Player} {source target : M.State}
    {event : M.Event}
    (hstep : M.AvailableStep source event target) :
    target ∈ (M.step event source).support :=
  hstep.2

theorem availableRunFrom_singleton
    {M : Machine Player} {source target : M.State} {event : M.Event}
    (hstep : M.AvailableStep source event target) :
    M.AvailableRunFrom source [event] target :=
  .cons hstep.available hstep.support (.nil target)

end AvailableStep

namespace Reaches

theorem refl (M : Machine Player) (state : M.State) :
    M.Reaches state state :=
  ⟨[], .nil state⟩

theorem step {M : Machine Player} {source target : M.State}
    {event : M.Event}
    (hstep : M.AvailableStep source event target) :
    M.Reaches source target :=
  ⟨[event], hstep.availableRunFrom_singleton⟩

theorem trans {M : Machine Player} {source mid target : M.State}
    (hleft : M.Reaches source mid) (hright : M.Reaches mid target) :
    M.Reaches source target := by
  rcases hleft with ⟨eventsLeft, runLeft⟩
  rcases hright with ⟨eventsRight, runRight⟩
  exact ⟨eventsLeft ++ eventsRight, runLeft.append runRight⟩

theorem mem_runEventsFrom_support
    {M : Machine Player} {source target : M.State}
    (hreaches : M.Reaches source target) :
    ∃ events, target ∈ (M.runEventsFrom events source).support := by
  rcases hreaches with ⟨events, hrun⟩
  exact ⟨events, hrun.mem_runEventsFrom_support⟩

end Reaches

/-- Execute a sequence of macro steps, where each macro step is represented by
a list of primitive machine events.  This is the trace shape induced by a
checkpoint or frontier-round presentation. -/
noncomputable def runEventBatchesFrom
    (M : Machine Player) (batches : List (List M.Event)) (state : M.State) :
    PMF M.State :=
  batches.foldl
    (fun acc events => acc.bind fun current => M.runEventsFrom events current)
    (PMF.pure state)

@[simp] theorem runEventBatchesFrom_nil
    (M : Machine Player) (state : M.State) :
    M.runEventBatchesFrom [] state = PMF.pure state := rfl

@[simp] theorem runEventBatchesFrom_singleton
    (M : Machine Player) (events : List M.Event) (state : M.State) :
    M.runEventBatchesFrom [events] state = M.runEventsFrom events state := by
  simp [runEventBatchesFrom]

/-- Folding event batches over an arbitrary input distribution is the same as
binding that distribution into `runEventBatchesFrom`. -/
private theorem runEventBatchesFrom_foldl_eq_bind
    (M : Machine Player) (batches : List (List M.Event))
    (acc : PMF M.State) :
    batches.foldl
        (fun acc events => acc.bind fun current => M.runEventsFrom events current)
        acc =
      acc.bind fun current => M.runEventBatchesFrom batches current := by
  induction batches generalizing acc with
  | nil =>
      change acc = acc.bind PMF.pure
      exact (PMF.bind_pure acc).symm
  | cons events batches ih =>
      change
        batches.foldl
            (fun acc events => acc.bind fun current =>
              M.runEventsFrom events current)
            (acc.bind fun current => M.runEventsFrom events current) =
          acc.bind fun current =>
            M.runEventBatchesFrom (events :: batches) current
      rw [ih, PMF.bind_bind]
      congr
      funext current
      rw [runEventBatchesFrom]
      simp only [List.foldl_cons, PMF.pure_bind]
      exact (ih (M.runEventsFrom events current)).symm

/-- Running event batches is the same as running their flattened primitive event
list. -/
theorem runEventBatchesFrom_eq_runEventsFrom_flatten
    (M : Machine Player) (batches : List (List M.Event)) (state : M.State) :
    M.runEventBatchesFrom batches state =
      M.runEventsFrom batches.flatten state := by
  induction batches generalizing state with
  | nil =>
      rfl
  | cons events batches ih =>
      rw [runEventBatchesFrom]
      simp only [List.foldl_cons]
      rw [runEventBatchesFrom_foldl_eq_bind]
      simp only [PMF.pure_bind]
      simp_rw [ih]
      rw [← runEventsFrom_append]
      rfl

/-- Executing appended event-batch lists is Kleisli composition of the two
event-batch runs. -/
theorem runEventBatchesFrom_append
    (M : Machine Player) (batches₁ batches₂ : List (List M.Event))
    (state : M.State) :
    M.runEventBatchesFrom (batches₁ ++ batches₂) state =
      (M.runEventBatchesFrom batches₁ state).bind fun current =>
        M.runEventBatchesFrom batches₂ current := by
  rw [runEventBatchesFrom]
  rw [List.foldl_append]
  rw [runEventBatchesFrom_foldl_eq_bind]
  rfl

/-- A list of primitive event batches is semantically available along one
supported checkpoint execution from a source state to a destination state. -/
inductive AvailableRunBatchesFrom (M : Machine Player) :
    M.State → List (List M.Event) → M.State → Prop where
  | nil (state : M.State) :
      AvailableRunBatchesFrom M state [] state
  | cons {source mid dst : M.State} {batch : List M.Event}
      {batches : List (List M.Event)} :
      AvailableRunFrom M source batch mid →
      AvailableRunBatchesFrom M mid batches dst →
      AvailableRunBatchesFrom M source (batch :: batches) dst

namespace AvailableRunBatchesFrom

theorem mem_runEventBatchesFrom_support
    {M : Machine Player} {source dst : M.State}
    {batches : List (List M.Event)}
    (hrun : M.AvailableRunBatchesFrom source batches dst) :
    dst ∈ (M.runEventBatchesFrom batches source).support := by
  induction hrun with
  | nil state =>
      simp
  | cons hbatch _ ih =>
      rw [Machine.runEventBatchesFrom]
      simp only [List.foldl_cons, PMF.pure_bind]
      rw [runEventBatchesFrom_foldl_eq_bind]
      rw [PMF.mem_support_bind_iff]
      exact ⟨_, hbatch.mem_runEventsFrom_support, ih⟩

end AvailableRunBatchesFrom

/-- An event-batch machine trace records the event batches executed so far and the
current checkpoint state. -/
abbrev EventBatchTrace (M : Machine Player) : Type :=
  List (List M.Event) × M.State

/-- A history-dependent law for selecting the next event batch of primitive events.

The law sees the event-batch trace prefix, not only the current state. This matches
strategic schedulers whose choices can depend on public/history information
while still running through the machine's primitive transition semantics. -/
abbrev EventBatchLaw (M : Machine Player) : Type :=
  M.EventBatchTrace → PMF (List M.Event)

/-- A history-dependent event-batch law is legal when every supported batch from
a nonterminal checkpoint has an available primitive execution from that
checkpoint. -/
def IsLegalEventBatchLaw (M : Machine Player) (law : M.EventBatchLaw) : Prop :=
  ∀ trace, ¬ M.terminal trace.2 → ∀ {batch},
    batch ∈ (law trace).support →
      ∃ dst, M.AvailableRunFrom trace.2 batch dst

/-- Event-batch laws bundled with their primitive availability proof. -/
abbrev LegalEventBatchLaw (M : Machine Player) : Type :=
  { law : M.EventBatchLaw // M.IsLegalEventBatchLaw law }

/-- Bounded event-batch trace distribution from an arbitrary event-batch trace prefix.
Execution stops once the current state is terminal; otherwise one event batch is
sampled, run through the primitive machine semantics, and appended to the
prefix. -/
noncomputable def eventBatchTraceDistFrom
    (M : Machine Player) (law : M.EventBatchLaw) :
    Nat → M.EventBatchTrace → PMF M.EventBatchTrace
  | 0, trace => PMF.pure trace
  | horizon + 1, trace => by
      classical
      exact
        if M.terminal trace.2 then
          PMF.pure trace
        else
          (law trace).bind fun batch =>
            (M.runEventBatchesFrom [batch] trace.2).bind fun next =>
              M.eventBatchTraceDistFrom law horizon
                (trace.1 ++ [batch], next)

@[simp] theorem eventBatchTraceDistFrom_zero
    (M : Machine Player) (law : M.EventBatchLaw) (trace : M.EventBatchTrace) :
    M.eventBatchTraceDistFrom law 0 trace = PMF.pure trace := rfl

theorem eventBatchTraceDistFrom_succ_terminal
    (M : Machine Player) (law : M.EventBatchLaw)
    (horizon : Nat) (trace : M.EventBatchTrace)
    (hterminal : M.terminal trace.2) :
    M.eventBatchTraceDistFrom law (horizon + 1) trace = PMF.pure trace := by
  simp [eventBatchTraceDistFrom, hterminal]

theorem eventBatchTraceDistFrom_succ_nonterminal
    (M : Machine Player) (law : M.EventBatchLaw)
    (horizon : Nat) (trace : M.EventBatchTrace)
    (hterminal : ¬ M.terminal trace.2) :
    M.eventBatchTraceDistFrom law (horizon + 1) trace =
      (law trace).bind fun batch =>
        (M.runEventBatchesFrom [batch] trace.2).bind fun next =>
          M.eventBatchTraceDistFrom law horizon
            (trace.1 ++ [batch], next) := by
  simp [eventBatchTraceDistFrom, hterminal]

/-- Bounded event-batch trace distribution from the machine initial state. -/
noncomputable def eventBatchTraceDist
    (M : Machine Player) (law : M.EventBatchLaw) (horizon : Nat) :
    PMF M.EventBatchTrace :=
  M.eventBatchTraceDistFrom law horizon ([], M.init)

@[simp] theorem eventBatchTraceDist_zero
    (M : Machine Player) (law : M.EventBatchLaw) :
    M.eventBatchTraceDist law 0 = PMF.pure ([], M.init) := rfl

/-- One scheduled machine step. -/
noncomputable def stepDist
    (M : Machine Player) (law : M.EventLaw) (state : M.State) :
    PMF M.State :=
  (law state).bind fun event => M.step event state

/-- Bounded event/state trace distribution from a given state. The state list
starts with the input state and has one more entry than the event list. -/
noncomputable def traceDistFrom
    (M : Machine Player) (law : M.EventLaw) :
    Nat → M.State → PMF (List M.Event × List M.State)
  | 0, state => PMF.pure ([], [state])
  | horizon + 1, state =>
      (law state).bind fun event =>
        (M.step event state).bind fun next =>
          (M.traceDistFrom law horizon next).map fun trace =>
            (event :: trace.1, state :: trace.2)

@[simp] theorem traceDistFrom_zero
    (M : Machine Player) (law : M.EventLaw) (state : M.State) :
    M.traceDistFrom law 0 state = PMF.pure ([], [state]) := rfl

theorem traceDistFrom_succ
    (M : Machine Player) (law : M.EventLaw)
    (horizon : Nat) (state : M.State) :
    M.traceDistFrom law (horizon + 1) state =
      (law state).bind fun event =>
        (M.step event state).bind fun next =>
          (M.traceDistFrom law horizon next).map fun trace =>
            (event :: trace.1, state :: trace.2) := rfl

/-- Bounded event/state trace distribution from the machine initial state. -/
noncomputable def traceDist
    (M : Machine Player) (law : M.EventLaw) (horizon : Nat) :
    PMF (List M.Event × List M.State) :=
  M.traceDistFrom law horizon M.init

@[simp] theorem traceDist_zero
    (M : Machine Player) (law : M.EventLaw) :
    M.traceDist law 0 = PMF.pure ([], [M.init]) := rfl

/-- Partial outcome kernel induced by a scheduled event law, starting from an
arbitrary machine state. A bounded horizon may stop before a terminal outcome
exists, so the marginal is over `Option M.Outcome`. -/
noncomputable def outcomeKernelFrom
    (M : Machine Player) (law : M.EventLaw) :
    Nat → M.State → PMF (Option M.Outcome)
  | 0, state => PMF.pure (M.outcome state)
  | horizon + 1, state =>
      (law state).bind fun event =>
        (M.step event state).bind fun next =>
          M.outcomeKernelFrom law horizon next

@[simp] theorem outcomeKernelFrom_zero
    (M : Machine Player) (law : M.EventLaw) (state : M.State) :
    M.outcomeKernelFrom law 0 state = PMF.pure (M.outcome state) := rfl

theorem outcomeKernelFrom_succ
    (M : Machine Player) (law : M.EventLaw)
    (horizon : Nat) (state : M.State) :
    M.outcomeKernelFrom law (horizon + 1) state =
      (law state).bind fun event =>
        (M.step event state).bind fun next =>
          M.outcomeKernelFrom law horizon next := rfl

/-- Partial outcome kernel induced by a scheduled event law from the machine
initial state. -/
noncomputable def outcomeKernel
    (M : Machine Player) (law : M.EventLaw) (horizon : Nat) :
    PMF (Option M.Outcome) :=
  M.outcomeKernelFrom law horizon M.init

@[simp] theorem outcomeKernel_zero
    (M : Machine Player) (law : M.EventLaw) :
    M.outcomeKernel law 0 = PMF.pure (M.outcome M.init) := rfl

end Machine

end Vegas
