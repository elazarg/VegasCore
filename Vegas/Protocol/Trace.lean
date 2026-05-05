import Vegas.Protocol.Machine

/-!
# Machine trace semantics

Bounded event/state traces produced by running a `Machine` under a scheduling
`EventLaw`.

`traceDist M law n` is the distribution over `(events, states)` lists obtained
by stepping the machine `n` primitive events from the initial state, where each
step samples an event from `law` and then samples a successor from
`Machine.step`. `traceDistFrom` is the same starting from a given state.

`outcomeKernelFrom` is the same terminal-outcome marginal, written as a
state-recursive kernel from an arbitrary starting state. `outcomeKernel`
specializes it to `M.init`. This is the distribution Kuhn-style realization
theorems compare.

These are *the* trace semantics for `Machine`. The earlier syntax-directed
`Vegas.Trace` (Vegas/TraceSemantics.lean) is the equivalent notion at the
checked-program IR level; the long-term direction is to derive its theorems
from this machine-level trace and remove the redundant inductive layer.
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

/-- Execute a sequence of macro steps, where each macro step is represented by
a list of primitive machine events.  This is the trace shape induced by a
frontier-round FOSG presentation. -/
noncomputable def runEventBlocksFrom
    (M : Machine Player) (blocks : List (List M.Event)) (state : M.State) :
    PMF M.State :=
  blocks.foldl
    (fun acc events => acc.bind fun current => M.runEventsFrom events current)
    (PMF.pure state)

@[simp] theorem runEventBlocksFrom_nil
    (M : Machine Player) (state : M.State) :
    M.runEventBlocksFrom [] state = PMF.pure state := rfl

@[simp] theorem runEventBlocksFrom_singleton
    (M : Machine Player) (events : List M.Event) (state : M.State) :
    M.runEventBlocksFrom [events] state = M.runEventsFrom events state := by
  simp [runEventBlocksFrom]

/-- Folding event blocks over an arbitrary input distribution is the same as
binding that distribution into `runEventBlocksFrom`. -/
private theorem runEventBlocksFrom_foldl_eq_bind
    (M : Machine Player) (blocks : List (List M.Event))
    (acc : PMF M.State) :
    blocks.foldl
        (fun acc events => acc.bind fun current => M.runEventsFrom events current)
        acc =
      acc.bind fun current => M.runEventBlocksFrom blocks current := by
  induction blocks generalizing acc with
  | nil =>
      change acc = acc.bind PMF.pure
      exact (PMF.bind_pure acc).symm
  | cons events blocks ih =>
      change
        blocks.foldl
            (fun acc events => acc.bind fun current =>
              M.runEventsFrom events current)
            (acc.bind fun current => M.runEventsFrom events current) =
          acc.bind fun current =>
            M.runEventBlocksFrom (events :: blocks) current
      rw [ih, PMF.bind_bind]
      congr
      funext current
      rw [runEventBlocksFrom]
      simp only [List.foldl_cons, PMF.pure_bind]
      exact (ih (M.runEventsFrom events current)).symm

/-- Running event blocks is the same as running their flattened primitive event
list. -/
theorem runEventBlocksFrom_eq_runEventsFrom_flatten
    (M : Machine Player) (blocks : List (List M.Event)) (state : M.State) :
    M.runEventBlocksFrom blocks state =
      M.runEventsFrom blocks.flatten state := by
  induction blocks generalizing state with
  | nil =>
      rfl
  | cons events blocks ih =>
      rw [runEventBlocksFrom]
      simp only [List.foldl_cons]
      rw [runEventBlocksFrom_foldl_eq_bind]
      simp only [PMF.pure_bind]
      simp_rw [ih]
      rw [← runEventsFrom_append]
      rfl

/-- Executing appended event-block lists is Kleisli composition of the two
blocked runs. -/
theorem runEventBlocksFrom_append
    (M : Machine Player) (blocks₁ blocks₂ : List (List M.Event))
    (state : M.State) :
    M.runEventBlocksFrom (blocks₁ ++ blocks₂) state =
      (M.runEventBlocksFrom blocks₁ state).bind fun current =>
        M.runEventBlocksFrom blocks₂ current := by
  rw [runEventBlocksFrom]
  rw [List.foldl_append]
  rw [runEventBlocksFrom_foldl_eq_bind]
  rfl

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

/-- Outcome kernel induced by a scheduled event law, starting from an arbitrary
machine state. -/
noncomputable def outcomeKernelFrom
    (M : Machine Player) (law : M.EventLaw) :
    Nat → M.State → PMF M.Outcome
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

/-- Outcome kernel induced by a scheduled event law from the machine initial
state. -/
noncomputable def outcomeKernel
    (M : Machine Player) (law : M.EventLaw) (horizon : Nat) :
    PMF M.Outcome :=
  M.outcomeKernelFrom law horizon M.init

@[simp] theorem outcomeKernel_zero
    (M : Machine Player) (law : M.EventLaw) :
    M.outcomeKernel law 0 = PMF.pure (M.outcome M.init) := rfl

end Machine

end Vegas
