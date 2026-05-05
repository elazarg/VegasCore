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
