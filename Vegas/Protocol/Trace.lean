import Vegas.Protocol.Machine

/-!
# Machine trace semantics

Bounded event/state traces produced by running a `Machine` under a scheduling
`EventLaw`.

`traceDist M law n` is the distribution over `(events, states)` lists obtained
by stepping the machine `n` primitive events from the initial state, where each
step samples an event from `law` and then samples a successor from
`Machine.step`. `traceDistFrom` is the same starting from a given state.

`outcomeKernel` marginalizes a trace to the terminal `M.Outcome`. This is the
distribution Kuhn-style realization theorems compare.

These are *the* trace semantics for `Machine`. The earlier syntax-directed
`Vegas.Trace` (Vegas/TraceSemantics.lean) is the equivalent notion at the
checked-program IR level; the long-term direction is to derive its theorems
from this machine-level trace and remove the redundant inductive layer.
-/

namespace Vegas

namespace Machine

variable {Player : Type}

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

/-- Outcome kernel induced by a scheduled event law: the terminal-state
marginal of `traceDist`. -/
noncomputable def outcomeKernel
    (M : Machine Player) (law : M.EventLaw) (horizon : Nat) :
    PMF M.Outcome :=
  (M.traceDist law horizon).map fun trace =>
    M.outcome (trace.2.getLast?.getD M.init)

end Machine

end Vegas
