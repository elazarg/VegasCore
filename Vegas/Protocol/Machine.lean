import Vegas.Protocol.EventGraph
import GameTheory.Core.KernelGame
import GameTheory.Languages.InfoModel

/-!
# Protocol information machines

`Machine` is the executable protocol semantics derived from action-graph data.
It is an observation-aware asynchronous state machine:

* one primitive step is one enabled player move or one internal move;
* transitions are PMF-valued;
* states expose public and player-local observations;

The structure is deliberately generic. Concrete syntax and blockchain runtimes
should elaborate to or refine this carrier before stating strategic claims.
-/

namespace Vegas

open GameTheory

/-- Canonical protocol information machine.

The primitive execution event is a single enabled move: either one player makes
one concrete choice, or the machine performs one internal protocol event such as
frontier finalization. Simultaneous rounds, transaction schedules, FOSG
histories, and game-tree serializations are presentations derived from this
carrier; they are not baked into it. -/
structure Machine (Player : Type) where
  State : Type
  Action : Player → Type
  Internal : Type
  Public : Type
  Obs : Player → Type
  Outcome : Type
  init : State
  available : State → (player : Player) → Set (Action player)
  availableInternal : State → Set Internal
  stepPlay : (player : Player) → Action player → State → PMF State
  stepInternal : Internal → State → PMF State
  terminal : State → Prop
  publicView : State → Public
  observe : (player : Player) → State → Obs player
  outcome : State → Outcome
  utility : Outcome → Payoff Player

namespace Machine

variable {Player : Type}

/-- One primitive machine event. -/
inductive Event (M : Machine Player) where
  | play (player : Player) (action : M.Action player)
  | internal (event : M.Internal)

/-- Event availability at the current machine state. -/
def EventAvailable (M : Machine Player) (state : M.State) :
    M.Event → Prop
  | .play player action => action ∈ M.available state player
  | .internal event => event ∈ M.availableInternal state

/-- Total step kernel for primitive machine events. Legality is a separate
predicate because reactive runtimes usually expose a total transition surface,
while semantic runs restrict attention to available events. -/
def step (M : Machine Player) : M.Event → M.State → PMF M.State
  | .play player action, state => M.stepPlay player action state
  | .internal event, state => M.stepInternal event state

/-- Positive-support transition relation induced by one primitive event. -/
def StepRel (M : Machine Player)
    (event : M.Event) (source target : M.State) : Prop :=
  M.step event source target ≠ 0

/-- Event/state prefix for the asynchronous machine.

The invariant records the execution-shape fact: a prefix with `n` primitive
events has `n + 1` states. Derived views such as FOSG presentations use this
as their world type so observations and strategy recall are attached to the
same execution object as the machine run. -/
structure RunPrefix (M : Machine Player) where
  events : List M.Event
  states : List M.State
  length_eq : states.length = events.length + 1

namespace RunPrefix

variable {M : Machine Player}

@[ext] theorem ext
    {left right : M.RunPrefix}
    (hevents : left.events = right.events)
    (hstates : left.states = right.states) :
    left = right := by
  cases left
  cases right
  cases hevents
  cases hstates
  rfl

/-- Initial asynchronous machine prefix. -/
def init (M : Machine Player) : M.RunPrefix where
  events := []
  states := [M.init]
  length_eq := by simp

/-- Endpoint state of an asynchronous machine prefix. -/
def lastState (pref : M.RunPrefix) : M.State :=
  pref.states.getLast?.getD M.init

/-- Extend a prefix by one primitive event and one successor state. -/
def snoc (pref : M.RunPrefix) (event : M.Event)
    (next : M.State) : M.RunPrefix where
  events := pref.events ++ [event]
  states := pref.states ++ [next]
  length_eq := by
    simp [pref.length_eq]

@[simp] theorem init_events (M : Machine Player) :
    (RunPrefix.init M).events = [] := rfl

@[simp] theorem init_states (M : Machine Player) :
    (RunPrefix.init M).states = [M.init] := rfl

@[simp] theorem init_lastState (M : Machine Player) :
    (RunPrefix.init M).lastState = M.init := rfl

@[simp] theorem snoc_events
    (pref : M.RunPrefix) (event : M.Event) (next : M.State) :
    (pref.snoc event next).events = pref.events ++ [event] := rfl

@[simp] theorem snoc_states
    (pref : M.RunPrefix) (event : M.Event) (next : M.State) :
    (pref.snoc event next).states = pref.states ++ [next] := rfl

@[simp] theorem snoc_lastState
    (pref : M.RunPrefix) (event : M.Event) (next : M.State) :
    (pref.snoc event next).lastState = next := by
  unfold lastState snoc
  simp

end RunPrefix

@[simp] theorem step_play
    (M : Machine Player) (player : Player)
    (action : M.Action player) (state : M.State) :
    M.step (.play player action) state =
      M.stepPlay player action state := rfl

@[simp] theorem step_internal
    (M : Machine Player) (event : M.Internal) (state : M.State) :
    M.step (.internal event) state =
      M.stepInternal event state := rfl

@[simp] theorem eventAvailable_play
    (M : Machine Player) (state : M.State)
    (player : Player) (action : M.Action player) :
    M.EventAvailable state (.play player action) ↔
      action ∈ M.available state player := Iff.rfl

@[simp] theorem eventAvailable_internal
    (M : Machine Player) (state : M.State) (event : M.Internal) :
    M.EventAvailable state (.internal event) ↔
      event ∈ M.availableInternal state := Iff.rfl

/-- A law for selecting the next primitive event at a state.

This is presentation data, not part of the machine. Different traces, FOSG
views, runtime schedulers, or tests can supply different laws and then prove
the preservation theorem they need. -/
abbrev EventLaw (M : Machine Player) : Type :=
  M.State → PMF M.Event

/-- An event law is legal when, before terminal states, it puts mass only on
currently available primitive events. Terminal states have no semantic next
event; trace users should either stop there or rely on total machine steps for
post-terminal stutter behavior. -/
def IsLegalEventLaw (M : Machine Player) (law : M.EventLaw) : Prop :=
  ∀ (state : M.State), ¬ M.terminal state → ∀ {event : M.Event},
    event ∈ (law state).support → M.EventAvailable state event

/-- Legal event laws for the asynchronous machine. -/
abbrev LegalEventLaw (M : Machine Player) : Type :=
  { law : M.EventLaw // M.IsLegalEventLaw law }

namespace LegalEventLaw

/-- Forget the legality proof of an event law. -/
def toEventLaw (M : Machine Player) (law : M.LegalEventLaw) : M.EventLaw :=
  law.val

theorem eventAvailable_of_mem_support
    (M : Machine Player) (law : M.LegalEventLaw)
    (state : M.State) {event : M.Event}
    (hterminal : ¬ M.terminal state)
    (hmem : event ∈ (law.toEventLaw M state).support) :
    M.EventAvailable state event :=
  law.2 state hterminal hmem

end LegalEventLaw

end Machine

end Vegas
