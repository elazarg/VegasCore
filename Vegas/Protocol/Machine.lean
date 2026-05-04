import Vegas.Protocol.ActionGraph
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

/-- An event law is legal when it puts mass only on currently available
primitive events. -/
def IsLegalEventLaw (M : Machine Player) (law : M.EventLaw) : Prop :=
  ∀ (state : M.State) {event : M.Event},
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
    (hmem : event ∈ (law.toEventLaw M state).support) :
    M.EventAvailable state event :=
  law.2 state hmem

end LegalEventLaw

end Machine

namespace ActionGraph

variable {Player Action Field Param Guard Join : Type}
variable [DecidableEq Action] [DecidableEq Field]

/-- One concrete player packet for the frontier LTS of an action graph. -/
structure FrontierChoice
    (G : ActionGraph Player Action Field Param Guard Join)
    (Value : Type) (_who : Player) where
  delta : Slice Field (StoredValue Value)
  tag : PlayTag Action

/-- Executable semantics for an action graph.

The graph fixes the state shape: `State = ActionGraph.Configuration`. This
record supplies only the pieces the graph cannot know by itself: concrete
player choice types, internal events, availability, PMF-valued execution
kernels, observations, outcome extraction, and utilities. Backend
implementations with extra state should relate to `Semantics.toMachine` by
machine refinement instead of changing the source denotation. -/
structure Semantics
    (G : ActionGraph Player Action Field Param Guard Join) where
  Value : Type
  Choice : Player → Type
  Internal : Type
  Public : Type
  Obs : Player → Type
  Outcome : Type
  available : G.Configuration Value → (player : Player) → Set (Choice player)
  availableInternal : G.Configuration Value → Set Internal
  stepPlay :
    (player : Player) → Choice player →
      G.Configuration Value → PMF (G.Configuration Value)
  stepInternal :
    Internal → G.Configuration Value → PMF (G.Configuration Value)
  publicView : G.Configuration Value → Public
  observe : (player : Player) → G.Configuration Value → Obs player
  outcome : G.Configuration Value → Outcome
  utility : Outcome → Payoff Player
  stepPlay_done_eq_or_advance :
    ∀ {player : Player} {choice : Choice player}
      {source target : G.Configuration Value},
      target ∈ (stepPlay player choice source).support →
        target.frontier.done = source.frontier.done ∨
          target.frontier.done = G.advance source.frontier.done
  stepInternal_done_eq_or_advance :
    ∀ {event : Internal} {source target : G.Configuration Value},
      target ∈ (stepInternal event source).support →
        target.frontier.done = source.frontier.done ∨
          target.frontier.done = G.advance source.frontier.done
  terminal_iff_completeAt :
    ∀ state : G.Configuration Value,
      state.isTerminal ↔ G.CompleteAt state.frontier.done

namespace Semantics

variable {G : ActionGraph Player Action Field Param Guard Join}

/-- The canonical machine directly executing an action graph frontier
configuration. The source state is graph configuration; stochasticity and
value-level execution are supplied by the graph semantics record. -/
noncomputable def toMachine (S : Semantics G) : Machine Player where
  State := G.Configuration S.Value
  Action := S.Choice
  Internal := S.Internal
  Public := S.Public
  Obs := S.Obs
  Outcome := S.Outcome
  init := Configuration.initial G
  available := S.available
  availableInternal := S.availableInternal
  stepPlay := S.stepPlay
  stepInternal := S.stepInternal
  terminal := Configuration.isTerminal
  publicView := S.publicView
  observe := S.observe
  outcome := S.outcome
  utility := S.utility

@[simp] theorem toMachine_init (S : Semantics G) :
    S.toMachine.init = Configuration.initial G := rfl

@[simp] theorem toMachine_available
    (S : Semantics G) (cfg : S.toMachine.State) (who : Player)
    (choice : S.toMachine.Action who) :
    S.toMachine.available cfg who choice = S.available cfg who choice := rfl

@[simp] theorem toMachine_availableInternal
    (S : Semantics G) (cfg : S.toMachine.State)
    (event : S.toMachine.Internal) :
    S.toMachine.availableInternal cfg event =
      S.availableInternal cfg event := rfl

@[simp] theorem toMachine_stepPlay
    (S : Semantics G) (who : Player)
    (choice : S.toMachine.Action who) (cfg : S.toMachine.State) :
    S.toMachine.stepPlay who choice cfg =
      S.stepPlay who choice cfg := rfl

@[simp] theorem toMachine_stepInternal
    (S : Semantics G) (event : S.toMachine.Internal)
    (cfg : S.toMachine.State) :
    S.toMachine.stepInternal event cfg =
      S.stepInternal event cfg := rfl

@[simp] theorem toMachine_terminal
    (S : Semantics G) (cfg : S.toMachine.State) :
    S.toMachine.terminal cfg = cfg.isTerminal := rfl

@[simp] theorem toMachine_publicView
    (S : Semantics G) (cfg : S.toMachine.State) :
    S.toMachine.publicView cfg = S.publicView cfg := rfl

@[simp] theorem toMachine_observe
    (S : Semantics G) (who : Player) (cfg : S.toMachine.State) :
    S.toMachine.observe who cfg = S.observe who cfg := rfl

@[simp] theorem toMachine_outcome
    (S : Semantics G) (cfg : S.toMachine.State) :
    S.toMachine.outcome cfg = S.outcome cfg := rfl

theorem toMachine_terminal_iff_completeAt
    (S : Semantics G) (cfg : S.toMachine.State) :
    S.toMachine.terminal cfg ↔
      G.CompleteAt cfg.frontier.done :=
  S.terminal_iff_completeAt cfg

theorem toMachine_terminal_iff_frontier_empty
    (S : Semantics G) (cfg : S.toMachine.State) :
    S.toMachine.terminal cfg ↔ cfg.enabled = ∅ := by
  rw [S.toMachine_terminal_iff_completeAt cfg]
  exact (G.frontier_eq_empty_iff_completeAt cfg.frontier.done).symm

theorem stepPlay_done_eq_or_advance_of_support
    (S : Semantics G)
    {player : Player} {choice : S.Choice player}
    {source target : G.Configuration S.Value}
    (hmem : target ∈ (S.stepPlay player choice source).support) :
    target.frontier.done = source.frontier.done ∨
      target.frontier.done = G.advance source.frontier.done :=
  S.stepPlay_done_eq_or_advance hmem

theorem stepInternal_done_eq_or_advance_of_support
    (S : Semantics G)
    {event : S.Internal} {source target : G.Configuration S.Value}
    (hmem : target ∈ (S.stepInternal event source).support) :
    target.frontier.done = source.frontier.done ∨
      target.frontier.done = G.advance source.frontier.done :=
  S.stepInternal_done_eq_or_advance hmem

theorem toMachine_step_done_eq_or_advance_of_support
    (S : Semantics G)
    {event : S.toMachine.Event} {source target : S.toMachine.State}
    (hmem : target ∈ (S.toMachine.step event source).support) :
    target.frontier.done = source.frontier.done ∨
      target.frontier.done = G.advance source.frontier.done := by
  cases event with
  | play player choice =>
      exact S.stepPlay_done_eq_or_advance_of_support hmem
  | internal event =>
      exact S.stepInternal_done_eq_or_advance_of_support hmem

theorem toMachine_eq_of_eq
    {S₁ S₂ : Semantics G} (h : S₁ = S₂) :
    S₁.toMachine = S₂.toMachine := by
  cases h
  rfl

end Semantics

end ActionGraph

end Vegas
