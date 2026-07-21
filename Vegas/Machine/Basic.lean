import GameTheory.Core.KernelGame
import GameTheory.Languages.InfoModel

/-!
# Protocol information machines

`Machine` is the executable protocol semantics derived from action-graph data.
It is an observation-aware asynchronous state machine:

* one primitive step is one enabled player move or one internal move;
* transitions are PMF-valued;
* states expose public and player-local observations;

The structure is deliberately generic. Concrete syntax and external runtimes
should elaborate to or refine this carrier before stating strategic claims.
-/

namespace Vegas

open GameTheory

/-- Canonical protocol information machine.

The primitive execution event is a single enabled move: either one player makes
one concrete choice, or the machine performs one internal protocol event such as
frontier finalization. Simultaneous rounds, execution schedules, checkpoint
histories, and game-tree serializations are presentations derived from this
carrier; they are not baked into it. Outcomes are partial at this layer:
nonterminal or malformed states can report no game payoff instead of forcing a
cutoff convention into the base semantics. -/
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
  outcome : State → Option Outcome
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

end Machine

end Vegas
