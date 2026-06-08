import GameTheory.Core.JointAction
import Math.BoundedLists
import Math.PMFProduct
import Mathlib.Algebra.BigOperators.Ring.Finset
import Vegas.Machine.Bounded
import Vegas.Machine.Trace

/-!
# Native round views of machines

A `RoundView` is the machine-native strategic game form used by Vegas.  It
packages player-facing simultaneous rounds over machine states, finite-horizon
histories, reachable legal strategies, and outcome kernels without routing
through a separate extensive-form presentation.
-/

namespace Vegas

open GameTheory
open scoped BigOperators

namespace Machine

variable {Player : Type}

/-- A player-facing round view of a machine.  The action alphabet is owned by
the view because a strategic round need not be a single primitive machine
event. -/
structure RoundView (M : Machine Player) where
  Act : Player → Type
  active : M.State → Finset Player
  availableActions : M.State → (player : Player) → Set (Act player)
  transition :
    (state : M.State) →
      {a : JointAction Act //
        JointActionLegal Act active M.terminal availableActions state a} →
      PMF M.State
  /-- Ordered primitive events used to replay or audit one supported round
  transition. This is not part of the strategic observation interface:
  histories and information states are built from public/player observations,
  not from this list. -/
  eventBatch : M.State → JointAction Act → M.State → List M.Event
  terminal_active_eq_empty :
    ∀ {state : M.State}, M.terminal state → active state = ∅
  nonterminal_exists_legal :
    ∀ {state : M.State}, ¬ M.terminal state →
      ∃ a : JointAction Act,
        JointActionLegal Act active M.terminal availableActions state a

namespace RoundView

variable {M : Machine Player}

/-- A round view is operationally certified when every supported strategic
round transition is replayable by the primitive machine events recorded in
`eventBatch`.

This is intentionally not a field of `RoundView`: some round views are only
mathematical presentations. Refinement-facing bridges should require this
certificate before making claims about primitive-machine traces. -/
def OperationallyCertified (view : M.RoundView) : Prop :=
  ∀ {state}
    (action :
      {a : JointAction view.Act //
        JointActionLegal view.Act view.active M.terminal
          view.availableActions state a})
    {dst},
      view.transition state action dst ≠ 0 →
        M.AvailableRunFrom state
          (view.eventBatch state action.1 dst) dst

/-- Terminal predicate for a horizon-bounded round view. -/
def boundedTerminal (_view : M.RoundView) (horizon : Nat)
    (state : M.BoundedState horizon) : Prop :=
  M.terminal state.state ∨ horizon ≤ state.depth

/-- Active players before the cutoff; none are active at the cutoff. -/
def boundedActive (view : M.RoundView) (horizon : Nat)
    (state : M.BoundedState horizon) : Finset Player :=
  if horizon ≤ state.depth then ∅ else view.active state.state

/-- Available round actions before the cutoff; no actions at the cutoff. -/
def boundedAvailableActions (view : M.RoundView) (horizon : Nat)
    (state : M.BoundedState horizon) (player : Player) :
    Set (view.Act player) :=
  if horizon ≤ state.depth then ∅
  else view.availableActions state.state player

abbrev BoundedLegalAction
    (view : M.RoundView) (horizon : Nat)
    (state : M.BoundedState horizon) : Type :=
  {a : JointAction view.Act //
    JointActionLegal view.Act (view.boundedActive horizon)
      (view.boundedTerminal horizon)
      (view.boundedAvailableActions horizon) state a}

/-- Local legality of one player's optional move at a bounded state. -/
def boundedLocallyLegalAtState
    (view : M.RoundView) (horizon : Nat)
    (state : M.BoundedState horizon) (player : Player) :
    Option (view.Act player) → Prop
  | some action =>
      player ∈ view.boundedActive horizon state ∧
        action ∈ view.boundedAvailableActions horizon state player
  | none => player ∉ view.boundedActive horizon state

theorem boundedLegal_iff_forall
    (view : M.RoundView) (horizon : Nat)
    {state : M.BoundedState horizon} {a : JointAction view.Act} :
    JointActionLegal view.Act (view.boundedActive horizon)
        (view.boundedTerminal horizon)
        (view.boundedAvailableActions horizon) state a ↔
      ¬ view.boundedTerminal horizon state ∧
        ∀ player, view.boundedLocallyLegalAtState horizon state player
          (a player) := by
  unfold JointActionLegal boundedLocallyLegalAtState
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro player
    cases hmove : a player with
    | none => simpa [hmove] using h.2 player
    | some action => simpa [hmove] using h.2 player
  · intro h
    refine ⟨h.1, ?_⟩
    intro player
    cases hmove : a player with
    | none => simpa [hmove] using h.2 player
    | some action => simpa [hmove] using h.2 player

/-- Optional moves available to a player at a bounded state. -/
def boundedAvailableMovesAtState
    (view : M.RoundView) (horizon : Nat)
    (state : M.BoundedState horizon) (player : Player) :
    Set (Option (view.Act player)) :=
  { move | view.boundedLocallyLegalAtState horizon state player move }

theorem mem_boundedAvailableMovesAtState_iff
    {view : M.RoundView} {horizon : Nat}
    {state : M.BoundedState horizon} {player : Player}
    {move : Option (view.Act player)} :
    move ∈ view.boundedAvailableMovesAtState horizon state player ↔
      view.boundedLocallyLegalAtState horizon state player move := by
  rfl

/-- Repackage a legal bounded action as a legal unbounded action for the
underlying checkpoint state. -/
noncomputable def boundedActionToAction
    (view : M.RoundView) (horizon : Nat)
    (state : M.BoundedState horizon)
    (action : view.BoundedLegalAction horizon state) :
    {a : JointAction view.Act //
      JointActionLegal view.Act view.active M.terminal view.availableActions
        state.state a} := by
  classical
  have hcut : ¬ horizon ≤ state.depth := by
    intro hle
    exact action.2.1 (Or.inr hle)
  have hterm : ¬ M.terminal state.state := by
    intro h
    exact action.2.1 (Or.inl h)
  refine ⟨action.1, hterm, ?_⟩
  intro player
  have hlocal := action.2.2 player
  cases hmove : action.1 player with
  | none =>
      have hnot :
          player ∉ view.boundedActive horizon state := by
        simpa [hmove] using hlocal
      simpa [boundedActive, hcut] using hnot
  | some choice =>
      have hpair :
          player ∈ view.boundedActive horizon state ∧
            choice ∈ view.boundedAvailableActions horizon state player := by
        simpa [hmove] using hlocal
      exact ⟨by simpa [boundedActive, hcut] using hpair.1,
        by simpa [boundedAvailableActions, hcut] using hpair.2⟩

/-- Horizon-bounded round transition.  The bound is a presentation cutoff; each
round increments the counter by one. -/
noncomputable def boundedTransition
    (view : M.RoundView) (horizon : Nat)
    (state : M.BoundedState horizon)
    (action : view.BoundedLegalAction horizon state) :
    PMF (M.BoundedState horizon) :=
  (view.transition state.state
    (view.boundedActionToAction horizon state action)).map
    (fun next =>
      state.succ
        (by
          have hnot : ¬ horizon ≤ state.depth := by
            intro hle
            exact action.2.1 (Or.inr hle)
          exact Nat.lt_of_not_ge hnot)
        next)

@[simp] theorem boundedTransition_map_state
    (view : M.RoundView) (horizon : Nat)
    (state : M.BoundedState horizon)
    (action : view.BoundedLegalAction horizon state) :
    PMF.map (fun bounded => bounded.state)
        (view.boundedTransition horizon state action) =
      view.transition state.state
        (view.boundedActionToAction horizon state action) := by
  rw [boundedTransition]
  trans
      (view.transition state.state
        (view.boundedActionToAction horizon state action)).map id
  · rw [PMF.map_comp]
    congr
  · exact PMF.map_id _

/-- Supported bounded transitions increment the presentation depth by one. -/
theorem boundedTransition_support_depth
    (view : M.RoundView) (horizon : Nat)
    (state : M.BoundedState horizon)
    (action : view.BoundedLegalAction horizon state)
    {dst : M.BoundedState horizon}
    (hsupp : view.boundedTransition horizon state action dst ≠ 0) :
    dst.depth = state.depth + 1 := by
  have hmem :
      dst ∈ (view.boundedTransition horizon state action).support := by
    exact (PMF.mem_support_iff _ _).2 hsupp
  rw [boundedTransition] at hmem
  rcases (PMF.mem_support_map_iff _ _ _).mp hmem with
    ⟨next, _hnext, hdst⟩
  rw [← hdst]
  simp [BoundedState.succ]

/-- One realized bounded round. -/
structure BoundedStep (view : M.RoundView) (horizon : Nat) where
  src : M.BoundedState horizon
  act : view.BoundedLegalAction horizon src
  dst : M.BoundedState horizon
  support : view.boundedTransition horizon src act dst ≠ 0

namespace BoundedStep

variable {view : M.RoundView} {horizon : Nat}

/-- Player `player`'s realized local action, if any, in a step. -/
abbrev ownAction? (step : view.BoundedStep horizon) (player : Player) :
    Option (view.Act player) :=
  step.act.1 player

/-- Public observation emitted by a step. -/
abbrev publicObs (step : view.BoundedStep horizon) : M.Public :=
  M.publicView step.dst.state

/-- Private observation for a player emitted by a step. -/
abbrev privateObs (step : view.BoundedStep horizon) (player : Player) :
    M.Obs player :=
  M.observe player step.dst.state

end BoundedStep

section FiniteStep

variable (view : M.RoundView) (horizon : Nat)
variable [Fintype Player] [Fintype M.State]
variable [∀ player, Fintype (Option (view.Act player))]

/-- Finite legal-action carrier induced by finite optional action choices. -/
noncomputable instance instFintypeBoundedLegalAction
    (state : M.BoundedState horizon) :
    Fintype (view.BoundedLegalAction horizon state) := by
  classical
  unfold BoundedLegalAction
  infer_instance

private abbrev BoundedStepData :=
  Σ state : M.BoundedState horizon,
    view.BoundedLegalAction horizon state × M.BoundedState horizon

/-- Finite realized-step carrier induced by finite states and legal actions. -/
noncomputable instance instFintypeBoundedStep :
    Fintype (view.BoundedStep horizon) := by
  classical
  letI : Fintype (M.BoundedState horizon) := Machine.BoundedState.instFintype
  let e :
      view.BoundedStep horizon ≃
        {t : BoundedStepData view horizon //
          view.boundedTransition horizon t.1 t.2.1 t.2.2 ≠ 0} :=
    { toFun := fun step => ⟨⟨step.src, step.act, step.dst⟩, step.support⟩
      invFun := fun t =>
        { src := t.1.1
          act := t.1.2.1
          dst := t.1.2.2
          support := t.2 }
      left_inv := by
        intro step
        cases step
        rfl
      right_inv := by
        intro t
        cases t
        rfl }
  exact Fintype.ofEquiv _ e.symm

end FiniteStep

/-- Chaining predicate for a list of bounded round steps. -/
def StepChainFrom (view : M.RoundView) (horizon : Nat) :
    M.BoundedState horizon → List (view.BoundedStep horizon) → Prop
  | _, [] => True
  | state, step :: steps =>
      step.src = state ∧ view.StepChainFrom horizon step.dst steps

/-- Last bounded state reached by a list of chained bounded steps. -/
def lastStateFrom (view : M.RoundView) (horizon : Nat) :
    M.BoundedState horizon → List (view.BoundedStep horizon) →
      M.BoundedState horizon
  | state, [] => state
  | _, step :: steps => view.lastStateFrom horizon step.dst steps

theorem lastStateFrom_append_singleton
    (view : M.RoundView) (horizon : Nat)
    (state : M.BoundedState horizon)
    (steps : List (view.BoundedStep horizon))
    (step : view.BoundedStep horizon) :
    view.lastStateFrom horizon state (steps ++ [step]) = step.dst := by
  induction steps generalizing state with
  | nil =>
      simp [lastStateFrom]
  | cons head tail ih =>
      simp [lastStateFrom, ih]

theorem StepChainFrom.snoc
    {view : M.RoundView} {horizon : Nat}
    {state : M.BoundedState horizon}
    {steps : List (view.BoundedStep horizon)}
    (hchain : view.StepChainFrom horizon state steps)
    (step : view.BoundedStep horizon)
    (hsrc : step.src = view.lastStateFrom horizon state steps) :
    view.StepChainFrom horizon state (steps ++ [step]) := by
  induction steps generalizing state with
  | nil =>
      simp [StepChainFrom, lastStateFrom] at hsrc ⊢
      simpa using And.intro hsrc trivial
  | cons head tail ih =>
      rcases hchain with ⟨hsrc₀, htail⟩
      simpa [StepChainFrom, List.cons_append] using
        And.intro hsrc₀ (ih (state := head.dst) htail hsrc)

theorem StepChainFrom.left
    {view : M.RoundView} {horizon : Nat}
    {state : M.BoundedState horizon}
    {steps₁ steps₂ : List (view.BoundedStep horizon)}
    (hchain : view.StepChainFrom horizon state (steps₁ ++ steps₂)) :
    view.StepChainFrom horizon state steps₁ := by
  induction steps₁ generalizing state with
  | nil =>
      simp [StepChainFrom]
  | cons step steps ih =>
      rcases hchain with ⟨hsrc, htail⟩
      simpa [StepChainFrom, List.cons_append] using
        And.intro hsrc (ih (state := step.dst) htail)

theorem StepChainFrom.right
    {view : M.RoundView} {horizon : Nat}
    {state : M.BoundedState horizon}
    {steps₁ steps₂ : List (view.BoundedStep horizon)}
    (hchain : view.StepChainFrom horizon state (steps₁ ++ steps₂)) :
    view.StepChainFrom horizon
      (view.lastStateFrom horizon state steps₁) steps₂ := by
  induction steps₁ generalizing state with
  | nil =>
      simpa [StepChainFrom, lastStateFrom] using hchain
  | cons step steps ih =>
      rcases hchain with ⟨_hsrc, htail⟩
      simpa [StepChainFrom, lastStateFrom, List.cons_append] using
        ih (state := step.dst) htail

/-- Bundled finite history of realized bounded rounds from the initial bounded
state. -/
structure BoundedHistory (view : M.RoundView) (horizon : Nat) where
  steps : List (view.BoundedStep horizon)
  chain : view.StepChainFrom horizon (BoundedState.init M horizon) steps

namespace BoundedHistory

variable {view : M.RoundView} {horizon : Nat}

@[ext] theorem ext
    {h h' : view.BoundedHistory horizon}
    (hsteps : h.steps = h'.steps) :
    h = h' := by
  cases h
  cases h'
  cases hsteps
  rfl

/-- Empty bounded history at the initial bounded state. -/
def nil (view : M.RoundView) (horizon : Nat) :
    view.BoundedHistory horizon :=
  ⟨[], trivial⟩

/-- Last bounded state of a bounded history. -/
def lastState (h : view.BoundedHistory horizon) :
    M.BoundedState horizon :=
  view.lastStateFrom horizon (BoundedState.init M horizon) h.steps

/-- Append one realized step to a bounded history. -/
def snoc (h : view.BoundedHistory horizon)
    (action : view.BoundedLegalAction horizon h.lastState)
    (dst : M.BoundedState horizon)
    (support : view.boundedTransition horizon h.lastState action dst ≠ 0) :
    view.BoundedHistory horizon :=
  { steps := h.steps ++ [⟨h.lastState, action, dst, support⟩]
    chain := StepChainFrom.snoc h.chain
      ⟨h.lastState, action, dst, support⟩ rfl }

/-- Append a concrete realized step whose source matches the current endpoint. -/
def appendStep (h : view.BoundedHistory horizon)
    (step : view.BoundedStep horizon)
    (hsrc : step.src = h.lastState) :
    view.BoundedHistory horizon :=
  { steps := h.steps ++ [step]
    chain := StepChainFrom.snoc h.chain step hsrc }

@[simp] theorem steps_nil :
    (nil view horizon).steps = [] := rfl

@[simp] theorem lastState_nil :
    (nil view horizon).lastState = BoundedState.init M horizon := rfl

@[simp] theorem steps_snoc
    (h : view.BoundedHistory horizon)
    (action : view.BoundedLegalAction horizon h.lastState)
    (dst : M.BoundedState horizon)
    (support : view.boundedTransition horizon h.lastState action dst ≠ 0) :
    (h.snoc action dst support).steps =
      h.steps ++ [⟨h.lastState, action, dst, support⟩] := rfl

@[simp] theorem lastState_snoc
    (h : view.BoundedHistory horizon)
    (action : view.BoundedLegalAction horizon h.lastState)
    (dst : M.BoundedState horizon)
    (support : view.boundedTransition horizon h.lastState action dst ≠ 0) :
    (h.snoc action dst support).lastState = dst := by
  simpa [lastState, snoc] using
    view.lastStateFrom_append_singleton horizon
      (BoundedState.init M horizon) h.steps
      ⟨h.lastState, action, dst, support⟩

@[simp] theorem lastState_appendStep
    (h : view.BoundedHistory horizon)
    (step : view.BoundedStep horizon)
    (hsrc : step.src = h.lastState) :
    (h.appendStep step hsrc).lastState = step.dst := by
  simpa [lastState, appendStep] using
    view.lastStateFrom_append_singleton horizon
      (BoundedState.init M horizon) h.steps step

/-- Prefix relation on realized bounded histories. -/
def IsPrefix (h h' : view.BoundedHistory horizon) : Prop :=
  ∃ suffix : List (view.BoundedStep horizon), h'.steps = h.steps ++ suffix

/-- Terminality of the current endpoint of a bounded history. -/
def IsTerminal (h : view.BoundedHistory horizon) : Prop :=
  view.boundedTerminal horizon h.lastState

theorem not_isTerminal_of_legalAction
    (h : view.BoundedHistory horizon)
    (action : view.BoundedLegalAction horizon h.lastState) :
    ¬ h.IsTerminal := by
  intro hterm
  exact action.2.1 hterm

end BoundedHistory

/-- Along a bounded round chain, the presentation depth is the starting depth
plus the number of realized rounds. -/
theorem lastState_depth_from
    (view : M.RoundView) (horizon : Nat) :
    ∀ {start : M.BoundedState horizon}
      {steps : List (view.BoundedStep horizon)},
      view.StepChainFrom horizon start steps →
      (view.lastStateFrom horizon start steps).depth =
        start.depth + steps.length
  | start, [], _hchain => by
      simp [lastStateFrom]
  | start, step :: steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      let action : view.BoundedLegalAction horizon start :=
        hsrc ▸ step.act
      have hsupp :
          view.boundedTransition horizon start action step.dst ≠ 0 := by
        subst hsrc
        simpa [action] using step.support
      have hstep :
          step.dst.depth = start.depth + 1 :=
        view.boundedTransition_support_depth horizon start action hsupp
      have htailLen :
          (view.lastStateFrom horizon step.dst steps).depth =
            step.dst.depth + steps.length :=
        lastState_depth_from
          (view := view) (horizon := horizon) htail
      calc
        (view.lastStateFrom horizon start (step :: steps)).depth =
          (view.lastStateFrom horizon step.dst steps).depth := rfl
        _ = step.dst.depth + steps.length := htailLen
        _ = (start.depth + 1) + steps.length := by rw [hstep]
        _ = start.depth + (step :: steps).length := by
          simp [Nat.add_assoc, Nat.add_comm]

/-- In a bounded round history, the presentation depth is exactly the number
of realized rounds. -/
theorem history_depth
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon) :
    h.lastState.depth = h.steps.length := by
  have hlen :=
    view.lastState_depth_from (horizon := horizon) h.chain
  simpa [BoundedHistory.lastState] using hlen

/-- Every bounded round history has length at most its presentation horizon. -/
theorem history_length_le
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon) :
    h.steps.length ≤ horizon := by
  rw [← view.history_depth horizon h]
  exact h.lastState.depth_le

/-- Local player-visible events: own actions and resulting observations. -/
inductive PlayerEvent
    (view : M.RoundView) (player : Player) where
  | act : view.Act player → PlayerEvent view player
  | obs : M.Obs player → M.Public → PlayerEvent view player

namespace PlayerEvent

variable {view : M.RoundView} {player : Player}

/-- Extract the public component carried by an event, if any. -/
def publicPart : PlayerEvent view player → Option M.Public
  | .act _ => none
  | .obs _ pub => some pub

/-- Extract the player's own action component carried by an event, if any. -/
def actionPart : PlayerEvent view player → Option (view.Act player)
  | .act action => some action
  | .obs _ _ => none

/-- Extract the full private/public observation component carried by an event,
if any. -/
def observationPart :
    PlayerEvent view player → Option (M.Obs player × M.Public)
  | .act _ => none
  | .obs priv pub => some (priv, pub)

/-- Finite player events from finite native actions and observations. -/
@[reducible]
noncomputable def instFintype
    [Fintype (view.Act player)]
    [Fintype (M.Obs player)]
    [Fintype M.Public] :
    Fintype (PlayerEvent view player) := by
  classical
  exact
    Fintype.ofEquiv
      (Sum (view.Act player) (M.Obs player × M.Public))
      { toFun := fun event =>
          match event with
          | Sum.inl action => PlayerEvent.act action
          | Sum.inr payload => PlayerEvent.obs payload.1 payload.2
        invFun := fun event =>
          match event with
          | .act action => Sum.inl action
          | .obs priv pub => Sum.inr (priv, pub)
        left_inv := by
          intro event
          cases event <;> rfl
        right_inv := by
          intro event
          cases event <;> rfl }

end PlayerEvent

/-- Player information states for a native round view. -/
abbrev InfoState (view : M.RoundView) (player : Player) : Type :=
  List (PlayerEvent view player)

namespace InfoState

variable {view : M.RoundView} {player : Player}

/-- Last element of a list, as an `Option`. -/
def last? {α : Type} : List α → Option α
  | [] => none
  | [x] => some x
  | _ :: xs => last? xs

@[simp] theorem last?_append_singleton {α : Type} (xs : List α) (x : α) :
    last? (xs ++ [x]) = some x := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      cases ys with
      | nil => rfl
      | cons z zs =>
          simpa [last?] using ih

/-- Observation events extracted from an information state. -/
def observationEvents (s : view.InfoState player) :
    List (M.Obs player × M.Public) :=
  s.filterMap (PlayerEvent.observationPart (view := view) (player := player))

/-- Latest private/public observation recorded in an information state. -/
def latestObservation? (s : view.InfoState player) :
    Option (M.Obs player × M.Public) :=
  last? (observationEvents s)

@[simp] theorem observationEvents_nil :
    observationEvents ([] : view.InfoState player) = [] := rfl

@[simp] theorem latestObservation?_nil :
    latestObservation? ([] : view.InfoState player) = none := rfl

theorem latestObservation?_append_obs
    (s : view.InfoState player) (priv : M.Obs player)
    (pub : M.Public) :
    latestObservation? (s ++ [PlayerEvent.obs priv pub]) =
      some (priv, pub) := by
  unfold latestObservation? observationEvents
  rw [List.filterMap_append]
  change last?
      (List.filterMap PlayerEvent.observationPart s ++ [(priv, pub)]) =
    some (priv, pub)
  exact last?_append_singleton _ _

theorem latestObservation?_append_act_obs
    (s : view.InfoState player) (action : view.Act player)
    (priv : M.Obs player) (pub : M.Public) :
    latestObservation?
      (s ++ [PlayerEvent.act action, PlayerEvent.obs priv pub]) =
      some (priv, pub) := by
  unfold latestObservation? observationEvents
  rw [List.filterMap_append]
  change last?
      (List.filterMap PlayerEvent.observationPart s ++ [(priv, pub)]) =
    some (priv, pub)
  exact last?_append_singleton _ _

end InfoState

namespace BoundedStep

variable {view : M.RoundView} {horizon : Nat}
variable {player : Player}

/-- Player `player`'s visible event sequence generated by one realized step. -/
def playerView (step : view.BoundedStep horizon) (player : Player) :
    List (PlayerEvent view player) :=
  match step.ownAction? player with
  | some action =>
      [.act action, .obs (step.privateObs player) step.publicObs]
  | none => [.obs (step.privateObs player) step.publicObs]

/-- If a player acts in a realized bounded step, that action is the first
player-visible event for the step, followed by the resulting observation. -/
theorem playerView_of_ownAction?_eq_some
    (step : view.BoundedStep horizon) (player : Player)
    {action : view.Act player}
    (hact : step.ownAction? player = some action) :
    step.playerView player =
      [.act action, .obs (step.privateObs player) step.publicObs] := by
  simp [playerView, hact]

/-- If a player does not act in a realized bounded step, the step contributes
only the resulting observation to that player's view. -/
theorem playerView_of_ownAction?_eq_none
    (step : view.BoundedStep horizon) (player : Player)
    (hact : step.ownAction? player = none) :
    step.playerView player =
      [.obs (step.privateObs player) step.publicObs] := by
  simp [playerView, hact]

theorem latestObservation?_append_playerView
    (s : view.InfoState player) (step : view.BoundedStep horizon) :
    InfoState.latestObservation? (s ++ step.playerView player) =
      some (step.privateObs player, step.publicObs) := by
  cases hact : step.ownAction? player with
  | none =>
      simp [playerView, hact, InfoState.latestObservation?_append_obs]
  | some action =>
      simp [playerView, hact, InfoState.latestObservation?_append_act_obs]

/-- One realized bounded step contributes exactly one private/public
observation to a player's information state. -/
theorem observationEvents_playerView
    (step : view.BoundedStep horizon) (player : Player) :
    InfoState.observationEvents (step.playerView player) =
      [(step.privateObs player, step.publicObs)] := by
  cases hact : step.ownAction? player with
  | none =>
      simp [playerView, hact, InfoState.observationEvents,
        PlayerEvent.observationPart]
  | some action =>
      simp [playerView, hact, InfoState.observationEvents,
        PlayerEvent.observationPart]

/-- One bounded step contributes at most two player-visible events: the
player's own action, if any, and the resulting observation. -/
theorem playerView_length_le_two
    (step : view.BoundedStep horizon) (player : Player) :
    (step.playerView player).length ≤ 2 := by
  cases hact : step.ownAction? player with
  | none =>
      simp [playerView, hact]
  | some action =>
      simp [playerView, hact]

end BoundedStep

namespace BoundedHistory

variable {view : M.RoundView} {horizon : Nat}

/-- Public observations induced by a list of realized bounded steps. -/
def publicViewFrom : List (view.BoundedStep horizon) → List M.Public
  | [] => []
  | step :: steps => step.publicObs :: publicViewFrom steps

/-- Player `player`'s information state induced by a list of realized bounded
steps. -/
def playerViewFrom (player : Player) :
    List (view.BoundedStep horizon) → view.InfoState player
  | [] => []
  | step :: steps => step.playerView player ++ playerViewFrom player steps

/-- Observation events induced by a list of realized bounded steps. -/
theorem observationEvents_playerViewFrom
    (player : Player) :
    ∀ steps : List (view.BoundedStep horizon),
      InfoState.observationEvents
          (playerViewFrom (view := view) player steps) =
        steps.map fun step => (step.privateObs player, step.publicObs)
  | [] => by
      simp [playerViewFrom, InfoState.observationEvents]
  | step :: steps => by
      rw [playerViewFrom]
      rw [InfoState.observationEvents, List.filterMap_append]
      change
        InfoState.observationEvents (step.playerView player) ++
          InfoState.observationEvents (playerViewFrom player steps) =
            (step.privateObs player, step.publicObs) ::
              steps.map (fun step => (step.privateObs player, step.publicObs))
      rw [BoundedStep.observationEvents_playerView]
      rw [observationEvents_playerViewFrom player steps]
      rfl

/-- Public observation history of a bounded history. -/
def publicView (h : view.BoundedHistory horizon) : List M.Public :=
  publicViewFrom h.steps

/-- Player `player`'s information state along a bounded history. -/
def playerView (h : view.BoundedHistory horizon) (player : Player) :
    view.InfoState player :=
  playerViewFrom player h.steps

theorem playerViewFrom_append_singleton
    (player : Player) (steps : List (view.BoundedStep horizon))
    (step : view.BoundedStep horizon) :
    playerViewFrom (view := view) player (steps ++ [step]) =
      playerViewFrom (view := view) player steps ++ step.playerView player := by
  induction steps with
  | nil =>
      simp [playerViewFrom]
  | cons head tail ih =>
      simp [playerViewFrom, ih, List.append_assoc]

/-- A player's view contains one observation event for each realized bounded
step. Own actions may add action events, but they do not change this count. -/
theorem observationEvents_playerViewFrom_length
    (player : Player) :
    ∀ steps : List (view.BoundedStep horizon),
      (InfoState.observationEvents
          (playerViewFrom (view := view) player steps)).length =
        steps.length
  | [] => by
      simp [playerViewFrom, InfoState.observationEvents]
  | step :: steps => by
      rw [playerViewFrom]
      rw [InfoState.observationEvents, List.filterMap_append]
      have htail :=
        observationEvents_playerViewFrom_length player steps
      change
        (InfoState.observationEvents (step.playerView player) ++
            InfoState.observationEvents
              (playerViewFrom player steps)).length =
          (step :: steps).length
      rw [BoundedStep.observationEvents_playerView, List.length_append,
        htail]
      simp [Nat.add_comm]

/-- A player's bounded-history view contains one observation event for each
realized bounded step. -/
theorem observationEvents_playerView_length
    (h : view.BoundedHistory horizon) (player : Player) :
    (InfoState.observationEvents (h.playerView player)).length =
      h.steps.length := by
  simpa [playerView] using
    observationEvents_playerViewFrom_length
      (view := view) (horizon := horizon) player h.steps

/-- A player's raw information-state list has length at most twice the number
of realized bounded steps. -/
theorem playerViewFrom_length_le_two_mul
    (player : Player) :
    ∀ steps : List (view.BoundedStep horizon),
      (playerViewFrom (view := view) player steps).length ≤
        2 * steps.length
  | [] => by
      simp [playerViewFrom]
  | step :: steps => by
      rw [playerViewFrom, List.length_append]
      have hstep :
          (step.playerView player).length ≤ 2 :=
        BoundedStep.playerView_length_le_two step player
      have htail :
          (playerViewFrom (view := view) player steps).length ≤
            2 * steps.length :=
        playerViewFrom_length_le_two_mul player steps
      have hsum :
          (step.playerView player).length +
              (playerViewFrom (view := view) player steps).length ≤
            2 + 2 * steps.length :=
        Nat.add_le_add hstep htail
      have htarget : 2 + 2 * steps.length = 2 * (step :: steps).length := by
        simp
        omega
      exact hsum.trans_eq htarget

/-- A player's bounded-history information state has length at most twice the
presentation horizon. -/
theorem playerView_length_le_two_mul_horizon
    (h : view.BoundedHistory horizon) (player : Player) :
    (h.playerView player).length ≤ 2 * horizon := by
  unfold playerView
  have hview :
      (playerViewFrom (view := view) player h.steps).length ≤
        2 * h.steps.length :=
    playerViewFrom_length_le_two_mul
      (view := view) (horizon := horizon) player h.steps
  have hsteps : 2 * h.steps.length ≤ 2 * horizon :=
    Nat.mul_le_mul_left 2 (view.history_length_le horizon h)
  exact hview.trans hsteps

/-- Equal player information states have equal endpoint presentation depth,
because each realized bounded step contributes exactly one observation event. -/
theorem depth_eq_of_playerView_eq
    (h h' : view.BoundedHistory horizon) (player : Player)
    (hinfo : h.playerView player = h'.playerView player) :
    h.lastState.depth = h'.lastState.depth := by
  have hobsLen :
      (InfoState.observationEvents (h.playerView player)).length =
        (InfoState.observationEvents (h'.playerView player)).length := by
    rw [hinfo]
  have hsteps :
      h.steps.length = h'.steps.length := by
    simpa [observationEvents_playerView_length] using hobsLen
  calc
    h.lastState.depth = h.steps.length := view.history_depth horizon h
    _ = h'.steps.length := hsteps
    _ = h'.lastState.depth := (view.history_depth horizon h').symm

/-- Appending a concrete realized step appends exactly that step's player view. -/
theorem playerView_appendStep
    (h : view.BoundedHistory horizon)
    (player : Player)
    (step : view.BoundedStep horizon)
    (hsrc : step.src = h.lastState) :
    (h.appendStep step hsrc).playerView player =
      h.playerView player ++ step.playerView player := by
  simpa [playerView, appendStep] using
    playerViewFrom_append_singleton
      (view := view) (horizon := horizon) player h.steps step

/-- Appending a supported legal action appends exactly the resulting realized
step's player-visible events. -/
theorem playerView_snoc
    (h : view.BoundedHistory horizon)
    (player : Player)
    (action : view.BoundedLegalAction horizon h.lastState)
    (dst : M.BoundedState horizon)
    (support : view.boundedTransition horizon h.lastState action dst ≠ 0) :
    (h.snoc action dst support).playerView player =
      h.playerView player ++
        (BoundedStep.playerView
          (view := view) (horizon := horizon)
          ⟨h.lastState, action, dst, support⟩ player) := by
  simpa [snoc, appendStep] using
    playerView_appendStep
      (view := view) (horizon := horizon) h player
      ⟨h.lastState, action, dst, support⟩ rfl

/-- If player `player` acts in the realized step appended to a history, that
step appends the selected action and then the resulting observation to the
player's information state. -/
theorem playerView_snoc_of_ownAction?_eq_some
    (h : view.BoundedHistory horizon)
    (player : Player)
    (action : view.BoundedLegalAction horizon h.lastState)
    (dst : M.BoundedState horizon)
    (support : view.boundedTransition horizon h.lastState action dst ≠ 0)
    {own : view.Act player}
    (hact :
      (⟨h.lastState, action, dst, support⟩ :
        view.BoundedStep horizon).ownAction? player = some own) :
    (h.snoc action dst support).playerView player =
      h.playerView player ++
        [.act own,
          .obs (M.observe player dst.state) (M.publicView dst.state)] := by
  rw [playerView_snoc]
  rw [BoundedStep.playerView_of_ownAction?_eq_some
    (step := ⟨h.lastState, action, dst, support⟩)
    (player := player) hact]

/-- Appending a concrete realized step updates the latest observation to the
destination observation of that step. -/
theorem latestObservation?_playerView_appendStep
    (h : view.BoundedHistory horizon)
    (player : Player)
    (step : view.BoundedStep horizon)
    (hsrc : step.src = h.lastState) :
    InfoState.latestObservation?
        ((h.appendStep step hsrc).playerView player) =
      some (step.privateObs player, step.publicObs) := by
  rw [playerView_appendStep]
  exact BoundedStep.latestObservation?_append_playerView
    (h.playerView player) step

/-- In a nonempty bounded native history, the latest private/public
observation is the observation of the endpoint machine state. -/
theorem latestObservation?_history_of_ne_nil
    (h : view.BoundedHistory horizon) (player : Player)
    (hne : h.steps ≠ []) :
    InfoState.latestObservation? (h.playerView player) =
      some (M.observe player h.lastState.state,
        M.publicView h.lastState.state) := by
  cases h with
  | mk steps chain =>
      induction steps using List.reverseRecOn with
      | nil =>
          exact False.elim (hne rfl)
      | append_singleton steps step ih =>
          let hprefix : view.BoundedHistory horizon :=
            { steps := steps
              chain := StepChainFrom.left
                (view := view) (steps₁ := steps) (steps₂ := [step]) chain }
          have hright :
              view.StepChainFrom horizon
                (view.lastStateFrom horizon
                  (BoundedState.init M horizon) steps)
                [step] :=
            StepChainFrom.right
              (view := view) (steps₁ := steps) (steps₂ := [step]) chain
          have hsrc : step.src = hprefix.lastState := by
            simpa [hprefix, BoundedHistory.lastState, StepChainFrom] using
              hright.1
          let hfull : view.BoundedHistory horizon :=
            hprefix.appendStep step hsrc
          have hEq :
              ({ steps := steps ++ [step], chain := chain } :
                  view.BoundedHistory horizon) = hfull := by
            ext
            rfl
          rw [hEq]
          unfold hfull
          simpa using
            latestObservation?_playerView_appendStep
              (view := view) hprefix player step hsrc

end BoundedHistory

/-- The set of optional moves available to a player at the endpoint of a
bounded history. -/
def boundedAvailableMoves
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon) (player : Player) :
    Set (Option (view.Act player)) :=
  view.boundedAvailableMovesAtState horizon h.lastState player

theorem mem_boundedAvailableMoves_iff
    {view : M.RoundView} {horizon : Nat}
    {h : view.BoundedHistory horizon} {player : Player}
    {move : Option (view.Act player)} :
    move ∈ view.boundedAvailableMoves horizon h player ↔
      view.boundedLocallyLegalAtState horizon h.lastState player move := by
  rfl

/-- At every bounded history, each player has at least one legal optional
move.  At terminal/cutoff states this move is `none`; otherwise it is the
player's component of any legal joint action. -/
theorem boundedAvailableMoves_nonempty
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon) (player : Player) :
    ∃ move : Option (view.Act player),
      move ∈ view.boundedAvailableMoves horizon h player := by
  classical
  by_cases hterm : view.boundedTerminal horizon h.lastState
  · refine ⟨none, ?_⟩
    rw [mem_boundedAvailableMoves_iff]
    cases hterm with
    | inl hmachine =>
        simp [boundedLocallyLegalAtState, boundedActive,
          view.terminal_active_eq_empty hmachine]
    | inr hcut =>
        simp [boundedLocallyLegalAtState, boundedActive, hcut]
  · rcases view.nonterminal_exists_legal
      (state := h.lastState.state)
      (by
        intro hmachine
        exact hterm (Or.inl hmachine)) with ⟨action, haction⟩
    have hcut : ¬ horizon ≤ h.lastState.depth := by
      intro hle
      exact hterm (Or.inr hle)
    let boundedAction : JointAction view.Act := action
    have hbounded :
        JointActionLegal view.Act (view.boundedActive horizon)
          (view.boundedTerminal horizon)
          (view.boundedAvailableActions horizon) h.lastState boundedAction := by
      refine ⟨hterm, ?_⟩
      intro who
      have hlocal := haction.2 who
      cases hmove : action who with
      | none =>
          have hnot : who ∉ view.active h.lastState.state := by
            simpa [hmove] using hlocal
          simpa [boundedAction, boundedActive, hcut, hmove] using hnot
      | some choice =>
          have hpair :
              who ∈ view.active h.lastState.state ∧
                choice ∈ view.availableActions h.lastState.state who := by
            simpa [hmove] using hlocal
          simpa [boundedAction, boundedActive, boundedAvailableActions,
            hcut, hmove] using hpair
    exact ⟨boundedAction player, by
      rw [mem_boundedAvailableMoves_iff]
      cases hmove : boundedAction player with
      | none =>
          simpa [boundedLocallyLegalAtState, hmove] using hbounded.2 player
      | some action =>
          simpa [boundedLocallyLegalAtState, hmove] using hbounded.2 player⟩

/-- A round view has observable menus when a player's current information
state determines that player's legal optional moves. Native legal strategies
already quantify over all histories realizing the same information state; this
predicate says those histories agree on the menu. -/
def MenusObservable (view : M.RoundView) (horizon : Nat) : Prop :=
  ∀ player (h h' : view.BoundedHistory horizon),
    h.playerView player = h'.playerView player →
      view.boundedAvailableMoves horizon h player =
        view.boundedAvailableMoves horizon h' player

/-- The legal optional moves associated with an information state. -/
def boundedAvailableMovesAtInfoState
    (view : M.RoundView) (horizon : Nat)
    (player : Player) (info : view.InfoState player) :
    Set (Option (view.Act player)) :=
  { move |
    ∃ h : view.BoundedHistory horizon,
      h.playerView player = info ∧
        move ∈ view.boundedAvailableMoves horizon h player }

theorem mem_boundedAvailableMovesAtInfoState_of_history
    {view : M.RoundView} {horizon : Nat} {player : Player}
    (h : view.BoundedHistory horizon) {move : Option (view.Act player)}
    (hmove : move ∈ view.boundedAvailableMoves horizon h player) :
    move ∈ view.boundedAvailableMovesAtInfoState horizon player
      (h.playerView player) :=
  ⟨h, rfl, hmove⟩

/-- Information states realized by at least one native bounded history. -/
def ReachableInfoState
    (view : M.RoundView) (horizon : Nat) (player : Player) : Type :=
  { info : view.InfoState player //
    ∃ h : view.BoundedHistory horizon, h.playerView player = info }

/-- The reachable information state induced by a realized native bounded
history. -/
def reachableInfoStateOfHistory
    (view : M.RoundView) (horizon : Nat) (player : Player)
    (h : view.BoundedHistory horizon) :
    view.ReachableInfoState horizon player :=
  ⟨h.playerView player, h, rfl⟩

@[simp] theorem reachableInfoStateOfHistory_val
    (view : M.RoundView) (horizon : Nat) (player : Player)
    (h : view.BoundedHistory horizon) :
    (view.reachableInfoStateOfHistory horizon player h).1 =
      h.playerView player := rfl

section FiniteHistory

variable (view : M.RoundView) (horizon : Nat)
variable [Fintype Player] [Fintype M.State]
variable [∀ player, Fintype (Option (view.Act player))]

/-- Finite-history enumeration from the built-in bounded presentation depth. -/
@[reducible]
noncomputable def instFintypeBoundedHistory :
    Fintype (view.BoundedHistory horizon) := by
  classical
  letI : Fintype (view.BoundedStep horizon) :=
    instFintypeBoundedStep view horizon
  letI : DecidableEq (view.BoundedStep horizon) := Classical.decEq _
  let enum :=
    Math.BoundedLists.listsUpToLength
      (Finset.univ : Finset (view.BoundedStep horizon)) horizon
  let f :
      view.BoundedHistory horizon →
        {xs : List (view.BoundedStep horizon) // xs ∈ enum} := fun h =>
    ⟨h.steps,
      Math.BoundedLists.mem_listsUpToLength_of_forall_mem
        (s := (Finset.univ : Finset (view.BoundedStep horizon)))
        (view.history_length_le horizon h) (by intro x hx; simp)⟩
  have hf : Function.Injective f := by
    intro h h' hh
    apply BoundedHistory.ext
    exact congrArg Subtype.val hh
  haveI : Finite {xs : List (view.BoundedStep horizon) // xs ∈ enum} :=
    Finite.of_fintype _
  haveI : Finite (view.BoundedHistory horizon) :=
    Finite.of_injective f hf
  exact Fintype.ofFinite (view.BoundedHistory horizon)

noncomputable instance instFintypeReachableInfoState
    (player : Player) :
    Fintype (view.ReachableInfoState horizon player) := by
  classical
  letI : Fintype (view.BoundedHistory horizon) :=
    view.instFintypeBoundedHistory horizon
  let f :
      view.BoundedHistory horizon →
        view.ReachableInfoState horizon player := fun h =>
    view.reachableInfoStateOfHistory horizon player h
  have hf : Function.Surjective f := by
    intro info
    rcases info.2 with ⟨h, hinfo⟩
    refine ⟨h, ?_⟩
    apply Subtype.ext
    exact hinfo
  haveI : Finite (view.ReachableInfoState horizon player) :=
    Finite.of_surjective f hf
  exact Fintype.ofFinite (view.ReachableInfoState horizon player)

end FiniteHistory

section FiniteInfoState

variable (view : M.RoundView) (horizon : Nat)

/-- Finite information-state enumeration from a finite player-visible event
alphabet. This avoids requiring the whole machine state to be finite, which is
important for graph machines whose raw store carrier is intentionally not a
finite type. -/
@[reducible]
noncomputable def instFintypeReachableInfoStateOfFinitePlayerEvent
    (player : Player)
    [Fintype (PlayerEvent view player)] :
    Fintype (view.ReachableInfoState horizon player) := by
  classical
  letI : DecidableEq (PlayerEvent view player) := Classical.decEq _
  let enum :=
    Math.BoundedLists.listsUpToLength
      (Finset.univ : Finset (PlayerEvent view player)) (2 * horizon)
  let f :
      view.ReachableInfoState horizon player →
        {xs : List (PlayerEvent view player) // xs ∈ enum} := fun info =>
    ⟨info.1,
      by
        rcases info.2 with ⟨h, hinfo⟩
        rw [← hinfo]
        exact
          Math.BoundedLists.mem_listsUpToLength_of_forall_mem
            (s := (Finset.univ : Finset (PlayerEvent view player)))
            (BoundedHistory.playerView_length_le_two_mul_horizon
              (view := view) (horizon := horizon) h player)
            (by intro event hevent; simp)⟩
  have hf : Function.Injective f := by
    intro left right h
    apply Subtype.ext
    exact
      congrArg
        (fun x : {xs : List (PlayerEvent view player) // xs ∈ enum} =>
          (x : List (PlayerEvent view player))) h
  haveI :
      Finite {xs : List (PlayerEvent view player) // xs ∈ enum} :=
    Finite.of_fintype _
  haveI : Finite (view.ReachableInfoState horizon player) :=
    Finite.of_injective f hf
  exact Fintype.ofFinite (view.ReachableInfoState horizon player)

end FiniteInfoState

/-- Pure strategy over reachable native information states. -/
abbrev ReachablePureStrategy
    (view : M.RoundView) (horizon : Nat) (player : Player) : Type :=
  view.ReachableInfoState horizon player → Option (view.Act player)

/-- Behavioral strategy over reachable native information states. -/
abbrev ReachableBehavioralStrategy
    (view : M.RoundView) (horizon : Nat) (player : Player) : Type :=
  view.ReachableInfoState horizon player → PMF (Option (view.Act player))

/-- Joint reachable pure strategy profile. -/
abbrev ReachablePureProfile (view : M.RoundView) (horizon : Nat) : Type :=
  ∀ player, view.ReachablePureStrategy horizon player

/-- Joint reachable behavioral strategy profile. -/
abbrev ReachableBehavioralProfile (view : M.RoundView) (horizon : Nat) : Type :=
  ∀ player, view.ReachableBehavioralStrategy horizon player

/-- A reachable pure strategy is legal if it chooses an available move at every
realizing bounded history. -/
def IsLegalReachablePureStrategy
    (view : M.RoundView) (horizon : Nat)
    (player : Player) (σ : view.ReachablePureStrategy horizon player) :
    Prop :=
  ∀ h : view.BoundedHistory horizon,
    σ (view.reachableInfoStateOfHistory horizon player h) ∈
      view.boundedAvailableMoves horizon h player

/-- A reachable behavioral strategy is legal if its support stays within the
available move set at every realizing bounded history. -/
def IsLegalReachableBehavioralStrategy
    (view : M.RoundView) (horizon : Nat)
    (player : Player)
    (σ : view.ReachableBehavioralStrategy horizon player) : Prop :=
  ∀ (h : view.BoundedHistory horizon) {move : Option (view.Act player)},
    move ∈
      (σ (view.reachableInfoStateOfHistory horizon player h)).support →
      move ∈ view.boundedAvailableMoves horizon h player

/-- The subtype of legal reachable pure strategies for a player. -/
abbrev BoundedPureStrategy
    (view : M.RoundView) (horizon : Nat) (player : Player) : Type :=
  { σ : view.ReachablePureStrategy horizon player //
    view.IsLegalReachablePureStrategy horizon player σ }

/-- The subtype of legal reachable behavioral strategies for a player. -/
abbrev BoundedBehavioralStrategy
    (view : M.RoundView) (horizon : Nat) (player : Player) : Type :=
  { σ : view.ReachableBehavioralStrategy horizon player //
    view.IsLegalReachableBehavioralStrategy horizon player σ }

/-- A profile of legal reachable pure strategies. -/
abbrev BoundedPureProfile (view : M.RoundView) (horizon : Nat) : Type :=
  ∀ player, view.BoundedPureStrategy horizon player

/-- A profile of legal reachable behavioral strategies. -/
abbrev BoundedBehavioralProfile (view : M.RoundView) (horizon : Nat) : Type :=
  ∀ player, view.BoundedBehavioralStrategy horizon player

/-- Forget the legality proofs on a legal reachable pure profile. -/
abbrev BoundedPureProfile.toProfile
    {view : M.RoundView} {horizon : Nat}
    (σ : view.BoundedPureProfile horizon) :
    view.ReachablePureProfile horizon :=
  fun player => (σ player).1

/-- Forget the legality proofs on a legal reachable behavioral profile. -/
abbrev BoundedBehavioralProfile.toProfile
    {view : M.RoundView} {horizon : Nat}
    (σ : view.BoundedBehavioralProfile horizon) :
    view.ReachableBehavioralProfile horizon :=
  fun player => (σ player).1

section FiniteStrategy

variable (view : M.RoundView) (horizon : Nat)
variable [Fintype Player] [Fintype M.State]
variable [∀ player, Fintype (Option (view.Act player))]

noncomputable instance instFintypeReachablePureStrategy
    (player : Player) :
    Fintype (view.ReachablePureStrategy horizon player) := by
  classical
  letI : Fintype (view.ReachableInfoState horizon player) :=
    view.instFintypeReachableInfoState horizon player
  dsimp [ReachablePureStrategy]
  infer_instance

noncomputable instance instFintypeBoundedPureStrategy
    (player : Player) :
    Fintype (view.BoundedPureStrategy horizon player) := by
  classical
  dsimp [BoundedPureStrategy]
  infer_instance

noncomputable instance instFintypeBoundedPureProfile :
    Fintype (view.BoundedPureProfile horizon) := by
  classical
  dsimp [BoundedPureProfile]
  infer_instance

end FiniteStrategy

/-- Lift a pure reachable profile to a behavioral reachable profile. -/
noncomputable def pureToBehavioral
    (view : M.RoundView) (horizon : Nat)
    (σ : view.ReachablePureProfile horizon) :
    view.ReachableBehavioralProfile horizon :=
  fun player info => PMF.pure (σ player info)

@[simp] theorem pureToBehavioral_apply
    (view : M.RoundView) (horizon : Nat)
    (σ : view.ReachablePureProfile horizon)
    (player : Player) (info : view.ReachableInfoState horizon player) :
    view.pureToBehavioral horizon σ player info =
      PMF.pure (σ player info) := rfl

theorem legalBehavioral_of_legalPure
    {view : M.RoundView} {horizon : Nat}
    (σ : view.ReachablePureProfile horizon)
    (hσ : ∀ player,
      view.IsLegalReachablePureStrategy horizon player (σ player)) :
    ∀ player,
      view.IsLegalReachableBehavioralStrategy horizon player
        ((view.pureToBehavioral horizon σ) player) := by
  intro player h move hmove
  rw [pureToBehavioral_apply] at hmove
  rw [PMF.support_pure, Set.mem_singleton_iff] at hmove
  subst hmove
  exact hσ player h

/-- Lift a legal pure profile to a legal behavioral profile. -/
noncomputable def legalPureToBehavioral
    (view : M.RoundView) (horizon : Nat)
    (σ : view.BoundedPureProfile horizon) :
    view.BoundedBehavioralProfile horizon :=
  fun player =>
    ⟨view.pureToBehavioral horizon σ.toProfile player,
      (legalBehavioral_of_legalPure
        (view := view) (horizon := horizon) σ.toProfile
        (fun p => (σ p).2)) player⟩

namespace BoundedHistory

variable {view : M.RoundView} {horizon : Nat}

/-- Total history extension by a legal action and candidate destination. If the
transition mass is zero, the history is left unchanged; this branch contributes
zero mass inside the induced PMF kernels. -/
noncomputable def extendByOutcome
    (h : view.BoundedHistory horizon)
    (action : view.BoundedLegalAction horizon h.lastState)
    (dst : M.BoundedState horizon) :
    view.BoundedHistory horizon :=
  if hsupp : view.boundedTransition horizon h.lastState action dst ≠ 0 then
    h.snoc action dst hsupp
  else h

theorem extendByOutcome_of_support
    (h : view.BoundedHistory horizon)
    (action : view.BoundedLegalAction horizon h.lastState)
    (dst : M.BoundedState horizon)
    (hsupp : view.boundedTransition horizon h.lastState action dst ≠ 0) :
    h.extendByOutcome action dst = h.snoc action dst hsupp := by
  simp [extendByOutcome, hsupp]

end BoundedHistory

section Execution

variable [Fintype Player]

/-- Product distribution on optional joint moves induced by a legal behavioral
profile at a realized native bounded history. -/
noncomputable def jointActionDist
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon)
    (h : view.BoundedHistory horizon) : PMF (JointAction view.Act) := by
  classical
  exact Math.PMFProduct.pmfPi fun player =>
    (σ player).1 (view.reachableInfoStateOfHistory horizon player h)

@[simp] theorem jointActionDist_apply
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon)
    (h : view.BoundedHistory horizon)
    (a : JointAction view.Act) :
    view.jointActionDist horizon σ h a =
      ∏ player,
        (σ player).1
          (view.reachableInfoStateOfHistory horizon player h) (a player) := by
  classical
  simp [jointActionDist, Math.PMFProduct.pmfPi_apply]

theorem jointActionDist_legalPureToBehavioral_eq_pure
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (π : view.BoundedPureProfile horizon)
    (h : view.BoundedHistory horizon) :
    view.jointActionDist horizon (view.legalPureToBehavioral horizon π) h =
      PMF.pure
        (fun player =>
          (π player).1
            (view.reachableInfoStateOfHistory horizon player h)) := by
  classical
  rw [jointActionDist]
  change
    Math.PMFProduct.pmfPi
        (fun player =>
          PMF.pure
            ((π player).1
              (view.reachableInfoStateOfHistory horizon player h))) =
      PMF.pure
        (fun player =>
          (π player).1
            (view.reachableInfoStateOfHistory horizon player h))
  exact Math.PMFProduct.pmfPi_pure _

theorem legalBehavioralProfile_jointActionDist_eq_zero_of_not_legal
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon)
    (h : view.BoundedHistory horizon)
    (hterm : ¬ view.boundedTerminal horizon h.lastState)
    {a : JointAction view.Act}
    (ha :
      ¬ JointActionLegal view.Act (view.boundedActive horizon)
        (view.boundedTerminal horizon)
        (view.boundedAvailableActions horizon) h.lastState a) :
    view.jointActionDist horizon σ h a = 0 := by
  classical
  rw [view.jointActionDist_apply horizon σ h]
  have hnotLocal :
      ¬ ∀ player,
        view.boundedLocallyLegalAtState horizon h.lastState player
          (a player) := by
    intro hall
    exact ha ((view.boundedLegal_iff_forall horizon).2 ⟨hterm, hall⟩)
  rw [not_forall] at hnotLocal
  rcases hnotLocal with ⟨player, hplayer⟩
  have hsupp :
      a player ∉
        ((σ player).1
          (view.reachableInfoStateOfHistory horizon player h)).support := by
    intro hmem
    exact hplayer ((σ player).2 h hmem)
  have hzero :
      ((σ player).1
          (view.reachableInfoStateOfHistory horizon player h)) (a player) = 0 := by
    exact (PMF.apply_eq_zero_iff _ _).2 hsupp
  rw [Finset.prod_eq_zero_iff]
  exact ⟨player, by simp, hzero⟩

open Classical in
theorem legalBehavioralProfile_legalJointMass_eq_one
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon)
    (h : view.BoundedHistory horizon)
    (hterm : ¬ view.boundedTerminal horizon h.lastState) :
    ∑ a :
        { a : JointAction view.Act //
          JointActionLegal view.Act (view.boundedActive horizon)
            (view.boundedTerminal horizon)
            (view.boundedAvailableActions horizon) h.lastState a },
      view.jointActionDist horizon σ h a.1 = 1 := by
  have hmass : ∑ a : JointAction view.Act,
      view.jointActionDist horizon σ h a = 1 := by
    have := PMF.tsum_coe (view.jointActionDist horizon σ h)
    rwa [tsum_fintype] at this
  calc
    ∑ a :
        { a : JointAction view.Act //
          JointActionLegal view.Act (view.boundedActive horizon)
            (view.boundedTerminal horizon)
            (view.boundedAvailableActions horizon) h.lastState a },
      view.jointActionDist horizon σ h a.1
      =
        ∑ a : JointAction view.Act,
          if JointActionLegal view.Act (view.boundedActive horizon)
              (view.boundedTerminal horizon)
              (view.boundedAvailableActions horizon) h.lastState a then
            view.jointActionDist horizon σ h a
          else 0 := by
            have hsub :
                ∑ a ∈
                    Finset.subtype
                      (fun a : JointAction view.Act =>
                        JointActionLegal view.Act (view.boundedActive horizon)
                          (view.boundedTerminal horizon)
                          (view.boundedAvailableActions horizon)
                          h.lastState a)
                      (Finset.univ : Finset (JointAction view.Act)),
                  view.jointActionDist horizon σ h a.1 =
                ∑ a :
                    { a : JointAction view.Act //
                      JointActionLegal view.Act (view.boundedActive horizon)
                        (view.boundedTerminal horizon)
                        (view.boundedAvailableActions horizon)
                        h.lastState a },
                  view.jointActionDist horizon σ h a.1 := by
              simp
            rw [← hsub, Finset.sum_subtype_eq_sum_filter, Finset.sum_filter]
    _ = ∑ a : JointAction view.Act,
        view.jointActionDist horizon σ h a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          by_cases ha :
              JointActionLegal view.Act (view.boundedActive horizon)
                (view.boundedTerminal horizon)
                (view.boundedAvailableActions horizon) h.lastState a
          · simp [ha]
          · simp [ha,
              view.legalBehavioralProfile_jointActionDist_eq_zero_of_not_legal
                horizon σ h hterm ha]
    _ = 1 := hmass

open Classical in
/-- The induced probability law on legal joint actions at a nonterminal
bounded history. -/
noncomputable def legalActionLaw
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon)
    (h : view.BoundedHistory horizon)
    (hterm : ¬ view.boundedTerminal horizon h.lastState) :
    PMF (view.BoundedLegalAction horizon h.lastState) := by
  exact PMF.ofFintype
    (fun a => view.jointActionDist horizon σ h a.1)
    (view.legalBehavioralProfile_legalJointMass_eq_one horizon σ h hterm)

@[simp] theorem legalActionLaw_apply
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon)
    (h : view.BoundedHistory horizon)
    (hterm : ¬ view.boundedTerminal horizon h.lastState)
    (a : view.BoundedLegalAction horizon h.lastState) :
    view.legalActionLaw horizon σ h hterm a =
      view.jointActionDist horizon σ h a.1 := by
  rw [legalActionLaw, PMF.ofFintype_apply]

/-- A legal round-action law can be consumed sequentially by first sampling any
finite projection of the legal action, then sampling the original legal action
conditioned on that projected value.

This is the frontier-side law used when a simultaneous round action is replayed
as source-order choices: the first source query samples a projection of the
frontier action, while the conditioned remainder keeps the joint frontier law
unchanged. -/
theorem legalActionLaw_disintegrate
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon)
    (h : view.BoundedHistory horizon)
    (hterm : ¬ view.boundedTerminal horizon h.lastState)
    {β : Type} [Finite β]
    (project : view.BoundedLegalAction horizon h.lastState → β) :
    view.legalActionLaw horizon σ h hterm =
      (Math.ProbabilityMassFunction.pushforward
          (view.legalActionLaw horizon σ h hterm) project).bind
        (fun value =>
          Math.ProbabilityMassFunction.condOn
            (view.legalActionLaw horizon σ h hterm) project value) := by
  exact
    Math.ProbabilityMassFunction.bind_pushforward_condOn_pure
      (view.legalActionLaw horizon σ h hterm) project

/-- The conditioned remainder in `legalActionLaw_disintegrate` is supported on
legal actions whose projection is the sampled value. -/
theorem legalActionLaw_condOn_support_project
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon)
    (h : view.BoundedHistory horizon)
    (hterm : ¬ view.boundedTerminal horizon h.lastState)
    {β : Type}
    (project : view.BoundedLegalAction horizon h.lastState → β)
    (value : β)
    (hvalue :
      Math.ProbabilityMassFunction.pushforward
        (view.legalActionLaw horizon σ h hterm) project value ≠ 0)
    {action : view.BoundedLegalAction horizon h.lastState}
    (haction :
      action ∈
        (Math.ProbabilityMassFunction.condOn
          (view.legalActionLaw horizon σ h hterm) project value).support) :
    project action = value :=
  Math.ProbabilityMassFunction.condOn_support_project
    (view.legalActionLaw horizon σ h hterm) project value hvalue haction

theorem legalActionLaw_legalPureToBehavioral_eq_pure
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (π : view.BoundedPureProfile horizon)
    (h : view.BoundedHistory horizon)
    (hterm : ¬ view.boundedTerminal horizon h.lastState) :
    view.legalActionLaw horizon
        (view.legalPureToBehavioral horizon π) h hterm =
      PMF.pure
        ⟨fun player =>
            (π player).1
              (view.reachableInfoStateOfHistory horizon player h),
          (view.boundedLegal_iff_forall horizon).2
            ⟨hterm, fun player => (π player).2 h⟩⟩ := by
  classical
  let joint : JointAction view.Act := fun player =>
    (π player).1 (view.reachableInfoStateOfHistory horizon player h)
  let hlegal :
      JointActionLegal view.Act (view.boundedActive horizon)
        (view.boundedTerminal horizon)
        (view.boundedAvailableActions horizon) h.lastState joint :=
    (view.boundedLegal_iff_forall horizon).2
      ⟨hterm, fun player => (π player).2 h⟩
  apply PMF.ext
  intro action
  rw [legalActionLaw_apply,
    jointActionDist_legalPureToBehavioral_eq_pure]
  by_cases haction : action.1 = joint
  · have hsub :
        action = (⟨joint, hlegal⟩ :
          view.BoundedLegalAction horizon h.lastState) := by
      exact Subtype.ext haction
    subst action
    simp [joint]
  · have hsub :
        action ≠ (⟨joint, hlegal⟩ :
          view.BoundedLegalAction horizon h.lastState) := by
      intro hEq
      exact haction (congrArg Subtype.val hEq)
    simp [PMF.pure_apply, haction, hsub, joint]

private theorem sum_subtype_eq_sum_ite
    {α M₀ : Type} [Fintype α] [AddCommMonoid M₀]
    {p : α → Prop} [DecidablePred p] (F : (a : α) → p a → M₀) :
    (∑ x : { a : α // p a }, F x.1 x.2) =
      ∑ a : α, if h : p a then F a h else 0 := by
  classical
  let f : α → M₀ := fun a => if h : p a then F a h else 0
  have hsub :
      (Finset.subtype p (Finset.univ : Finset α)).sum (fun x => f x.1) =
        ∑ x : { a : α // p a }, F x.1 x.2 := by
    have huniv :
        Finset.subtype p (Finset.univ : Finset α) =
          (Finset.univ : Finset { a : α // p a }) := by
      ext x
      simp
    rw [huniv]
    refine Finset.sum_congr rfl ?_
    intro x _
    simp only [f]
    have hp : p x.1 := x.2
    simp [hp]
  calc
    ∑ x : { a : α // p a }, F x.1 x.2 =
        (Finset.subtype p (Finset.univ : Finset α)).sum
          (fun x => f x.1) := hsub.symm
    _ = ∑ a : α, if p a then f a else 0 := by
      simpa [Finset.sum_filter] using
        (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset α)) (p := p) (f := f))
    _ = ∑ a : α, f a := by
      refine Finset.sum_congr rfl ?_
      intro a _
      by_cases hp : p a <;> simp [f, hp]
    _ = ∑ a : α, if h : p a then F a h else 0 := rfl

open Classical in
theorem legalActionLaw_bind_eq_jointActionDist_bind
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon)
    (h : view.BoundedHistory horizon)
    (hterm : ¬ view.boundedTerminal horizon h.lastState)
    {β : Type} (fallback : β)
    (K : view.BoundedLegalAction horizon h.lastState → PMF β) :
    (view.legalActionLaw horizon σ h hterm).bind K =
      (view.jointActionDist horizon σ h).bind fun joint =>
        if hlegal :
            JointActionLegal view.Act (view.boundedActive horizon)
              (view.boundedTerminal horizon)
              (view.boundedAvailableActions horizon) h.lastState joint then
          K ⟨joint, hlegal⟩
        else
          PMF.pure fallback := by
  ext b
  rw [PMF.bind_apply, PMF.bind_apply, tsum_fintype, tsum_fintype]
  calc
    ∑ action : view.BoundedLegalAction horizon h.lastState,
        view.legalActionLaw horizon σ h hterm action *
          K action b
      =
        ∑ action : view.BoundedLegalAction horizon h.lastState,
          view.jointActionDist horizon σ h action.1 *
            K action b := by
          refine Finset.sum_congr rfl ?_
          intro action _
          rw [view.legalActionLaw_apply horizon σ h hterm]
    _ =
        ∑ joint : JointAction view.Act,
          (if hlegal :
              JointActionLegal view.Act (view.boundedActive horizon)
                (view.boundedTerminal horizon)
                (view.boundedAvailableActions horizon) h.lastState joint then
            view.jointActionDist horizon σ h joint *
              K ⟨joint, hlegal⟩ b
          else 0) := by
          exact
            sum_subtype_eq_sum_ite
              (F := fun joint hlegal =>
                view.jointActionDist horizon σ h joint *
                  K ⟨joint, hlegal⟩ b)
    _ =
        ∑ joint : JointAction view.Act,
          view.jointActionDist horizon σ h joint *
            (if hlegal :
                JointActionLegal view.Act (view.boundedActive horizon)
                  (view.boundedTerminal horizon)
                  (view.boundedAvailableActions horizon) h.lastState joint then
              K ⟨joint, hlegal⟩
            else
              PMF.pure fallback) b := by
          refine Finset.sum_congr rfl ?_
          intro joint _
          by_cases hlegal :
              JointActionLegal view.Act (view.boundedActive horizon)
                (view.boundedTerminal horizon)
                (view.boundedAvailableActions horizon) h.lastState joint
          · simp [hlegal]
          · have hzero :
                view.jointActionDist horizon σ h joint = 0 :=
              view.legalBehavioralProfile_jointActionDist_eq_zero_of_not_legal
                horizon σ h hterm hlegal
            simp [hlegal, hzero]

namespace BoundedHistory

/-- Horizon-bounded run distribution on native bounded histories induced by a
legal behavioral profile. Terminal histories absorb. -/
noncomputable def runDistFrom
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon) :
    Nat → view.BoundedHistory horizon → PMF (view.BoundedHistory horizon)
  | 0, h => PMF.pure h
  | n + 1, h => by
      classical
      if hterm : view.boundedTerminal horizon h.lastState then
        exact PMF.pure h
      else
        exact (view.legalActionLaw horizon σ h hterm).bind fun action =>
          (view.boundedTransition horizon h.lastState action).bind fun dst =>
            runDistFrom view horizon σ n (h.extendByOutcome action dst)

@[simp] theorem runDistFrom_zero
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon)
    (h : view.BoundedHistory horizon) :
    runDistFrom view horizon σ 0 h = PMF.pure h := rfl

@[simp] theorem runDistFrom_succ_terminal
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon)
    (n : Nat) (h : view.BoundedHistory horizon)
    (hterm : view.boundedTerminal horizon h.lastState) :
    runDistFrom view horizon σ (n + 1) h = PMF.pure h := by
  classical
  simp [runDistFrom, hterm]

@[simp] theorem runDistFrom_succ_nonterminal
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon)
    (n : Nat) (h : view.BoundedHistory horizon)
    (hterm : ¬ view.boundedTerminal horizon h.lastState) :
    runDistFrom view horizon σ (n + 1) h =
      (view.legalActionLaw horizon σ h hterm).bind fun action =>
        (view.boundedTransition horizon h.lastState action).bind fun dst =>
          runDistFrom view horizon σ n
            (h.extendByOutcome action dst) := by
  classical
  simp [runDistFrom, hterm]

theorem runDistFrom_terminal
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon)
    (n : Nat) (h : view.BoundedHistory horizon)
    (hterm : view.boundedTerminal horizon h.lastState) :
    runDistFrom view horizon σ n h = PMF.pure h := by
  induction n with
  | zero => rfl
  | succ n _ =>
      rw [runDistFrom_succ_terminal view horizon σ n h hterm]

theorem runDistFrom_bind_runDistFrom
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon)
    (m n : Nat) (h : view.BoundedHistory horizon) :
    (runDistFrom view horizon σ m h).bind
        (fun h' => runDistFrom view horizon σ n h') =
      runDistFrom view horizon σ (m + n) h := by
  induction m generalizing h with
  | zero =>
      simp [runDistFrom]
  | succ m ih =>
      by_cases hterm : view.boundedTerminal horizon h.lastState
      · rw [runDistFrom_succ_terminal view horizon σ m h hterm]
        rw [PMF.pure_bind]
        rw [runDistFrom_terminal view horizon σ n h hterm]
        rw [runDistFrom_terminal view horizon σ (m + 1 + n) h hterm]
      · rw [runDistFrom_succ_nonterminal view horizon σ m h hterm]
        rw [PMF.bind_bind]
        simp_rw [PMF.bind_bind]
        conv_lhs =>
          arg 2
          ext action
          arg 2
          ext dst
          rw [ih]
        rw [show m + 1 + n = m + n + 1 by omega]
        rw [runDistFrom_succ_nonterminal view horizon σ (m + n) h hterm]

/-- Supported bounded executions either absorb at a bounded-terminal history,
or realize all remaining round steps. -/
theorem runDistFrom_support_terminal_or_length_ge
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon) :
    ∀ n (start dst : view.BoundedHistory horizon),
      dst ∈ (runDistFrom view horizon σ n start).support →
        view.boundedTerminal horizon dst.lastState ∨
          start.steps.length + n ≤ dst.steps.length
  | 0, start, dst, hsupport => by
      have hdst : dst = start := by
        simpa [runDistFrom, PMF.support_pure, Set.mem_singleton_iff]
          using hsupport
      subst dst
      exact Or.inr (by simp)
  | n + 1, start, dst, hsupport => by
      classical
      by_cases hterm : view.boundedTerminal horizon start.lastState
      · have hdst : dst = start := by
          simpa [runDistFrom, hterm, PMF.support_pure,
            Set.mem_singleton_iff] using hsupport
        subst dst
        exact Or.inl hterm
      · have hsupport' :
            dst ∈
              ((view.legalActionLaw horizon σ start hterm).bind
                fun action =>
                  (view.boundedTransition horizon start.lastState action).bind
                    fun next =>
                      runDistFrom view horizon σ n
                        (start.extendByOutcome action next)).support := by
          simpa [runDistFrom, hterm] using hsupport
        rw [PMF.mem_support_bind_iff] at hsupport'
        rcases hsupport' with ⟨action, _haction, hnextSupport⟩
        rw [PMF.mem_support_bind_iff] at hnextSupport
        rcases hnextSupport with ⟨next, hnext, htail⟩
        have hnextMass :
            view.boundedTransition horizon start.lastState action next ≠ 0 :=
          (PMF.mem_support_iff _ _).1 hnext
        have hlenExtend :
            (start.extendByOutcome action next).steps.length =
              start.steps.length + 1 := by
          rw [BoundedHistory.extendByOutcome_of_support
            start action next hnextMass]
          simp [BoundedHistory.snoc]
        rcases
            runDistFrom_support_terminal_or_length_ge
              view horizon σ n
              (start.extendByOutcome action next) dst htail with
          hdstTerm | hlenTail
        · exact Or.inl hdstTerm
        · exact Or.inr (by omega)

end BoundedHistory

/-- Bounded run distribution from the initial native bounded history. -/
noncomputable def runDist
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (steps : Nat) (σ : view.BoundedBehavioralProfile horizon) :
    PMF (view.BoundedHistory horizon) :=
  BoundedHistory.runDistFrom view horizon σ steps
    (BoundedHistory.nil view horizon)

/-- Running exactly the bounded horizon from the initial history can only
support bounded-terminal histories.  A supported run either reaches machine
terminality earlier or consumes the full presentation cutoff. -/
theorem runDist_support_terminal_at_horizon
    (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon)
    (h : view.BoundedHistory horizon)
    (hsupport : h ∈ (view.runDist horizon horizon σ).support) :
    view.boundedTerminal horizon h.lastState := by
  rcases
      BoundedHistory.runDistFrom_support_terminal_or_length_ge
        view horizon σ horizon (BoundedHistory.nil view horizon) h
        (by simpa [runDist] using hsupport) with
    hterm | hlen
  · exact hterm
  · right
    rw [view.history_depth horizon h]
    simpa using hlen

end Execution

/-- Primitive event batches extracted from a native bounded history. -/
noncomputable def boundedHistoryEventBatches
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon) :
    List (List M.Event) :=
  h.steps.map fun step =>
    view.eventBatch step.src.state step.act.1 step.dst.state

/-- Project a native bounded history to primitive event batches and checkpoint
machine state. -/
noncomputable def boundedHistoryTrace
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon) : M.EventBatchTrace :=
  (view.boundedHistoryEventBatches horizon h, h.lastState.state)

/-- Event-batched primitive trace kernel induced by a native bounded behavioral
profile. -/
noncomputable def boundedEventBatchTraceFromBehavioral
    (view : M.RoundView) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (β : view.BoundedBehavioralProfile horizon)
    (steps : Nat) : PMF M.EventBatchTrace :=
  PMF.map (view.boundedHistoryTrace horizon)
    (view.runDist horizon steps β)

/-- Event-batched primitive trace kernel induced by a native bounded pure profile. -/
noncomputable def boundedEventBatchTraceFromPure
    (view : M.RoundView) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (π : view.BoundedPureProfile horizon)
    (steps : Nat) : PMF M.EventBatchTrace :=
  view.boundedEventBatchTraceFromBehavioral horizon
    (view.legalPureToBehavioral horizon π) steps

@[simp] theorem boundedEventBatchTraceFromBehavioral_legalPureToBehavioral
    (view : M.RoundView) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (π : view.BoundedPureProfile horizon) (steps : Nat) :
    view.boundedEventBatchTraceFromBehavioral horizon
        (view.legalPureToBehavioral horizon π) steps =
      view.boundedEventBatchTraceFromPure horizon π steps := rfl

/-- Outcome kernel induced by a native bounded behavioral profile. -/
noncomputable def boundedOutcomeFromBehavioral
    (view : M.RoundView) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (β : view.BoundedBehavioralProfile horizon)
    (steps : Nat) : PMF (Option M.Outcome) :=
  PMF.map (fun trace : M.EventBatchTrace => M.outcome trace.2)
    (view.boundedEventBatchTraceFromBehavioral horizon β steps)

/-- Outcome kernel induced by a native bounded pure profile. -/
noncomputable def boundedOutcomeFromPure
    (view : M.RoundView) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (π : view.BoundedPureProfile horizon)
    (steps : Nat) : PMF (Option M.Outcome) :=
  PMF.map (fun trace : M.EventBatchTrace => M.outcome trace.2)
    (view.boundedEventBatchTraceFromPure horizon π steps)

@[simp] theorem boundedOutcomeFromBehavioral_legalPureToBehavioral
    (view : M.RoundView) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (π : view.BoundedPureProfile horizon) (steps : Nat) :
    view.boundedOutcomeFromBehavioral horizon
        (view.legalPureToBehavioral horizon π) steps =
      view.boundedOutcomeFromPure horizon π steps := rfl

end RoundView

end Machine

end Vegas
