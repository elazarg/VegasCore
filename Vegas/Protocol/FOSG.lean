import Vegas.Protocol.Machine
import GameTheory.Languages.FOSG.Compile

/-!
# FOSG views of protocol machines

This module derives sequential game-theoretic views from protocol machines.
The canonical direction is `Machine -> FOSG`: an asynchronous protocol machine
executes one primitive event at a time, while a FOSG view exposes one selected
primitive source at each prefix and wraps the resulting `Machine.step` with
history.

`Machine.FOSGView` is the only generic protocol-to-FOSG adapter in this module.
It selects the next primitive source of an asynchronous event machine; legality
and transition lemmas state exactly how the derived FOSG projects back to
`Machine.step`.
-/

namespace Vegas

open GameTheory

namespace Machine

variable {Player : Type} [DecidableEq Player]

/-- A one-player FOSG joint action for an asynchronous machine view. -/
def singletonJointAction
    (M : Machine Player) (player : Player) (action : M.Action player) :
    JointAction M.Action :=
  fun other =>
    if h : other = player then
      some (Eq.ndrec action (by cases h; rfl))
    else
      none

@[simp] theorem singletonJointAction_self
    (M : Machine Player) (player : Player) (action : M.Action player) :
    singletonJointAction M player action player = some action := by
  simp [singletonJointAction]

@[simp] theorem singletonJointAction_other
    (M : Machine Player) {player other : Player}
    (action : M.Action player) (hother : other ≠ player) :
    singletonJointAction M player action other = none := by
  simp [singletonJointAction, hother]

/-- Which primitive source a sequential FOSG presentation exposes next. -/
inductive Turn (M : Machine Player) where
  | play (player : Player)
  | internal (event : M.Internal)

namespace Turn

/-- A selected turn is available at a machine state when it can actually make
progress there. Player turns require at least one available concrete action;
internal turns require the selected internal event to be available. -/
def AvailableAt (M : Machine Player) (state : M.State) :
    M.Turn → Prop
  | .play player => ∃ action : M.Action player, action ∈ M.available state player
  | .internal event => event ∈ M.availableInternal state

end Turn

/-- Horizon-bounded event/state prefix for finite sequential views of an
asynchronous protocol machine.

The unbounded `RunPrefix` remains the reactive execution prefix. A bounded
prefix is the same data plus the presentation fact that at most `horizon`
primitive events have elapsed. -/
structure BoundedRunPrefix (M : Machine Player) (horizon : Nat) where
  pref : M.RunPrefix
  length_le : pref.events.length ≤ horizon

namespace BoundedRunPrefix

variable {M : Machine Player} {horizon : Nat}

private theorem length_eq_of_mem_listsOfLength {α : Type} [DecidableEq α]
    (s : Finset α) :
    ∀ {xs : List α} {n : Nat},
      xs ∈ Math.BoundedLists.listsOfLength s n → xs.length = n
  | _xs, 0, h => by
      simpa [Math.BoundedLists.listsOfLength] using h
  | _xs, n + 1, h => by
      change _ ∈
        (s ×ˢ Math.BoundedLists.listsOfLength s n).image
          (fun p : α × List α => p.1 :: p.2) at h
      rcases Finset.mem_image.mp h with ⟨p, hp, rfl⟩
      have hxs : p.2 ∈ Math.BoundedLists.listsOfLength s n :=
        (Finset.mem_product.mp hp).2
      have hlen := length_eq_of_mem_listsOfLength s hxs
      simp [hlen]

private theorem length_le_of_mem_listsUpToLength {α : Type} [DecidableEq α]
    (s : Finset α) {xs : List α} {n : Nat}
    (h : xs ∈ Math.BoundedLists.listsUpToLength s n) :
    xs.length ≤ n := by
  change xs ∈
    (Finset.range (n + 1)).biUnion
      (fun k => Math.BoundedLists.listsOfLength s k) at h
  rcases Finset.mem_biUnion.mp h with ⟨k, hk, hxs⟩
  have hlen : xs.length = k :=
    length_eq_of_mem_listsOfLength s hxs
  have hkle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  omega

omit [DecidableEq Player] in
@[ext] theorem ext
    {left right : M.BoundedRunPrefix horizon}
    (hpref : left.pref = right.pref) :
    left = right := by
  cases left
  cases right
  cases hpref
  rfl

/-- Initial bounded asynchronous machine prefix. -/
def init (M : Machine Player) (horizon : Nat) :
    M.BoundedRunPrefix horizon where
  pref := RunPrefix.init M
  length_le := by simp

/-- Endpoint state of a bounded asynchronous machine prefix. -/
def lastState (pref : M.BoundedRunPrefix horizon) : M.State :=
  pref.pref.lastState

/-- Extend a bounded prefix by one primitive event and one successor state. -/
def snoc (pref : M.BoundedRunPrefix horizon)
    (hlt : pref.pref.events.length < horizon)
    (event : M.Event) (next : M.State) :
    M.BoundedRunPrefix horizon where
  pref := pref.pref.snoc event next
  length_le := by
    simp [RunPrefix.snoc]
    omega

omit [DecidableEq Player] in
@[simp] theorem init_pref (M : Machine Player) (horizon : Nat) :
    (BoundedRunPrefix.init M horizon).pref = RunPrefix.init M := rfl

omit [DecidableEq Player] in
@[simp] theorem init_lastState (M : Machine Player) (horizon : Nat) :
    (BoundedRunPrefix.init M horizon).lastState = M.init := rfl

omit [DecidableEq Player] in
@[simp] theorem snoc_pref
    (pref : M.BoundedRunPrefix horizon)
    (hlt : pref.pref.events.length < horizon)
    (event : M.Event) (next : M.State) :
    (pref.snoc hlt event next).pref =
      pref.pref.snoc event next := rfl

omit [DecidableEq Player] in
@[simp] theorem snoc_lastState
    (pref : M.BoundedRunPrefix horizon)
    (hlt : pref.pref.events.length < horizon)
    (event : M.Event) (next : M.State) :
    (pref.snoc hlt event next).lastState = next := by
  simp [lastState, snoc]

/-- Finite enumeration of bounded asynchronous machine prefixes. -/
noncomputable def finset (M : Machine Player) (horizon : Nat)
    [Fintype M.Event] [Fintype M.State] :
    Finset (M.BoundedRunPrefix horizon) := by
  classical
  let eventLists :=
    Math.BoundedLists.listsUpToLength
      (Finset.univ : Finset M.Event) horizon
  let stateLists :=
    Math.BoundedLists.listsUpToLength
      (Finset.univ : Finset M.State) (horizon + 1)
  exact
    (eventLists ×ˢ stateLists).attach.image fun pair =>
      if hlen : pair.1.2.length = pair.1.1.length + 1 then
        { pref :=
            { events := pair.1.1
              states := pair.1.2
              length_eq := hlen }
          length_le := by
            have hmem : pair.1.1 ∈ eventLists :=
              (Finset.mem_product.mp pair.2).1
            exact length_le_of_mem_listsUpToLength
              (Finset.univ : Finset M.Event) hmem }
      else
        BoundedRunPrefix.init M horizon

omit [DecidableEq Player] in
theorem mem_finset
    (M : Machine Player) (horizon : Nat)
    [Fintype M.Event] [Fintype M.State]
    (pref : M.BoundedRunPrefix horizon) :
    pref ∈ BoundedRunPrefix.finset M horizon := by
  classical
  let eventLists :=
    Math.BoundedLists.listsUpToLength
      (Finset.univ : Finset M.Event) horizon
  let stateLists :=
    Math.BoundedLists.listsUpToLength
      (Finset.univ : Finset M.State) (horizon + 1)
  have hevents : pref.pref.events ∈ eventLists := by
    exact Math.BoundedLists.mem_listsUpToLength_of_forall_mem
      pref.length_le (by intro _ _; simp)
  have hstateLen : pref.pref.states.length ≤ horizon + 1 := by
    rw [pref.pref.length_eq]
    exact Nat.succ_le_succ pref.length_le
  have hstates : pref.pref.states ∈ stateLists := by
    exact Math.BoundedLists.mem_listsUpToLength_of_forall_mem
      hstateLen (by intro _ _; simp)
  refine Finset.mem_image.mpr ?_
  refine
    ⟨⟨(pref.pref.events, pref.pref.states), ?_⟩, ?_⟩
  · exact Finset.mem_product.mpr ⟨hevents, hstates⟩
  · simp [pref.pref.length_eq]

noncomputable instance instFintype
    [Fintype M.Event] [Fintype M.State] :
    Fintype (M.BoundedRunPrefix horizon) :=
  Fintype.mk (BoundedRunPrefix.finset M horizon)
    (BoundedRunPrefix.mem_finset M horizon)

end BoundedRunPrefix

/-- Sequential FOSG presentation of an asynchronous machine.

The view chooses which primitive source is exposed at each machine prefix. This
choice is presentation data: the transition below remains the original
`Machine.step`, and the view must prove that every nonterminal selected source
is available. -/
structure FOSGView (M : Machine Player) where
  turn : M.RunPrefix → M.Turn
  terminal_not_play :
    ∀ {pref : M.RunPrefix} {player : Player},
      M.terminal pref.lastState → turn pref ≠ .play player
  turn_available :
    ∀ {pref : M.RunPrefix},
      ¬ M.terminal pref.lastState →
        (turn pref).AvailableAt M pref.lastState
  reward :
    (src : M.RunPrefix) → M.Event → M.RunPrefix → Player → ℝ

namespace FOSGView

variable {M : Machine Player}

/-- Active players exposed by an asynchronous-machine FOSG view. Internal
turns and terminal states have no active strategic player. -/
def active (view : M.FOSGView) (pref : M.RunPrefix) : Finset Player :=
  match view.turn pref with
  | .play player => {player}
  | .internal _ => ∅

/-- Concrete actions exposed by an asynchronous-machine FOSG view. Only the
selected player, if any, inherits the machine's available concrete actions. -/
def availableActions (view : M.FOSGView)
    (pref : M.RunPrefix) (player : Player) : Set (M.Action player) :=
  match view.turn pref with
  | .play selected =>
      if player = selected then M.available pref.lastState player else ∅
  | .internal _ => ∅

/-- The selected primitive event agrees with the exposed FOSG turn and with the
active coordinate of the legal joint action whenever that coordinate is
present. -/
def EventRepresentsLegalJointAction
    (view : M.FOSGView) (pref : M.RunPrefix)
    (action :
      {a : JointAction M.Action //
        JointActionLegal M.Action view.active
          (fun pref : M.RunPrefix => M.terminal pref.lastState)
          view.availableActions pref a})
    (event : M.Event) : Prop :=
  (∀ internal, view.turn pref = .internal internal →
    event = .internal internal) ∧
  (∀ player (choice : M.Action player),
    view.turn pref = .play player →
      action.1 player = some choice →
        event = .play player choice)

/-- Extract the available primitive machine event represented by a legal FOSG
joint action at a prefix, together with its representation fact. -/
noncomputable def selectedEventOfLegalJointActionWithSpec
    (view : M.FOSGView) (pref : M.RunPrefix)
    (action :
      {a : JointAction M.Action //
        JointActionLegal M.Action view.active
          (fun pref : M.RunPrefix => M.terminal pref.lastState)
          view.availableActions pref a}) :
    {event : M.Event //
      M.EventAvailable pref.lastState event ∧
        view.EventRepresentsLegalJointAction pref action event} := by
  classical
  cases hturn : view.turn pref with
  | internal event =>
      have havailable :
          event ∈ M.availableInternal pref.lastState := by
        have hturnAvailable := view.turn_available (pref := pref) action.2.1
        rw [hturn] at hturnAvailable
        simpa [Turn.AvailableAt] using hturnAvailable
      exact ⟨.internal event,
        by simpa [Machine.EventAvailable] using havailable,
        by
          constructor
          · intro internal hinternal
            rw [hturn] at hinternal
            cases hinternal
            rfl
          · intro player choice hplay _hmove
            rw [hturn] at hplay
            cases hplay⟩
  | play player =>
      cases hmove : action.1 player with
      | some choice =>
          have hlocal := action.2.2 player
          have hchoice :
              choice ∈ M.available pref.lastState player := by
            have hpair :
                player ∈ view.active pref ∧
                  choice ∈ view.availableActions pref player := by
              simpa [hmove] using hlocal
            simpa [availableActions, hturn] using hpair.2
          exact ⟨.play player choice,
            by simpa [Machine.EventAvailable] using hchoice,
            by
              constructor
              · intro internal hinternal
                rw [hturn] at hinternal
                cases hinternal
              · intro other otherChoice hplay hsome
                rw [hturn] at hplay
                cases hplay
                rw [hmove] at hsome
                cases hsome
                rfl⟩
      | none =>
          have havailable :
              ∃ choice : M.Action player,
                choice ∈ M.available pref.lastState player := by
            have hturnAvailable :=
              view.turn_available (pref := pref) action.2.1
            rw [hturn] at hturnAvailable
            simpa [Turn.AvailableAt] using hturnAvailable
          exact ⟨.play player (Classical.choose havailable),
            by
              simpa [Machine.EventAvailable] using
                (Classical.choose_spec havailable),
            by
              constructor
              · intro internal hinternal
                rw [hturn] at hinternal
                cases hinternal
              · intro other otherChoice hplay hsome
                rw [hturn] at hplay
                cases hplay
                rw [hmove] at hsome
                cases hsome⟩

/-- Extract the primitive machine event represented by a legal FOSG joint
action at a prefix. -/
noncomputable def eventOfLegalJointAction
    (view : M.FOSGView) (pref : M.RunPrefix)
    (action :
      {a : JointAction M.Action //
        JointActionLegal M.Action view.active
          (fun pref : M.RunPrefix => M.terminal pref.lastState)
          view.availableActions pref a}) :
    M.Event :=
  (view.selectedEventOfLegalJointActionWithSpec pref action).1

theorem eventOfLegalJointAction_available
    (view : M.FOSGView) (pref : M.RunPrefix)
    (action :
      {a : JointAction M.Action //
        JointActionLegal M.Action view.active
          (fun pref : M.RunPrefix => M.terminal pref.lastState)
          view.availableActions pref a}) :
    M.EventAvailable pref.lastState
      (view.eventOfLegalJointAction pref action) :=
  (view.selectedEventOfLegalJointActionWithSpec pref action).2.1

theorem eventOfLegalJointAction_represents
    (view : M.FOSGView) (pref : M.RunPrefix)
    (action :
      {a : JointAction M.Action //
        JointActionLegal M.Action view.active
          (fun pref : M.RunPrefix => M.terminal pref.lastState)
          view.availableActions pref a}) :
    view.EventRepresentsLegalJointAction pref action
      (view.eventOfLegalJointAction pref action) :=
  (view.selectedEventOfLegalJointActionWithSpec pref action).2.2

theorem eventOfLegalJointAction_eq_play_of_turn_action
    (view : M.FOSGView) (pref : M.RunPrefix)
    (action :
      {a : JointAction M.Action //
        JointActionLegal M.Action view.active
          (fun pref : M.RunPrefix => M.terminal pref.lastState)
          view.availableActions pref a})
    {player : Player} {choice : M.Action player}
    (hturn : view.turn pref = .play player)
    (hmove : action.1 player = some choice) :
    view.eventOfLegalJointAction pref action = .play player choice :=
  (view.eventOfLegalJointAction_represents pref action).2
    player choice hturn hmove

/-- Extract the available primitive machine event represented by a legal FOSG
joint action at a prefix. -/
noncomputable def selectedEventOfLegalJointAction
    (view : M.FOSGView) (pref : M.RunPrefix)
    (action :
      {a : JointAction M.Action //
        JointActionLegal M.Action view.active
          (fun pref : M.RunPrefix => M.terminal pref.lastState)
          view.availableActions pref a}) :
    {event : M.Event // M.EventAvailable pref.lastState event} :=
  ⟨view.eventOfLegalJointAction pref action,
    view.eventOfLegalJointAction_available pref action⟩

/-- Interpret an asynchronous protocol machine as a FOSG over event/state
prefixes. -/
noncomputable def toFOSG (view : M.FOSGView) :
    FOSG Player M.RunPrefix M.Action M.Obs M.Public where
  init := RunPrefix.init M
  active := view.active
  availableActions := view.availableActions
  terminal := fun pref => M.terminal pref.lastState
  transition := fun pref action =>
    (M.step (view.eventOfLegalJointAction pref action) pref.lastState).map
      (fun next =>
        pref.snoc (view.eventOfLegalJointAction pref action) next)
  reward := fun pref action dst player =>
    view.reward pref (view.eventOfLegalJointAction pref action) dst player
  privObs := fun player _pref _action dst =>
    M.observe player dst.lastState
  pubObs := fun _pref _action dst =>
    M.publicView dst.lastState
  terminal_active_eq_empty := by
    intro pref hterminal
    cases hturn : view.turn pref with
    | internal event =>
        simp [active, hturn]
    | play player =>
        exact False.elim (view.terminal_not_play hterminal hturn)
  terminal_no_legal := by
    intro _pref _action hterminal hlegal
    exact hlegal.1 hterminal
  nonterminal_exists_legal := by
    intro pref hterminal
    have havailable := view.turn_available (pref := pref) hterminal
    cases hturn : view.turn pref with
    | internal event =>
        refine ⟨GameTheory.FOSG.noopAction M.Action, ⟨hterminal, ?_⟩⟩
        intro player
        simp [GameTheory.FOSG.noopAction, active, hturn]
    | play player =>
        rw [hturn] at havailable
        rcases havailable with ⟨choice, hchoice⟩
        refine ⟨singletonJointAction M player choice, ⟨hterminal, ?_⟩⟩
        intro other
        by_cases hother : other = player
        · subst hother
          simp [singletonJointAction, active, availableActions, hturn, hchoice]
        · simp [singletonJointAction, active, hturn, hother]

@[simp] theorem toFOSG_init (view : M.FOSGView) :
    view.toFOSG.init = RunPrefix.init M := rfl

@[simp] theorem toFOSG_active (view : M.FOSGView)
    (pref : M.RunPrefix) :
    view.toFOSG.active pref = view.active pref := rfl

@[simp] theorem toFOSG_availableActions (view : M.FOSGView)
    (pref : M.RunPrefix) (player : Player) :
    view.toFOSG.availableActions pref player =
      view.availableActions pref player := rfl

@[simp] theorem toFOSG_terminal (view : M.FOSGView)
    (pref : M.RunPrefix) :
    view.toFOSG.terminal pref = M.terminal pref.lastState := rfl

@[simp] theorem toFOSG_transition (view : M.FOSGView)
    (pref : M.RunPrefix)
    (action : view.toFOSG.LegalAction pref) :
    view.toFOSG.transition pref action =
      (M.step (view.eventOfLegalJointAction pref action) pref.lastState).map
        (fun next =>
          pref.snoc (view.eventOfLegalJointAction pref action) next) := rfl

@[simp] theorem toFOSG_reward (view : M.FOSGView)
    (pref : M.RunPrefix)
    (action : view.toFOSG.LegalAction pref)
    (dst : M.RunPrefix) (player : Player) :
    view.toFOSG.reward pref action dst player =
      view.reward pref (view.eventOfLegalJointAction pref action) dst player := rfl

@[simp] theorem toFOSG_privObs (view : M.FOSGView)
    (player : Player) (pref : M.RunPrefix)
    (action : view.toFOSG.LegalAction pref)
    (dst : M.RunPrefix) :
    view.toFOSG.privObs player pref action dst =
      M.observe player dst.lastState := rfl

@[simp] theorem toFOSG_pubObs (view : M.FOSGView)
    (pref : M.RunPrefix)
    (action : view.toFOSG.LegalAction pref)
    (dst : M.RunPrefix) :
    view.toFOSG.pubObs pref action dst =
      M.publicView dst.lastState := rfl

/-- Projecting one derived-FOSG transition to its endpoint state gives exactly
the selected asynchronous machine step. -/
theorem transition_map_lastState_eq_step
    (view : M.FOSGView) (pref : M.RunPrefix)
    (action : view.toFOSG.LegalAction pref) :
    PMF.map (fun dst : M.RunPrefix => dst.lastState)
        (view.toFOSG.transition pref action) =
      M.step (view.eventOfLegalJointAction pref action) pref.lastState := by
  rw [toFOSG_transition]
  rw [PMF.map_comp]
  change
    PMF.map
        (fun dst : M.State =>
          (pref.snoc (view.eventOfLegalJointAction pref action) dst).lastState)
        (M.step (view.eventOfLegalJointAction pref action) pref.lastState) =
      M.step (view.eventOfLegalJointAction pref action) pref.lastState
  simpa using
    (PMF.map_id
      (p := M.step (view.eventOfLegalJointAction pref action) pref.lastState))

/-- Event law induced at a nonterminal FOSG history by a legal behavioral
profile of the derived FOSG. -/
noncomputable def eventLawAtHistory
    (view : M.FOSGView)
    [Fintype Player]
    [∀ player : Player, Fintype (Option (M.Action player))]
    (profile : view.toFOSG.LegalBehavioralProfile)
    (h : view.toFOSG.History)
    (hterm : ¬ view.toFOSG.terminal h.lastState) : PMF M.Event :=
  (view.toFOSG.legalActionLaw profile h hterm).map
    (fun action => view.eventOfLegalJointAction h.lastState action)

/-- One-step FOSG execution, projected to machine states, is the original
machine step under the event law induced by the same FOSG behavioral profile. -/
theorem legalActionLaw_bind_transition_lastState_eq_machine_stepDist
    (view : M.FOSGView)
    [Fintype Player]
    [∀ player : Player, Fintype (Option (M.Action player))]
    (profile : view.toFOSG.LegalBehavioralProfile)
    (h : view.toFOSG.History)
    (hterm : ¬ view.toFOSG.terminal h.lastState) :
    (view.toFOSG.legalActionLaw profile h hterm).bind
        (fun action =>
          PMF.map (fun dst : M.RunPrefix => dst.lastState)
            (view.toFOSG.transition h.lastState action)) =
      (view.eventLawAtHistory profile h hterm).bind
        (fun event => M.step event h.lastState.lastState) := by
  rw [eventLawAtHistory, PMF.bind_map]
  congr
  funext action
  exact view.transition_map_lastState_eq_step h.lastState action

/-- Terminal predicate for a horizon-bounded sequential view. The horizon
branch is presentation data; it does not change the underlying machine. -/
def boundedTerminal (_view : M.FOSGView) (horizon : Nat)
    (pref : M.BoundedRunPrefix horizon) : Prop :=
  M.terminal pref.lastState ∨ horizon ≤ pref.pref.events.length

/-- Active player set for a horizon-bounded asynchronous-machine FOSG view. At
the cutoff there are no active players; before the cutoff this is the selected
player, if any, of the underlying machine view. -/
def boundedActive (view : M.FOSGView) (horizon : Nat)
    (pref : M.BoundedRunPrefix horizon) : Finset Player :=
  if horizon ≤ pref.pref.events.length then ∅ else view.active pref.pref

/-- Available concrete actions for a horizon-bounded asynchronous-machine FOSG
view. At the cutoff no concrete action is available. -/
def boundedAvailableActions (view : M.FOSGView) (horizon : Nat)
    (pref : M.BoundedRunPrefix horizon) (player : Player) :
    Set (M.Action player) :=
  if horizon ≤ pref.pref.events.length then ∅
  else view.availableActions pref.pref player

/-- The selected bounded primitive event agrees with the exposed FOSG turn and
with the active coordinate of the legal joint action whenever that coordinate
is present. -/
def BoundedEventRepresentsLegalJointAction
    (view : M.FOSGView) (horizon : Nat)
    (pref : M.BoundedRunPrefix horizon)
    (action :
      {a : JointAction M.Action //
        JointActionLegal M.Action (view.boundedActive horizon)
          (view.boundedTerminal horizon)
          (view.boundedAvailableActions horizon) pref a})
    (event : M.Event) : Prop :=
  (∀ internal, view.turn pref.pref = .internal internal →
    event = .internal internal) ∧
  (∀ player (choice : M.Action player),
    view.turn pref.pref = .play player →
      action.1 player = some choice →
        event = .play player choice)

/-- Extract the available primitive machine event represented by a legal action
in a bounded asynchronous-machine FOSG view, together with its representation
fact. -/
noncomputable def selectedBoundedEventOfLegalJointActionWithSpec
    (view : M.FOSGView) (horizon : Nat)
    (pref : M.BoundedRunPrefix horizon)
    (action :
      {a : JointAction M.Action //
        JointActionLegal M.Action (view.boundedActive horizon)
          (view.boundedTerminal horizon)
          (view.boundedAvailableActions horizon) pref a}) :
    {event : M.Event //
      M.EventAvailable pref.lastState event ∧
        view.BoundedEventRepresentsLegalJointAction horizon pref action event} := by
  classical
  cases hturn : view.turn pref.pref with
  | internal event =>
      have hmachine : ¬ M.terminal pref.lastState := by
        intro h
        exact action.2.1 (Or.inl h)
      have havailable :
          event ∈ M.availableInternal pref.lastState := by
        have hturnAvailable := view.turn_available (pref := pref.pref) hmachine
        rw [hturn] at hturnAvailable
        simpa [Turn.AvailableAt, BoundedRunPrefix.lastState] using hturnAvailable
      exact ⟨.internal event,
        by simpa [Machine.EventAvailable] using havailable,
        by
          constructor
          · intro internal hinternal
            rw [hturn] at hinternal
            cases hinternal
            rfl
          · intro player choice hplay _hmove
            rw [hturn] at hplay
            cases hplay⟩
  | play player =>
      cases hmove : action.1 player with
      | some choice =>
          have hcut : ¬ horizon ≤ pref.pref.events.length := by
            intro hle
            exact action.2.1 (Or.inr hle)
          have hlocal := action.2.2 player
          have hchoice :
              choice ∈ M.available pref.lastState player := by
            have hpair :
                player ∈ view.boundedActive horizon pref ∧
                  choice ∈ view.boundedAvailableActions horizon pref player := by
              simpa [hmove] using hlocal
            simpa [boundedAvailableActions, availableActions,
              BoundedRunPrefix.lastState, hcut, hturn] using hpair.2
          exact ⟨.play player choice,
            by simpa [Machine.EventAvailable] using hchoice,
            by
              constructor
              · intro internal hinternal
                rw [hturn] at hinternal
                cases hinternal
              · intro other otherChoice hplay hsome
                rw [hturn] at hplay
                cases hplay
                rw [hmove] at hsome
                cases hsome
                rfl⟩
      | none =>
          have hmachine : ¬ M.terminal pref.lastState := by
            intro hterminal
            exact action.2.1 (Or.inl hterminal)
          have havailable :
              ∃ choice : M.Action player,
                choice ∈ M.available pref.lastState player := by
            have hturnAvailable :=
              view.turn_available (pref := pref.pref) hmachine
            rw [hturn] at hturnAvailable
            simpa [Turn.AvailableAt, BoundedRunPrefix.lastState] using
              hturnAvailable
          exact ⟨.play player (Classical.choose havailable),
            by
              simpa [Machine.EventAvailable] using
                (Classical.choose_spec havailable),
            by
              constructor
              · intro internal hinternal
                rw [hturn] at hinternal
                cases hinternal
              · intro other otherChoice hplay hsome
                rw [hturn] at hplay
                cases hplay
                rw [hmove] at hsome
                cases hsome⟩

/-- Extract the primitive machine event represented by a legal action in a
bounded asynchronous-machine FOSG view. -/
noncomputable def boundedEventOfLegalJointAction
    (view : M.FOSGView) (horizon : Nat)
    (pref : M.BoundedRunPrefix horizon)
    (action :
      {a : JointAction M.Action //
        JointActionLegal M.Action (view.boundedActive horizon)
          (view.boundedTerminal horizon)
          (view.boundedAvailableActions horizon) pref a}) :
    M.Event :=
  (view.selectedBoundedEventOfLegalJointActionWithSpec horizon pref action).1

theorem boundedEventOfLegalJointAction_available
    (view : M.FOSGView) (horizon : Nat)
    (pref : M.BoundedRunPrefix horizon)
    (action :
      {a : JointAction M.Action //
        JointActionLegal M.Action (view.boundedActive horizon)
          (view.boundedTerminal horizon)
          (view.boundedAvailableActions horizon) pref a}) :
    M.EventAvailable pref.lastState
      (view.boundedEventOfLegalJointAction horizon pref action) :=
  (view.selectedBoundedEventOfLegalJointActionWithSpec horizon pref action).2.1

theorem boundedEventOfLegalJointAction_represents
    (view : M.FOSGView) (horizon : Nat)
    (pref : M.BoundedRunPrefix horizon)
    (action :
      {a : JointAction M.Action //
        JointActionLegal M.Action (view.boundedActive horizon)
          (view.boundedTerminal horizon)
          (view.boundedAvailableActions horizon) pref a}) :
    view.BoundedEventRepresentsLegalJointAction horizon pref action
      (view.boundedEventOfLegalJointAction horizon pref action) :=
  (view.selectedBoundedEventOfLegalJointActionWithSpec horizon pref action).2.2

theorem boundedEventOfLegalJointAction_eq_play_of_turn_action
    (view : M.FOSGView) (horizon : Nat)
    (pref : M.BoundedRunPrefix horizon)
    (action :
      {a : JointAction M.Action //
        JointActionLegal M.Action (view.boundedActive horizon)
          (view.boundedTerminal horizon)
          (view.boundedAvailableActions horizon) pref a})
    {player : Player} {choice : M.Action player}
    (hturn : view.turn pref.pref = .play player)
    (hmove : action.1 player = some choice) :
    view.boundedEventOfLegalJointAction horizon pref action =
      .play player choice :=
  (view.boundedEventOfLegalJointAction_represents horizon pref action).2
    player choice hturn hmove

/-- Extract the available primitive machine event represented by a legal action
in a bounded asynchronous-machine FOSG view. -/
noncomputable def selectedBoundedEventOfLegalJointAction
    (view : M.FOSGView) (horizon : Nat)
    (pref : M.BoundedRunPrefix horizon)
    (action :
      {a : JointAction M.Action //
        JointActionLegal M.Action (view.boundedActive horizon)
          (view.boundedTerminal horizon)
          (view.boundedAvailableActions horizon) pref a}) :
    {event : M.Event // M.EventAvailable pref.lastState event} :=
  ⟨view.boundedEventOfLegalJointAction horizon pref action,
    view.boundedEventOfLegalJointAction_available horizon pref action⟩

/-- Interpret an asynchronous protocol machine as a horizon-bounded FOSG over
bounded event/state prefixes.

The transition kernel remains the selected `Machine.step`; the bound only
turns the presentation terminal at the requested horizon. -/
noncomputable def toBoundedFOSG (view : M.FOSGView) (horizon : Nat) :
    FOSG Player (M.BoundedRunPrefix horizon) M.Action M.Obs M.Public where
  init := BoundedRunPrefix.init M horizon
  active := view.boundedActive horizon
  availableActions := view.boundedAvailableActions horizon
  terminal := view.boundedTerminal horizon
  transition := fun pref action =>
    (M.step (view.boundedEventOfLegalJointAction horizon pref action)
      pref.lastState).map
      (fun next =>
        pref.snoc
          (by
            have hnot :
                ¬ horizon ≤ pref.pref.events.length := by
              intro hle
              exact action.2.1 (Or.inr hle)
            exact Nat.lt_of_not_ge hnot)
          (view.boundedEventOfLegalJointAction horizon pref action) next)
  reward := fun pref action dst player =>
    view.reward pref.pref
      (view.boundedEventOfLegalJointAction horizon pref action)
      dst.pref player
  privObs := fun player _pref _action dst =>
    M.observe player dst.lastState
  pubObs := fun _pref _action dst =>
    M.publicView dst.lastState
  terminal_active_eq_empty := by
    intro pref hterminal
    by_cases hcut : horizon ≤ pref.pref.events.length
    · simp [boundedActive, hcut]
    · have hmachine : M.terminal pref.lastState := by
        cases hterminal with
        | inl h => exact h
        | inr h => exact False.elim (hcut h)
      cases hturn : view.turn pref.pref with
      | internal event =>
          simp [boundedActive, active, hcut, hturn]
      | play player =>
          exact False.elim (view.terminal_not_play hmachine hturn)
  terminal_no_legal := by
    intro _pref _action hterminal hlegal
    exact hlegal.1 hterminal
  nonterminal_exists_legal := by
    intro pref hterminal
    have hmachine : ¬ M.terminal pref.lastState := by
      intro h
      exact hterminal (Or.inl h)
    have hcut : ¬ horizon ≤ pref.pref.events.length := by
      intro h
      exact hterminal (Or.inr h)
    have havailable := view.turn_available (pref := pref.pref) hmachine
    cases hturn : view.turn pref.pref with
    | internal event =>
        refine ⟨GameTheory.FOSG.noopAction M.Action, ⟨hterminal, ?_⟩⟩
        intro player
        simp [GameTheory.FOSG.noopAction, boundedActive, active, hturn, hcut]
    | play player =>
        rw [hturn] at havailable
        rcases havailable with ⟨choice, hchoice⟩
        refine ⟨singletonJointAction M player choice, ⟨hterminal, ?_⟩⟩
        intro other
        by_cases hother : other = player
        · subst hother
          simp [singletonJointAction, boundedActive, boundedAvailableActions,
            active, availableActions, hturn, hcut, hchoice]
        · simp [singletonJointAction, boundedActive, active, hturn, hcut,
            hother]

@[simp] theorem toBoundedFOSG_init (view : M.FOSGView) (horizon : Nat) :
    (view.toBoundedFOSG horizon).init =
      BoundedRunPrefix.init M horizon := rfl

@[simp] theorem toBoundedFOSG_active (view : M.FOSGView)
    (horizon : Nat) (pref : M.BoundedRunPrefix horizon) :
    (view.toBoundedFOSG horizon).active pref =
      view.boundedActive horizon pref := rfl

@[simp] theorem toBoundedFOSG_availableActions (view : M.FOSGView)
    (horizon : Nat) (pref : M.BoundedRunPrefix horizon)
    (player : Player) :
    (view.toBoundedFOSG horizon).availableActions pref player =
      view.boundedAvailableActions horizon pref player := rfl

@[simp] theorem toBoundedFOSG_terminal (view : M.FOSGView)
    (horizon : Nat) (pref : M.BoundedRunPrefix horizon) :
    (view.toBoundedFOSG horizon).terminal pref =
      view.boundedTerminal horizon pref := rfl

@[simp] theorem toBoundedFOSG_transition (view : M.FOSGView)
    (horizon : Nat) (pref : M.BoundedRunPrefix horizon)
    (action : (view.toBoundedFOSG horizon).LegalAction pref) :
    (view.toBoundedFOSG horizon).transition pref action =
      (M.step (view.boundedEventOfLegalJointAction horizon pref action)
        pref.lastState).map
        (fun next =>
          pref.snoc
            (by
              have hnot :
                  ¬ horizon ≤ pref.pref.events.length := by
                intro hle
                exact action.2.1 (Or.inr hle)
              exact Nat.lt_of_not_ge hnot)
            (view.boundedEventOfLegalJointAction horizon pref action) next) :=
  rfl

@[simp] theorem toBoundedFOSG_privObs (view : M.FOSGView)
    (horizon : Nat) (player : Player)
    (pref : M.BoundedRunPrefix horizon)
    (action : (view.toBoundedFOSG horizon).LegalAction pref)
    (dst : M.BoundedRunPrefix horizon) :
    (view.toBoundedFOSG horizon).privObs player pref action dst =
      M.observe player dst.lastState := rfl

@[simp] theorem toBoundedFOSG_pubObs (view : M.FOSGView)
    (horizon : Nat) (pref : M.BoundedRunPrefix horizon)
    (action : (view.toBoundedFOSG horizon).LegalAction pref)
    (dst : M.BoundedRunPrefix horizon) :
    (view.toBoundedFOSG horizon).pubObs pref action dst =
      M.publicView dst.lastState := rfl

/-- Projecting one bounded derived-FOSG transition to its endpoint state gives
exactly the selected asynchronous machine step. -/
theorem toBoundedFOSG_transition_map_lastState_eq_step
    (view : M.FOSGView) (horizon : Nat)
    (pref : M.BoundedRunPrefix horizon)
    (action : (view.toBoundedFOSG horizon).LegalAction pref) :
    PMF.map (fun dst : M.BoundedRunPrefix horizon => dst.lastState)
        ((view.toBoundedFOSG horizon).transition pref action) =
      M.step (view.boundedEventOfLegalJointAction horizon pref action)
        pref.lastState := by
  rw [toBoundedFOSG_transition]
  rw [PMF.map_comp]
  change
    PMF.map
        (fun dst : M.State =>
          (pref.snoc
            (by
              have hnot :
                  ¬ horizon ≤ pref.pref.events.length := by
                intro hle
                exact action.2.1 (Or.inr hle)
              exact Nat.lt_of_not_ge hnot)
            (view.boundedEventOfLegalJointAction horizon pref action)
            dst).lastState)
        (M.step (view.boundedEventOfLegalJointAction horizon pref action)
          pref.lastState) =
      M.step (view.boundedEventOfLegalJointAction horizon pref action)
        pref.lastState
  simpa using
    (PMF.map_id
      (p := M.step
        (view.boundedEventOfLegalJointAction horizon pref action)
        pref.lastState))

/-- Every supported bounded-FOSG transition appends exactly one primitive event
to the destination prefix. -/
theorem toBoundedFOSG_transition_support_events_length
    (view : M.FOSGView) (horizon : Nat)
    (pref : M.BoundedRunPrefix horizon)
    (action : (view.toBoundedFOSG horizon).LegalAction pref)
    {dst : M.BoundedRunPrefix horizon}
    (hsupp :
      (view.toBoundedFOSG horizon).transition pref action dst ≠ 0) :
    dst.pref.events.length = pref.pref.events.length + 1 := by
  have hmem :
      dst ∈ ((view.toBoundedFOSG horizon).transition pref action).support := by
    exact (PMF.mem_support_iff _ _).2 hsupp
  rw [toBoundedFOSG_transition] at hmem
  rcases (PMF.mem_support_map_iff _ _ _).mp hmem with
    ⟨next, _hnext, hdst⟩
  rw [← hdst]
  simp [BoundedRunPrefix.snoc, RunPrefix.snoc]

/-- Along a bounded asynchronous-machine-derived FOSG chain, the endpoint
prefix event length is the starting prefix event length plus the number of
realized FOSG steps. -/
theorem toBoundedFOSG_lastState_events_length_from
    (view : M.FOSGView) (horizon : Nat) :
    ∀ {start : M.BoundedRunPrefix horizon}
      {steps : List (view.toBoundedFOSG horizon).Step},
      (view.toBoundedFOSG horizon).StepChainFrom start steps →
      ((view.toBoundedFOSG horizon).lastStateFrom start steps).pref.events.length =
        start.pref.events.length + steps.length
  | start, [], _hchain => by
      simp [GameTheory.FOSG.lastStateFrom]
  | start, step :: steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      let action : (view.toBoundedFOSG horizon).LegalAction start :=
        hsrc ▸ step.act
      have hsupp :
          (view.toBoundedFOSG horizon).transition start action step.dst ≠ 0 := by
        subst hsrc
        simpa [action] using step.support
      have hstep :
          step.dst.pref.events.length =
            start.pref.events.length + 1 :=
        view.toBoundedFOSG_transition_support_events_length
          horizon start action hsupp
      have htailLen :
          ((view.toBoundedFOSG horizon).lastStateFrom step.dst steps).pref.events.length =
            step.dst.pref.events.length + steps.length :=
        toBoundedFOSG_lastState_events_length_from
          (view := view) (horizon := horizon) htail
      calc
        ((view.toBoundedFOSG horizon).lastStateFrom start (step :: steps)).pref.events.length
            =
          ((view.toBoundedFOSG horizon).lastStateFrom step.dst steps).pref.events.length := rfl
        _ = step.dst.pref.events.length + steps.length := htailLen
        _ = (start.pref.events.length + 1) + steps.length := by rw [hstep]
        _ = start.pref.events.length + (step :: steps).length := by
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- In a bounded asynchronous-machine-derived FOSG history, the stored machine
prefix has exactly one primitive event for each realized FOSG step. -/
theorem toBoundedFOSG_history_events_length
    (view : M.FOSGView) (horizon : Nat)
    (h : (view.toBoundedFOSG horizon).History) :
    h.lastState.pref.events.length = h.steps.length := by
  have hlen :=
    view.toBoundedFOSG_lastState_events_length_from
      (horizon := horizon) h.chain
  simpa [GameTheory.FOSG.History.lastState]
    using hlen

/-- A bounded asynchronous-machine-derived FOSG player view contains exactly
one observation event for each realized FOSG step. Own-action events are
additional recall data and do not affect this count. -/
theorem toBoundedFOSG_history_playerView_observationEvents_length
    (view : M.FOSGView) (horizon : Nat)
    (h : (view.toBoundedFOSG horizon).History) (player : Player) :
    (GameTheory.FOSG.InfoState.observationEvents
      (G := view.toBoundedFOSG horizon) (i := player)
      (h.playerView player)).length = h.steps.length := by
  let G := view.toBoundedFOSG horizon
  change
    (GameTheory.FOSG.InfoState.observationEvents
      (G := G) (i := player)
      (GameTheory.FOSG.History.playerViewFrom
        (G := G) player h.steps)).length = h.steps.length
  induction h.steps with
  | nil =>
      rfl
  | cons step steps ih =>
      have ihsucc := congrArg Nat.succ ih
      cases hmove : step.ownAction? player with
      | none =>
          simpa [GameTheory.FOSG.History.playerViewFrom,
            GameTheory.FOSG.Step.playerView,
            GameTheory.FOSG.InfoState.observationEvents, hmove,
            Nat.add_comm] using ihsucc
      | some action =>
          simpa [GameTheory.FOSG.History.playerViewFrom,
            GameTheory.FOSG.Step.playerView,
            GameTheory.FOSG.InfoState.observationEvents, hmove,
            Nat.add_comm] using ihsucc

/-- In a nonempty bounded asynchronous-machine-derived FOSG history, the latest
private/public observation is the observation of the endpoint machine state. -/
theorem toBoundedFOSG_latestObservation?_history_of_ne_nil
    (view : M.FOSGView) (horizon : Nat) (player : Player)
    (h : (view.toBoundedFOSG horizon).History)
    (hne : h.steps ≠ []) :
    GameTheory.FOSG.InfoState.latestObservation?
        (G := view.toBoundedFOSG horizon) (i := player)
        (h.playerView player) =
      some (M.observe player h.lastState.lastState,
        M.publicView h.lastState.lastState) := by
  let G := view.toBoundedFOSG horizon
  cases h with
  | mk steps chain =>
      induction steps using List.reverseRecOn with
      | nil =>
          exact False.elim (hne rfl)
      | append_singleton steps step ih =>
          let hprefix : G.History :=
            { steps := steps
              chain := GameTheory.FOSG.StepChainFrom.left
                (G := G) (es₁ := steps) (es₂ := [step]) chain }
          have hright :
              G.StepChainFrom (G.lastStateFrom G.init steps) [step] :=
            GameTheory.FOSG.StepChainFrom.right
              (G := G) (es₁ := steps) (es₂ := [step]) chain
          have hsrc : step.src = hprefix.lastState := by
            simpa [hprefix, GameTheory.FOSG.History.lastState,
              GameTheory.FOSG.StepChainFrom] using hright.1
          let hfull : G.History := hprefix.appendStep step hsrc
          have hEq :
              ({ steps := steps ++ [step], chain := chain } : G.History) =
                hfull := by
            ext
            rfl
          rw [hEq]
          unfold hfull
          simpa [G, toBoundedFOSG_privObs, toBoundedFOSG_pubObs] using
            GameTheory.FOSG.History.latestObservation?_playerView_appendStep
              (G := G) hprefix player step hsrc

/-- The horizon-bounded asynchronous-machine-derived FOSG is bounded by its
presentation horizon. -/
theorem toBoundedFOSG_boundedHorizon
    (view : M.FOSGView) (horizon : Nat) :
    (view.toBoundedFOSG horizon).BoundedHorizon horizon := by
  intro h hlen
  change (view.toBoundedFOSG horizon).terminal h.lastState
  rw [toBoundedFOSG_terminal]
  exact Or.inr (by
    rw [view.toBoundedFOSG_history_events_length horizon h, hlen])

end FOSGView

end Machine

end Vegas
