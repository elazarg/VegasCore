/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Theorems.Kuhn
import Vegas.Machine.KernelGame

/-!
# Kuhn adapter: action and model construction

The adapter action at an information state (`KuhnActionAtInfo`), default/
nonempty instances, joint-action assembly, and the adapter step and model
(`kuhnStep`, `kuhnModel`) connecting native round views to the Kuhn theorem.
-/

namespace Vegas

open GameTheory

namespace Machine

variable {Player : Type} {M : Machine Player}

namespace RoundView


/-- A Kuhn-adapter action at a reachable native information state is an
optional native move that is legal at every bounded history realizing that
information state. -/
def KuhnActionAtInfo
    (view : M.RoundView) (horizon : Nat)
    (player : Player)
    (info : view.ReachableInfoState horizon player) : Type :=
  { move : Option (view.Act player) //
    ∀ h : view.BoundedHistory horizon,
      view.reachableInfoStateOfHistory horizon player h = info →
        move ∈ view.boundedAvailableMoves horizon h player }

namespace KuhnActionAtInfo

variable {view : M.RoundView} {horizon : Nat}
variable {player : Player} {info : view.ReachableInfoState horizon player}

@[simp] theorem val_mk
    (move : Option (view.Act player))
    (hlegal :
      ∀ h : view.BoundedHistory horizon,
        view.reachableInfoStateOfHistory horizon player h = info →
          move ∈ view.boundedAvailableMoves horizon h player) :
    (Subtype.mk move hlegal :
      view.KuhnActionAtInfo horizon player info).1 = move := rfl

end KuhnActionAtInfo

open Classical in
noncomputable instance instFintypeKuhnActionAtInfo
    (view : M.RoundView) (horizon : Nat)
    (player : Player) (info : view.ReachableInfoState horizon player)
    [Fintype (Option (view.Act player))] :
    Fintype (view.KuhnActionAtInfo horizon player info) := by
  unfold KuhnActionAtInfo
  infer_instance

/-- Menu observability gives a default adapter action at every reachable native
information state. -/
noncomputable def defaultKuhnActionAtInfo
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player) (info : view.ReachableInfoState horizon player) :
    view.KuhnActionAtInfo horizon player info := by
  classical
  let h₀ : view.BoundedHistory horizon := Classical.choose info.2
  have hinfo₀ : h₀.playerView player = info.1 :=
    Classical.choose_spec info.2
  let move : Option (view.Act player) :=
    Classical.choose (view.boundedAvailableMoves_nonempty horizon h₀ player)
  have hmove : move ∈ view.boundedAvailableMoves horizon h₀ player :=
    Classical.choose_spec (view.boundedAvailableMoves_nonempty horizon h₀ player)
  refine ⟨move, ?_⟩
  intro h hinfo
  have hview :
      h₀.playerView player = h.playerView player := by
    have hinfo' := congrArg Subtype.val hinfo
    simpa [reachableInfoStateOfHistory, hinfo₀] using hinfo'.symm
  have hmenus := hMenus player h₀ h hview
  simpa [hmenus] using hmove

/-- Menu observability makes every adapter action type nonempty. -/
@[reducible]
noncomputable def instNonemptyKuhnActionAtInfo
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon) :
    ∀ player info,
      Nonempty (view.KuhnActionAtInfo horizon player info) :=
  fun player info =>
    ⟨view.defaultKuhnActionAtInfo horizon hMenus player info⟩

/-- Menu observability gives a canonical legal pure strategy: at each
reachable information state, choose an arbitrary move from the common legal
menu for that information state. -/
noncomputable def defaultBoundedPureStrategy
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player) :
    view.BoundedPureStrategy horizon player :=
  ⟨fun info =>
      (view.defaultKuhnActionAtInfo horizon hMenus player info).1,
    by
      intro history
      exact
        (view.defaultKuhnActionAtInfo horizon hMenus player
          (view.reachableInfoStateOfHistory horizon player history)).2
          history rfl⟩

/-- Menu observability makes every native bounded pure strategy space
nonempty. -/
@[reducible]
noncomputable def instNonemptyBoundedPureStrategyOfMenus
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon) :
    ∀ player, Nonempty (view.BoundedPureStrategy horizon player) :=
  fun player =>
    ⟨view.defaultBoundedPureStrategy horizon hMenus player⟩

/-- Joint Kuhn-adapter action at a concrete bounded history. -/
abbrev KuhnActionAtHistory
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon) : Type :=
  ∀ player,
    view.KuhnActionAtInfo horizon player
      (view.reachableInfoStateOfHistory horizon player h)

/-- Forget the per-player legality proof carried by an adapter action. -/
def kuhnJointAction
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon)
    (action : view.KuhnActionAtHistory horizon h) :
    JointAction view.Act :=
  fun player => (action player).1

/-- A nonterminal adapter action is a legal native bounded joint action. -/
theorem kuhnJointAction_legal
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon)
    (hterm : ¬ view.boundedTerminal horizon h.lastState)
    (action : view.KuhnActionAtHistory horizon h) :
    JointActionLegal view.Act
      (view.boundedActive horizon)
      (view.boundedTerminal horizon)
      (view.boundedAvailableActions horizon)
      h.lastState
      (view.kuhnJointAction horizon h action) :=
  (view.boundedLegal_iff_forall horizon).2
    ⟨hterm, fun player => (action player).2 h rfl⟩

/-- Repackage a nonterminal adapter action as the native legal-action subtype. -/
def kuhnLegalAction
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon)
    (hterm : ¬ view.boundedTerminal horizon h.lastState)
    (action : view.KuhnActionAtHistory horizon h) :
    view.BoundedLegalAction horizon h.lastState :=
  ⟨view.kuhnJointAction horizon h action,
    view.kuhnJointAction_legal horizon h hterm action⟩

/-- Convert a native legal bounded joint action at a history into the
corresponding Kuhn-adapter action. `MenusObservable` upgrades legality at this
history to legality at every history with the same player information state. -/
def kuhnActionOfLegalAction
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (h : view.BoundedHistory horizon)
    (action : view.BoundedLegalAction horizon h.lastState) :
    view.KuhnActionAtHistory horizon h :=
  fun player =>
    ⟨action.1 player,
      fun h' hinfo => by
        have hview :
            h.playerView player = h'.playerView player := by
          have hinfo' := congrArg Subtype.val hinfo
          simpa [reachableInfoStateOfHistory] using hinfo'.symm
        have hmenus := hMenus player h h' hview
        have hlocal :
            action.1 player ∈
              view.boundedAvailableMoves horizon h player := by
          rw [mem_boundedAvailableMoves_iff]
          exact (view.boundedLegal_iff_forall horizon).1 action.2 |>.2 player
        simpa [hmenus] using hlocal⟩

@[simp] theorem kuhnJointAction_of_legalAction
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (h : view.BoundedHistory horizon)
    (action : view.BoundedLegalAction horizon h.lastState) :
    view.kuhnJointAction horizon h
        (view.kuhnActionOfLegalAction horizon hMenus h action) =
      action.1 := rfl

@[simp] theorem kuhnLegalAction_of_legalAction
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (h : view.BoundedHistory horizon)
    (hterm : ¬ view.boundedTerminal horizon h.lastState)
    (action : view.BoundedLegalAction horizon h.lastState) :
    view.kuhnLegalAction horizon h hterm
        (view.kuhnActionOfLegalAction horizon hMenus h action) =
      action := by
  apply Subtype.ext
  rfl

/-- One adapter-machine step. Terminal histories absorb; otherwise the native
bounded transition is lifted to histories by appending the realized round. -/
noncomputable def kuhnStep
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon)
    (action : view.KuhnActionAtHistory horizon h) :
    PMF (view.BoundedHistory horizon) := by
  classical
  if hterm : view.boundedTerminal horizon h.lastState then
    exact PMF.pure h
  else
    let legalAction := view.kuhnLegalAction horizon h hterm action
    exact
      (view.boundedTransition horizon h.lastState legalAction).map
        (fun dst => h.extendByOutcome legalAction dst)

@[simp] theorem kuhnStep_terminal
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon)
    (action : view.KuhnActionAtHistory horizon h)
    (hterm : view.boundedTerminal horizon h.lastState) :
    view.kuhnStep horizon h action = PMF.pure h := by
  simp [kuhnStep, hterm]

@[simp] theorem kuhnStep_nonterminal
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon)
    (action : view.KuhnActionAtHistory horizon h)
    (hterm : ¬ view.boundedTerminal horizon h.lastState) :
    view.kuhnStep horizon h action =
      (view.boundedTransition horizon h.lastState
          (view.kuhnLegalAction horizon h hterm action)).map
        (fun dst =>
          h.extendByOutcome
            (view.kuhnLegalAction horizon h hterm action) dst) := by
  simp [kuhnStep, hterm]

/-- The `ObsModelCore` proof adapter associated with a native bounded round
view.  Its states are native bounded histories and its observations are the
reachable native information states already used by `BoundedPureStrategy` and
`BoundedBehavioralStrategy`. -/
noncomputable def kuhnModel
    (view : M.RoundView) (horizon : Nat)
    (_hMenus : view.MenusObservable horizon) :
    ObsModelCore Player
      (view.BoundedHistory horizon)
      (fun player => view.ReachableInfoState horizon player)
      (fun player info => view.KuhnActionAtInfo horizon player info) where
  infoState := fun _ => InfoStateCore.identity _
  observe := fun player h =>
    view.reachableInfoStateOfHistory horizon player h
  machine :=
    { init := BoundedHistory.nil view horizon
      step := view.kuhnStep horizon }

@[simp] theorem kuhnModel_init
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon) :
    (view.kuhnModel horizon hMenus).init =
      BoundedHistory.nil view horizon := rfl

@[simp] theorem kuhnModel_observe
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player) (h : view.BoundedHistory horizon) :
    (view.kuhnModel horizon hMenus).observe player h =
      view.reachableInfoStateOfHistory horizon player h := rfl

@[simp] theorem kuhnModel_projectStates
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player) (trace : List (view.BoundedHistory horizon)) :
    (view.kuhnModel horizon hMenus).projectStates player trace =
      view.reachableInfoStateOfHistory horizon player
        ((view.kuhnModel horizon hMenus).lastState trace) := by
  have hcurrent :=
    ObsModelCore.currentObs_projectStates
      (view.kuhnModel horizon hMenus) player trace
  simpa [kuhnModel, ObsModelCore.currentObs] using hcurrent

@[simp]
theorem kuhnActionAtInfo_cast_val
    (view : M.RoundView) (horizon : Nat)
    {player : Player}
    {info info' : view.ReachableInfoState horizon player}
    (hinfo : info = info')
    (action : view.KuhnActionAtInfo horizon player info) :
    ((hinfo ▸ action : view.KuhnActionAtInfo horizon player info').1) =
      action.1 := by
  cases hinfo
  rfl

theorem kuhnJointAction_castJointAction
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (trace : List (view.BoundedHistory horizon))
    (action :
      ∀ player,
        view.KuhnActionAtInfo horizon player
          ((view.kuhnModel horizon hMenus).currentObs player
            ((view.kuhnModel horizon hMenus).projectStates player trace))) :
    view.kuhnJointAction horizon
        ((view.kuhnModel horizon hMenus).lastState trace)
        ((view.kuhnModel horizon hMenus).castJointAction trace action) =
      fun player => (action player).1 := by
  funext player
  simp [kuhnJointAction, ObsModelCore.castJointAction]

theorem kuhnActionAtHistory_eq_of_terminal
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon)
    (hterm : view.boundedTerminal horizon h.lastState)
    (left right : view.KuhnActionAtHistory horizon h) :
    left = right := by
  funext player
  apply Subtype.ext
  have hleft :
      (left player).1 ∈ view.boundedAvailableMoves horizon h player :=
    (left player).2 h rfl
  have hright :
      (right player).1 ∈ view.boundedAvailableMoves horizon h player :=
    (right player).2 h rfl
  rw [mem_boundedAvailableMoves_iff] at hleft hright
  have leftNone : (left player).1 = none := by
    cases hmove : (left player).1 with
    | none => rfl
    | some action =>
        cases hterm with
        | inl hmachine =>
            have hactive := view.terminal_active_eq_empty hmachine
            simp [boundedLocallyLegalAtState, boundedActive, hmove,
              hactive] at hleft
        | inr hcut =>
            simp [boundedLocallyLegalAtState, boundedActive,
              boundedAvailableActions, hmove, hcut] at hleft
  have rightNone : (right player).1 = none := by
    cases hmove : (right player).1 with
    | none => rfl
    | some action =>
        cases hterm with
        | inl hmachine =>
            have hactive := view.terminal_active_eq_empty hmachine
            simp [boundedLocallyLegalAtState, boundedActive, hmove,
              hactive] at hright
        | inr hcut =>
            simp [boundedLocallyLegalAtState, boundedActive,
              boundedAvailableActions, hmove, hcut] at hright
  rw [leftNone, rightNone]


end RoundView

end Machine

end Vegas
