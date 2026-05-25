import GameTheory.Languages.FOSG.Compile
import Vegas.Machine.KernelGame

/-!
# Round-view FOSG presentation

This module presents a native `Machine.RoundView` as a bounded
factored-observation stochastic game.  The world state is the bounded machine
state, actions and observations are exactly those of the round view, and
rewards are paid on transitions into bounded-terminal states.
-/

namespace Vegas

open GameTheory

namespace Machine
namespace RoundView

variable {Player : Type} [DecidableEq Player]
variable {M : Machine Player}

/-- One-step terminal reward used by the FOSG presentation of a bounded round
view.  Nonterminal transitions pay zero; transitions into terminal or cutoff
states pay the machine outcome utility, with an explicit cutoff utility when
the machine has no outcome at that state. -/
noncomputable def terminalReward
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    (_src : M.BoundedState horizon)
    (_action : view.BoundedLegalAction horizon _src)
    (dst : M.BoundedState horizon) : Payoff Player := by
  classical
  exact
    if view.boundedTerminal horizon dst then
      optionOutcomeUtility M cutoff (M.outcome dst.state)
    else
      fun _ => 0

/-- Bounded FOSG presentation of a native round view. -/
noncomputable def toFOSG
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player) :
    FOSG Player (M.BoundedState horizon) view.Act M.Obs M.Public where
  init := BoundedState.init M horizon
  active := view.boundedActive horizon
  availableActions := view.boundedAvailableActions horizon
  terminal := view.boundedTerminal horizon
  transition := view.boundedTransition horizon
  reward := fun src action dst player =>
    terminalReward view horizon cutoff src action dst player
  privObs := fun player _src _action dst => M.observe player dst.state
  pubObs := fun _src _action dst => M.publicView dst.state
  terminal_active_eq_empty := by
    intro state hterm
    cases hterm with
    | inl hmachine =>
        by_cases hcut : horizon ≤ state.depth
        · simp [boundedActive, hcut]
        · simp [boundedActive, hcut, view.terminal_active_eq_empty hmachine]
    | inr hcut =>
        simp [boundedActive, hcut]
  terminal_no_legal := by
    intro _state _action hterm hlegal
    exact hlegal.1 hterm
  nonterminal_exists_legal := by
    intro state hnotTerm
    have hmachine : ¬ M.terminal state.state := by
      intro h
      exact hnotTerm (Or.inl h)
    have hcut : ¬ horizon ≤ state.depth := by
      intro h
      exact hnotTerm (Or.inr h)
    rcases view.nonterminal_exists_legal (state := state.state) hmachine with
      ⟨action, haction⟩
    refine ⟨action, hnotTerm, ?_⟩
    intro player
    have hlocal := haction.2 player
    cases hmove : action player with
    | none =>
        have hnotActive : player ∉ view.active state.state := by
          simpa [hmove] using hlocal
        simpa [boundedActive, hcut, hmove] using hnotActive
    | some choice =>
        have hpair :
            player ∈ view.active state.state ∧
              choice ∈ view.availableActions state.state player := by
          simpa [hmove] using hlocal
        exact
          ⟨by simpa [boundedActive, hcut] using hpair.1,
            by simpa [boundedAvailableActions, hcut] using hpair.2⟩

@[simp] theorem toFOSG_init
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player) :
    (view.toFOSG horizon cutoff).init = BoundedState.init M horizon := rfl

@[simp] theorem toFOSG_terminal
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    (state : M.BoundedState horizon) :
    (view.toFOSG horizon cutoff).terminal state =
      view.boundedTerminal horizon state := rfl

@[simp] theorem toFOSG_active
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    (state : M.BoundedState horizon) :
    (view.toFOSG horizon cutoff).active state =
      view.boundedActive horizon state := rfl

@[simp] theorem toFOSG_availableActions
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    (state : M.BoundedState horizon) (player : Player) :
    (view.toFOSG horizon cutoff).availableActions state player =
      view.boundedAvailableActions horizon state player := rfl

@[simp] theorem toFOSG_transition
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    (state : M.BoundedState horizon)
    (action : (view.toFOSG horizon cutoff).LegalAction state) :
    (view.toFOSG horizon cutoff).transition state action =
      view.boundedTransition horizon state action := rfl

@[simp] theorem toFOSG_reward
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    (state : M.BoundedState horizon)
    (action : (view.toFOSG horizon cutoff).LegalAction state)
    (dst : M.BoundedState horizon) (player : Player) :
    (view.toFOSG horizon cutoff).reward state action dst player =
      terminalReward view horizon cutoff state action dst player := rfl

@[simp] theorem toFOSG_privObs
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    (player : Player) (state : M.BoundedState horizon)
    (action : (view.toFOSG horizon cutoff).LegalAction state)
    (dst : M.BoundedState horizon) :
    (view.toFOSG horizon cutoff).privObs player state action dst =
      M.observe player dst.state := rfl

@[simp] theorem toFOSG_pubObs
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)
    (state : M.BoundedState horizon)
    (action : (view.toFOSG horizon cutoff).LegalAction state)
    (dst : M.BoundedState horizon) :
    (view.toFOSG horizon cutoff).pubObs state action dst =
      M.publicView dst.state := rfl

namespace ToFOSG

variable (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)

/-- Along a FOSG history generated from a bounded round view, the bounded
presentation depth is the starting depth plus the number of FOSG steps. -/
theorem lastState_depth_from :
    ∀ {start : M.BoundedState horizon}
      {steps : List (view.toFOSG horizon cutoff).Step},
      (view.toFOSG horizon cutoff).StepChainFrom start steps →
      ((view.toFOSG horizon cutoff).lastStateFrom start steps).depth =
        start.depth + steps.length
  | start, [], _hchain => by
      simp [FOSG.lastStateFrom]
  | start, step :: steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      let action : view.BoundedLegalAction horizon start :=
        hsrc ▸ step.act
      have hsupp :
          view.boundedTransition horizon start action step.dst ≠ 0 := by
        subst hsrc
        simpa [toFOSG, action] using step.support
      have hstep :
          step.dst.depth = start.depth + 1 :=
        view.boundedTransition_support_depth horizon start action hsupp
      have htailLen :
          ((view.toFOSG horizon cutoff).lastStateFrom step.dst steps).depth =
            step.dst.depth + steps.length :=
        lastState_depth_from (start := step.dst) htail
      calc
        ((view.toFOSG horizon cutoff).lastStateFrom start
            (step :: steps)).depth =
          ((view.toFOSG horizon cutoff).lastStateFrom step.dst steps).depth := rfl
        _ = step.dst.depth + steps.length := htailLen
        _ = (start.depth + 1) + steps.length := by rw [hstep]
        _ = start.depth + (step :: steps).length := by
          simp [Nat.add_assoc, Nat.add_comm]

/-- FOSG histories generated from a bounded round view have endpoint depth
equal to their history length. -/
theorem history_depth
    (h : (view.toFOSG horizon cutoff).History) :
    h.lastState.depth = h.steps.length := by
  have hdepth :=
    lastState_depth_from (view := view) (horizon := horizon)
      (cutoff := cutoff) h.chain
  simpa [FOSG.History.lastState] using hdepth

/-- The bounded FOSG presentation has the declared horizon. -/
theorem boundedHorizon :
    (view.toFOSG horizon cutoff).BoundedHorizon horizon := by
  intro h hlen
  unfold FOSG.History.IsTerminal
  rw [toFOSG_terminal]
  exact Or.inr (by
    rw [history_depth (view := view) (horizon := horizon)
      (cutoff := cutoff) h, hlen])

end ToFOSG

/-- Bounded-horizon proof for the FOSG presentation of a round view. -/
theorem toFOSG_boundedHorizon
    (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player) :
    (view.toFOSG horizon cutoff).BoundedHorizon horizon :=
  ToFOSG.boundedHorizon view horizon cutoff

end RoundView
end Machine

end Vegas
