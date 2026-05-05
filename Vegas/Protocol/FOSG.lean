import Vegas.Protocol.Machine
import GameTheory.Languages.FOSG.Compile

/-!
# FOSG views of protocol machines

This module derives factored-observation stochastic games from protocol
machines at strategic checkpoints.  A FOSG step is a player-facing round over
machine states, not a selected primitive machine event.  The view owns the
round action alphabet; for graph protocols a single player's round action can
therefore cover every owned node in the current frontier.
-/

namespace Vegas

open GameTheory

namespace Machine

variable {Player : Type}

/-- Horizon-bounded state wrapper for finite FOSG presentations.  The counter
is presentation data; the underlying machine state remains the semantic state. -/
structure BoundedState (M : Machine Player) (horizon : Nat) where
  state : M.State
  depth : Nat
  depth_le : depth ≤ horizon

namespace BoundedState

variable {M : Machine Player} {horizon : Nat}

@[ext] theorem ext
    {left right : M.BoundedState horizon}
    (hstate : left.state = right.state)
    (hdepth : left.depth = right.depth) :
    left = right := by
  cases left
  cases right
  cases hstate
  cases hdepth
  rfl

/-- Initial bounded presentation state. -/
def init (M : Machine Player) (horizon : Nat) : M.BoundedState horizon where
  state := M.init
  depth := 0
  depth_le := by omega

/-- Step the bounded presentation counter. -/
def succ (pref : M.BoundedState horizon)
    (hlt : pref.depth < horizon) (next : M.State) :
    M.BoundedState horizon where
  state := next
  depth := pref.depth + 1
  depth_le := by omega

@[simp] theorem init_state (M : Machine Player) (horizon : Nat) :
    (BoundedState.init M horizon).state = M.init := rfl

@[simp] theorem init_depth (M : Machine Player) (horizon : Nat) :
    (BoundedState.init M horizon).depth = 0 := rfl

@[simp] theorem succ_state
    (pref : M.BoundedState horizon) (hlt : pref.depth < horizon)
    (next : M.State) :
    (pref.succ hlt next).state = next := rfl

@[simp] theorem succ_depth
    (pref : M.BoundedState horizon) (hlt : pref.depth < horizon)
    (next : M.State) :
    (pref.succ hlt next).depth = pref.depth + 1 := rfl

@[reducible] noncomputable instance instFintype
    [Fintype M.State] :
    Fintype (M.BoundedState horizon) := by
  classical
  let e :
      M.BoundedState horizon ≃ M.State × Fin (horizon + 1) :=
    { toFun := fun s =>
        (s.state, ⟨s.depth, Nat.lt_succ_of_le s.depth_le⟩)
      invFun := fun p =>
        { state := p.1
          depth := p.2.1
          depth_le := Nat.le_of_lt_succ p.2.2 }
      left_inv := by
        intro s
        cases s
        rfl
      right_inv := by
        intro p
        cases p
        rfl }
  exact Fintype.ofEquiv _ e.symm

end BoundedState

variable [DecidableEq Player]

/-- A checkpoint FOSG view of a machine.

The view supplies its own FOSG action type.  This is essential for frontier
rounds: a player-facing action need not be a single primitive machine action. -/
structure FOSGView (M : Machine Player) where
  Act : Player → Type
  active : M.State → Finset Player
  availableActions : M.State → (player : Player) → Set (Act player)
  transition :
    (state : M.State) →
      {a : JointAction Act //
        JointActionLegal Act active M.terminal availableActions state a} →
      PMF M.State
  reward :
    (src : M.State) →
      {a : JointAction Act //
        JointActionLegal Act active M.terminal availableActions src a} →
      M.State → Player → ℝ
  terminal_active_eq_empty :
    ∀ {state : M.State}, M.terminal state → active state = ∅
  nonterminal_exists_legal :
    ∀ {state : M.State}, ¬ M.terminal state →
      ∃ a : JointAction Act,
        JointActionLegal Act active M.terminal availableActions state a

namespace FOSGView

variable {M : Machine Player}

/-- Interpret a checkpoint machine view as a native FOSG over machine states. -/
noncomputable def toFOSG (view : M.FOSGView) :
    FOSG Player M.State view.Act M.Obs M.Public where
  init := M.init
  active := view.active
  availableActions := view.availableActions
  terminal := M.terminal
  transition := view.transition
  reward := view.reward
  privObs := fun player _src _action dst => M.observe player dst
  pubObs := fun _src _action dst => M.publicView dst
  terminal_active_eq_empty := view.terminal_active_eq_empty
  terminal_no_legal := by
    intro _state _action hterminal hlegal
    exact hlegal.1 hterminal
  nonterminal_exists_legal := view.nonterminal_exists_legal

@[simp] theorem toFOSG_init (view : M.FOSGView) :
    view.toFOSG.init = M.init := rfl

@[simp] theorem toFOSG_active (view : M.FOSGView)
    (state : M.State) :
    view.toFOSG.active state = view.active state := rfl

@[simp] theorem toFOSG_availableActions (view : M.FOSGView)
    (state : M.State) (player : Player) :
    view.toFOSG.availableActions state player =
      view.availableActions state player := rfl

@[simp] theorem toFOSG_terminal (view : M.FOSGView)
    (state : M.State) :
    view.toFOSG.terminal state = M.terminal state := rfl

@[simp] theorem toFOSG_transition (view : M.FOSGView)
    (state : M.State) (action : view.toFOSG.LegalAction state) :
    view.toFOSG.transition state action =
      view.transition state action := rfl

@[simp] theorem toFOSG_reward (view : M.FOSGView)
    (state : M.State) (action : view.toFOSG.LegalAction state)
    (dst : M.State) (player : Player) :
    view.toFOSG.reward state action dst player =
      view.reward state action dst player := rfl

@[simp] theorem toFOSG_privObs (view : M.FOSGView)
    (player : Player) (state : M.State)
    (action : view.toFOSG.LegalAction state)
    (dst : M.State) :
    view.toFOSG.privObs player state action dst =
      M.observe player dst := rfl

@[simp] theorem toFOSG_pubObs (view : M.FOSGView)
    (state : M.State) (action : view.toFOSG.LegalAction state)
    (dst : M.State) :
    view.toFOSG.pubObs state action dst =
      M.publicView dst := rfl

/-- Terminal predicate for a horizon-bounded checkpoint view. -/
def boundedTerminal (_view : M.FOSGView) (horizon : Nat)
    (state : M.BoundedState horizon) : Prop :=
  M.terminal state.state ∨ horizon ≤ state.depth

/-- Active players before the cutoff; none are active at the cutoff. -/
def boundedActive (view : M.FOSGView) (horizon : Nat)
    (state : M.BoundedState horizon) : Finset Player :=
  if horizon ≤ state.depth then ∅ else view.active state.state

/-- Available round actions before the cutoff; no actions at the cutoff. -/
def boundedAvailableActions (view : M.FOSGView) (horizon : Nat)
    (state : M.BoundedState horizon) (player : Player) :
    Set (view.Act player) :=
  if horizon ≤ state.depth then ∅
  else view.availableActions state.state player

/-- Repackage a legal bounded action as a legal unbounded action for the
underlying checkpoint state. -/
noncomputable def boundedActionToAction
    (view : M.FOSGView) (horizon : Nat)
    (state : M.BoundedState horizon)
    (action :
      {a : JointAction view.Act //
        JointActionLegal view.Act (view.boundedActive horizon)
          (view.boundedTerminal horizon)
          (view.boundedAvailableActions horizon) state a}) :
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

/-- Horizon-bounded checkpoint FOSG.  The bound is a presentation cutoff; each
FOSG round increments the counter by one. -/
noncomputable def toBoundedFOSG (view : M.FOSGView) (horizon : Nat) :
    FOSG Player (M.BoundedState horizon) view.Act M.Obs M.Public where
  init := BoundedState.init M horizon
  active := view.boundedActive horizon
  availableActions := view.boundedAvailableActions horizon
  terminal := view.boundedTerminal horizon
  transition := fun state action =>
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
  reward := fun state action dst player =>
    view.reward state.state
      (view.boundedActionToAction horizon state action)
      dst.state player
  privObs := fun player _src _action dst => M.observe player dst.state
  pubObs := fun _src _action dst => M.publicView dst.state
  terminal_active_eq_empty := by
    intro state hterminal
    by_cases hcut : horizon ≤ state.depth
    · simp [boundedActive, hcut]
    · have hmachine : M.terminal state.state := by
        cases hterminal with
        | inl h => exact h
        | inr h => exact False.elim (hcut h)
      simp [boundedActive, hcut, view.terminal_active_eq_empty hmachine]
  terminal_no_legal := by
    intro _state _action hterminal hlegal
    exact hlegal.1 hterminal
  nonterminal_exists_legal := by
    intro state hterminal
    have hmachine : ¬ M.terminal state.state := by
      intro h
      exact hterminal (Or.inl h)
    have hcut : ¬ horizon ≤ state.depth := by
      intro h
      exact hterminal (Or.inr h)
    rcases view.nonterminal_exists_legal hmachine with ⟨action, haction⟩
    refine ⟨action, ?_⟩
    refine ⟨hterminal, ?_⟩
    intro player
    cases hmove : action player with
    | none =>
        have hnot : player ∉ view.active state.state := by
          simpa [hmove] using haction.2 player
        simpa [boundedActive, hcut, hmove] using hnot
    | some choice =>
        have hpair :
            player ∈ view.active state.state ∧
              choice ∈ view.availableActions state.state player := by
          simpa [hmove] using haction.2 player
        exact ⟨by simpa [boundedActive, hcut] using hpair.1,
          by simpa [boundedAvailableActions, hcut] using hpair.2⟩

@[simp] theorem toBoundedFOSG_init
    (view : M.FOSGView) (horizon : Nat) :
    (view.toBoundedFOSG horizon).init =
      BoundedState.init M horizon := rfl

@[simp] theorem toBoundedFOSG_active
    (view : M.FOSGView) (horizon : Nat)
    (state : M.BoundedState horizon) :
    (view.toBoundedFOSG horizon).active state =
      view.boundedActive horizon state := rfl

@[simp] theorem toBoundedFOSG_availableActions
    (view : M.FOSGView) (horizon : Nat)
    (state : M.BoundedState horizon) (player : Player) :
    (view.toBoundedFOSG horizon).availableActions state player =
      view.boundedAvailableActions horizon state player := rfl

@[simp] theorem toBoundedFOSG_terminal
    (view : M.FOSGView) (horizon : Nat)
    (state : M.BoundedState horizon) :
    (view.toBoundedFOSG horizon).terminal state =
      view.boundedTerminal horizon state := rfl

@[simp] theorem toBoundedFOSG_transition
    (view : M.FOSGView) (horizon : Nat)
    (state : M.BoundedState horizon)
    (action : (view.toBoundedFOSG horizon).LegalAction state) :
    (view.toBoundedFOSG horizon).transition state action =
      (view.transition state.state
        (view.boundedActionToAction horizon state action)).map
        (fun next =>
          state.succ
            (by
              have hnot : ¬ horizon ≤ state.depth := by
                intro hle
                exact action.2.1 (Or.inr hle)
              exact Nat.lt_of_not_ge hnot)
            next) := rfl

@[simp] theorem toBoundedFOSG_privObs
    (view : M.FOSGView) (horizon : Nat) (player : Player)
    (state : M.BoundedState horizon)
    (action : (view.toBoundedFOSG horizon).LegalAction state)
    (dst : M.BoundedState horizon) :
    (view.toBoundedFOSG horizon).privObs player state action dst =
      M.observe player dst.state := rfl

@[simp] theorem toBoundedFOSG_pubObs
    (view : M.FOSGView) (horizon : Nat)
    (state : M.BoundedState horizon)
    (action : (view.toBoundedFOSG horizon).LegalAction state)
    (dst : M.BoundedState horizon) :
    (view.toBoundedFOSG horizon).pubObs state action dst =
      M.publicView dst.state := rfl

/-- Supported bounded transitions increment the presentation depth by one. -/
theorem toBoundedFOSG_transition_support_depth
    (view : M.FOSGView) (horizon : Nat)
    (state : M.BoundedState horizon)
    (action : (view.toBoundedFOSG horizon).LegalAction state)
    {dst : M.BoundedState horizon}
    (hsupp :
      (view.toBoundedFOSG horizon).transition state action dst ≠ 0) :
    dst.depth = state.depth + 1 := by
  have hmem :
      dst ∈ ((view.toBoundedFOSG horizon).transition state action).support := by
    exact (PMF.mem_support_iff _ _).2 hsupp
  rw [toBoundedFOSG_transition] at hmem
  rcases (PMF.mem_support_map_iff _ _ _).mp hmem with
    ⟨next, _hnext, hdst⟩
  rw [← hdst]
  simp [BoundedState.succ]

/-- Along a bounded checkpoint FOSG chain, the presentation depth is the
starting depth plus the number of realized FOSG steps. -/
theorem toBoundedFOSG_lastState_depth_from
    (view : M.FOSGView) (horizon : Nat) :
    ∀ {start : M.BoundedState horizon}
      {steps : List (view.toBoundedFOSG horizon).Step},
      (view.toBoundedFOSG horizon).StepChainFrom start steps →
      ((view.toBoundedFOSG horizon).lastStateFrom start steps).depth =
        start.depth + steps.length
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
          step.dst.depth = start.depth + 1 :=
        view.toBoundedFOSG_transition_support_depth
          horizon start action hsupp
      have htailLen :
          ((view.toBoundedFOSG horizon).lastStateFrom step.dst steps).depth =
            step.dst.depth + steps.length :=
        toBoundedFOSG_lastState_depth_from
          (view := view) (horizon := horizon) htail
      calc
        ((view.toBoundedFOSG horizon).lastStateFrom start (step :: steps)).depth
            =
          ((view.toBoundedFOSG horizon).lastStateFrom step.dst steps).depth := rfl
        _ = step.dst.depth + steps.length := htailLen
        _ = (start.depth + 1) + steps.length := by rw [hstep]
        _ = start.depth + (step :: steps).length := by
          simp [Nat.add_assoc, Nat.add_comm]

/-- In a bounded checkpoint FOSG history, the presentation depth is exactly
the number of realized FOSG rounds. -/
theorem toBoundedFOSG_history_depth
    (view : M.FOSGView) (horizon : Nat)
    (h : (view.toBoundedFOSG horizon).History) :
    h.lastState.depth = h.steps.length := by
  have hlen :=
    view.toBoundedFOSG_lastState_depth_from
      (horizon := horizon) h.chain
  simpa [GameTheory.FOSG.History.lastState]
    using hlen

/-- A bounded checkpoint FOSG player view contains exactly one observation
event for each realized FOSG round. -/
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

/-- In a nonempty bounded checkpoint FOSG history, the latest private/public
observation is the observation of the endpoint machine state. -/
theorem toBoundedFOSG_latestObservation?_history_of_ne_nil
    (view : M.FOSGView) (horizon : Nat) (player : Player)
    (h : (view.toBoundedFOSG horizon).History)
    (hne : h.steps ≠ []) :
    GameTheory.FOSG.InfoState.latestObservation?
        (G := view.toBoundedFOSG horizon) (i := player)
        (h.playerView player) =
      some (M.observe player h.lastState.state,
        M.publicView h.lastState.state) := by
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

/-- The horizon-bounded checkpoint FOSG is bounded by its presentation
horizon. -/
theorem toBoundedFOSG_boundedHorizon
    (view : M.FOSGView) (horizon : Nat) :
    (view.toBoundedFOSG horizon).BoundedHorizon horizon := by
  intro h hlen
  change (view.toBoundedFOSG horizon).terminal h.lastState
  rw [toBoundedFOSG_terminal]
  exact Or.inr (by
    rw [view.toBoundedFOSG_history_depth horizon h, hlen])

/-! ## Machine-view strategy carriers and outcome kernels -/

abbrev PureStrategy (view : M.FOSGView) (player : Player) : Type :=
  view.toFOSG.ReachableLegalPureStrategy player

abbrev PureProfile (view : M.FOSGView) : Type :=
  view.toFOSG.ReachableLegalPureProfile

abbrev BehavioralStrategy (view : M.FOSGView) (player : Player) : Type :=
  view.toFOSG.ReachableLegalBehavioralStrategy player

abbrev BehavioralProfile (view : M.FOSGView) : Type :=
  view.toFOSG.ReachableLegalBehavioralProfile

abbrev MixedProfile (view : M.FOSGView) : Type :=
  ∀ player, PMF (view.PureStrategy player)

noncomputable def historyOutcome
    (view : M.FOSGView) (h : view.toFOSG.History) : M.Outcome :=
  M.outcome h.lastState

noncomputable def outcomeFromBehavioral
    (view : M.FOSGView)
    [Fintype Player] [Fintype M.State]
    [∀ i, Fintype (Option (view.Act i))]
    [DecidablePred view.toFOSG.terminal]
    (β : view.BehavioralProfile) (horizon : Nat) :
    PMF M.Outcome :=
  PMF.map view.historyOutcome (view.toFOSG.runDist horizon β.extend)

noncomputable def outcomeFromPure
    (view : M.FOSGView)
    [Fintype Player] [Fintype M.State]
    [∀ i, Fintype (Option (view.Act i))]
    [DecidablePred view.toFOSG.terminal]
    (π : view.PureProfile) (horizon : Nat) :
    PMF M.Outcome :=
  PMF.map view.historyOutcome
    (view.toFOSG.runDist horizon (view.toFOSG.legalPureToBehavioral π.extend))

abbrev BoundedPureStrategy
    (view : M.FOSGView) (horizon : Nat) (player : Player) : Type :=
  (view.toBoundedFOSG horizon).ReachableLegalPureStrategy player

abbrev BoundedPureProfile (view : M.FOSGView) (horizon : Nat) : Type :=
  (view.toBoundedFOSG horizon).ReachableLegalPureProfile

abbrev BoundedBehavioralStrategy
    (view : M.FOSGView) (horizon : Nat) (player : Player) : Type :=
  (view.toBoundedFOSG horizon).ReachableLegalBehavioralStrategy player

abbrev BoundedBehavioralProfile (view : M.FOSGView) (horizon : Nat) : Type :=
  (view.toBoundedFOSG horizon).ReachableLegalBehavioralProfile

abbrev BoundedMixedProfile (view : M.FOSGView) (horizon : Nat) : Type :=
  ∀ player, PMF (view.BoundedPureStrategy horizon player)

noncomputable def boundedHistoryOutcome
    (view : M.FOSGView) (horizon : Nat)
    (h : (view.toBoundedFOSG horizon).History) : M.Outcome :=
  M.outcome h.lastState.state

noncomputable def boundedOutcomeFromBehavioral
    (view : M.FOSGView) (horizon : Nat)
    [Fintype Player] [Fintype (M.BoundedState horizon)]
    [∀ i, Fintype (Option (view.Act i))]
    [DecidablePred (view.toBoundedFOSG horizon).terminal]
    (β : view.BoundedBehavioralProfile horizon)
    (steps : Nat) : PMF M.Outcome :=
  PMF.map (view.boundedHistoryOutcome horizon)
    ((view.toBoundedFOSG horizon).runDist steps β.extend)

noncomputable def boundedOutcomeFromPure
    (view : M.FOSGView) (horizon : Nat)
    [Fintype Player] [Fintype (M.BoundedState horizon)]
    [∀ i, Fintype (Option (view.Act i))]
    [DecidablePred (view.toBoundedFOSG horizon).terminal]
    (π : view.BoundedPureProfile horizon)
    (steps : Nat) : PMF M.Outcome :=
  PMF.map (view.boundedHistoryOutcome horizon)
    ((view.toBoundedFOSG horizon).runDist steps
      ((view.toBoundedFOSG horizon).legalPureToBehavioral π.extend))

end FOSGView

end Machine

end Vegas
