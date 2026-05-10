import Vegas.GameBridge.FOSG.StateSufficiency
import Vegas.Strategic.KernelGame
import Vegas.Strategic.Vocabulary
import Vegas.Strategic.Local
import Vegas.Strategic.Domination
import Vegas.Strategic.Transport
import Vegas.Theorems.Progress
import Vegas.Theorems.Visibility

/-!
# Strategy-Surface Theorems

Project-facing names for the fact that player-facing menus and legal actions
are determined by the observations available to the acting player.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A player's whole frontier-round optional menu is determined by the public
transcript together with that player's private observation. -/
theorem checkedProgram_roundMenu_eq_of_observation_eq
    (g : WFProgram P L) (who : P)
    {left right : (programEventGraph g).Configuration}
    (hpriv : eventGraphObserve g who left = eventGraphObserve g who right)
    (hpub : eventGraphPublicView g left = eventGraphPublicView g right) :
    EventGraph.roundMenu (programEventGraph g) left who =
      EventGraph.roundMenu (programEventGraph g) right who :=
  eventGraph_roundMenu_eq_of_observation_eq g who hpriv hpub

/-- Membership in a player's frontier-round menu is transported across equal
public transcript and private observation. -/
theorem checkedProgram_roundMenu_mem_iff_of_observation_eq
    (g : WFProgram P L) (who : P)
    {left right : (programEventGraph g).Configuration}
    (hpriv : eventGraphObserve g who left = eventGraphObserve g who right)
    (hpub : eventGraphPublicView g left = eventGraphPublicView g right)
    (move :
      Option (EventGraph.PlayerRoundAction (programEventGraph g) who)) :
    move ∈ EventGraph.roundMenu (programEventGraph g) left who ↔
      move ∈ EventGraph.roundMenu (programEventGraph g) right who := by
  rw [checkedProgram_roundMenu_eq_of_observation_eq g who hpriv hpub]

/-- At the current bounded FOSG history endpoint, a player's available optional
moves are determined by the current private and public observations, provided
both histories are before the presentation cutoff. -/
theorem checkedProgram_availableMoves_eq_of_currentObservation_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hcut : ¬ horizon ≤ h.lastState.depth)
    (hcut' : ¬ horizon ≤ h'.lastState.depth)
    (hpriv :
      eventGraphObserve g who h.lastState.state =
        eventGraphObserve g who h'.lastState.state)
    (hpub :
      eventGraphPublicView g h.lastState.state =
        eventGraphPublicView g h'.lastState.state) :
    ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who =
      ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMoves h' who :=
  eventGraph_availableMoves_eq_of_currentObservation_eq
    g horizon who hcut hcut' hpriv hpub

/-- Membership in the current optional move set is transported by equality of
current private and public observations. -/
theorem checkedProgram_availableMoves_mem_iff_of_currentObservation_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hcut : ¬ horizon ≤ h.lastState.depth)
    (hcut' : ¬ horizon ≤ h'.lastState.depth)
    (hpriv :
      eventGraphObserve g who h.lastState.state =
        eventGraphObserve g who h'.lastState.state)
    (hpub :
      eventGraphPublicView g h.lastState.state =
        eventGraphPublicView g h'.lastState.state)
    (move : Option ((eventGraphFOSGView g).Act who)) :
    move ∈ ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who ↔
      move ∈
        ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMoves h' who := by
  rw [checkedProgram_availableMoves_eq_of_currentObservation_eq
    g horizon who hcut hcut' hpriv hpub]

/-- For nonempty bounded FOSG histories before cutoff, equality of latest
private/public observations determines a player's whole optional move set. -/
theorem checkedProgram_availableMoves_eq_of_latestObservation_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hcut : ¬ horizon ≤ h.lastState.depth)
    (hcut' : ¬ horizon ≤ h'.lastState.depth)
    (hne : h.steps ≠ [])
    (hne' : h'.steps ≠ [])
    (hlatest :
      GameTheory.FOSG.InfoState.latestObservation?
          (G := (eventGraphFOSGView g).toBoundedFOSG horizon)
          (i := who) (h.playerView who) =
        GameTheory.FOSG.InfoState.latestObservation?
          (G := (eventGraphFOSGView g).toBoundedFOSG horizon)
          (i := who) (h'.playerView who)) :
    ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who =
      ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMoves h' who :=
  eventGraph_availableMoves_eq_of_latestObservation_eq
    g horizon who hcut hcut' hne hne' hlatest

/-- Membership in the current optional move set is transported by equality of
latest private/public observations. -/
theorem checkedProgram_availableMoves_mem_iff_of_latestObservation_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hcut : ¬ horizon ≤ h.lastState.depth)
    (hcut' : ¬ horizon ≤ h'.lastState.depth)
    (hne : h.steps ≠ [])
    (hne' : h'.steps ≠ [])
    (hlatest :
      GameTheory.FOSG.InfoState.latestObservation?
          (G := (eventGraphFOSGView g).toBoundedFOSG horizon)
          (i := who) (h.playerView who) =
        GameTheory.FOSG.InfoState.latestObservation?
          (G := (eventGraphFOSGView g).toBoundedFOSG horizon)
          (i := who) (h'.playerView who))
    (move : Option ((eventGraphFOSGView g).Act who)) :
    move ∈ ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who ↔
      move ∈
        ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMoves h' who := by
  rw [checkedProgram_availableMoves_eq_of_latestObservation_eq
    g horizon who hcut hcut' hne hne' hlatest]

/-- Equal FOSG player views determine equal concrete action sets at histories. -/
theorem checkedProgram_availableActions_eq_of_playerView_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hinfo : h.playerView who = h'.playerView who) :
    ((eventGraphFOSGView g).toBoundedFOSG horizon).availableActionsAtHistory
        h who =
      ((eventGraphFOSGView g).toBoundedFOSG horizon).availableActionsAtHistory
        h' who :=
  ((eventGraphFOSGView g).toBoundedFOSG horizon).availableActions_eq_of_playerView_eq
    (checkedProgram_boundedFOSG_legalObservable g horizon) who hinfo

/-- The optional move set attached to a reachable information state is the same
as the optional move set at any history realizing that information state. -/
theorem checkedProgram_availableMovesAtInfoState_eq_of_history
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)) :
    ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMovesAtInfoState
        who (h.playerView who) =
      ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who :=
  ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMovesAtInfoState_eq_of_history
    (checkedProgram_boundedFOSG_legalObservable g horizon) who h

/-- Hidden value changes outside a player's current observation cannot change
that player's available moves. -/
theorem available_moves_invariant_under_unseen_hidden_values
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hcut : ¬ horizon ≤ h.lastState.depth)
    (hcut' : ¬ horizon ≤ h'.lastState.depth)
    (hpriv :
      eventGraphObserve g who h.lastState.state =
        eventGraphObserve g who h'.lastState.state)
    (hpub :
      eventGraphPublicView g h.lastState.state =
        eventGraphPublicView g h'.lastState.state) :
    ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who =
      ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMoves h' who :=
  checkedProgram_availableMoves_eq_of_currentObservation_eq
    g horizon who hcut hcut' hpriv hpub

/-- Pure strategies are extensional in player information state. -/
theorem pureStrategy_ext_of_playerView_eq
    (g : WFProgram P L) (who : P) (σ : pureStrategyAt g who)
    {h h' : (eventGraphRoundView g).BoundedHistory
      (syntaxSteps g.prog)}
    (hview : h.playerView who = h'.playerView who) :
    σ.1 ((eventGraphRoundView g).reachableInfoStateOfHistory
        (syntaxSteps g.prog) who h) =
      σ.1 ((eventGraphRoundView g).reachableInfoStateOfHistory
        (syntaxSteps g.prog) who h') := by
  apply congrArg σ.1
  apply Subtype.ext
  simpa using hview

/-- Behavioral strategies are extensional in player information state. -/
theorem behavioralStrategy_ext_of_playerView_eq
    (g : WFProgram P L) (who : P) (σ : behavioralStrategyPMFAt g who)
    {h h' : (eventGraphRoundView g).BoundedHistory
      (syntaxSteps g.prog)}
    (hview : h.playerView who = h'.playerView who) :
    σ.1 ((eventGraphRoundView g).reachableInfoStateOfHistory
        (syntaxSteps g.prog) who h) =
      σ.1 ((eventGraphRoundView g).reachableInfoStateOfHistory
        (syntaxSteps g.prog) who h') := by
  apply congrArg σ.1
  apply Subtype.ext
  simpa using hview

/-- Pure strategies cannot branch on data absent from the player's information
state. -/
theorem strategy_cannot_condition_on_unseen_hidden_values
    (g : WFProgram P L) (who : P) (σ : pureStrategyAt g who)
    {h h' : (eventGraphRoundView g).BoundedHistory
      (syntaxSteps g.prog)}
    (hview : h.playerView who = h'.playerView who) :
    σ.1 ((eventGraphRoundView g).reachableInfoStateOfHistory
        (syntaxSteps g.prog) who h) =
      σ.1 ((eventGraphRoundView g).reachableInfoStateOfHistory
        (syntaxSteps g.prog) who h') :=
  pureStrategy_ext_of_playerView_eq g who σ hview

/-- The reachable-legal pure strategy carrier never selects an unavailable
optional move at a realizing history. -/
theorem legal_strategy_never_selects_illegal_action
    (g : WFProgram P L) (who : P) (σ : pureStrategyAt g who)
    (h : (eventGraphRoundView g).BoundedHistory
      (syntaxSteps g.prog)) :
    σ.1 ((eventGraphRoundView g).reachableInfoStateOfHistory
        (syntaxSteps g.prog) who h) ∈
      (eventGraphRoundView g).boundedAvailableMoves
        (syntaxSteps g.prog) h who := by
  exact σ.2 h

/-- If an earlier commit is blocked by a frontier reveal, no strategy-facing
machine action for that commit is available.  This is the strategy-surface
form of the commit/reveal information barrier. -/
theorem prior_commit_not_available_when_reveal_frontier
    (g : WFProgram P L) (who : P)
    {cfg : (programEventGraph g).Configuration}
    {commit reveal : ProgramNode g.prog}
    {owner : P} {field : ProgramField g.prog}
    {guard : EventGraph.EventGuard L (ProgramField g.prog)
      (ProgramField.ty (p := g.prog)) field}
    {source target : ProgramField g.prog}
    {hty : source.ty = target.ty}
    {action : EventGraph.PlayerAction (programEventGraph g) who}
    (hrevealFrontier : reveal ∈ cfg.frontier)
    (hcommit :
      ProgramNode.sem g.obligations commit =
        EventGraph.NodeSem.commit owner field guard)
    (hreveal :
      ProgramNode.sem g.obligations reveal =
        EventGraph.NodeSem.reveal source target hty)
    (hrank : commit.rank < reveal.rank)
    (hactionNode : action.node = commit) :
    action ∉ EventGraph.available (programEventGraph g) cfg who := by
  intro havailable
  rcases havailable with ⟨hcommitFrontier, _hactor, _hslice, _haction⟩
  have hcommitFrontier' : commit ∈ cfg.frontier := by
    rw [← hactionNode]
    exact hcommitFrontier
  exact reveal_not_frontier_with_prior_commit
    g hcommitFrontier' hrevealFrontier hcommit hreveal hrank

/-- Active players before terminal/cutoff have a nonempty concrete action set. -/
theorem availableActionsAtHistory_nonempty_of_not_terminal_active
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History))
    (hnotTerminal :
      ¬ ((eventGraphFOSGView g).toBoundedFOSG horizon).terminal h.lastState)
    (hactive :
      who ∈ ((eventGraphFOSGView g).toBoundedFOSG horizon).active h.lastState) :
    Set.Nonempty
      (((eventGraphFOSGView g).toBoundedFOSG horizon).availableActionsAtHistory
        h who) := by
  let G := (eventGraphFOSGView g).toBoundedFOSG horizon
  rcases G.exists_legal_of_not_terminal (w := h.lastState) hnotTerminal with
    ⟨action, hlegal⟩
  have hlocal : G.locallyLegalAtState h.lastState who (action who) :=
    ((G.legal_iff_forall).mp hlegal).2 who
  cases haction : action who with
  | none =>
      have hnotActive : who ∉ G.active h.lastState := by
        simpa [FOSG.locallyLegalAtState, haction] using hlocal
      exact False.elim (hnotActive hactive)
  | some act =>
      refine ⟨act, ?_⟩
      rw [FOSG.mem_availableActionsAtHistory_iff]
      simpa [FOSG.locallyLegalAtState, haction] using hlocal

/-- Every reachable-legal pure strategy chooses only locally available
information-state moves. -/
theorem checkedProgram_pureStrategy_chooses_available_info_moves
    (g : WFProgram P L) (who : P) (σ : pureStrategyAt g who) :
    PureStrategyChoosesOnly g who (MoveAvailableAtInfo g who) σ :=
  pureStrategy_chooses_available g who σ

/-- Every reachable-legal behavioral strategy supports only locally available
information-state moves. -/
theorem checkedProgram_behavioralStrategy_supports_available_info_moves
    (g : WFProgram P L) (who : P)
    (σ : behavioralStrategyPMFAt g who) :
    BehavioralStrategySupportsOnly g who (MoveAvailableAtInfo g who) σ :=
  behavioralStrategy_supports_available g who σ

/-- In any checked Vegas PMF-behavioral strategic form, a Nash profile cannot
play a strictly dominated strategy. -/
theorem checkedProgram_nash_avoids_strictly_dominated_strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {σ : StrategyProfile g} (hN : IsNash g σ)
    (who : P) {s : Strategy g who}
    (hdom : StrictlyDominates g who s (σ who)) :
    False :=
  IsNash.not_strictly_dominated_strategy hN hdom

/-- In any checked Vegas PMF-behavioral strategic form, repairably bad
strategies cannot occur in Nash profiles. -/
theorem checkedProgram_nash_avoids_repairable_bad_strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (who : P) (R : StrictDominationRepair g who)
    {σ : StrategyProfile g} (hN : IsNash g σ) :
    ¬ R.Bad (σ who) :=
  R.nash_avoids_bad hN

/-- In any checked Vegas pure strategic form, a pure Nash profile cannot play a
strictly dominated pure strategy. -/
theorem checkedProgram_pureNash_avoids_strictly_dominated_strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    {σ : pureProfileAt g} (hN : IsPureNash g σ)
    (who : P) {s : pureStrategyAt g who}
    (hdom : PureStrictlyDominates g who s (σ who)) :
    False :=
  IsPureNash.not_strictly_dominated_strategy hN hdom

/-- In any checked Vegas pure strategic form, repairably bad pure strategies
cannot occur in pure Nash profiles. -/
theorem checkedProgram_pureNash_avoids_repairable_bad_strategy
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (who : P) (R : PureStrictDominationRepair g who)
    {σ : pureProfileAt g} (hN : IsPureNash g σ) :
    ¬ R.Bad (σ who) :=
  R.nash_avoids_bad hN

end Vegas
