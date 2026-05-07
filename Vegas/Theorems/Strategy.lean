import Vegas.Protocol.StateSufficiency
import Vegas.Protocol.Strategic
import Vegas.Theorems.Progress

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
    {left right : (syntaxProtocolGraph g).Configuration}
    (hpriv : syntaxGraphObserve g who left = syntaxGraphObserve g who right)
    (hpub : syntaxGraphPublicView g left = syntaxGraphPublicView g right) :
    ProtocolGraph.roundMenu (syntaxProtocolGraph g) left who =
      ProtocolGraph.roundMenu (syntaxProtocolGraph g) right who :=
  syntaxGraph_roundMenu_eq_of_observation_eq g who hpriv hpub

/-- Membership in a player's frontier-round menu is transported across equal
public transcript and private observation. -/
theorem checkedProgram_roundMenu_mem_iff_of_observation_eq
    (g : WFProgram P L) (who : P)
    {left right : (syntaxProtocolGraph g).Configuration}
    (hpriv : syntaxGraphObserve g who left = syntaxGraphObserve g who right)
    (hpub : syntaxGraphPublicView g left = syntaxGraphPublicView g right)
    (move :
      Option (ProtocolGraph.PlayerRoundAction (syntaxProtocolGraph g) who)) :
    move ∈ ProtocolGraph.roundMenu (syntaxProtocolGraph g) left who ↔
      move ∈ ProtocolGraph.roundMenu (syntaxProtocolGraph g) right who := by
  rw [checkedProgram_roundMenu_eq_of_observation_eq g who hpriv hpub]

/-- At the current bounded FOSG history endpoint, a player's available optional
moves are determined by the current private and public observations, provided
both histories are before the presentation cutoff. -/
theorem checkedProgram_availableMoves_eq_of_currentObservation_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hcut : ¬ horizon ≤ h.lastState.depth)
    (hcut' : ¬ horizon ≤ h'.lastState.depth)
    (hpriv :
      syntaxGraphObserve g who h.lastState.state =
        syntaxGraphObserve g who h'.lastState.state)
    (hpub :
      syntaxGraphPublicView g h.lastState.state =
        syntaxGraphPublicView g h'.lastState.state) :
    ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who =
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h' who :=
  syntaxGraph_availableMoves_eq_of_currentObservation_eq
    g horizon who hcut hcut' hpriv hpub

/-- Membership in the current optional move set is transported by equality of
current private and public observations. -/
theorem checkedProgram_availableMoves_mem_iff_of_currentObservation_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hcut : ¬ horizon ≤ h.lastState.depth)
    (hcut' : ¬ horizon ≤ h'.lastState.depth)
    (hpriv :
      syntaxGraphObserve g who h.lastState.state =
        syntaxGraphObserve g who h'.lastState.state)
    (hpub :
      syntaxGraphPublicView g h.lastState.state =
        syntaxGraphPublicView g h'.lastState.state)
    (move : Option ((syntaxGraphFOSGView g).Act who)) :
    move ∈ ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who ↔
      move ∈
        ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h' who := by
  rw [checkedProgram_availableMoves_eq_of_currentObservation_eq
    g horizon who hcut hcut' hpriv hpub]

/-- For nonempty bounded FOSG histories before cutoff, equality of latest
private/public observations determines a player's whole optional move set. -/
theorem checkedProgram_availableMoves_eq_of_latestObservation_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hcut : ¬ horizon ≤ h.lastState.depth)
    (hcut' : ¬ horizon ≤ h'.lastState.depth)
    (hne : h.steps ≠ [])
    (hne' : h'.steps ≠ [])
    (hlatest :
      GameTheory.FOSG.InfoState.latestObservation?
          (G := (syntaxGraphFOSGView g).toBoundedFOSG horizon)
          (i := who) (h.playerView who) =
        GameTheory.FOSG.InfoState.latestObservation?
          (G := (syntaxGraphFOSGView g).toBoundedFOSG horizon)
          (i := who) (h'.playerView who)) :
    ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who =
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h' who :=
  syntaxGraph_availableMoves_eq_of_latestObservation_eq
    g horizon who hcut hcut' hne hne' hlatest

/-- Membership in the current optional move set is transported by equality of
latest private/public observations. -/
theorem checkedProgram_availableMoves_mem_iff_of_latestObservation_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hcut : ¬ horizon ≤ h.lastState.depth)
    (hcut' : ¬ horizon ≤ h'.lastState.depth)
    (hne : h.steps ≠ [])
    (hne' : h'.steps ≠ [])
    (hlatest :
      GameTheory.FOSG.InfoState.latestObservation?
          (G := (syntaxGraphFOSGView g).toBoundedFOSG horizon)
          (i := who) (h.playerView who) =
        GameTheory.FOSG.InfoState.latestObservation?
          (G := (syntaxGraphFOSGView g).toBoundedFOSG horizon)
          (i := who) (h'.playerView who))
    (move : Option ((syntaxGraphFOSGView g).Act who)) :
    move ∈ ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who ↔
      move ∈
        ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h' who := by
  rw [checkedProgram_availableMoves_eq_of_latestObservation_eq
    g horizon who hcut hcut' hne hne' hlatest]

/-- Equal FOSG player views determine equal concrete action sets at histories. -/
theorem checkedProgram_availableActions_eq_of_playerView_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hinfo : h.playerView who = h'.playerView who) :
    ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableActionsAtHistory
        h who =
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableActionsAtHistory
        h' who :=
  ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableActions_eq_of_playerView_eq
    (checkedProgram_boundedFOSG_legalObservable g horizon) who hinfo

/-- The optional move set attached to a reachable information state is the same
as the optional move set at any history realizing that information state. -/
theorem checkedProgram_availableMovesAtInfoState_eq_of_history
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (h : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History)) :
    ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMovesAtInfoState
        who (h.playerView who) =
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who :=
  ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMovesAtInfoState_eq_of_history
    (checkedProgram_boundedFOSG_legalObservable g horizon) who h

/-- Hidden value changes outside a player's current observation cannot change
that player's available moves. -/
theorem available_moves_invariant_under_unseen_hidden_values
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hcut : ¬ horizon ≤ h.lastState.depth)
    (hcut' : ¬ horizon ≤ h'.lastState.depth)
    (hpriv :
      syntaxGraphObserve g who h.lastState.state =
        syntaxGraphObserve g who h'.lastState.state)
    (hpub :
      syntaxGraphPublicView g h.lastState.state =
        syntaxGraphPublicView g h'.lastState.state) :
    ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who =
      ((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableMoves h' who :=
  checkedProgram_availableMoves_eq_of_currentObservation_eq
    g horizon who hcut hcut' hpriv hpub

/-- Pure strategies are extensional in player information state. -/
theorem pureStrategy_ext_of_playerView_eq
    (g : WFProgram P L) (who : P) (σ : pureStrategyAt g who)
    {h h' : (((syntaxGraphFOSGView g).toBoundedFOSG
      (syntaxSteps g.prog)).History)}
    (hview : h.playerView who = h'.playerView who) :
    σ.1 (((syntaxGraphFOSGView g).toBoundedFOSG
        (syntaxSteps g.prog)).reachableInfoStateOfHistory who h) =
      σ.1 (((syntaxGraphFOSGView g).toBoundedFOSG
        (syntaxSteps g.prog)).reachableInfoStateOfHistory who h') := by
  apply congrArg σ.1
  apply Subtype.ext
  simpa using hview

/-- Behavioral strategies are extensional in player information state. -/
theorem behavioralStrategy_ext_of_playerView_eq
    (g : WFProgram P L) (who : P) (σ : behavioralStrategyPMFAt g who)
    {h h' : (((syntaxGraphFOSGView g).toBoundedFOSG
      (syntaxSteps g.prog)).History)}
    (hview : h.playerView who = h'.playerView who) :
    σ.1 (((syntaxGraphFOSGView g).toBoundedFOSG
        (syntaxSteps g.prog)).reachableInfoStateOfHistory who h) =
      σ.1 (((syntaxGraphFOSGView g).toBoundedFOSG
        (syntaxSteps g.prog)).reachableInfoStateOfHistory who h') := by
  apply congrArg σ.1
  apply Subtype.ext
  simpa using hview

/-- Pure strategies cannot branch on data absent from the player's information
state. -/
theorem strategy_cannot_condition_on_unseen_hidden_values
    (g : WFProgram P L) (who : P) (σ : pureStrategyAt g who)
    {h h' : (((syntaxGraphFOSGView g).toBoundedFOSG
      (syntaxSteps g.prog)).History)}
    (hview : h.playerView who = h'.playerView who) :
    σ.1 (((syntaxGraphFOSGView g).toBoundedFOSG
        (syntaxSteps g.prog)).reachableInfoStateOfHistory who h) =
      σ.1 (((syntaxGraphFOSGView g).toBoundedFOSG
        (syntaxSteps g.prog)).reachableInfoStateOfHistory who h') :=
  pureStrategy_ext_of_playerView_eq g who σ hview

/-- The reachable-legal pure strategy carrier never selects an unavailable
optional move at a realizing history. -/
theorem legal_strategy_never_selects_illegal_action
    (g : WFProgram P L) (who : P) (σ : pureStrategyAt g who)
    (h : (((syntaxGraphFOSGView g).toBoundedFOSG
      (syntaxSteps g.prog)).History)) :
    σ.1 (((syntaxGraphFOSGView g).toBoundedFOSG
        (syntaxSteps g.prog)).reachableInfoStateOfHistory who h) ∈
      ((syntaxGraphFOSGView g).toBoundedFOSG
        (syntaxSteps g.prog)).availableMoves h who := by
  exact σ.2 h

/-- Active players before terminal/cutoff have a nonempty concrete action set. -/
theorem availableActionsAtHistory_nonempty_of_not_terminal_active
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (h : (((syntaxGraphFOSGView g).toBoundedFOSG horizon).History))
    (hnotTerminal :
      ¬ ((syntaxGraphFOSGView g).toBoundedFOSG horizon).terminal h.lastState)
    (hactive :
      who ∈ ((syntaxGraphFOSGView g).toBoundedFOSG horizon).active h.lastState) :
    Set.Nonempty
      (((syntaxGraphFOSGView g).toBoundedFOSG horizon).availableActionsAtHistory
        h who) := by
  let G := (syntaxGraphFOSGView g).toBoundedFOSG horizon
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

end Vegas
