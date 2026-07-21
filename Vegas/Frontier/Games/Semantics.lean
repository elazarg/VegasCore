/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.Kuhn
import Vegas.Frontier.SourceAdequacy
import Vegas.EventGraph.FiniteState
import GameTheory.Core.GameForm
import GameTheory.Core.GameSimulation
import GameTheory.Concepts.Transport.Corners
import GameTheory.Concepts.Equilibrium.SolutionConcepts
import GameTheory.Concepts.Equilibrium.NashCorrelatedEq
import GameTheory.Concepts.Foundations.GameMorphism
import GameTheory.Concepts.Correlation.GameMorphism
import GameTheory.Concepts.Mixed.GameMorphism
import GameTheory.Theorems.CorrelatedEqExistence
import GameTheory.Concepts.Existence.NashExistenceMixed

/-!
# Program-facing compiled frontier games: semantics package

The `FrontierGameSemantics` package pairs the canonical pure/behavioral frontier
games of a finite checked program with the menu-observability theorem needed by
the Kuhn realization. The event graph remains the semantic IR.
-/

namespace Vegas

namespace ToEventGraph

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}


/-- A compiled checked program with its completed frontier game semantics.

The package stores the paired pure/behavioral frontier games once, together
with the menu observability theorem needed by the Kuhn realization theorems.
-/
structure FrontierGameSemantics
    (program : WFProgram P L) [FiniteDomains program] where
  games :
    CompletedFrontierKuhnGames (compile program.core)
      (frontierPresentation
        (compile program.core)
        (compile_guardLive program))
  menus :
    games.view.MenusObservable
      (completionBound (compile program.core))

namespace FrontierGameSemantics

variable {program : WFProgram P L} [FiniteDomains program]

/-- The compiled event graph and payoff projection used by this semantic
package. -/
noncomputable def compiled
    (_semantics : FrontierGameSemantics program) :
    CompiledProgram P L :=
  compile program.core

/-- Completed pure-strategy frontier game. -/
noncomputable def pure
    (semantics : FrontierGameSemantics program) :
    CompletedFrontierPureKernelGame (compile program.core)
      (frontierPresentation
        (compile program.core)
        (compile_guardLive program)) :=
  semantics.games.pure

/-- Completed behavioral-strategy frontier game. -/
noncomputable def behavioral
    (semantics : FrontierGameSemantics program) :
    CompletedFrontierBehavioralKernelGame (compile program.core)
      (frontierPresentation
        (compile program.core)
        (compile_guardLive program)) :=
  semantics.games.behavioral

/-- Concrete pure-strategy kernel game exposed by the compiled frontier
semantics. -/
noncomputable def pureGame
    (semantics : FrontierGameSemantics program) :
    KernelGame P :=
  semantics.pure.game

/-- Concrete behavioral-strategy kernel game exposed by the compiled frontier
semantics. -/
noncomputable def behavioralGame
    (semantics : FrontierGameSemantics program) :
    KernelGame P :=
  semantics.behavioral.game

/-- Completion horizon used by the canonical frontier semantics. -/
noncomputable def horizon (_semantics : FrontierGameSemantics program) : Nat :=
  completionBound (compile program.core)

/-- The canonical behavioral frontier round view is an operational
presentation: every supported strategic round transition has a replaying
primitive event batch. -/
theorem view_operationallyCertified
    (semantics : FrontierGameSemantics program) :
    semantics.games.view.OperationallyCertified :=
  semantics.games.view_operationallyCertified

/-- Finite carrier for the canonical pure-strategy game. This is the finite
strategic-analysis surface; behavioral analysis is connected to it by Kuhn
realization theorems rather than by enumerating PMF-valued behavioral
strategies. -/
@[reducible]
noncomputable def pureStrategyFintype
    (semantics : FrontierGameSemantics program)
    (player : P) :
    Fintype (semantics.pureGame.Strategy player) :=
  semantics.games.pureStrategyFintype player

/-- The canonical pure-strategy carrier is nonempty for every player: menu
observability supplies a legal default move at each reachable information
state. -/
theorem pureStrategyNonempty
    (semantics : FrontierGameSemantics program)
    (player : P) :
    Nonempty (semantics.pureGame.Strategy player) := by
  classical
  let view := semantics.games.view
  let h :
      Nonempty (view.BoundedPureStrategy semantics.horizon player) :=
    (view.instNonemptyBoundedPureStrategyOfMenus
      semantics.horizon semantics.menus) player
  simpa [pureGame, pure, CompletedFrontierPureKernelGame.game,
    CompletedFrontierPureKernelGame.view, CompletedFrontierKuhnGames.pure,
    CompletedFrontierKuhnGames.view, horizon, view] using h

/-- Mixed extension of the finite pure-strategy frontier game. -/
noncomputable def mixedPureGame
    (semantics : FrontierGameSemantics program) :
    KernelGame P :=
  semantics.pureGame.mixedExtension

/-- Pure-strategy completed frontier histories. These are checkpoint histories
at the strategic frontier level, not primitive event schedules. -/
abbrev PureHistory (semantics : FrontierGameSemantics program) : Type :=
  (semantics.pure.view).BoundedHistory semantics.horizon

/-- Behavioral-strategy completed frontier histories. -/
abbrev BehavioralHistory (semantics : FrontierGameSemantics program) : Type :=
  (semantics.behavioral.view).BoundedHistory semantics.horizon

/-- Finite carrier for completed pure-strategy frontier histories. -/
@[reducible]
noncomputable def pureHistoryFintype
    (semantics : FrontierGameSemantics program) :
    Fintype semantics.PureHistory := by
  classical
  letI :
      ∀ field : Fin (compile program.core).graph.fieldCount,
        Fintype
          (L.Val ((compile program.core).graph.fieldRow field).ty) :=
    semantics.games.fieldFintype
  letI : Fintype (PrimitiveMachine (compile program.core)).State := by
    change Fintype (EventGraph.ReachableConfig (compile program.core).graph)
    exact
      EventGraph.StateSnapshot.reachableConfigFintype
        (compile program.core).graph
        (compile program.core).graphWF
  letI :
      ∀ player,
        Fintype (Option ((semantics.pure.view).Act player)) := by
    change ∀ player, Fintype (Option (semantics.games.view.Act player))
    exact semantics.games.kuhnOptionalMoveFintype
  exact
    (semantics.pure.view).instFintypeBoundedHistory semantics.horizon

/-- Public checkpoint-observation history exposed by the frontier strategic
presentation. -/
abbrev PublicHistory (_semantics : FrontierGameSemantics program) : Type :=
  List (EventGraph.PublicObservation (compile program.core).graph)

/-- Terminal public graph observation reached by the frontier strategic
presentation. -/
abbrev TerminalPublicObservation
    (_semantics : FrontierGameSemantics program) : Type :=
  EventGraph.PublicObservation (compile program.core).graph

/-- Distribution over completed frontier histories under a pure profile. -/
noncomputable def pureHistoryKernel
    (semantics : FrontierGameSemantics program)
    (σ : semantics.pureGame.Profile) :
    PMF semantics.PureHistory :=
  (semantics.pure.view).runDist semantics.horizon semantics.horizon
    ((semantics.pure.view).legalPureToBehavioral semantics.horizon σ)

/-- Distribution over completed frontier histories under a behavioral profile. -/
noncomputable def behavioralHistoryKernel
    (semantics : FrontierGameSemantics program)
    (σ : semantics.behavioralGame.Profile) :
    PMF semantics.BehavioralHistory :=
  (semantics.behavioral.view).runDist semantics.horizon semantics.horizon σ

/-- Pure-strategy game form whose outcomes are completed frontier histories. -/
noncomputable def pureHistoryGameForm
    (semantics : FrontierGameSemantics program) :
    GameForm P where
  Strategy := semantics.pureGame.Strategy
  Outcome := semantics.PureHistory
  outcomeKernel := semantics.pureHistoryKernel

/-- Behavioral-strategy game form whose outcomes are completed frontier
histories. -/
noncomputable def behavioralHistoryGameForm
    (semantics : FrontierGameSemantics program) :
    GameForm P where
  Strategy := semantics.behavioralGame.Strategy
  Outcome := semantics.BehavioralHistory
  outcomeKernel := semantics.behavioralHistoryKernel

/-- Payoff vector assigned to an optional compiled outcome. The fallback is
used only off the support of completed frontier kernels. -/
noncomputable def optionOutcomePayoff
    (_semantics : FrontierGameSemantics program)
    (result : Option (PrimitiveMachine (compile program.core)).Outcome) :
    Payoff P :=
  fun who =>
    Machine.RoundView.optionOutcomeUtility
      (PrimitiveMachine (compile program.core)) 0 result who

/-- Utility read from a completed pure-strategy frontier history. -/
noncomputable def pureHistoryUtility
    (semantics : FrontierGameSemantics program) :
    semantics.PureHistory → Payoff P :=
  fun history =>
    semantics.optionOutcomePayoff
      ((PrimitiveMachine (compile program.core)).outcome
        history.lastState.state)

/-- Utility read from a completed behavioral-strategy frontier history. -/
noncomputable def behavioralHistoryUtility
    (semantics : FrontierGameSemantics program) :
    semantics.BehavioralHistory → Payoff P :=
  fun history =>
    semantics.optionOutcomePayoff
      ((PrimitiveMachine (compile program.core)).outcome
        history.lastState.state)

/-- Pure-strategy kernel game whose outcomes are completed frontier histories,
not only terminal payoff vectors. -/
noncomputable def pureHistoryKernelGame
    (semantics : FrontierGameSemantics program) :
    KernelGame P :=
  semantics.pureHistoryGameForm.withUtility semantics.pureHistoryUtility

/-- Behavioral-strategy kernel game whose outcomes are completed frontier
histories, not only terminal payoff vectors. -/
noncomputable def behavioralHistoryKernelGame
    (semantics : FrontierGameSemantics program) :
    KernelGame P :=
  semantics.behavioralHistoryGameForm.withUtility
    semantics.behavioralHistoryUtility

/-- Pure-strategy game form whose outcomes are public checkpoint-observation
histories. -/
noncomputable def purePublicHistoryGameForm
    (semantics : FrontierGameSemantics program) :
    GameForm P where
  Strategy := semantics.pureGame.Strategy
  Outcome := semantics.PublicHistory
  outcomeKernel := fun σ =>
    PMF.map (fun history : semantics.PureHistory => history.publicView)
      (semantics.pureHistoryKernel σ)

/-- Behavioral-strategy game form whose outcomes are public
checkpoint-observation histories. -/
noncomputable def behavioralPublicHistoryGameForm
    (semantics : FrontierGameSemantics program) :
    GameForm P where
  Strategy := semantics.behavioralGame.Strategy
  Outcome := semantics.PublicHistory
  outcomeKernel := fun σ =>
    PMF.map (fun history : semantics.BehavioralHistory => history.publicView)
      (semantics.behavioralHistoryKernel σ)

/-- Pure-strategy game form whose outcomes are terminal public graph
observations. -/
noncomputable def pureTerminalPublicGameForm
    (semantics : FrontierGameSemantics program) :
    GameForm P where
  Strategy := semantics.pureGame.Strategy
  Outcome := semantics.TerminalPublicObservation
  outcomeKernel := fun σ =>
    PMF.map
      (fun history : semantics.PureHistory =>
        (PrimitiveMachine (compile program.core)).publicView
          history.lastState.state)
      (semantics.pureHistoryKernel σ)

/-- Behavioral-strategy game form whose outcomes are terminal public graph
observations. -/
noncomputable def behavioralTerminalPublicGameForm
    (semantics : FrontierGameSemantics program) :
    GameForm P where
  Strategy := semantics.behavioralGame.Strategy
  Outcome := semantics.TerminalPublicObservation
  outcomeKernel := fun σ =>
    PMF.map
      (fun history : semantics.BehavioralHistory =>
        (PrimitiveMachine (compile program.core)).publicView
          history.lastState.state)
      (semantics.behavioralHistoryKernel σ)

/-- Store reconstructed from a terminal public observation. Only public fields
present in the observation are available. -/
noncomputable def terminalPublicStore
    (_semantics : FrontierGameSemantics program)
    (obs : EventGraph.PublicObservation (compile program.core).graph) :
    EventGraph.Store L := by
  classical
  intro field
  exact
    if hfield : field < (compile program.core).graph.fieldCount then
      let ref : Fin (compile program.core).graph.fieldCount :=
        ⟨field, hfield⟩
      match obs.fieldValue? ref with
      | none => none
      | some value =>
          some
            { ty := ((compile program.core).graph.fieldRow ref).ty
              value := value }
    else
      none

/-- Utility attached to terminal public observations. Malformed public
observations outside the completed-run support receive the zero payoff vector;
reachable terminal observations contain the compiled public payoff reads. -/
noncomputable def terminalPublicUtility
    (semantics : FrontierGameSemantics program) :
    semantics.TerminalPublicObservation → Payoff P :=
  fun obs =>
    match
      EventGraph.evalPayoffs? (compile program.core).payoffs
        (semantics.terminalPublicStore obs) with
    | some outcome => (PrimitiveMachine (compile program.core)).utility outcome
    | none => 0

/-- Pure-strategy kernel game whose outcomes are terminal public graph
observations. This is a finite public-outcome strategic surface. -/
noncomputable def pureTerminalPublicKernelGame
    (semantics : FrontierGameSemantics program) :
    KernelGame P :=
  semantics.pureTerminalPublicGameForm.withUtility
    semantics.terminalPublicUtility

/-- Behavioral-strategy kernel game whose outcomes are terminal public graph
observations. -/
noncomputable def behavioralTerminalPublicKernelGame
    (semantics : FrontierGameSemantics program) :
    KernelGame P :=
  semantics.behavioralTerminalPublicGameForm.withUtility
    semantics.terminalPublicUtility

/-- Mixed extension of the finite terminal-public pure frontier game. -/
noncomputable def mixedPureTerminalPublicGame
    (semantics : FrontierGameSemantics program) :
    KernelGame P :=
  semantics.pureTerminalPublicKernelGame.mixedExtension

/-- Mixed Nash existence for the finite terminal-public pure-strategy game.

Unlike the payoff-vector surface, this game has a finite outcome carrier by
construction: terminal public observations are finite snapshots of a finite
compiled graph with finite field domains. -/
theorem terminalPublicMixedNash_exists
    (semantics : FrontierGameSemantics program) :
    ∃ mixed : semantics.mixedPureTerminalPublicGame.Profile,
      semantics.mixedPureTerminalPublicGame.IsNash mixed := by
  classical
  letI :
      ∀ player,
        Finite (semantics.pureTerminalPublicKernelGame.Strategy player) :=
    fun player => by
      letI : Fintype (semantics.pureGame.Strategy player) :=
        semantics.pureStrategyFintype player
      have hfinite : Finite (semantics.pureGame.Strategy player) :=
        Finite.of_fintype _
      simpa [pureTerminalPublicKernelGame, pureTerminalPublicGameForm] using
        hfinite
  letI :
      ∀ player,
        Nonempty (semantics.pureTerminalPublicKernelGame.Strategy player) :=
    fun player => by
      simpa [pureTerminalPublicKernelGame, pureTerminalPublicGameForm] using
        semantics.pureStrategyNonempty player
  letI :
      ∀ field : Fin (compile program.core).graph.fieldCount,
        Fintype (L.Val ((compile program.core).graph.fieldRow field).ty) :=
    semantics.games.fieldFintype
  letI :
      Fintype (EventGraph.PublicObservation (compile program.core).graph) :=
    inferInstance
  letI :
      Finite semantics.pureTerminalPublicKernelGame.Outcome :=
    by
      change Finite
        (EventGraph.PublicObservation (compile program.core).graph)
      exact Finite.of_fintype _
  exact semantics.pureTerminalPublicKernelGame.mixed_nash_exists

@[simp] theorem pureHistoryGameForm_outcomeKernel
    (semantics : FrontierGameSemantics program)
    (σ : semantics.pureHistoryGameForm.Profile) :
    semantics.pureHistoryGameForm.outcomeKernel σ =
      semantics.pureHistoryKernel σ := rfl

@[simp] theorem behavioralHistoryGameForm_outcomeKernel
    (semantics : FrontierGameSemantics program)
    (σ : semantics.behavioralHistoryGameForm.Profile) :
    semantics.behavioralHistoryGameForm.outcomeKernel σ =
      semantics.behavioralHistoryKernel σ := rfl

@[simp] theorem pureHistoryKernelGame_toGameForm
    (semantics : FrontierGameSemantics program) :
    semantics.pureHistoryKernelGame.toGameForm =
      semantics.pureHistoryGameForm := rfl

@[simp] theorem behavioralHistoryKernelGame_toGameForm
    (semantics : FrontierGameSemantics program) :
    semantics.behavioralHistoryKernelGame.toGameForm =
      semantics.behavioralHistoryGameForm := rfl

@[simp] theorem pureHistoryKernelGame_outcomeKernel
    (semantics : FrontierGameSemantics program)
    (σ : semantics.pureHistoryKernelGame.Profile) :
    semantics.pureHistoryKernelGame.outcomeKernel σ =
      semantics.pureHistoryKernel σ := rfl

@[simp] theorem behavioralHistoryKernelGame_outcomeKernel
    (semantics : FrontierGameSemantics program)
    (σ : semantics.behavioralHistoryKernelGame.Profile) :
    semantics.behavioralHistoryKernelGame.outcomeKernel σ =
      semantics.behavioralHistoryKernel σ := rfl

@[simp] theorem pureTerminalPublicKernelGame_toGameForm
    (semantics : FrontierGameSemantics program) :
    semantics.pureTerminalPublicKernelGame.toGameForm =
      semantics.pureTerminalPublicGameForm := rfl

@[simp] theorem behavioralTerminalPublicKernelGame_toGameForm
    (semantics : FrontierGameSemantics program) :
    semantics.behavioralTerminalPublicKernelGame.toGameForm =
      semantics.behavioralTerminalPublicGameForm := rfl

@[simp] theorem pureTerminalPublicKernelGame_outcomeKernel
    (semantics : FrontierGameSemantics program)
    (σ : semantics.pureTerminalPublicKernelGame.Profile) :
    semantics.pureTerminalPublicKernelGame.outcomeKernel σ =
      semantics.pureTerminalPublicGameForm.outcomeKernel σ := rfl

@[simp] theorem behavioralTerminalPublicKernelGame_outcomeKernel
    (semantics : FrontierGameSemantics program)
    (σ : semantics.behavioralTerminalPublicKernelGame.Profile) :
    semantics.behavioralTerminalPublicKernelGame.outcomeKernel σ =
      semantics.behavioralTerminalPublicGameForm.outcomeKernel σ := rfl

@[simp] theorem purePublicHistoryGameForm_outcomeKernel
    (semantics : FrontierGameSemantics program)
    (σ : semantics.purePublicHistoryGameForm.Profile) :
    semantics.purePublicHistoryGameForm.outcomeKernel σ =
      PMF.map (fun history : semantics.PureHistory => history.publicView)
        (semantics.pureHistoryKernel σ) := rfl

@[simp] theorem behavioralPublicHistoryGameForm_outcomeKernel
    (semantics : FrontierGameSemantics program)
    (σ : semantics.behavioralPublicHistoryGameForm.Profile) :
    semantics.behavioralPublicHistoryGameForm.outcomeKernel σ =
      PMF.map (fun history : semantics.BehavioralHistory =>
        history.publicView) (semantics.behavioralHistoryKernel σ) := rfl

@[simp] theorem pureTerminalPublicGameForm_outcomeKernel
    (semantics : FrontierGameSemantics program)
    (σ : semantics.pureTerminalPublicGameForm.Profile) :
    semantics.pureTerminalPublicGameForm.outcomeKernel σ =
      PMF.map
        (fun history : semantics.PureHistory =>
          (PrimitiveMachine (compile program.core)).publicView
            history.lastState.state)
        (semantics.pureHistoryKernel σ) := rfl

@[simp] theorem behavioralTerminalPublicGameForm_outcomeKernel
    (semantics : FrontierGameSemantics program)
    (σ : semantics.behavioralTerminalPublicGameForm.Profile) :
    semantics.behavioralTerminalPublicGameForm.outcomeKernel σ =
      PMF.map
        (fun history : semantics.BehavioralHistory =>
          (PrimitiveMachine (compile program.core)).publicView
            history.lastState.state)
        (semantics.behavioralHistoryKernel σ) := rfl

/-- Pure payoff-vector play and completed-history play have the same joint
utility distribution. -/
theorem pureHistoryKernelGame_udist
    (semantics : FrontierGameSemantics program)
    (σ : semantics.pureGame.Profile) :
    semantics.pureHistoryKernelGame.udist σ =
      semantics.pureGame.udist σ := by
  classical
  let horizon := completionBound (compile program.core)
  let view := semantics.games.view
  let optionPayoff :
      Option (PrimitiveMachine (compile program.core)).Outcome →
        Payoff P :=
    semantics.optionOutcomePayoff
  have hoption :
      semantics.pure.optionOutcomeKernel σ =
        PMF.map
          (fun history : semantics.PureHistory =>
            (PrimitiveMachine (compile program.core)).outcome
              history.lastState.state)
          (semantics.pureHistoryKernel σ) := by
    exact view.boundedOutcomeFromPure_eq_map_history horizon horizon σ
  change
    (semantics.pureHistoryKernel σ).bind
        (fun history =>
          PMF.pure (semantics.pureHistoryUtility history)) =
      (semantics.pureGame.outcomeKernel σ).bind
        (fun outcome =>
          PMF.pure (semantics.pureGame.utility outcome))
  rw [show
      (semantics.pureHistoryKernel σ).bind
          (fun history =>
            PMF.pure (semantics.pureHistoryUtility history)) =
        PMF.map optionPayoff (semantics.pure.optionOutcomeKernel σ) by
        rw [hoption, PMF.map_comp]
        rfl]
  change
    PMF.map optionPayoff (semantics.pure.optionOutcomeKernel σ) =
      PMF.map (fun outcome =>
        (PrimitiveMachine (compile program.core)).utility outcome)
        (eraseNonePMF (semantics.pure.optionOutcomeKernel σ)
          (fun result hresult =>
            semantics.pure.optionOutcomeKernel_support_some σ hresult))
  rw [eraseNonePMF_map
    (dist := semantics.pure.optionOutcomeKernel σ)
    (htotal := fun result hresult =>
      semantics.pure.optionOutcomeKernel_support_some σ hresult)
    (f := fun outcome =>
      (PrimitiveMachine (compile program.core)).utility outcome)
    (fallback := (0 : Payoff P))]
  apply congrArg
    (fun f :
        Option (PrimitiveMachine (compile program.core)).Outcome →
          Payoff P =>
      PMF.map f (semantics.pure.optionOutcomeKernel σ))
  funext result who
  cases result <;> rfl

/-- Behavioral payoff-vector play and completed-history play have the same
joint utility distribution. -/
theorem behavioralHistoryKernelGame_udist
    (semantics : FrontierGameSemantics program)
    (σ : semantics.behavioralGame.Profile) :
    semantics.behavioralHistoryKernelGame.udist σ =
      semantics.behavioralGame.udist σ := by
  classical
  let horizon := completionBound (compile program.core)
  let view := semantics.games.view
  let optionPayoff :
      Option (PrimitiveMachine (compile program.core)).Outcome →
        Payoff P :=
    semantics.optionOutcomePayoff
  have hoption :
      semantics.behavioral.optionOutcomeKernel σ =
        PMF.map
          (fun history : semantics.BehavioralHistory =>
            (PrimitiveMachine (compile program.core)).outcome
              history.lastState.state)
          (semantics.behavioralHistoryKernel σ) := by
    exact view.boundedOutcomeFromBehavioral_eq_map_history horizon horizon σ
  change
    (semantics.behavioralHistoryKernel σ).bind
        (fun history =>
          PMF.pure (semantics.behavioralHistoryUtility history)) =
      (semantics.behavioralGame.outcomeKernel σ).bind
        (fun outcome =>
          PMF.pure (semantics.behavioralGame.utility outcome))
  rw [show
      (semantics.behavioralHistoryKernel σ).bind
          (fun history =>
            PMF.pure (semantics.behavioralHistoryUtility history)) =
        PMF.map optionPayoff
          (semantics.behavioral.optionOutcomeKernel σ) by
        rw [hoption, PMF.map_comp]
        rfl]
  change
    PMF.map optionPayoff (semantics.behavioral.optionOutcomeKernel σ) =
      PMF.map (fun outcome =>
        (PrimitiveMachine (compile program.core)).utility outcome)
        (eraseNonePMF (semantics.behavioral.optionOutcomeKernel σ)
          (fun result hresult =>
            semantics.behavioral.optionOutcomeKernel_support_some σ hresult))
  rw [eraseNonePMF_map
    (dist := semantics.behavioral.optionOutcomeKernel σ)
    (htotal := fun result hresult =>
      semantics.behavioral.optionOutcomeKernel_support_some σ hresult)
    (f := fun outcome =>
      (PrimitiveMachine (compile program.core)).utility outcome)
    (fallback := (0 : Payoff P))]
  apply congrArg
    (fun f :
        Option (PrimitiveMachine (compile program.core)).Outcome →
          Payoff P =>
      PMF.map f (semantics.behavioral.optionOutcomeKernel σ))
  funext result who
  cases result <;> rfl

/-- A pure frontier profile embedded as a behavioral profile has the same
completed-game outcome kernel. -/
theorem pureToBehavioralOutcomeKernel
    (semantics : FrontierGameSemantics program)
    (profile : semantics.pureGame.Profile) :
    semantics.behavioralGame.outcomeKernel
        ((semantics.behavioral.view).legalPureToBehavioral
          semantics.horizon profile) =
      semantics.pureGame.outcomeKernel profile := by
  ext outcome
  change semantics.behavioral.game.outcomeKernel
      ((semantics.behavioral.view).legalPureToBehavioral
        semantics.horizon profile) outcome =
    semantics.pure.game.outcomeKernel profile outcome
  rw [semantics.behavioral.outcomeKernel_apply,
    semantics.pure.outcomeKernel_apply]
  simp [FrontierGameSemantics.behavioral, FrontierGameSemantics.pure,
    CompletedFrontierBehavioralKernelGame.optionOutcomeKernel,
    CompletedFrontierPureKernelGame.optionOutcomeKernel,
    CompletedFrontierBehavioralKernelGame.view,
    CompletedFrontierPureKernelGame.view,
    CompletedFrontierKuhnGames.behavioral,
    CompletedFrontierKuhnGames.pure,
    FrontierGameSemantics.horizon]
  rfl

/-- A pure frontier profile embedded as a behavioral profile has the same joint
utility distribution. -/
theorem pureToBehavioralUdist
    (semantics : FrontierGameSemantics program)
    (profile : semantics.pureGame.Profile) :
    semantics.behavioralGame.udist
        ((semantics.behavioral.view).legalPureToBehavioral
          semantics.horizon profile) =
      semantics.pureGame.udist profile := by
  change
    (semantics.behavioralGame.outcomeKernel
        ((semantics.behavioral.view).legalPureToBehavioral
          semantics.horizon profile)).bind
        (fun outcome => PMF.pure (semantics.behavioralGame.utility outcome)) =
      (semantics.pureGame.outcomeKernel profile).bind
        (fun outcome => PMF.pure (semantics.pureGame.utility outcome))
  rw [semantics.pureToBehavioralOutcomeKernel profile]
  rfl

/-- Completed pure frontier histories and payoff outcomes induce the same
joint utility distribution.  This is a payoff-level equivalence, not a claim
that the history protocols have identical observations. -/
noncomputable def pureHistoryUtilityDistributionEquivalence
    (semantics : FrontierGameSemantics program) :
    KernelGame.Bisimulation
      semantics.pureGame semantics.pureHistoryKernelGame where
  stratEquiv := fun _ => Equiv.refl _
  udist_preserved := by
    intro σ
    exact semantics.pureHistoryKernelGame_udist σ

/-- Completed behavioral frontier histories and payoff outcomes induce the
same joint utility distribution.  This is a payoff-level equivalence, not a
claim that the history protocols have identical observations. -/
noncomputable def behavioralHistoryUtilityDistributionEquivalence
    (semantics : FrontierGameSemantics program) :
    KernelGame.Bisimulation
      semantics.behavioralGame semantics.behavioralHistoryKernelGame where
  stratEquiv := fun _ => Equiv.refl _
  udist_preserved := by
    intro σ
    exact semantics.behavioralHistoryKernelGame_udist σ

/-- Mixed Nash existence obtained on the finite completed-history game. -/
theorem pureHistoryMixedNash_exists
    (semantics : FrontierGameSemantics program) :
    ∃ mixed : semantics.pureHistoryKernelGame.mixedExtension.Profile,
      semantics.pureHistoryKernelGame.mixedExtension.IsNash mixed := by
  classical
  letI :
      ∀ player,
        Finite (semantics.pureHistoryKernelGame.Strategy player) :=
    fun player => by
      letI : Fintype (semantics.pureGame.Strategy player) :=
        semantics.pureStrategyFintype player
      simpa [pureHistoryKernelGame, pureHistoryGameForm] using
        (Finite.of_fintype (semantics.pureGame.Strategy player))
  letI :
      ∀ player,
        Nonempty (semantics.pureHistoryKernelGame.Strategy player) :=
    fun player => by
      simpa [pureHistoryKernelGame, pureHistoryGameForm] using
        semantics.pureStrategyNonempty player
  letI : Fintype semantics.PureHistory := semantics.pureHistoryFintype
  letI : Finite semantics.pureHistoryKernelGame.Outcome :=
    Finite.of_fintype semantics.PureHistory
  exact semantics.pureHistoryKernelGame.mixed_nash_exists

/-- Every finite-domain checked program has a mixed Nash equilibrium in its
canonical completed pure-strategy frontier game. -/
theorem mixedPureNash_exists
    (semantics : FrontierGameSemantics program) :
    ∃ mixed : semantics.mixedPureGame.Profile,
      semantics.mixedPureGame.IsNash mixed := by
  rcases semantics.pureHistoryMixedNash_exists with ⟨mixed, hNash⟩
  let equivalence :=
    semantics.pureHistoryUtilityDistributionEquivalence.symm
      |>.mixedExtension
      |>.toEUGameIsomorphism
  refine ⟨equivalence.profileEquiv mixed, ?_⟩
  simpa [mixedPureGame] using
    (equivalence.nash_iff mixed).mp hNash

/-- Every finite-domain checked program has a correlated equilibrium in its
canonical completed pure-strategy frontier game. -/
theorem pureCorrelatedEq_exists
    (semantics : FrontierGameSemantics program) :
    ∃ correlated : PMF semantics.pureGame.Profile,
      semantics.pureGame.IsCorrelatedEq correlated := by
  classical
  letI : Finite P := Finite.of_fintype P
  letI :
      ∀ player,
        Finite (semantics.pureHistoryKernelGame.Strategy player) :=
    fun player => by
      letI : Fintype (semantics.pureGame.Strategy player) :=
        semantics.pureStrategyFintype player
      simpa [pureHistoryKernelGame, pureHistoryGameForm] using
        (Finite.of_fintype (semantics.pureGame.Strategy player))
  letI :
      ∀ player,
        Nonempty (semantics.pureHistoryKernelGame.Strategy player) :=
    fun player => by
      simpa [pureHistoryKernelGame, pureHistoryGameForm] using
        semantics.pureStrategyNonempty player
  letI : Fintype semantics.PureHistory := semantics.pureHistoryFintype
  letI : Finite semantics.pureHistoryKernelGame.Outcome :=
    Finite.of_fintype semantics.PureHistory
  rcases semantics.pureHistoryKernelGame.correlatedEq_exists with
    ⟨correlated, hCorrelated⟩
  let equivalence :=
    semantics.pureHistoryUtilityDistributionEquivalence.symm
      |>.toEUGameIsomorphism
  exact
    ⟨equivalence.realize correlated,
      (equivalence.correlatedEq_iff correlated).mp hCorrelated⟩

/-- Every finite-domain checked program has a coarse correlated equilibrium
in its canonical completed pure-strategy frontier game. -/
theorem pureCoarseCorrelatedEq_exists
    (semantics : FrontierGameSemantics program) :
    ∃ correlated : PMF semantics.pureGame.Profile,
      semantics.pureGame.IsCoarseCorrelatedEq correlated := by
  rcases semantics.pureCorrelatedEq_exists with ⟨correlated, hCorrelated⟩
  exact ⟨correlated, hCorrelated.toCoarseCorrelatedEq⟩

/-- A legal pure strategy chooses an available optional move at every
reachable completed-frontier history realizing its information state. -/
theorem pureStrategy_chooses_available
    (semantics : FrontierGameSemantics program)
    {who : P} (strategy : semantics.pureGame.Strategy who)
    (history : semantics.PureHistory) :
    strategy.1
        ((semantics.pure.view).reachableInfoStateOfHistory
          semantics.horizon who history) ∈
      (semantics.pure.view).boundedAvailableMoves
        semantics.horizon history who := by
  exact strategy.2 history

/-- A legal behavioral strategy assigns probability only to available optional
moves at every reachable completed-frontier history realizing its information
state. -/
theorem behavioralStrategy_supports_available
    (semantics : FrontierGameSemantics program)
    {who : P} (strategy : semantics.behavioralGame.Strategy who)
    (history : semantics.BehavioralHistory)
    {move : Option ((semantics.behavioral.view).Act who)}
    (hmove :
      move ∈
        (strategy.1
          ((semantics.behavioral.view).reachableInfoStateOfHistory
            semantics.horizon who history)).support) :
    move ∈
      (semantics.behavioral.view).boundedAvailableMoves
        semantics.horizon history who := by
  exact strategy.2 history hmove

/-- Pure strategies are functions of the player information state; equal
player views induce equal chosen optional moves. -/
theorem pureStrategy_eq_of_playerView_eq
    (semantics : FrontierGameSemantics program)
    {who : P} (strategy : semantics.pureGame.Strategy who)
    {left right : semantics.PureHistory}
    (hview : left.playerView who = right.playerView who) :
    strategy.1
        ((semantics.pure.view).reachableInfoStateOfHistory
          semantics.horizon who left) =
      strategy.1
        ((semantics.pure.view).reachableInfoStateOfHistory
          semantics.horizon who right) := by
  apply congrArg strategy.1
  apply Subtype.ext
  exact hview

/-- Behavioral strategies are functions of the player information state; equal
player views induce equal action distributions. -/
theorem behavioralStrategy_eq_of_playerView_eq
    (semantics : FrontierGameSemantics program)
    {who : P} (strategy : semantics.behavioralGame.Strategy who)
    {left right : semantics.BehavioralHistory}
    (hview : left.playerView who = right.playerView who) :
    strategy.1
        ((semantics.behavioral.view).reachableInfoStateOfHistory
          semantics.horizon who left) =
      strategy.1
        ((semantics.behavioral.view).reachableInfoStateOfHistory
          semantics.horizon who right) := by
  apply congrArg strategy.1
  apply Subtype.ext
  exact hview

/-- Canonical behavioral profile realizing a product-mixed pure profile in the
completed frontier game. -/
noncomputable def mixedToBehavioralProfile
    (semantics : FrontierGameSemantics program)
    (mixed : ∀ player, PMF (semantics.pureGame.Strategy player)) :
    semantics.behavioralGame.Profile := by
  simpa [pureGame, behavioralGame, pure, behavioral] using
    semantics.games.mixedPureToBehavioralProfile_of_menus
      semantics.menus mixed

/-- The canonical mixed-to-behavioral profile has the same completed-game
outcome kernel as the product-mixed pure profile. -/
theorem mixedToBehavioralProfileOutcomeKernel
    (semantics : FrontierGameSemantics program)
    (mixed : ∀ player, PMF (semantics.pureGame.Strategy player)) :
    semantics.behavioralGame.outcomeKernel
        (semantics.mixedToBehavioralProfile mixed) =
      (Math.PMFProduct.pmfPi mixed).bind
        (fun pureProfile =>
          semantics.pureGame.outcomeKernel pureProfile) := by
  simpa [pureGame, behavioralGame, pure, behavioral,
    mixedToBehavioralProfile] using
    semantics.games.mixedPureToBehavioralOutcomeKernel_eq_of_menus
      semantics.menus mixed

open Classical in
/-- Product mixed pure-strategy deviation induced by one behavioral frontier
strategy. -/
noncomputable def behavioralStrategyToMixedPure
    (semantics : FrontierGameSemantics program)
    (who : P)
    (deviation : semantics.behavioralGame.Strategy who) :
    PMF (semantics.pureGame.Strategy who) := by
  simpa [pureGame, behavioralGame, pure, behavioral] using
    semantics.games.behavioralStrategyToMixedPure
      semantics.menus who deviation

/-- The canonical mixed-to-behavioral profile satisfies the unilateral
deviation law needed for Nash transport. -/
theorem mixedToBehavioralUnilateralDeviationOutcomeKernel
    (semantics : FrontierGameSemantics program)
    (mixed : semantics.mixedPureGame.Profile)
    (who : P)
    (deviation : semantics.behavioralGame.Strategy who) :
    let mixedDeviation :=
      semantics.behavioralStrategyToMixedPure who deviation
    semantics.behavioralGame.outcomeKernel
        (Function.update
          (semantics.mixedToBehavioralProfile mixed)
          who deviation) =
      semantics.mixedPureGame.outcomeKernel
        (Function.update mixed who mixedDeviation) := by
  classical
  let mixedDeviation :=
    semantics.behavioralStrategyToMixedPure who deviation
  simpa [pureGame, behavioralGame, mixedPureGame, pure, behavioral,
    mixedToBehavioralProfile, behavioralStrategyToMixedPure,
    KernelGame.mixedExtension, GameForm.mixedExtension_outcomeKernel, mixedDeviation] using
    semantics.games
      |>.mixedPureToBehavioralUnilateralDeviationOutcomeKernel_eq_of_menus
        semantics.menus mixed who deviation

open Classical in
/-- Updating one player's mixed-pure marginal leaves every other player's
canonical behavioral realization unchanged. -/
theorem mixedToBehavioralProfile_update_ne
    (semantics : FrontierGameSemantics program)
    (mixed : semantics.mixedPureGame.Profile)
    {who player : P} (hne : player ≠ who)
    (mixedDeviation : semantics.mixedPureGame.Strategy who) :
    semantics.mixedToBehavioralProfile
        (Function.update mixed who mixedDeviation) player =
      semantics.mixedToBehavioralProfile mixed player := by
  classical
  let horizon := completionBound (compile program.core)
  let view := semantics.games.view
  letI : ∀ player, Fintype (Option (view.Act player)) :=
    semantics.games.kuhnOptionalMoveFintype
  letI :
      ∀ player,
        Finite ((view.kuhnModel horizon semantics.menus).InfoState player) :=
    semantics.games.kuhnInfoFinite horizon semantics.menus
  exact view.mixedPureToBehavioralProfile_update_ne
    horizon semantics.menus mixed hne mixedDeviation

open Classical in
/-- Every unilateral mixed-pure deviation from a mixed profile has a matching
unilateral behavioral deviation from its canonical Kuhn realization, with the
same completed-game outcome kernel. -/
theorem mixedToBehavioralMixedDeviationOutcomeKernel
    (semantics : FrontierGameSemantics program)
    (mixed : semantics.mixedPureGame.Profile)
    (who : P)
    (mixedDeviation : semantics.mixedPureGame.Strategy who) :
    ∃ behavioralDeviation : semantics.behavioralGame.Strategy who,
      semantics.mixedPureGame.outcomeKernel
          (Function.update mixed who mixedDeviation) =
        semantics.behavioralGame.outcomeKernel
          (Function.update
            (semantics.mixedToBehavioralProfile mixed)
            who behavioralDeviation) := by
  classical
  let mixed' : semantics.mixedPureGame.Profile :=
    Function.update mixed who mixedDeviation
  let behavioralDeviation : semantics.behavioralGame.Strategy who :=
    semantics.mixedToBehavioralProfile mixed' who
  refine ⟨behavioralDeviation, ?_⟩
  have hprofile :
      Function.update
          (semantics.mixedToBehavioralProfile mixed)
          who behavioralDeviation =
        semantics.mixedToBehavioralProfile mixed' := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [behavioralDeviation]
    · rw [Function.update_of_ne hplayer]
      exact (semantics.mixedToBehavioralProfile_update_ne
        mixed hplayer mixedDeviation).symm
  rw [hprofile]
  exact (semantics.mixedToBehavioralProfileOutcomeKernel mixed').symm

/-- Mixed pure strategies can be realized by behavioral strategies with the
same completed-game outcome kernel. -/
theorem mixedToBehavioral
    (semantics : FrontierGameSemantics program)
    (mixed : ∀ player, PMF (semantics.pureGame.Strategy player)) :
    ∃ behavioralProfile : semantics.behavioralGame.Profile,
      semantics.behavioralGame.outcomeKernel behavioralProfile =
        (Math.PMFProduct.pmfPi mixed).bind
          (fun pureProfile =>
            semantics.pureGame.outcomeKernel pureProfile) :=
  ⟨semantics.mixedToBehavioralProfile mixed,
    semantics.mixedToBehavioralProfileOutcomeKernel mixed⟩

/-- Mixed pure strategies can be realized by behavioral strategies with the
same concrete completed-game outcome kernel. -/
theorem mixedToBehavioralOutcomeKernel
    (semantics : FrontierGameSemantics program)
    (mixed : semantics.mixedPureGame.Profile) :
    ∃ behavioralProfile : semantics.behavioralGame.Profile,
      semantics.behavioralGame.outcomeKernel behavioralProfile =
        semantics.mixedPureGame.outcomeKernel mixed := by
  refine ⟨semantics.mixedToBehavioralProfile mixed, ?_⟩
  simpa [mixedPureGame, pureGame, KernelGame.mixedExtension,
    GameForm.mixedExtension_outcomeKernel] using
    semantics.mixedToBehavioralProfileOutcomeKernel mixed

/-- Mixed pure strategies can be realized by behavioral strategies with the
same expected utility for every player. -/
theorem mixedToBehavioralEU
    (semantics : FrontierGameSemantics program)
    (mixed : semantics.mixedPureGame.Profile) :
    ∃ behavioralProfile : semantics.behavioralGame.Profile,
      semantics.behavioralGame.outcomeKernel behavioralProfile =
        semantics.mixedPureGame.outcomeKernel mixed ∧
      ∀ player,
        semantics.behavioralGame.eu behavioralProfile player =
          semantics.mixedPureGame.eu mixed player := by
  rcases semantics.mixedToBehavioralOutcomeKernel mixed with
    ⟨behavioralProfile, hkernel⟩
  refine ⟨behavioralProfile, hkernel, ?_⟩
  intro player
  calc
    semantics.behavioralGame.eu behavioralProfile player
        =
      Math.Probability.expect
        (semantics.behavioralGame.outcomeKernel behavioralProfile)
        (fun outcome => semantics.behavioralGame.utility outcome player) := rfl
    _ =
      Math.Probability.expect
        (semantics.mixedPureGame.outcomeKernel mixed)
        (fun outcome => semantics.behavioralGame.utility outcome player) := by
          rw [hkernel]
          rfl
    _ =
      semantics.mixedPureGame.eu mixed player := by
          rfl

/-- Relation saying that a behavioral profile realizes a mixed-pure profile
with the same completed-game outcome kernel. This is the profile-level Kuhn
fact proved by the current compiler pipeline; it intentionally does not claim
deviation preservation. -/
def MixedPureToBehavioralProfileRealizes
    (semantics : FrontierGameSemantics program)
    (mixed : semantics.mixedPureGame.Profile)
    (behavioralProfile : semantics.behavioralGame.Profile) : Prop :=
  semantics.behavioralGame.outcomeKernel behavioralProfile =
    semantics.mixedPureGame.outcomeKernel mixed

/-- The mixed-pure-to-behavioral realization relating profile laws with the same
correlated outcome law. This does not by itself transport Nash equilibria. -/
noncomputable def mixedPureToBehavioralRealization
    (semantics : FrontierGameSemantics program) :
    KernelGame.Realization
      semantics.mixedPureGame semantics.behavioralGame
      (GameForm.ViewFamily.const (F := semantics.mixedPureGame.toGameForm)
        (U := P) id)
      (GameForm.ViewFamily.const (F := semantics.behavioralGame.toGameForm)
        (U := P) id) where
  rel := fun mixedLaw behavioralLaw =>
    semantics.behavioralGame.toGameForm.correlatedOutcome behavioralLaw =
      semantics.mixedPureGame.toGameForm.correlatedOutcome mixedLaw
  law_eq := by
    intro mixedLaw behavioralLaw hrel player
    dsimp [GameForm.ViewFamily.claw, GameForm.ViewFamily.const]
    exact congrArg (PMF.map id) hrel.symm

/-- Every mixed-pure profile has at least one behavioral profile related by
the profile-level realization relation. -/
theorem mixedPureToBehavioralProfileRealizes_exists
    (semantics : FrontierGameSemantics program)
    (mixed : semantics.mixedPureGame.Profile) :
    ∃ behavioralProfile : semantics.behavioralGame.Profile,
      semantics.MixedPureToBehavioralProfileRealizes
        mixed behavioralProfile :=
  semantics.mixedToBehavioralOutcomeKernel mixed

/-- Product mixed pure-strategy profile induced by a behavioral frontier
profile. -/
noncomputable def behavioralToMixedPure
    (semantics : FrontierGameSemantics program)
    (behavioralProfile : semantics.behavioralGame.Profile) :
    semantics.mixedPureGame.Profile :=
  semantics.games.behavioralToMixedPure semantics.menus behavioralProfile

/-- Behavioral profiles and their induced product mixed pure-strategy profiles
have the same completed-game outcome kernel. -/
theorem behavioralToMixedPureOutcomeKernel
    (semantics : FrontierGameSemantics program)
    (behavioralProfile : semantics.behavioralGame.Profile) :
    semantics.behavioralGame.outcomeKernel behavioralProfile =
      semantics.mixedPureGame.outcomeKernel
        (semantics.behavioralToMixedPure behavioralProfile) := by
  simpa [pureGame, behavioralGame, mixedPureGame, pure, behavioral,
    behavioralToMixedPure, KernelGame.mixedExtension,
    GameForm.mixedExtension_outcomeKernel] using
    semantics.games.behavioralToProductMixedOutcomeKernel
      semantics.menus behavioralProfile

/-- Behavioral profiles and their induced product mixed pure-strategy profiles
have the same expected utility for every player. -/
theorem behavioralToMixedPureEU
    (semantics : FrontierGameSemantics program)
    (behavioralProfile : semantics.behavioralGame.Profile) :
    ∀ player,
      semantics.behavioralGame.eu behavioralProfile player =
        semantics.mixedPureGame.eu
          (semantics.behavioralToMixedPure behavioralProfile) player := by
  intro player
  have hkernel :=
    semantics.behavioralToMixedPureOutcomeKernel behavioralProfile
  calc
    semantics.behavioralGame.eu behavioralProfile player
        =
      Math.Probability.expect
        (semantics.behavioralGame.outcomeKernel behavioralProfile)
        (fun outcome => semantics.behavioralGame.utility outcome player) := rfl
    _ =
      Math.Probability.expect
        (semantics.mixedPureGame.outcomeKernel
          (semantics.behavioralToMixedPure behavioralProfile))
        (fun outcome => semantics.behavioralGame.utility outcome player) := by
          rw [hkernel]
          rfl
    _ =
      semantics.mixedPureGame.eu
        (semantics.behavioralToMixedPure behavioralProfile) player := by
          rfl

theorem behavioralToMixedPure_update
    (semantics : FrontierGameSemantics program)
    (behavioralProfile : semantics.behavioralGame.Profile)
    (who : P)
    (deviation : semantics.behavioralGame.Strategy who) :
    semantics.behavioralToMixedPure
        (Function.update behavioralProfile who deviation) =
      Function.update
        (semantics.behavioralToMixedPure behavioralProfile)
        who
        ((semantics.behavioralToMixedPure
          (Function.update behavioralProfile who deviation)) who) := by
  classical
  let horizon := completionBound (compile program.core)
  let view := semantics.games.view
  letI : ∀ player, Fintype (Option (view.Act player)) :=
    semantics.games.kuhnOptionalMoveFintype
  letI :
      ∀ player,
        Finite ((view.kuhnModel horizon semantics.menus).InfoState player) :=
    semantics.games.kuhnInfoFinite horizon semantics.menus
  letI :
      ∀ player,
        Fintype ((view.kuhnModel horizon semantics.menus).InfoState player) :=
    fun player => Fintype.ofFinite _
  exact view.behavioralToMixedPure_update
    horizon semantics.menus behavioralProfile who deviation

/-- Native completed-frontier Kuhn strategic equivalence.

This is the strategy/deviation-level package behind the equilibrium-facing
corollaries: mixed-pure and behavioral frontier profiles have canonical
translations preserving completed outcome kernels, and one-player deviations
can be matched across the two presentations. -/
structure KuhnStrategicEquivalence
    (semantics : FrontierGameSemantics program) where
  mixedToBehavioral :
    semantics.mixedPureGame.Profile → semantics.behavioralGame.Profile
  behavioralToMixed :
    semantics.behavioralGame.Profile → semantics.mixedPureGame.Profile
  mixed_to_behavioral_outcome :
    ∀ mixed,
      semantics.behavioralGame.outcomeKernel (mixedToBehavioral mixed) =
        semantics.mixedPureGame.outcomeKernel mixed
  behavioral_to_mixed_outcome :
    ∀ behavioral,
      semantics.behavioralGame.outcomeKernel behavioral =
        semantics.mixedPureGame.outcomeKernel (behavioralToMixed behavioral)
  behavioral_deviation_to_mixed_deviation :
    ∀ mixed (who : P)
      (behavioralDeviation : semantics.behavioralGame.Strategy who),
      ∃ mixedDeviation : semantics.mixedPureGame.Strategy who,
        semantics.behavioralGame.outcomeKernel
            (Function.update (mixedToBehavioral mixed)
              who behavioralDeviation) =
          semantics.mixedPureGame.outcomeKernel
            (Function.update mixed who mixedDeviation)
  mixed_deviation_to_behavioral_deviation :
    ∀ mixed (who : P)
      (mixedDeviation : semantics.mixedPureGame.Strategy who),
      ∃ behavioralDeviation : semantics.behavioralGame.Strategy who,
        semantics.mixedPureGame.outcomeKernel
            (Function.update mixed who mixedDeviation) =
          semantics.behavioralGame.outcomeKernel
            (Function.update (mixedToBehavioral mixed)
              who behavioralDeviation)
  arbitrary_behavioral_deviation_to_mixed_deviation :
    ∀ behavioral (who : P)
      (behavioralDeviation : semantics.behavioralGame.Strategy who),
      ∃ mixedDeviation : semantics.mixedPureGame.Strategy who,
        semantics.behavioralGame.outcomeKernel
            (Function.update behavioral who behavioralDeviation) =
          semantics.mixedPureGame.outcomeKernel
            (Function.update (behavioralToMixed behavioral)
              who mixedDeviation)

open Classical in
/-- Canonical native completed-frontier Kuhn strategic equivalence. -/
noncomputable def kuhnStrategicEquivalence
    (semantics : FrontierGameSemantics program) :
    KuhnStrategicEquivalence semantics where
  mixedToBehavioral := semantics.mixedToBehavioralProfile
  behavioralToMixed := semantics.behavioralToMixedPure
  mixed_to_behavioral_outcome := by
    intro mixed
    simpa [mixedPureGame, pureGame, KernelGame.mixedExtension,
      GameForm.mixedExtension_outcomeKernel] using
      semantics.mixedToBehavioralProfileOutcomeKernel mixed
  behavioral_to_mixed_outcome := by
    intro behavioral
    exact semantics.behavioralToMixedPureOutcomeKernel behavioral
  behavioral_deviation_to_mixed_deviation := by
    intro mixed who behavioralDeviation
    exact
      ⟨semantics.behavioralStrategyToMixedPure who behavioralDeviation,
        semantics.mixedToBehavioralUnilateralDeviationOutcomeKernel
          mixed who behavioralDeviation⟩
  mixed_deviation_to_behavioral_deviation := by
    intro mixed who mixedDeviation
    exact semantics.mixedToBehavioralMixedDeviationOutcomeKernel
      mixed who mixedDeviation
  arbitrary_behavioral_deviation_to_mixed_deviation := by
    intro behavioral who behavioralDeviation
    let deviated : semantics.behavioralGame.Profile :=
      Function.update behavioral who behavioralDeviation
    let mixedDeviation : semantics.mixedPureGame.Strategy who :=
      (semantics.behavioralToMixedPure deviated) who
    refine ⟨mixedDeviation, ?_⟩
    have hupdate :
        Function.update
            (semantics.behavioralToMixedPure behavioral)
            who mixedDeviation =
          semantics.behavioralToMixedPure deviated := by
      exact
        (semantics.behavioralToMixedPure_update
          behavioral who behavioralDeviation).symm
    rw [hupdate]
    exact semantics.behavioralToMixedPureOutcomeKernel deviated

/-- The behavioral-to-product-mixed Kuhn direction as a standard one-way
Nash deviation simulation. A target behavioral deviation is matched by the
corresponding one-player update of the induced product mixed profile. -/
noncomputable def behavioralToMixedPureNashDeviationSimulation
    (semantics : FrontierGameSemantics program) :
    KernelGame.NashDeviationSimulation
      semantics.mixedPureGame semantics.behavioralGame
      semantics.mixedPureGame.Outcome where
  viewG := { observe := fun _ => id }
  viewH := { observe := fun _ => id }
  rel := fun mixed behavioralProfile =>
    mixed = semantics.behavioralToMixedPure behavioralProfile
  law_eq := by
    intro mixed behavioralProfile hrel _
    subst mixed
    dsimp [GameForm.ViewFamily.plaw]
    exact
      congrArg (PMF.map id)
        (semantics.behavioralToMixedPureOutcomeKernel
          behavioralProfile).symm
  simulate_target_deviation := by
    intro mixed behavioralProfile hrel who behavioralDeviation
    let deviated : semantics.behavioralGame.Profile :=
      Function.update behavioralProfile who behavioralDeviation
    let mixedDeviation : semantics.mixedPureGame.Strategy who :=
      (semantics.behavioralToMixedPure deviated) who
    refine ⟨mixedDeviation, ?_⟩
    subst mixed
    have hupdate :
        Function.update
            (semantics.behavioralToMixedPure behavioralProfile)
            who mixedDeviation =
          semantics.behavioralToMixedPure deviated := by
      exact
        (semantics.behavioralToMixedPure_update
          behavioralProfile who behavioralDeviation).symm
    dsimp [GameForm.ViewFamily.plaw]
    rw [hupdate]
    exact
      congrArg (PMF.map id)
        (semantics.behavioralToMixedPureOutcomeKernel deviated).symm

/-- Canonical mixed-pure/behavioral Kuhn equivalence as a standard two-way
Nash deviation bisimulation. The relation pairs each mixed-pure profile with
its canonical behavioral realization. -/
noncomputable def mixedPureToBehavioralNashDeviationBisimulation
    (semantics : FrontierGameSemantics program) :
    KernelGame.NashDeviationBisimulation
      semantics.mixedPureGame semantics.behavioralGame
      semantics.mixedPureGame.Outcome where
  viewG := { observe := fun _ => id }
  viewH := { observe := fun _ => id }
  rel := fun mixed behavioralProfile =>
    behavioralProfile = semantics.mixedToBehavioralProfile mixed
  law_eq := by
    intro mixed behavioralProfile hrel _
    subst behavioralProfile
    dsimp [GameForm.ViewFamily.plaw]
    exact
      congrArg (PMF.map id)
        (semantics.mixedToBehavioralProfileOutcomeKernel mixed).symm
  simulate_target_deviation := by
    intro mixed behavioralProfile hrel who behavioralDeviation
    subst behavioralProfile
    let mixedDeviation : semantics.mixedPureGame.Strategy who :=
      semantics.behavioralStrategyToMixedPure who behavioralDeviation
    refine ⟨mixedDeviation, ?_⟩
    have hdeviation :=
      semantics.mixedToBehavioralUnilateralDeviationOutcomeKernel
        mixed who behavioralDeviation
    dsimp [GameForm.ViewFamily.plaw]
    exact congrArg (PMF.map id) hdeviation.symm
  simulate_source_deviation := by
    intro mixed behavioralProfile hrel who mixedDeviation
    subst behavioralProfile
    rcases semantics.mixedToBehavioralMixedDeviationOutcomeKernel
        mixed who mixedDeviation with
      ⟨behavioralDeviation, hdeviation⟩
    refine ⟨behavioralDeviation, ?_⟩
    dsimp [GameForm.ViewFamily.plaw]
    exact congrArg (PMF.map id) hdeviation

/-- A Nash equilibrium of the induced product mixed pure-strategy game is a
behavioral Nash equilibrium. This is the Nash-safe Kuhn direction currently
proved at the program-facing layer: every behavioral unilateral deviation maps
to a unilateral product-mixed deviation of the same player. -/
theorem behavioralNash_of_inducedMixedPureNash
    (semantics : FrontierGameSemantics program)
    {behavioralProfile : semantics.behavioralGame.Profile}
    (hNash :
      semantics.mixedPureGame.IsNash
        (semantics.behavioralToMixedPure behavioralProfile)) :
    semantics.behavioralGame.IsNash behavioralProfile := by
  intro who deviation
  let deviated : semantics.behavioralGame.Profile :=
    Function.update behavioralProfile who deviation
  have hbase :=
    semantics.behavioralToMixedPureEU behavioralProfile who
  have hdev :=
    semantics.behavioralToMixedPureEU deviated who
  have hupdate :
      Function.update
          (semantics.behavioralToMixedPure behavioralProfile)
          who
          ((semantics.behavioralToMixedPure deviated) who) =
        semantics.behavioralToMixedPure deviated := by
    exact
      (semantics.behavioralToMixedPure_update
        behavioralProfile who deviation).symm
  have hmixed :=
    hNash who ((semantics.behavioralToMixedPure deviated) who)
  rw [hupdate] at hmixed
  calc
    semantics.behavioralGame.eu behavioralProfile who
        =
      semantics.mixedPureGame.eu
        (semantics.behavioralToMixedPure behavioralProfile) who := hbase
    _ ≥
      semantics.mixedPureGame.eu
        (semantics.behavioralToMixedPure deviated) who := hmixed
    _ =
      semantics.behavioralGame.eu deviated who := hdev.symm

/-- Deviation-preserving mixed-to-behavioral realization used to transport
mixed-pure Nash equilibria to behavioral Nash equilibria. -/
structure MixedPureToBehavioralDeviationSimulation
    (semantics : FrontierGameSemantics program) where
  realize :
    semantics.mixedPureGame.Profile →
      semantics.behavioralGame.Profile
  outcome_eq :
    ∀ mixed,
      semantics.behavioralGame.outcomeKernel (realize mixed) =
        semantics.mixedPureGame.outcomeKernel mixed
  simulate_deviation :
    ∀ mixed (who : P)
      (behavioralDeviation : semantics.behavioralGame.Strategy who),
      ∃ mixedDeviation : semantics.mixedPureGame.Strategy who,
        semantics.behavioralGame.outcomeKernel
            (Function.update (realize mixed) who behavioralDeviation) =
          semantics.mixedPureGame.outcomeKernel
            (Function.update mixed who mixedDeviation)

/-- Build the mixed-to-behavioral deviation simulation from the canonical
mixed-to-behavioral profile. -/
noncomputable def canonicalMixedPureToBehavioralDeviationSimulation
    (semantics : FrontierGameSemantics program) :
    MixedPureToBehavioralDeviationSimulation semantics where
  realize := semantics.mixedToBehavioralProfile
  outcome_eq := by
    intro mixed
    simpa [mixedPureGame, pureGame, KernelGame.mixedExtension,
      GameForm.mixedExtension_outcomeKernel] using
      semantics.mixedToBehavioralProfileOutcomeKernel mixed
  simulate_deviation := by
    intro mixed who behavioralDeviation
    refine
      ⟨semantics.behavioralStrategyToMixedPure who behavioralDeviation, ?_⟩
    exact
      semantics.mixedToBehavioralUnilateralDeviationOutcomeKernel
        mixed who behavioralDeviation

namespace MixedPureToBehavioralDeviationSimulation

variable {semantics : FrontierGameSemantics program}

/-- The compiler-facing deviation obligation as a standard game-theory
deviation simulation. The observed outcome is the completed payoff outcome
itself, so the two views are identity views over the shared outcome carrier. -/
noncomputable def toNashDeviationSimulation
    (simulation :
      MixedPureToBehavioralDeviationSimulation semantics) :
    KernelGame.NashDeviationSimulation
      semantics.mixedPureGame semantics.behavioralGame
      semantics.mixedPureGame.Outcome :=
  GameForm.NashDeviationSimulation.ofFunctionalRealization
    ({ observe := fun _ => id } : KernelGame.ViewFamily
      semantics.mixedPureGame P (fun _ => semantics.mixedPureGame.Outcome))
    ({ observe := fun _ => id } : KernelGame.ViewFamily
      semantics.behavioralGame P (fun _ => semantics.mixedPureGame.Outcome))
    simulation.realize
    (fun _ mixed => by
      dsimp [GameForm.ViewFamily.plaw]
      exact congrArg (PMF.map id) (simulation.outcome_eq mixed).symm)
    (fun mixed who behavioralDeviation => by
      rcases simulation.simulate_deviation mixed who behavioralDeviation with
        ⟨mixedDeviation, hdeviation⟩
      exact ⟨mixedDeviation, by
        dsimp [GameForm.ViewFamily.plaw]
        exact congrArg (PMF.map id) hdeviation.symm⟩)

/-- A deviation-preserving mixed-to-behavioral realization transports mixed
Nash equilibria to behavioral Nash equilibria. -/
theorem behavioralNash_of_mixedPureNash
    (simulation :
      MixedPureToBehavioralDeviationSimulation semantics)
    {mixed : semantics.mixedPureGame.Profile}
    (hNash : semantics.mixedPureGame.IsNash mixed) :
    semantics.behavioralGame.IsNash (simulation.realize mixed) := by
  intro who behavioralDeviation
  rcases simulation.simulate_deviation mixed who behavioralDeviation with
    ⟨mixedDeviation, hdeviation⟩
  have hbase :
      semantics.behavioralGame.eu
          (simulation.realize mixed) who =
        semantics.mixedPureGame.eu mixed who := by
    calc
      semantics.behavioralGame.eu
          (simulation.realize mixed) who
          =
        Math.Probability.expect
          (semantics.behavioralGame.outcomeKernel
            (simulation.realize mixed))
          (fun outcome =>
            semantics.behavioralGame.utility outcome who) := rfl
      _ =
        Math.Probability.expect
          (semantics.mixedPureGame.outcomeKernel mixed)
          (fun outcome =>
            semantics.behavioralGame.utility outcome who) := by
            rw [simulation.outcome_eq mixed]
            rfl
      _ =
        semantics.mixedPureGame.eu mixed who := by
            rfl
  have hdev :
      semantics.behavioralGame.eu
          (Function.update (simulation.realize mixed)
            who behavioralDeviation) who =
        semantics.mixedPureGame.eu
          (Function.update mixed who mixedDeviation) who := by
    calc
      semantics.behavioralGame.eu
          (Function.update (simulation.realize mixed)
            who behavioralDeviation) who
          =
        Math.Probability.expect
          (semantics.behavioralGame.outcomeKernel
            (Function.update (simulation.realize mixed)
              who behavioralDeviation))
          (fun outcome =>
            semantics.behavioralGame.utility outcome who) := rfl
      _ =
        Math.Probability.expect
          (semantics.mixedPureGame.outcomeKernel
            (Function.update mixed who mixedDeviation))
          (fun outcome =>
            semantics.behavioralGame.utility outcome who) := by
            rw [hdeviation]
            rfl
      _ =
        semantics.mixedPureGame.eu
          (Function.update mixed who mixedDeviation) who := by
            rfl
  calc
    semantics.behavioralGame.eu
        (simulation.realize mixed) who
        =
      semantics.mixedPureGame.eu mixed who := hbase
    _ ≥
      semantics.mixedPureGame.eu
        (Function.update mixed who mixedDeviation) who :=
        hNash who mixedDeviation
    _ =
      semantics.behavioralGame.eu
        (Function.update (simulation.realize mixed)
          who behavioralDeviation) who := hdev.symm

/-- A deviation-preserving mixed-to-behavioral realization turns mixed-pure
Nash existence into behavioral Nash existence. -/
theorem behavioralNash_exists_of_mixedPureNash_exists
    (simulation :
      MixedPureToBehavioralDeviationSimulation semantics)
    (hmixed :
      ∃ mixed : semantics.mixedPureGame.Profile,
        semantics.mixedPureGame.IsNash mixed) :
    ∃ behavioral : semantics.behavioralGame.Profile,
      semantics.behavioralGame.IsNash behavioral := by
  rcases hmixed with ⟨mixed, hNash⟩
  exact
    ⟨simulation.realize mixed,
      simulation.behavioralNash_of_mixedPureNash hNash⟩

/-- A deviation-preserving mixed-to-behavioral realization yields behavioral
Nash existence for every finite-domain checked program. -/
theorem behavioralNash_exists
    (simulation :
      MixedPureToBehavioralDeviationSimulation semantics) :
    ∃ behavioral : semantics.behavioralGame.Profile,
      semantics.behavioralGame.IsNash behavioral :=
  simulation.behavioralNash_exists_of_mixedPureNash_exists
    semantics.mixedPureNash_exists

end MixedPureToBehavioralDeviationSimulation

/-- Every finite-domain checked program has a behavioral Nash equilibrium. -/
theorem behavioralNash_exists
    (semantics : FrontierGameSemantics program) :
    ∃ behavioral : semantics.behavioralGame.Profile,
      semantics.behavioralGame.IsNash behavioral :=
  semantics.canonicalMixedPureToBehavioralDeviationSimulation
    |>.behavioralNash_exists

/-- Every finite-domain checked program has a correlated equilibrium on its
behavioral frontier strategy profiles. -/
theorem behavioralCorrelatedEq_exists
    (semantics : FrontierGameSemantics program) :
    ∃ correlated : PMF semantics.behavioralGame.Profile,
      semantics.behavioralGame.IsCorrelatedEq correlated := by
  rcases semantics.behavioralNash_exists with ⟨behavioral, hNash⟩
  exact ⟨PMF.pure behavioral, KernelGame.nash_pure_isCorrelatedEq hNash⟩

/-- Every finite-domain checked program has a coarse correlated equilibrium on
its behavioral frontier strategy profiles. -/
theorem behavioralCoarseCorrelatedEq_exists
    (semantics : FrontierGameSemantics program) :
    ∃ correlated : PMF semantics.behavioralGame.Profile,
      semantics.behavioralGame.IsCoarseCorrelatedEq correlated := by
  rcases semantics.behavioralNash_exists with ⟨behavioral, hNash⟩
  exact
    ⟨PMF.pure behavioral,
      KernelGame.nash_pure_isCoarseCorrelatedEq hNash⟩

/-- Behavioral strategies can be realized by a correlated distribution over
pure-strategy profiles with the same completed-game outcome kernel. This is a
correlated pure-profile distribution, not a product mixed profile. -/
theorem behavioralToCorrelatedPure
    (semantics : FrontierGameSemantics program)
    (behavioralProfile : semantics.behavioralGame.Profile) :
    ∃ correlated : PMF semantics.pureGame.Profile,
      semantics.behavioralGame.outcomeKernel behavioralProfile =
        correlated.bind fun pureProfile =>
          semantics.pureGame.outcomeKernel pureProfile := by
  simpa [pureGame, behavioralGame, pure, behavioral] using
    semantics.games.behavioralToCorrelatedPureOutcomeKernel
      semantics.menus behavioralProfile

/-- Behavioral strategies can be realized by a correlated distribution over
pure profiles with matching expected utility, assuming bounded utility for the
queried player. -/
theorem behavioralToCorrelatedPureEU_of_bounded
    (semantics : FrontierGameSemantics program)
    (behavioralProfile : semantics.behavioralGame.Profile)
    (player : P) {C : ℝ}
    (hbd :
      ∀ outcome, |semantics.pureGame.utility outcome player| ≤ C) :
    ∃ correlated : PMF semantics.pureGame.Profile,
      semantics.behavioralGame.outcomeKernel behavioralProfile =
        (correlated.bind fun pureProfile =>
          semantics.pureGame.outcomeKernel pureProfile) ∧
      semantics.behavioralGame.eu behavioralProfile player =
        Math.Probability.expect correlated
          (fun pureProfile => semantics.pureGame.eu pureProfile player) := by
  rcases semantics.behavioralToCorrelatedPure behavioralProfile with
    ⟨correlated, hkernel⟩
  refine ⟨correlated, hkernel, ?_⟩
  calc
    semantics.behavioralGame.eu behavioralProfile player
        =
      Math.Probability.expect
        (semantics.behavioralGame.outcomeKernel behavioralProfile)
        (fun outcome => semantics.behavioralGame.utility outcome player) := rfl
    _ =
      Math.Probability.expect
        (correlated.bind fun pureProfile =>
          semantics.pureGame.outcomeKernel pureProfile)
        (fun outcome => semantics.behavioralGame.utility outcome player) := by
          rw [hkernel]
          rfl
    _ =
      Math.Probability.expect
        (correlated.bind fun pureProfile =>
          semantics.pureGame.outcomeKernel pureProfile)
        (fun outcome => semantics.pureGame.utility outcome player) := by
          rfl
    _ =
      Math.Probability.expect correlated
        (fun pureProfile =>
          Math.Probability.expect
            (semantics.pureGame.outcomeKernel pureProfile)
            (fun outcome => semantics.pureGame.utility outcome player)) := by
          exact
            Math.Probability.expect_bind_of_bounded
              correlated
              (fun pureProfile =>
                semantics.pureGame.outcomeKernel pureProfile)
              (fun outcome => semantics.pureGame.utility outcome player)
              hbd
    _ =
      Math.Probability.expect correlated
        (fun pureProfile => semantics.pureGame.eu pureProfile player) := by
          rfl

/-- Every supported pure-strategy outcome is the declared source payoff
outcome at some terminal frontier history. -/
theorem pureOutcome_support_sourceOutcome
    (semantics : FrontierGameSemantics program)
    (σ : semantics.pureGame.Profile)
    {outcome : (PrimitiveMachine (compile program.core)).Outcome}
    (hsupport : outcome ∈
      (semantics.pureGame.outcomeKernel σ).support) :
    ∃ history : (semantics.pure.view).BoundedHistory
        (completionBound (compile program.core)),
      ∃ hterminal :
        EventGraph.Terminal (compile program.core).graph
          history.lastState.state.1,
        history ∈
          ((semantics.pure.view).runDist
            (completionBound (compile program.core))
            (completionBound (compile program.core))
            ((semantics.pure.view).legalPureToBehavioral
              (completionBound (compile program.core)) σ)).support ∧
        outcome =
          sourceOutcomeAtTerminal program.core
            history.lastState.state hterminal ∧
        (PrimitiveMachine (compile program.core)).AvailableRunBatchesFrom
          ((Machine.BoundedState.init
            (PrimitiveMachine (compile program.core))
            (completionBound (compile program.core))).state)
          ((semantics.pure.view).boundedHistoryEventBatches
            (completionBound (compile program.core)) history)
          history.lastState.state := by
  simpa [pureGame, pure] using
    semantics.pure.outcomeKernel_support_sourceOutcome σ hsupport

/-- The option-valued completed pure frontier kernel is the completed run
distribution pushed forward through the source payoff projection. -/
theorem pureOptionOutcomeKernel_eq_sourceMap
    (semantics : FrontierGameSemantics program)
    (σ : semantics.pureGame.Profile) :
    semantics.pure.optionOutcomeKernel σ =
      PMF.map
        (sourceOutcomeOptionAtHistory program.core)
        ((semantics.pure.view).runDist
          (completionBound (compile program.core))
          (completionBound (compile program.core))
          ((semantics.pure.view).legalPureToBehavioral
            (completionBound (compile program.core)) σ)) := by
  simpa [pureGame, pure] using
    semantics.pure.optionOutcomeKernel_eq_sourceMap σ

/-- Every supported behavioral-strategy outcome is the declared source payoff
outcome at some terminal frontier history. -/
theorem behavioralOutcome_support_sourceOutcome
    (semantics : FrontierGameSemantics program)
    (σ : semantics.behavioralGame.Profile)
    {outcome : (PrimitiveMachine (compile program.core)).Outcome}
    (hsupport : outcome ∈
      (semantics.behavioralGame.outcomeKernel σ).support) :
    ∃ history : (semantics.behavioral.view).BoundedHistory
        (completionBound (compile program.core)),
      ∃ hterminal :
        EventGraph.Terminal (compile program.core).graph
          history.lastState.state.1,
        history ∈
          ((semantics.behavioral.view).runDist
            (completionBound (compile program.core))
            (completionBound (compile program.core)) σ).support ∧
        outcome =
          sourceOutcomeAtTerminal program.core
            history.lastState.state hterminal ∧
        (PrimitiveMachine (compile program.core)).AvailableRunBatchesFrom
          ((Machine.BoundedState.init
            (PrimitiveMachine (compile program.core))
            (completionBound (compile program.core))).state)
          ((semantics.behavioral.view).boundedHistoryEventBatches
            (completionBound (compile program.core)) history)
          history.lastState.state := by
  simpa [behavioralGame, behavioral] using
    semantics.behavioral.outcomeKernel_support_sourceOutcome σ hsupport

/-- The option-valued completed behavioral frontier kernel is the completed
run distribution pushed forward through the source payoff projection. -/
theorem behavioralOptionOutcomeKernel_eq_sourceMap
    (semantics : FrontierGameSemantics program)
    (σ : semantics.behavioralGame.Profile) :
    semantics.behavioral.optionOutcomeKernel σ =
      PMF.map
        (sourceOutcomeOptionAtHistory program.core)
        ((semantics.behavioral.view).runDist
          (completionBound (compile program.core))
          (completionBound (compile program.core)) σ) := by
  simpa [behavioralGame, behavioral] using
    semantics.behavioral.optionOutcomeKernel_eq_sourceMap σ

end FrontierGameSemantics

/-- Canonical frontier game semantics for a finite checked program. -/
noncomputable def canonicalFrontierGameSemantics
    (program : WFProgram P L) [FiniteDomains program] :
    FrontierGameSemantics program where
  games := canonicalFrontierKuhnGames program
  menus := canonicalFrontierKuhnGames_menusObservable program


end ToEventGraph

end Vegas
