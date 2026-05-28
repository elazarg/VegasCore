import Vegas.Core.ToEventGraph.Kuhn
import Vegas.Core.ToEventGraph.SourceAdequacy
import GameTheory.Core.GameForm
import GameTheory.Core.GameSimulation
import GameTheory.Concepts.DeviationSimulation
import GameTheory.Concepts.SolutionConcepts
import GameTheory.Theorems.CorrelatedEqExistence
import GameTheory.Theorems.NashExistenceMixed

/-!
# Program-facing compiled frontier games

This module packages the canonical frontier semantics of a finite checked
program.  The event graph remains the semantic IR; the package only gathers
the game-facing views and theorems that are meant to be used together.
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
@[reducible]
noncomputable def pureStrategyNonempty
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

/-- Mixed Nash existence for the compiled pure-strategy game, stated with an
explicit payoff bound because compiled payoff outcomes are integer-valued and
therefore not a finite carrier by type alone. -/
theorem mixedPureNash_exists_of_bounded
    (semantics : FrontierGameSemantics program)
    {C : P → ℝ}
    (hbd :
      ∀ who outcome,
        |semantics.pureGame.utility outcome who| ≤ C who) :
    ∃ mixed : semantics.mixedPureGame.Profile,
      semantics.mixedPureGame.IsNash mixed := by
  classical
  letI :
      ∀ player,
        Finite (semantics.pureGame.Strategy player) :=
    fun player => by
      letI := semantics.pureStrategyFintype player
      infer_instance
  letI :
      ∀ player,
        Nonempty (semantics.pureGame.Strategy player) :=
    semantics.pureStrategyNonempty
  simpa [mixedPureGame] using
    semantics.pureGame.mixed_nash_exists_of_bounded hbd

/-- Pure-strategy completed frontier histories. These are checkpoint histories
at the strategic frontier level, not primitive event schedules. -/
abbrev PureHistory (semantics : FrontierGameSemantics program) : Type :=
  (semantics.pure.view).BoundedHistory semantics.horizon

/-- Behavioral-strategy completed frontier histories. -/
abbrev BehavioralHistory (semantics : FrontierGameSemantics program) : Type :=
  (semantics.behavioral.view).BoundedHistory semantics.horizon

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
  simpa [mixedPureTerminalPublicGame] using
    semantics.pureTerminalPublicKernelGame.mixed_nash_exists

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
    simpa [pureHistoryKernel, pure, CompletedFrontierPureKernelGame.view,
      CompletedFrontierKuhnGames.pure, CompletedFrontierKuhnGames.view,
      CompletedFrontierPureKernelGame.optionOutcomeKernel, horizon, view] using
      (view.boundedOutcomeFromPure_eq_map_history
        horizon horizon σ)
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
    simpa [behavioralHistoryKernel, behavioral,
      CompletedFrontierBehavioralKernelGame.view,
      CompletedFrontierKuhnGames.behavioral, CompletedFrontierKuhnGames.view,
      CompletedFrontierBehavioralKernelGame.optionOutcomeKernel, horizon, view] using
      (view.boundedOutcomeFromBehavioral_eq_map_history
        horizon horizon σ)
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
    simpa using semantics.pureHistoryKernelGame_udist σ

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
    simpa using semantics.behavioralHistoryKernelGame_udist σ

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
    KernelGame.mixedExtension, mixedDeviation] using
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
  simpa [mixedToBehavioralProfile, mixedPureGame, pureGame,
    behavioralGame, pure, behavioral, horizon, view] using
    view.mixedPureToBehavioralProfile_update_ne
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
  simpa [mixedPureGame, pureGame, KernelGame.mixedExtension] using
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

/-- The profile-level mixed-pure-to-behavioral realization as a standard
`GameTheory` profile realization. This is enough to compare outcome laws, but
not enough to transport Nash equilibria. -/
noncomputable def mixedPureToBehavioralProfileRealization
    (semantics : FrontierGameSemantics program) :
    KernelGame.ProfileRealization
      semantics.mixedPureGame semantics.behavioralGame
      semantics.mixedPureGame.Outcome where
  viewG := { observe := id }
  viewH := { observe := id }
  rel := semantics.MixedPureToBehavioralProfileRealizes
  law_eq := by
    intro mixed behavioralProfile hrel
    dsimp [GameForm.OutcomeView.law,
      MixedPureToBehavioralProfileRealizes] at hrel ⊢
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
    behavioralToMixedPure, KernelGame.mixedExtension] using
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
  simpa [behavioralToMixedPure, horizon, view] using
    view.behavioralToMixedPure_update
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
    simpa [mixedPureGame, pureGame, KernelGame.mixedExtension] using
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
  viewG := { observe := id }
  viewH := { observe := id }
  rel := fun mixed behavioralProfile =>
    mixed = semantics.behavioralToMixedPure behavioralProfile
  law_eq := by
    intro mixed behavioralProfile hrel
    subst mixed
    dsimp [GameForm.OutcomeView.law]
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
    dsimp [GameForm.OutcomeView.law]
    rw [hupdate]
    exact
      congrArg (PMF.map id)
        (semantics.behavioralToMixedPureOutcomeKernel deviated).symm

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
    simpa [mixedPureGame, pureGame, KernelGame.mixedExtension] using
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
  KernelGame.NashDeviationSimulation.ofFunctionalRealization
    ({ observe := id } : KernelGame.OutcomeView
      semantics.mixedPureGame semantics.mixedPureGame.Outcome)
    ({ observe := id } : KernelGame.OutcomeView
      semantics.behavioralGame semantics.mixedPureGame.Outcome)
    simulation.realize
    (fun mixed => by
      dsimp [GameForm.OutcomeView.law]
      exact congrArg (PMF.map id) (simulation.outcome_eq mixed).symm)
    (fun mixed who behavioralDeviation => by
      rcases simulation.simulate_deviation mixed who behavioralDeviation with
        ⟨mixedDeviation, hdeviation⟩
      exact ⟨mixedDeviation, by
        dsimp [GameForm.OutcomeView.law]
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

/-- With bounded compiled payoff utilities, a deviation-preserving
mixed-to-behavioral realization yields behavioral Nash existence. -/
theorem behavioralNash_exists_of_bounded
    (simulation :
      MixedPureToBehavioralDeviationSimulation semantics)
    {C : P → ℝ}
    (hbd :
      ∀ who outcome,
        |semantics.pureGame.utility outcome who| ≤ C who) :
    ∃ behavioral : semantics.behavioralGame.Profile,
      semantics.behavioralGame.IsNash behavioral :=
  simulation.behavioralNash_exists_of_mixedPureNash_exists
    (semantics.mixedPureNash_exists_of_bounded hbd)

end MixedPureToBehavioralDeviationSimulation

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

namespace WFProgram

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Program-facing entry point for the canonical completed-frontier strategic
semantics. -/
noncomputable def frontierSemantics
    (program : WFProgram P L) [FiniteDomains program] :
    ToEventGraph.FrontierGameSemantics program :=
  ToEventGraph.canonicalFrontierGameSemantics program

/-- Completed pure-strategy frontier game of a checked program. -/
noncomputable def pureFrontierGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.pureGame

/-- Completed behavioral-strategy frontier game of a checked program. -/
noncomputable def behavioralFrontierGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.behavioralGame

/-- Mixed extension of the completed pure-strategy frontier game. -/
noncomputable def mixedPureFrontierGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.mixedPureGame

/-- Pure-strategy game form over completed frontier histories. -/
noncomputable def pureFrontierHistoryGameForm
    (program : WFProgram P L) [FiniteDomains program] :
    GameForm P :=
  program.frontierSemantics.pureHistoryGameForm

/-- Behavioral-strategy game form over completed frontier histories. -/
noncomputable def behavioralFrontierHistoryGameForm
    (program : WFProgram P L) [FiniteDomains program] :
    GameForm P :=
  program.frontierSemantics.behavioralHistoryGameForm

/-- Pure-strategy game form over public checkpoint-observation histories. -/
noncomputable def pureFrontierPublicHistoryGameForm
    (program : WFProgram P L) [FiniteDomains program] :
    GameForm P :=
  program.frontierSemantics.purePublicHistoryGameForm

/-- Behavioral-strategy game form over public checkpoint-observation histories. -/
noncomputable def behavioralFrontierPublicHistoryGameForm
    (program : WFProgram P L) [FiniteDomains program] :
    GameForm P :=
  program.frontierSemantics.behavioralPublicHistoryGameForm

/-- Pure-strategy game form over terminal public graph observations. -/
noncomputable def pureFrontierTerminalPublicGameForm
    (program : WFProgram P L) [FiniteDomains program] :
    GameForm P :=
  program.frontierSemantics.pureTerminalPublicGameForm

/-- Behavioral-strategy game form over terminal public graph observations. -/
noncomputable def behavioralFrontierTerminalPublicGameForm
    (program : WFProgram P L) [FiniteDomains program] :
    GameForm P :=
  program.frontierSemantics.behavioralTerminalPublicGameForm

/-- Completed pure-strategy frontier-history game. -/
noncomputable def pureFrontierHistoryKernelGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.pureHistoryKernelGame

/-- Completed behavioral-strategy frontier-history game. -/
noncomputable def behavioralFrontierHistoryKernelGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.behavioralHistoryKernelGame

/-- Completed pure-strategy game over terminal public graph observations. -/
noncomputable def pureTerminalPublicFrontierGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.pureTerminalPublicKernelGame

/-- Completed behavioral-strategy game over terminal public graph observations. -/
noncomputable def behavioralTerminalPublicFrontierGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.behavioralTerminalPublicKernelGame

/-- Mixed extension of the terminal-public pure frontier game. -/
noncomputable def mixedPureTerminalPublicFrontierGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.mixedPureTerminalPublicGame

/-- Pure frontier strategies of a checked program. -/
abbrev PureFrontierStrategy
    (program : WFProgram P L) [FiniteDomains program] (player : P) : Type :=
  (program.pureFrontierGame).Strategy player

/-- Behavioral frontier strategies of a checked program. -/
abbrev BehavioralFrontierStrategy
    (program : WFProgram P L) [FiniteDomains program] (player : P) : Type :=
  (program.behavioralFrontierGame).Strategy player

/-- Mixed-pure frontier strategies of a checked program. -/
abbrev MixedPureFrontierStrategy
    (program : WFProgram P L) [FiniteDomains program] (player : P) : Type :=
  (program.mixedPureFrontierGame).Strategy player

/-- Pure frontier strategy profiles of a checked program. -/
abbrev PureFrontierProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  (program.pureFrontierGame).Profile

/-- Behavioral frontier strategy profiles of a checked program. -/
abbrev BehavioralFrontierProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  (program.behavioralFrontierGame).Profile

/-- Mixed pure frontier strategy profiles of a checked program. -/
abbrev MixedPureFrontierProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  (program.mixedPureFrontierGame).Profile

/-- A pure frontier profile embedded as a behavioral profile has the same
completed-game outcome kernel. -/
theorem pureToBehavioralFrontierOutcomeKernel
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    program.behavioralFrontierGame.outcomeKernel
        ((program.frontierSemantics.behavioral.view).legalPureToBehavioral
          program.frontierSemantics.horizon profile) =
      program.pureFrontierGame.outcomeKernel profile := by
  simpa [PureFrontierProfile, BehavioralFrontierProfile,
    pureFrontierGame, behavioralFrontierGame, frontierSemantics] using
    program.frontierSemantics.pureToBehavioralOutcomeKernel profile

/-- A pure frontier profile embedded as a behavioral profile has the same joint
utility distribution. -/
theorem pureToBehavioralFrontierUdist
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    program.behavioralFrontierGame.udist
        ((program.frontierSemantics.behavioral.view).legalPureToBehavioral
          program.frontierSemantics.horizon profile) =
      program.pureFrontierGame.udist profile := by
  simpa [PureFrontierProfile, BehavioralFrontierProfile,
    pureFrontierGame, behavioralFrontierGame, frontierSemantics] using
    program.frontierSemantics.pureToBehavioralUdist profile

/-- Completed pure frontier histories of a checked program. -/
abbrev PureFrontierHistory
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  program.frontierSemantics.PureHistory

/-- Completed behavioral frontier histories of a checked program. -/
abbrev BehavioralFrontierHistory
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  program.frontierSemantics.BehavioralHistory

/-- The checked program's native frontier round view has an operational
primitive-event replay certificate for each supported strategic round. -/
theorem frontierView_operationallyCertified
    (program : WFProgram P L) [FiniteDomains program] :
    program.frontierSemantics.games.view.OperationallyCertified :=
  program.frontierSemantics.view_operationallyCertified

/-- Public checkpoint-observation histories of a checked program. -/
abbrev PublicFrontierHistory
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  program.frontierSemantics.PublicHistory

/-- Terminal public graph observations of a checked program. -/
abbrev TerminalPublicFrontierObservation
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  program.frontierSemantics.TerminalPublicObservation

/-- Pure terminal-public frontier strategy profiles of a checked program. -/
abbrev PureTerminalPublicFrontierProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  (program.pureTerminalPublicFrontierGame).Profile

/-- Behavioral terminal-public frontier strategy profiles of a checked
program. -/
abbrev BehavioralTerminalPublicFrontierProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  (program.behavioralTerminalPublicFrontierGame).Profile

/-- Mixed pure terminal-public frontier strategy profiles of a checked
program. -/
abbrev MixedPureTerminalPublicFrontierProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  (program.mixedPureTerminalPublicFrontierGame).Profile

/-- Correlated pure frontier profiles of a checked program. -/
abbrev PureFrontierCorrelatedProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  PMF program.PureFrontierProfile

/-- Distributions over complete behavioral frontier profiles, used by
correlated-equilibrium predicates on the behavioral frontier game. This is not
a local behavioral recommendation device. -/
abbrev BehavioralFrontierCorrelatedProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  PMF program.BehavioralFrontierProfile

/-- Correlated terminal-public pure frontier profiles of a checked program. -/
abbrev PureTerminalPublicFrontierCorrelatedProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  PMF program.PureTerminalPublicFrontierProfile

/-- Distributions over complete terminal-public behavioral frontier profiles,
used by correlated-equilibrium predicates on the behavioral terminal-public
frontier game. This is not a local behavioral recommendation device. -/
abbrev BehavioralTerminalPublicFrontierCorrelatedProfile
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  PMF program.BehavioralTerminalPublicFrontierProfile

/-- Finite carrier for a player's pure frontier strategies. -/
@[reducible]
noncomputable def pureFrontierStrategyFintype
    (program : WFProgram P L) [FiniteDomains program] (player : P) :
    Fintype (program.PureFrontierStrategy player) :=
  program.frontierSemantics.pureStrategyFintype player

/-- Pure frontier strategy spaces are nonempty for all players. -/
@[reducible]
noncomputable def pureFrontierStrategyNonempty
    (program : WFProgram P L) [FiniteDomains program] (player : P) :
    Nonempty (program.PureFrontierStrategy player) :=
  program.frontierSemantics.pureStrategyNonempty player

/-- Expected utility in the pure completed-frontier game. -/
noncomputable def pureFrontierEU
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) (player : P) : ℝ :=
  program.pureFrontierGame.eu profile player

/-- Expected utility in the behavioral completed-frontier game. -/
noncomputable def behavioralFrontierEU
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) (player : P) : ℝ :=
  program.behavioralFrontierGame.eu profile player

/-- Expected utility in the pure terminal-public frontier game. -/
noncomputable def pureTerminalPublicFrontierEU
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureTerminalPublicFrontierProfile)
    (player : P) : ℝ :=
  program.pureTerminalPublicFrontierGame.eu profile player

/-- Expected utility in the behavioral terminal-public frontier game. -/
noncomputable def behavioralTerminalPublicFrontierEU
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralTerminalPublicFrontierProfile)
    (player : P) : ℝ :=
  program.behavioralTerminalPublicFrontierGame.eu profile player

/-- Correlated expected utility in the pure completed-frontier game. -/
noncomputable def pureFrontierCorrelatedEU
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierCorrelatedProfile) (player : P) : ℝ :=
  program.pureFrontierGame.correlatedEu profile player

/-- Correlated expected utility in the behavioral completed-frontier game. -/
noncomputable def behavioralFrontierCorrelatedEU
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierCorrelatedProfile)
    (player : P) : ℝ :=
  program.behavioralFrontierGame.correlatedEu profile player

/-- Nash predicate for the pure completed-frontier game. -/
def PureFrontierNash
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) : Prop :=
  program.pureFrontierGame.IsNash profile

/-- Nash predicate for the behavioral completed-frontier game. -/
def BehavioralFrontierNash
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) : Prop :=
  program.behavioralFrontierGame.IsNash profile

/-- Nash predicate for the mixed pure completed-frontier game. -/
def MixedPureFrontierNash
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.MixedPureFrontierProfile) : Prop :=
  program.mixedPureFrontierGame.IsNash profile

/-- Nash predicate for the pure terminal-public frontier game. -/
def PureTerminalPublicFrontierNash
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureTerminalPublicFrontierProfile) : Prop :=
  program.pureTerminalPublicFrontierGame.IsNash profile

/-- Nash predicate for the behavioral terminal-public frontier game. -/
def BehavioralTerminalPublicFrontierNash
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralTerminalPublicFrontierProfile) : Prop :=
  program.behavioralTerminalPublicFrontierGame.IsNash profile

/-- Nash predicate for the mixed pure terminal-public frontier game. -/
def MixedPureTerminalPublicFrontierNash
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.MixedPureTerminalPublicFrontierProfile) : Prop :=
  program.mixedPureTerminalPublicFrontierGame.IsNash profile

/-- Best-response predicate for behavioral frontier strategies. -/
def BehavioralFrontierBestResponse
    (program : WFProgram P L) [FiniteDomains program]
    (player : P) (profile : program.BehavioralFrontierProfile)
    (strategy : program.BehavioralFrontierStrategy player) : Prop :=
  program.behavioralFrontierGame.IsBestResponse player profile strategy

/-- Dominant-strategy predicate for behavioral frontier strategies. -/
def BehavioralFrontierDominant
    (program : WFProgram P L) [FiniteDomains program]
    (player : P) (strategy : program.BehavioralFrontierStrategy player) :
    Prop :=
  program.behavioralFrontierGame.IsDominant player strategy

/-- Strict Nash predicate for behavioral frontier profiles. -/
def BehavioralFrontierStrictNash
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) : Prop :=
  program.behavioralFrontierGame.IsStrictNash profile

/-- Strict dominant-strategy predicate for behavioral frontier strategies. -/
def BehavioralFrontierStrictDominant
    (program : WFProgram P L) [FiniteDomains program]
    (player : P) (strategy : program.BehavioralFrontierStrategy player) :
    Prop :=
  program.behavioralFrontierGame.IsStrictDominant player strategy

/-- Correlated-equilibrium predicate for behavioral frontier profiles. -/
def BehavioralFrontierCorrelatedEq
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierCorrelatedProfile) : Prop :=
  program.behavioralFrontierGame.IsCorrelatedEq profile

/-- Coarse-correlated-equilibrium predicate for behavioral frontier profiles. -/
def BehavioralFrontierCoarseCorrelatedEq
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierCorrelatedProfile) : Prop :=
  program.behavioralFrontierGame.IsCoarseCorrelatedEq profile

/-- Correlated-equilibrium predicate for pure frontier profiles. -/
def PureFrontierCorrelatedEq
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierCorrelatedProfile) : Prop :=
  program.pureFrontierGame.IsCorrelatedEq profile

/-- Coarse-correlated-equilibrium predicate for pure frontier profiles. -/
def PureFrontierCoarseCorrelatedEq
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierCorrelatedProfile) : Prop :=
  program.pureFrontierGame.IsCoarseCorrelatedEq profile

/-- Correlated-equilibrium predicate for terminal-public pure frontier
profiles. -/
def PureTerminalPublicFrontierCorrelatedEq
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureTerminalPublicFrontierCorrelatedProfile) : Prop :=
  program.pureTerminalPublicFrontierGame.IsCorrelatedEq profile

/-- Coarse-correlated-equilibrium predicate for terminal-public pure frontier
profiles. -/
def PureTerminalPublicFrontierCoarseCorrelatedEq
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureTerminalPublicFrontierCorrelatedProfile) : Prop :=
  program.pureTerminalPublicFrontierGame.IsCoarseCorrelatedEq profile

/-- Correlated-equilibrium predicate for terminal-public behavioral frontier
profiles. -/
def BehavioralTerminalPublicFrontierCorrelatedEq
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralTerminalPublicFrontierCorrelatedProfile) :
    Prop :=
  program.behavioralTerminalPublicFrontierGame.IsCorrelatedEq profile

/-- Coarse-correlated-equilibrium predicate for terminal-public behavioral
frontier profiles. -/
def BehavioralTerminalPublicFrontierCoarseCorrelatedEq
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralTerminalPublicFrontierCorrelatedProfile) :
    Prop :=
  program.behavioralTerminalPublicFrontierGame.IsCoarseCorrelatedEq profile

/-- Program-facing mixed-pure-to-behavioral deviation simulation type. -/
abbrev MixedPureToBehavioralFrontierDeviationSimulation
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  ToEventGraph.FrontierGameSemantics.MixedPureToBehavioralDeviationSimulation
    program.frontierSemantics

/-- Program-facing strategy/deviation-level Kuhn equivalence package. -/
abbrev FrontierKuhnStrategicEquivalence
    (program : WFProgram P L) [FiniteDomains program] : Type :=
  ToEventGraph.FrontierGameSemantics.KuhnStrategicEquivalence
    program.frontierSemantics

/-- Canonical strategy/deviation-level Kuhn equivalence for the completed
frontier games of a checked program. -/
noncomputable def frontierKuhnStrategicEquivalence
    (program : WFProgram P L) [FiniteDomains program] :
    program.FrontierKuhnStrategicEquivalence :=
  program.frontierSemantics.kuhnStrategicEquivalence

/-- Product mixed pure-strategy profile induced by a behavioral frontier
profile. -/
noncomputable def behavioralFrontierToMixedPure
    (program : WFProgram P L) [FiniteDomains program]
    (behavioral : program.BehavioralFrontierProfile) :
    program.MixedPureFrontierProfile :=
  program.frontierSemantics.behavioralToMixedPure behavioral

/-- Canonical behavioral frontier profile realizing a mixed-pure frontier
profile by Kuhn's mixed-to-behavioral construction. -/
noncomputable def mixedPureToBehavioralFrontierProfile
    (program : WFProgram P L) [FiniteDomains program]
    (mixed : program.MixedPureFrontierProfile) :
    program.BehavioralFrontierProfile :=
  program.frontierSemantics.mixedToBehavioralProfile mixed

/-- The canonical mixed-pure-to-behavioral frontier profile preserves the
completed-frontier outcome kernel. -/
theorem mixedPureToBehavioralFrontierProfile_outcomeKernel
    (program : WFProgram P L) [FiniteDomains program]
    (mixed : program.MixedPureFrontierProfile) :
    program.behavioralFrontierGame.outcomeKernel
        (program.mixedPureToBehavioralFrontierProfile mixed) =
      program.mixedPureFrontierGame.outcomeKernel mixed := by
  simpa [mixedPureToBehavioralFrontierProfile, frontierSemantics,
    behavioralFrontierGame, mixedPureFrontierGame,
    BehavioralFrontierProfile, MixedPureFrontierProfile] using
    program.frontierSemantics.mixedToBehavioralProfileOutcomeKernel mixed

/-- Program-facing canonical mixed-pure-to-behavioral deviation simulation. -/
noncomputable def canonicalMixedPureToBehavioralFrontierDeviationSimulation
    (program : WFProgram P L) [FiniteDomains program] :
    program.MixedPureToBehavioralFrontierDeviationSimulation :=
  program.frontierSemantics
    |>.canonicalMixedPureToBehavioralDeviationSimulation

/-- Every unilateral behavioral deviation from the canonical behavioral
realization of a mixed-pure frontier profile has a matching unilateral
mixed-pure deviation with the same completed-frontier outcome kernel. -/
theorem mixedPureFrontier_behavioralDeviation_to_mixedPure
    (program : WFProgram P L) [FiniteDomains program]
    (mixed : program.MixedPureFrontierProfile)
    (who : P)
    (behavioralDeviation : program.BehavioralFrontierStrategy who) :
    ∃ mixedDeviation : program.MixedPureFrontierStrategy who,
      program.behavioralFrontierGame.outcomeKernel
          (Function.update
            (program.mixedPureToBehavioralFrontierProfile mixed)
            who behavioralDeviation) =
        program.mixedPureFrontierGame.outcomeKernel
          (Function.update mixed who mixedDeviation) := by
  refine
    ⟨program.frontierSemantics.behavioralStrategyToMixedPure
      who behavioralDeviation, ?_⟩
  simpa [frontierSemantics, behavioralFrontierGame, mixedPureFrontierGame,
    mixedPureToBehavioralFrontierProfile, MixedPureFrontierProfile,
    BehavioralFrontierStrategy, MixedPureFrontierStrategy] using
    program.frontierSemantics
      |>.mixedToBehavioralUnilateralDeviationOutcomeKernel
        mixed who behavioralDeviation

/-- Every unilateral mixed-pure deviation has a matching unilateral behavioral
deviation from the canonical behavioral realization, with the same
completed-frontier outcome kernel. -/
theorem mixedPureFrontier_mixedDeviation_to_behavioral
    (program : WFProgram P L) [FiniteDomains program]
    (mixed : program.MixedPureFrontierProfile)
    (who : P)
    (mixedDeviation : program.MixedPureFrontierStrategy who) :
    ∃ behavioralDeviation : program.BehavioralFrontierStrategy who,
      program.mixedPureFrontierGame.outcomeKernel
          (Function.update mixed who mixedDeviation) =
        program.behavioralFrontierGame.outcomeKernel
          (Function.update
            (program.mixedPureToBehavioralFrontierProfile mixed)
            who behavioralDeviation) := by
  simpa [frontierSemantics, behavioralFrontierGame, mixedPureFrontierGame,
    mixedPureToBehavioralFrontierProfile, MixedPureFrontierProfile,
    BehavioralFrontierStrategy, MixedPureFrontierStrategy] using
    program.frontierSemantics
      |>.mixedToBehavioralMixedDeviationOutcomeKernel
        mixed who mixedDeviation

/-- Mixed pure strategies realize as behavioral strategies with the same
completed-frontier outcome kernel. -/
theorem mixedPureFrontier_to_behavioral
    (program : WFProgram P L) [FiniteDomains program]
    (mixed : program.MixedPureFrontierProfile) :
    ∃ behavioral : program.BehavioralFrontierProfile,
      program.behavioralFrontierGame.outcomeKernel behavioral =
        program.mixedPureFrontierGame.outcomeKernel mixed := by
  exact
    ⟨program.mixedPureToBehavioralFrontierProfile mixed,
      program.mixedPureToBehavioralFrontierProfile_outcomeKernel mixed⟩

/-- Mixed pure strategies realize as behavioral strategies with the same
completed-frontier outcome kernel and expected utility. -/
theorem mixedPureFrontier_to_behavioral_eu
    (program : WFProgram P L) [FiniteDomains program]
    (mixed : program.MixedPureFrontierProfile) :
    ∃ behavioral : program.BehavioralFrontierProfile,
      program.behavioralFrontierGame.outcomeKernel behavioral =
        program.mixedPureFrontierGame.outcomeKernel mixed ∧
      ∀ player,
        program.behavioralFrontierGame.eu behavioral player =
          program.mixedPureFrontierGame.eu mixed player := by
  simpa [frontierSemantics, behavioralFrontierGame, mixedPureFrontierGame,
    BehavioralFrontierProfile, MixedPureFrontierProfile] using
    program.frontierSemantics.mixedToBehavioralEU mixed

/-- Relation saying that a behavioral frontier profile realizes a mixed-pure
frontier profile with the same completed-game outcome kernel. -/
def MixedPureToBehavioralFrontierProfileRealizes
    (program : WFProgram P L) [FiniteDomains program]
    (mixed : program.MixedPureFrontierProfile)
    (behavioral : program.BehavioralFrontierProfile) : Prop :=
  program.frontierSemantics.MixedPureToBehavioralProfileRealizes
    mixed behavioral

/-- Program-facing profile-level mixed-pure-to-behavioral realization. This
does not include the deviation-preservation theorem needed for Nash transport. -/
noncomputable def mixedPureToBehavioralFrontierProfileRealization
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame.ProfileRealization
      program.mixedPureFrontierGame program.behavioralFrontierGame
      program.mixedPureFrontierGame.Outcome :=
  program.frontierSemantics.mixedPureToBehavioralProfileRealization

/-- Every mixed-pure frontier profile has a behavioral profile with the same
completed-game outcome kernel. -/
theorem mixedPureToBehavioralFrontierProfileRealizes_exists
    (program : WFProgram P L) [FiniteDomains program]
    (mixed : program.MixedPureFrontierProfile) :
    ∃ behavioral : program.BehavioralFrontierProfile,
      program.MixedPureToBehavioralFrontierProfileRealizes
        mixed behavioral := by
  simpa [MixedPureToBehavioralFrontierProfileRealizes,
    MixedPureFrontierProfile, BehavioralFrontierProfile,
    frontierSemantics] using
    program.frontierSemantics
      |>.mixedPureToBehavioralProfileRealizes_exists mixed

/-- Behavioral frontier strategies induce product mixed pure strategies with
the same completed-frontier outcome kernel. -/
theorem behavioralFrontier_to_mixedPure_outcomeKernel
    (program : WFProgram P L) [FiniteDomains program]
    (behavioral : program.BehavioralFrontierProfile) :
    program.behavioralFrontierGame.outcomeKernel behavioral =
      program.mixedPureFrontierGame.outcomeKernel
        (program.behavioralFrontierToMixedPure behavioral) := by
  simpa [behavioralFrontierToMixedPure, frontierSemantics,
    behavioralFrontierGame, mixedPureFrontierGame,
    BehavioralFrontierProfile, MixedPureFrontierProfile] using
    program.frontierSemantics.behavioralToMixedPureOutcomeKernel behavioral

/-- Every unilateral behavioral deviation from an arbitrary behavioral
frontier profile has a matching unilateral mixed-pure deviation from the
profile induced by behavioral-to-product-mixed Kuhn realization. -/
theorem behavioralFrontier_deviation_to_mixedPure
    (program : WFProgram P L) [FiniteDomains program]
    (behavioral : program.BehavioralFrontierProfile)
    (who : P)
    (behavioralDeviation : program.BehavioralFrontierStrategy who) :
    ∃ mixedDeviation : program.MixedPureFrontierStrategy who,
      program.behavioralFrontierGame.outcomeKernel
          (Function.update behavioral who behavioralDeviation) =
        program.mixedPureFrontierGame.outcomeKernel
          (Function.update
            (program.behavioralFrontierToMixedPure behavioral)
            who mixedDeviation) := by
  classical
  let equivalence := program.frontierKuhnStrategicEquivalence
  simpa [equivalence, frontierKuhnStrategicEquivalence,
    behavioralFrontierToMixedPure, frontierSemantics,
    behavioralFrontierGame, mixedPureFrontierGame,
    BehavioralFrontierProfile, MixedPureFrontierProfile,
    BehavioralFrontierStrategy, MixedPureFrontierStrategy] using
    equivalence.arbitrary_behavioral_deviation_to_mixed_deviation
      behavioral who behavioralDeviation

/-- Behavioral frontier strategies induce product mixed pure strategies with
the same joint utility distribution. -/
theorem behavioralFrontier_to_mixedPure_udist
    (program : WFProgram P L) [FiniteDomains program]
    (behavioral : program.BehavioralFrontierProfile) :
    program.behavioralFrontierGame.udist behavioral =
      program.mixedPureFrontierGame.udist
        (program.behavioralFrontierToMixedPure behavioral) := by
  change
    (program.behavioralFrontierGame.outcomeKernel behavioral).bind
        (fun outcome =>
          PMF.pure (program.behavioralFrontierGame.utility outcome)) =
      (program.mixedPureFrontierGame.outcomeKernel
          (program.behavioralFrontierToMixedPure behavioral)).bind
        (fun outcome =>
          PMF.pure (program.mixedPureFrontierGame.utility outcome))
  rw [program.behavioralFrontier_to_mixedPure_outcomeKernel behavioral]
  rfl

/-- Behavioral frontier strategies induce product mixed pure strategies with
the same expected utility. -/
theorem behavioralFrontier_to_mixedPure_eu
    (program : WFProgram P L) [FiniteDomains program]
    (behavioral : program.BehavioralFrontierProfile) :
    ∀ player,
      program.behavioralFrontierGame.eu behavioral player =
        program.mixedPureFrontierGame.eu
          (program.behavioralFrontierToMixedPure behavioral) player := by
  simpa [behavioralFrontierToMixedPure, frontierSemantics,
    behavioralFrontierGame, mixedPureFrontierGame,
    BehavioralFrontierProfile, MixedPureFrontierProfile] using
    program.frontierSemantics.behavioralToMixedPureEU behavioral

/-- Program-facing Nash deviation simulation for the proved
behavioral-to-product-mixed Kuhn direction. Its relation pairs a behavioral
frontier profile with its induced product mixed-pure frontier profile. -/
noncomputable def behavioralToMixedPureFrontierNashDeviationSimulation
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame.NashDeviationSimulation
      program.mixedPureFrontierGame program.behavioralFrontierGame
      program.mixedPureFrontierGame.Outcome :=
  program.frontierSemantics.behavioralToMixedPureNashDeviationSimulation

/-- Program-facing two-direction Kuhn outcome-equality schema for completed
frontier games. This packages the behavioral-to-product-mixed direction and
the mixed-pure-to-behavioral realizability direction at outcome-kernel level. -/
theorem frontierCompleteOutcomeKuhn
    (program : WFProgram P L) [FiniteDomains program] :
    GameTheory.Theorems.KuhnCompleteViaOutcome
      program.BehavioralFrontierProfile
      (∀ player, PMF (program.PureFrontierStrategy player))
      program.PureFrontierProfile
      program.pureFrontierGame.Outcome
      (fun behavioral =>
        Math.PMFProduct.pmfPi
          (program.behavioralFrontierToMixedPure behavioral))
      Math.PMFProduct.pmfPi
      program.behavioralFrontierGame.outcomeKernel
      program.pureFrontierGame.outcomeKernel := by
  simpa [BehavioralFrontierProfile, PureFrontierStrategy,
    PureFrontierProfile, pureFrontierGame, behavioralFrontierGame,
    behavioralFrontierToMixedPure, frontierSemantics,
    ToEventGraph.FrontierGameSemantics.pureGame,
    ToEventGraph.FrontierGameSemantics.behavioralGame] using
    program.frontierSemantics.games.completeOutcomeKuhn
      program.frontierSemantics.menus

/-- Behavioral frontier strategies realize as correlated distributions over
pure frontier profiles with the same completed-frontier outcome kernel. -/
theorem behavioralFrontier_to_correlatedPure
    (program : WFProgram P L) [FiniteDomains program]
    (behavioral : program.BehavioralFrontierProfile) :
    ∃ correlated : PMF program.PureFrontierProfile,
      program.behavioralFrontierGame.outcomeKernel behavioral =
        correlated.bind fun pureProfile =>
          program.pureFrontierGame.outcomeKernel pureProfile := by
  simpa [frontierSemantics, behavioralFrontierGame, pureFrontierGame,
    BehavioralFrontierProfile, PureFrontierProfile] using
    program.frontierSemantics.behavioralToCorrelatedPure behavioral

/-- Behavioral frontier strategies realize as correlated distributions over
pure frontier profiles with the same expected utility for one player, assuming
that player's payoff coordinate is bounded. -/
theorem behavioralFrontier_to_correlatedPure_eu_of_bounded
    (program : WFProgram P L) [FiniteDomains program]
    (behavioral : program.BehavioralFrontierProfile)
    (player : P) {C : ℝ}
    (hbd :
      ∀ outcome,
        |program.pureFrontierGame.utility outcome player| ≤ C) :
    ∃ correlated : PMF program.PureFrontierProfile,
      program.behavioralFrontierGame.outcomeKernel behavioral =
        (correlated.bind fun pureProfile =>
          program.pureFrontierGame.outcomeKernel pureProfile) ∧
      program.behavioralFrontierGame.eu behavioral player =
        Math.Probability.expect correlated
          (fun pureProfile =>
            program.pureFrontierGame.eu pureProfile player) := by
  simpa [frontierSemantics, behavioralFrontierGame, pureFrontierGame,
    BehavioralFrontierProfile, PureFrontierProfile] using
    program.frontierSemantics
      |>.behavioralToCorrelatedPureEU_of_bounded behavioral player hbd

/-- A legal pure frontier strategy chooses an available optional move at every
reachable completed-frontier history. -/
theorem pureFrontierStrategy_chooses_available
    (program : WFProgram P L) [FiniteDomains program]
    {player : P} (strategy : program.PureFrontierStrategy player)
    (history : program.PureFrontierHistory) :
    strategy.1
        ((program.frontierSemantics.pure.view).reachableInfoStateOfHistory
            program.frontierSemantics.horizon player history) ∈
      (program.frontierSemantics.pure.view).boundedAvailableMoves
          program.frontierSemantics.horizon history player := by
  simpa [PureFrontierStrategy, PureFrontierHistory, frontierSemantics] using
    program.frontierSemantics
      |>.pureStrategy_chooses_available strategy history

/-- A legal behavioral frontier strategy assigns probability only to available
optional moves. -/
theorem behavioralFrontierStrategy_supports_available
    (program : WFProgram P L) [FiniteDomains program]
    {player : P} (strategy : program.BehavioralFrontierStrategy player)
    (history : program.BehavioralFrontierHistory)
    {move : Option ((program.frontierSemantics.behavioral.view).Act player)}
    (hmove :
      move ∈
        (strategy.1
          ((program.frontierSemantics.behavioral.view).reachableInfoStateOfHistory
              program.frontierSemantics.horizon player history)).support) :
    move ∈
      (program.frontierSemantics.behavioral.view).boundedAvailableMoves
          program.frontierSemantics.horizon history player := by
  simpa [BehavioralFrontierStrategy, BehavioralFrontierHistory,
    frontierSemantics] using
    program.frontierSemantics
      |>.behavioralStrategy_supports_available strategy history hmove

/-- Pure frontier strategies depend only on the player's information state. -/
theorem pureFrontierStrategy_eq_of_playerView_eq
    (program : WFProgram P L) [FiniteDomains program]
    {player : P} (strategy : program.PureFrontierStrategy player)
    {left right : program.PureFrontierHistory}
    (hview : left.playerView player = right.playerView player) :
    strategy.1
        ((program.frontierSemantics.pure.view).reachableInfoStateOfHistory
            program.frontierSemantics.horizon player left) =
      strategy.1
        ((program.frontierSemantics.pure.view).reachableInfoStateOfHistory
            program.frontierSemantics.horizon player right) := by
  simpa [PureFrontierStrategy, PureFrontierHistory, frontierSemantics] using
    program.frontierSemantics
      |>.pureStrategy_eq_of_playerView_eq strategy hview

/-- Behavioral frontier strategies depend only on the player's information
state. -/
theorem behavioralFrontierStrategy_eq_of_playerView_eq
    (program : WFProgram P L) [FiniteDomains program]
    {player : P} (strategy : program.BehavioralFrontierStrategy player)
    {left right : program.BehavioralFrontierHistory}
    (hview : left.playerView player = right.playerView player) :
    strategy.1
        ((program.frontierSemantics.behavioral.view).reachableInfoStateOfHistory
            program.frontierSemantics.horizon player left) =
      strategy.1
        ((program.frontierSemantics.behavioral.view).reachableInfoStateOfHistory
            program.frontierSemantics.horizon player right) := by
  simpa [BehavioralFrontierStrategy, BehavioralFrontierHistory,
    frontierSemantics] using
    program.frontierSemantics
      |>.behavioralStrategy_eq_of_playerView_eq strategy hview

/-- The option-valued completed pure frontier kernel is the completed run
distribution pushed forward through the source payoff projection. -/
theorem pureFrontierOptionOutcomeKernel_eq_sourceMap
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    program.frontierSemantics.pure.optionOutcomeKernel profile =
      PMF.map
        (ToEventGraph.sourceOutcomeOptionAtHistory program.core)
        ((program.frontierSemantics.pure.view).runDist
          (ToEventGraph.completionBound
            (ToEventGraph.compile program.core))
          (ToEventGraph.completionBound
            (ToEventGraph.compile program.core))
          ((program.frontierSemantics.pure.view).legalPureToBehavioral
            (ToEventGraph.completionBound
              (ToEventGraph.compile program.core)) profile)) := by
  simpa [frontierSemantics, PureFrontierProfile] using
    program.frontierSemantics.pureOptionOutcomeKernel_eq_sourceMap profile

/-- The option-valued completed behavioral frontier kernel is the completed run
distribution pushed forward through the source payoff projection. -/
theorem behavioralFrontierOptionOutcomeKernel_eq_sourceMap
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.frontierSemantics.behavioral.optionOutcomeKernel profile =
      PMF.map
        (ToEventGraph.sourceOutcomeOptionAtHistory program.core)
        ((program.frontierSemantics.behavioral.view).runDist
          (ToEventGraph.completionBound
            (ToEventGraph.compile program.core))
          (ToEventGraph.completionBound
            (ToEventGraph.compile program.core)) profile) := by
  simpa [frontierSemantics, BehavioralFrontierProfile] using
    program.frontierSemantics.behavioralOptionOutcomeKernel_eq_sourceMap
      profile

/-- A Nash equilibrium of the induced product mixed pure frontier profile is a
behavioral Nash equilibrium. -/
theorem behavioralFrontier_nash_of_induced_mixedPure_nash
    (program : WFProgram P L) [FiniteDomains program]
    {behavioral : program.BehavioralFrontierProfile}
    (hNash :
      program.mixedPureFrontierGame.IsNash
        (program.behavioralFrontierToMixedPure behavioral)) :
    program.behavioralFrontierGame.IsNash behavioral := by
  simpa [behavioralFrontierToMixedPure, frontierSemantics,
    behavioralFrontierGame, mixedPureFrontierGame,
    BehavioralFrontierProfile, MixedPureFrontierProfile] using
    program.frontierSemantics.behavioralNash_of_inducedMixedPureNash hNash

/-- A deviation-preserving mixed-to-behavioral frontier realization transports
mixed-pure Nash equilibria to behavioral Nash equilibria. -/
theorem behavioralFrontier_nash_of_mixedPure_nash
    (program : WFProgram P L) [FiniteDomains program]
    (simulation :
      program.MixedPureToBehavioralFrontierDeviationSimulation)
    {mixed : program.MixedPureFrontierProfile}
    (hNash : program.MixedPureFrontierNash mixed) :
    program.BehavioralFrontierNash (simulation.realize mixed) := by
  simpa [MixedPureToBehavioralFrontierDeviationSimulation,
    MixedPureFrontierNash, BehavioralFrontierNash, frontierSemantics,
    mixedPureFrontierGame, behavioralFrontierGame,
    MixedPureFrontierProfile, BehavioralFrontierProfile] using
    simulation.behavioralNash_of_mixedPureNash hNash

/-- Bounded mixed Nash existence for the completed pure frontier payoff game. -/
theorem mixedPureFrontier_nash_exists_of_bounded
    (program : WFProgram P L) [FiniteDomains program]
    {C : P → ℝ}
    (hbd :
      ∀ player outcome,
        |program.pureFrontierGame.utility outcome player| ≤ C player) :
    ∃ mixed : program.MixedPureFrontierProfile,
      program.mixedPureFrontierGame.IsNash mixed := by
  simpa [frontierSemantics, pureFrontierGame, mixedPureFrontierGame,
    MixedPureFrontierProfile] using
    program.frontierSemantics.mixedPureNash_exists_of_bounded hbd

/-- Bounded correlated-equilibrium existence for the completed pure frontier
payoff game. -/
theorem pureFrontier_correlatedEq_exists_of_bounded
    (program : WFProgram P L) [FiniteDomains program]
    {C : P → ℝ}
    (hbd :
      ∀ player outcome,
        |program.pureFrontierGame.utility outcome player| ≤ C player) :
    ∃ correlated : PMF program.PureFrontierProfile,
      program.pureFrontierGame.IsCorrelatedEq correlated := by
  classical
  letI : Finite P := Finite.of_fintype P
  letI :
      ∀ player,
        Finite (program.pureFrontierGame.Strategy player) :=
    fun player => by
      letI : Fintype (program.pureFrontierGame.Strategy player) :=
        program.pureFrontierStrategyFintype player
      exact Finite.of_fintype _
  letI :
      ∀ player,
        Nonempty (program.pureFrontierGame.Strategy player) :=
    program.pureFrontierStrategyNonempty
  simpa [PureFrontierProfile] using
    program.pureFrontierGame.correlatedEq_exists_of_bounded hbd

/-- Bounded coarse-correlated-equilibrium existence for the completed pure
frontier payoff game. -/
theorem pureFrontier_coarseCorrelatedEq_exists_of_bounded
    (program : WFProgram P L) [FiniteDomains program]
    {C : P → ℝ}
    (hbd :
      ∀ player outcome,
        |program.pureFrontierGame.utility outcome player| ≤ C player) :
    ∃ correlated : PMF program.PureFrontierProfile,
      program.pureFrontierGame.IsCoarseCorrelatedEq correlated := by
  classical
  letI : Finite P := Finite.of_fintype P
  letI :
      ∀ player,
        Finite (program.pureFrontierGame.Strategy player) :=
    fun player => by
      letI : Fintype (program.pureFrontierGame.Strategy player) :=
        program.pureFrontierStrategyFintype player
      exact Finite.of_fintype _
  letI :
      ∀ player,
        Nonempty (program.pureFrontierGame.Strategy player) :=
    program.pureFrontierStrategyNonempty
  simpa [PureFrontierProfile] using
    program.pureFrontierGame.coarseCorrelatedEq_exists_of_bounded hbd

/-- With bounded compiled payoff utilities, a deviation-preserving
mixed-to-behavioral frontier realization yields behavioral Nash existence. -/
theorem behavioralFrontier_nash_exists_of_bounded
    (program : WFProgram P L) [FiniteDomains program]
    (simulation :
      program.MixedPureToBehavioralFrontierDeviationSimulation)
    {C : P → ℝ}
    (hbd :
      ∀ player outcome,
        |program.pureFrontierGame.utility outcome player| ≤ C player) :
    ∃ behavioral : program.BehavioralFrontierProfile,
      program.BehavioralFrontierNash behavioral := by
  simpa [MixedPureToBehavioralFrontierDeviationSimulation,
    BehavioralFrontierNash, frontierSemantics, pureFrontierGame,
    behavioralFrontierGame, BehavioralFrontierProfile] using
    simulation.behavioralNash_exists_of_bounded hbd

/-- Correlated-equilibrium existence for the finite terminal-public frontier
game. -/
theorem pureTerminalPublicFrontier_correlatedEq_exists
    (program : WFProgram P L) [FiniteDomains program] :
    ∃ correlated : PMF program.PureTerminalPublicFrontierProfile,
      program.pureTerminalPublicFrontierGame.IsCorrelatedEq correlated := by
  classical
  letI : Finite P := Finite.of_fintype P
  letI :
      ∀ player,
        Finite (program.pureTerminalPublicFrontierGame.Strategy player) :=
    fun player => by
      letI : Fintype (program.pureFrontierGame.Strategy player) :=
        program.frontierSemantics.pureStrategyFintype player
      have hfinite : Finite (program.pureFrontierGame.Strategy player) :=
        Finite.of_fintype _
      simpa [pureTerminalPublicFrontierGame,
        ToEventGraph.FrontierGameSemantics.pureTerminalPublicKernelGame,
        ToEventGraph.FrontierGameSemantics.pureTerminalPublicGameForm,
        pureFrontierGame, frontierSemantics] using hfinite
  letI :
      ∀ player,
        Nonempty (program.pureTerminalPublicFrontierGame.Strategy player) :=
    fun player => by
      simpa [pureTerminalPublicFrontierGame,
        ToEventGraph.FrontierGameSemantics.pureTerminalPublicKernelGame,
        ToEventGraph.FrontierGameSemantics.pureTerminalPublicGameForm,
        pureFrontierGame, frontierSemantics] using
        program.frontierSemantics.pureStrategyNonempty player
  letI :
      ∀ field : Fin (ToEventGraph.compile program.core).graph.fieldCount,
        Fintype
          (L.Val ((ToEventGraph.compile program.core).graph.fieldRow field).ty) :=
    program.frontierSemantics.games.fieldFintype
  letI :
      Fintype
        (EventGraph.PublicObservation
          (ToEventGraph.compile program.core).graph) :=
    inferInstance
  letI :
      Finite program.pureTerminalPublicFrontierGame.Outcome := by
    change Finite
      (EventGraph.PublicObservation (ToEventGraph.compile program.core).graph)
    exact Finite.of_fintype _
  simpa [PureTerminalPublicFrontierProfile] using
    program.pureTerminalPublicFrontierGame.correlatedEq_exists

/-- Coarse-correlated-equilibrium existence for the finite terminal-public
frontier game. -/
theorem pureTerminalPublicFrontier_coarseCorrelatedEq_exists
    (program : WFProgram P L) [FiniteDomains program] :
    ∃ correlated : PMF program.PureTerminalPublicFrontierProfile,
      program.pureTerminalPublicFrontierGame.IsCoarseCorrelatedEq
        correlated := by
  classical
  letI : Finite P := Finite.of_fintype P
  letI :
      ∀ player,
        Finite (program.pureTerminalPublicFrontierGame.Strategy player) :=
    fun player => by
      letI : Fintype (program.pureFrontierGame.Strategy player) :=
        program.frontierSemantics.pureStrategyFintype player
      have hfinite : Finite (program.pureFrontierGame.Strategy player) :=
        Finite.of_fintype _
      simpa [pureTerminalPublicFrontierGame,
        ToEventGraph.FrontierGameSemantics.pureTerminalPublicKernelGame,
        ToEventGraph.FrontierGameSemantics.pureTerminalPublicGameForm,
        pureFrontierGame, frontierSemantics] using hfinite
  letI :
      ∀ player,
        Nonempty (program.pureTerminalPublicFrontierGame.Strategy player) :=
    fun player => by
      simpa [pureTerminalPublicFrontierGame,
        ToEventGraph.FrontierGameSemantics.pureTerminalPublicKernelGame,
        ToEventGraph.FrontierGameSemantics.pureTerminalPublicGameForm,
        pureFrontierGame, frontierSemantics] using
        program.frontierSemantics.pureStrategyNonempty player
  letI :
      ∀ field : Fin (ToEventGraph.compile program.core).graph.fieldCount,
        Fintype
          (L.Val ((ToEventGraph.compile program.core).graph.fieldRow field).ty) :=
    program.frontierSemantics.games.fieldFintype
  letI :
      Fintype
        (EventGraph.PublicObservation
          (ToEventGraph.compile program.core).graph) :=
    inferInstance
  letI :
      Finite program.pureTerminalPublicFrontierGame.Outcome := by
    change Finite
      (EventGraph.PublicObservation (ToEventGraph.compile program.core).graph)
    exact Finite.of_fintype _
  simpa [PureTerminalPublicFrontierProfile] using
    program.pureTerminalPublicFrontierGame.coarseCorrelatedEq_exists

/-- Mixed Nash existence for the finite terminal-public frontier game. -/
theorem mixedPureTerminalPublicFrontier_nash_exists
    (program : WFProgram P L) [FiniteDomains program] :
    ∃ mixed : program.MixedPureTerminalPublicFrontierProfile,
      program.MixedPureTerminalPublicFrontierNash mixed := by
  simpa [frontierSemantics, mixedPureTerminalPublicFrontierGame,
    MixedPureTerminalPublicFrontierProfile,
    MixedPureTerminalPublicFrontierNash] using
    program.frontierSemantics.terminalPublicMixedNash_exists

end WFProgram

end Vegas
