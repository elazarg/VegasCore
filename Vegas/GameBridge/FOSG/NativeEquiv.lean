import Vegas.GameBridge.FOSG.FromCore
import Vegas.Strategic.Native

/-!
# Native/FOSG event-graph equivalence

The native strategic semantics for checked programs is defined from
`Machine.RoundView`.  The FOSG layer uses the same event-graph frontier rounds
as a factored-observation presentation.  This file transports histories,
information states, strategies, and bounded outcome kernels between the two
presentations.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

namespace NativeFOSG

/-! ## Steps and histories -/

noncomputable def nativeStepToFOSG (g : WFProgram P L) (horizon : Nat)
    (step : (eventGraphRoundView g).BoundedStep horizon) :
    (((eventGraphFOSGView g).toBoundedFOSG horizon).Step) := by
  refine ⟨step.src, step.act, step.dst, ?_⟩
  simpa [eventGraphRoundView, eventGraphFOSGView, EventGraph.toRoundView,
    EventGraph.toFOSGView, Machine.RoundView.boundedTransition,
    Machine.FOSGView.toBoundedFOSG] using step.support

noncomputable def fosgStepToNative (g : WFProgram P L) (horizon : Nat)
    (step : (((eventGraphFOSGView g).toBoundedFOSG horizon).Step)) :
    (eventGraphRoundView g).BoundedStep horizon := by
  refine ⟨step.src, step.act, step.dst, ?_⟩
  simpa [eventGraphRoundView, eventGraphFOSGView, EventGraph.toRoundView,
    EventGraph.toFOSGView, Machine.RoundView.boundedTransition,
    Machine.FOSGView.toBoundedFOSG] using step.support

@[simp] theorem fosgStepToNative_nativeStepToFOSG
    (g : WFProgram P L) (horizon : Nat)
    (step : (eventGraphRoundView g).BoundedStep horizon) :
    fosgStepToNative g horizon (nativeStepToFOSG g horizon step) = step := by
  cases step
  simp [nativeStepToFOSG, fosgStepToNative]

@[simp] theorem nativeStepToFOSG_fosgStepToNative
    (g : WFProgram P L) (horizon : Nat)
    (step : (((eventGraphFOSGView g).toBoundedFOSG horizon).Step)) :
    nativeStepToFOSG g horizon (fosgStepToNative g horizon step) = step := by
  cases step
  simp [nativeStepToFOSG, fosgStepToNative]

@[simp] theorem nativeStepToFOSG_src
    (g : WFProgram P L) (horizon : Nat)
    (step : (eventGraphRoundView g).BoundedStep horizon) :
    (nativeStepToFOSG g horizon step).src = step.src := rfl

@[simp] theorem nativeStepToFOSG_dst
    (g : WFProgram P L) (horizon : Nat)
    (step : (eventGraphRoundView g).BoundedStep horizon) :
    (nativeStepToFOSG g horizon step).dst = step.dst := rfl

@[simp] theorem fosgStepToNative_src
    (g : WFProgram P L) (horizon : Nat)
    (step : (((eventGraphFOSGView g).toBoundedFOSG horizon).Step)) :
    (fosgStepToNative g horizon step).src = step.src := rfl

@[simp] theorem fosgStepToNative_dst
    (g : WFProgram P L) (horizon : Nat)
    (step : (((eventGraphFOSGView g).toBoundedFOSG horizon).Step)) :
    (fosgStepToNative g horizon step).dst = step.dst := rfl

theorem nativeStepChainToFOSG (g : WFProgram P L) (horizon : Nat) :
    ∀ {start : (eventGraphMachine g).BoundedState horizon}
      {steps : List ((eventGraphRoundView g).BoundedStep horizon)},
      (eventGraphRoundView g).StepChainFrom horizon start steps →
      ((eventGraphFOSGView g).toBoundedFOSG horizon).StepChainFrom start
        (steps.map (nativeStepToFOSG g horizon))
  | _start, [], _hchain => by
      trivial
  | _start, _step :: _steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      exact ⟨by simpa using hsrc, nativeStepChainToFOSG g horizon htail⟩

theorem fosgStepChainToNative (g : WFProgram P L) (horizon : Nat) :
    ∀ {start : (eventGraphMachine g).BoundedState horizon}
      {steps : List (((eventGraphFOSGView g).toBoundedFOSG horizon).Step)},
      ((eventGraphFOSGView g).toBoundedFOSG horizon).StepChainFrom start steps →
      (eventGraphRoundView g).StepChainFrom horizon start
        (steps.map (fosgStepToNative g horizon))
  | _start, [], _hchain => by
      trivial
  | _start, _step :: _steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      exact ⟨by simpa using hsrc, fosgStepChainToNative g horizon htail⟩

theorem lastState_map_nativeToFOSG (g : WFProgram P L) (horizon : Nat) :
    ∀ {start : (eventGraphMachine g).BoundedState horizon}
      (steps : List ((eventGraphRoundView g).BoundedStep horizon)),
      ((eventGraphFOSGView g).toBoundedFOSG horizon).lastStateFrom start
          (steps.map (nativeStepToFOSG g horizon)) =
        (eventGraphRoundView g).lastStateFrom horizon start steps
  | _start, [] => by
      simp [GameTheory.FOSG.lastStateFrom, Machine.RoundView.lastStateFrom]
  | _start, step :: steps => by
      simpa [GameTheory.FOSG.lastStateFrom, Machine.RoundView.lastStateFrom,
        nativeStepToFOSG] using
        lastState_map_nativeToFOSG g horizon (start := step.dst) steps

theorem lastState_map_fosgToNative (g : WFProgram P L) (horizon : Nat) :
    ∀ {start : (eventGraphMachine g).BoundedState horizon}
      (steps : List (((eventGraphFOSGView g).toBoundedFOSG horizon).Step)),
      (eventGraphRoundView g).lastStateFrom horizon start
          (steps.map (fosgStepToNative g horizon)) =
        ((eventGraphFOSGView g).toBoundedFOSG horizon).lastStateFrom start steps
  | _start, [] => by
      simp [GameTheory.FOSG.lastStateFrom, Machine.RoundView.lastStateFrom]
  | _start, step :: steps => by
      simpa [GameTheory.FOSG.lastStateFrom, Machine.RoundView.lastStateFrom,
        fosgStepToNative] using
        lastState_map_fosgToNative g horizon (start := step.dst) steps

noncomputable def nativeHistoryToFOSG (g : WFProgram P L) (horizon : Nat)
    (h : (eventGraphRoundView g).BoundedHistory horizon) :
    (((eventGraphFOSGView g).toBoundedFOSG horizon).History) :=
  ⟨h.steps.map (nativeStepToFOSG g horizon), by
    simpa [eventGraphRoundView, eventGraphMachine, eventGraphFOSGView,
      Machine.FOSGView.toBoundedFOSG] using
      nativeStepChainToFOSG g horizon h.chain⟩

noncomputable def fosgHistoryToNative (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)) :
    (eventGraphRoundView g).BoundedHistory horizon :=
  ⟨h.steps.map (fosgStepToNative g horizon), by
    simpa [eventGraphRoundView, eventGraphMachine, eventGraphFOSGView,
      Machine.FOSGView.toBoundedFOSG] using
      fosgStepChainToNative g horizon h.chain⟩

@[simp] theorem nativeHistoryToFOSG_steps
    (g : WFProgram P L) (horizon : Nat)
    (h : (eventGraphRoundView g).BoundedHistory horizon) :
    (nativeHistoryToFOSG g horizon h).steps =
      h.steps.map (nativeStepToFOSG g horizon) := rfl

@[simp] theorem fosgHistoryToNative_steps
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)) :
    (fosgHistoryToNative g horizon h).steps =
      h.steps.map (fosgStepToNative g horizon) := rfl

@[simp] theorem nativeHistoryToFOSG_lastState
    (g : WFProgram P L) (horizon : Nat)
    (h : (eventGraphRoundView g).BoundedHistory horizon) :
    (nativeHistoryToFOSG g horizon h).lastState = h.lastState := by
  simp [nativeHistoryToFOSG, Machine.RoundView.BoundedHistory.lastState,
    GameTheory.FOSG.History.lastState, lastState_map_nativeToFOSG]

@[simp] theorem fosgHistoryToNative_lastState
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)) :
    (fosgHistoryToNative g horizon h).lastState = h.lastState := by
  simp [fosgHistoryToNative, Machine.RoundView.BoundedHistory.lastState,
    GameTheory.FOSG.History.lastState, lastState_map_fosgToNative]

@[simp] theorem fosgHistoryToNative_nativeHistoryToFOSG
    (g : WFProgram P L) (horizon : Nat)
    (h : (eventGraphRoundView g).BoundedHistory horizon) :
    fosgHistoryToNative g horizon (nativeHistoryToFOSG g horizon h) = h := by
  apply Machine.RoundView.BoundedHistory.ext
  rw [fosgHistoryToNative_steps, nativeHistoryToFOSG_steps]
  simp only [List.map_map]
  change
    List.map
        (fun step => fosgStepToNative g horizon (nativeStepToFOSG g horizon step))
        h.steps = h.steps
  induction h.steps with
  | nil =>
      rfl
  | cons step steps ih =>
      simp

@[simp] theorem nativeHistoryToFOSG_fosgHistoryToNative
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)) :
    nativeHistoryToFOSG g horizon (fosgHistoryToNative g horizon h) = h := by
  apply GameTheory.FOSG.History.ext
  rw [nativeHistoryToFOSG_steps, fosgHistoryToNative_steps]
  simp only [List.map_map]
  change
    List.map
        (fun step => nativeStepToFOSG g horizon (fosgStepToNative g horizon step))
        h.steps = h.steps
  induction h.steps with
  | nil =>
      rfl
  | cons step steps ih =>
      simp

/-! ## Player information states -/

def nativePlayerEventToFOSG (g : WFProgram P L) (horizon : Nat) (who : P) :
    Machine.RoundView.PlayerEvent (eventGraphRoundView g) who →
      GameTheory.FOSG.PlayerEvent ((eventGraphFOSGView g).toBoundedFOSG horizon) who
  | .act action => .act action
  | .obs priv pub => .obs priv pub

def fosgPlayerEventToNative (g : WFProgram P L) (horizon : Nat) (who : P) :
    GameTheory.FOSG.PlayerEvent ((eventGraphFOSGView g).toBoundedFOSG horizon) who →
      Machine.RoundView.PlayerEvent (eventGraphRoundView g) who
  | .act action => .act action
  | .obs priv pub => .obs priv pub

@[simp] theorem fosgPlayerEventToNative_nativePlayerEventToFOSG
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (ev : Machine.RoundView.PlayerEvent (eventGraphRoundView g) who) :
    fosgPlayerEventToNative g horizon who
        (nativePlayerEventToFOSG g horizon who ev) = ev := by
  cases ev <;> rfl

@[simp] theorem nativePlayerEventToFOSG_fosgPlayerEventToNative
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (ev : GameTheory.FOSG.PlayerEvent
      ((eventGraphFOSGView g).toBoundedFOSG horizon) who) :
    nativePlayerEventToFOSG g horizon who
        (fosgPlayerEventToNative g horizon who ev) = ev := by
  cases ev <;> rfl

def nativeInfoToFOSG (g : WFProgram P L) (horizon : Nat) (who : P)
    (info : (eventGraphRoundView g).InfoState who) :
    ((eventGraphFOSGView g).toBoundedFOSG horizon).InfoState who :=
  info.map (nativePlayerEventToFOSG g horizon who)

def fosgInfoToNative (g : WFProgram P L) (horizon : Nat) (who : P)
    (info : ((eventGraphFOSGView g).toBoundedFOSG horizon).InfoState who) :
    (eventGraphRoundView g).InfoState who :=
  info.map (fosgPlayerEventToNative g horizon who)

@[simp] theorem fosgInfoToNative_nativeInfoToFOSG
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (info : (eventGraphRoundView g).InfoState who) :
    fosgInfoToNative g horizon who (nativeInfoToFOSG g horizon who info) =
      info := by
  unfold nativeInfoToFOSG fosgInfoToNative
  simp only [List.map_map]
  change
    List.map
        (fun ev =>
          fosgPlayerEventToNative g horizon who
            (nativePlayerEventToFOSG g horizon who ev)) info = info
  induction info with
  | nil =>
      rfl
  | cons ev rest ih =>
      simp

@[simp] theorem nativeInfoToFOSG_fosgInfoToNative
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (info : ((eventGraphFOSGView g).toBoundedFOSG horizon).InfoState who) :
    nativeInfoToFOSG g horizon who (fosgInfoToNative g horizon who info) =
      info := by
  unfold nativeInfoToFOSG fosgInfoToNative
  simp only [List.map_map]
  change
    List.map
        (fun ev =>
          nativePlayerEventToFOSG g horizon who
            (fosgPlayerEventToNative g horizon who ev)) info = info
  induction info with
  | nil =>
      rfl
  | cons ev rest ih =>
      simp

theorem nativeStepToFOSG_playerView
    (g : WFProgram P L) (horizon : Nat)
    (step : (eventGraphRoundView g).BoundedStep horizon) (who : P) :
    GameTheory.FOSG.Step.playerView (nativeStepToFOSG g horizon step) who =
      (Machine.RoundView.BoundedStep.playerView step who).map
        (nativePlayerEventToFOSG g horizon who) := by
  cases step with
  | mk src act dst support =>
      cases hact : (act : JointAction (eventGraphRoundView g).Act) who with
      | none =>
          simp [nativeStepToFOSG, nativePlayerEventToFOSG,
            GameTheory.FOSG.Step.playerView, Machine.RoundView.BoundedStep.playerView,
            GameTheory.FOSG.Step.ownAction?, Machine.RoundView.BoundedStep.ownAction?,
            hact, GameTheory.FOSG.Step.privateObs, GameTheory.FOSG.Step.publicObs,
            Machine.RoundView.BoundedStep.privateObs,
            Machine.RoundView.BoundedStep.publicObs,
            Machine.FOSGView.toBoundedFOSG]
      | some _action =>
          simp [nativeStepToFOSG, nativePlayerEventToFOSG,
            GameTheory.FOSG.Step.playerView, Machine.RoundView.BoundedStep.playerView,
            GameTheory.FOSG.Step.ownAction?, Machine.RoundView.BoundedStep.ownAction?,
            hact, GameTheory.FOSG.Step.privateObs, GameTheory.FOSG.Step.publicObs,
            Machine.RoundView.BoundedStep.privateObs,
            Machine.RoundView.BoundedStep.publicObs,
            Machine.FOSGView.toBoundedFOSG]

theorem fosgStepToNative_playerView
    (g : WFProgram P L) (horizon : Nat)
    (step : (((eventGraphFOSGView g).toBoundedFOSG horizon).Step)) (who : P) :
    Machine.RoundView.BoundedStep.playerView
        (fosgStepToNative g horizon step) who =
      (GameTheory.FOSG.Step.playerView step who).map
        (fosgPlayerEventToNative g horizon who) := by
  cases step with
  | mk src act dst support =>
      cases hact : (act : JointAction (eventGraphFOSGView g).Act) who with
      | none =>
          simp [fosgStepToNative, fosgPlayerEventToNative,
            GameTheory.FOSG.Step.playerView, Machine.RoundView.BoundedStep.playerView,
            GameTheory.FOSG.Step.ownAction?, Machine.RoundView.BoundedStep.ownAction?,
            hact, GameTheory.FOSG.Step.privateObs, GameTheory.FOSG.Step.publicObs,
            Machine.RoundView.BoundedStep.privateObs,
            Machine.RoundView.BoundedStep.publicObs,
            Machine.FOSGView.toBoundedFOSG]
      | some _action =>
          simp [fosgStepToNative, fosgPlayerEventToNative,
            GameTheory.FOSG.Step.playerView, Machine.RoundView.BoundedStep.playerView,
            GameTheory.FOSG.Step.ownAction?, Machine.RoundView.BoundedStep.ownAction?,
            hact, GameTheory.FOSG.Step.privateObs, GameTheory.FOSG.Step.publicObs,
            Machine.RoundView.BoundedStep.privateObs,
            Machine.RoundView.BoundedStep.publicObs,
            Machine.FOSGView.toBoundedFOSG]

theorem nativePlayerViewFromToFOSG
    (g : WFProgram P L) (horizon : Nat) (who : P) :
    ∀ (steps : List ((eventGraphRoundView g).BoundedStep horizon)),
      GameTheory.FOSG.History.playerViewFrom
          (G := (eventGraphFOSGView g).toBoundedFOSG horizon) who
          (steps.map (nativeStepToFOSG g horizon)) =
        nativeInfoToFOSG g horizon who
          (Machine.RoundView.BoundedHistory.playerViewFrom
            (view := eventGraphRoundView g) (horizon := horizon) who steps)
  | [] => by
      simp [GameTheory.FOSG.History.playerViewFrom,
        Machine.RoundView.BoundedHistory.playerViewFrom, nativeInfoToFOSG]
  | step :: steps => by
      simp [GameTheory.FOSG.History.playerViewFrom,
        Machine.RoundView.BoundedHistory.playerViewFrom,
        nativeStepToFOSG_playerView g horizon step who,
        nativePlayerViewFromToFOSG g horizon who steps,
        nativeInfoToFOSG, List.map_append]

theorem fosgPlayerViewFromToNative
    (g : WFProgram P L) (horizon : Nat) (who : P) :
    ∀ (steps :
        List (((eventGraphFOSGView g).toBoundedFOSG horizon).Step)),
      Machine.RoundView.BoundedHistory.playerViewFrom
          (view := eventGraphRoundView g) (horizon := horizon) who
          (steps.map (fosgStepToNative g horizon)) =
        fosgInfoToNative g horizon who
          (GameTheory.FOSG.History.playerViewFrom
            (G := (eventGraphFOSGView g).toBoundedFOSG horizon) who steps)
  | [] => by
      simp [GameTheory.FOSG.History.playerViewFrom,
        Machine.RoundView.BoundedHistory.playerViewFrom, fosgInfoToNative]
  | step :: steps => by
      simp [GameTheory.FOSG.History.playerViewFrom,
        Machine.RoundView.BoundedHistory.playerViewFrom,
        fosgStepToNative_playerView g horizon step who,
        fosgPlayerViewFromToNative g horizon who steps,
        fosgInfoToNative, List.map_append]

@[simp] theorem nativeHistoryToFOSG_playerView
    (g : WFProgram P L) (horizon : Nat)
    (h : (eventGraphRoundView g).BoundedHistory horizon) (who : P) :
    (nativeHistoryToFOSG g horizon h).playerView who =
      nativeInfoToFOSG g horizon who (h.playerView who) := by
  simpa [nativeHistoryToFOSG, Machine.RoundView.BoundedHistory.playerView,
    GameTheory.FOSG.History.playerView] using
    nativePlayerViewFromToFOSG g horizon who h.steps

@[simp] theorem fosgHistoryToNative_playerView
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History))
    (who : P) :
    (fosgHistoryToNative g horizon h).playerView who =
      fosgInfoToNative g horizon who (h.playerView who) := by
  simpa [fosgHistoryToNative, Machine.RoundView.BoundedHistory.playerView,
    GameTheory.FOSG.History.playerView] using
    fosgPlayerViewFromToNative g horizon who h.steps

noncomputable def nativeReachableInfoToFOSG
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (info : (eventGraphRoundView g).ReachableInfoState horizon who) :
    ((eventGraphFOSGView g).toBoundedFOSG horizon).ReachableInfoState who := by
  refine ⟨nativeInfoToFOSG g horizon who info.1, ?_⟩
  rcases info.2 with ⟨h, hinfo⟩
  refine ⟨nativeHistoryToFOSG g horizon h, ?_⟩
  simp [hinfo]

noncomputable def fosgReachableInfoToNative
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (info : ((eventGraphFOSGView g).toBoundedFOSG horizon).ReachableInfoState who) :
    (eventGraphRoundView g).ReachableInfoState horizon who := by
  refine ⟨fosgInfoToNative g horizon who info.1, ?_⟩
  rcases info.2 with ⟨h, hinfo⟩
  refine ⟨fosgHistoryToNative g horizon h, ?_⟩
  simp [hinfo]

@[simp] theorem nativeReachableInfoToFOSG_of_history
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (h : (eventGraphRoundView g).BoundedHistory horizon) :
    nativeReachableInfoToFOSG g horizon who
        ((eventGraphRoundView g).reachableInfoStateOfHistory horizon who h) =
      ((eventGraphFOSGView g).toBoundedFOSG horizon).reachableInfoStateOfHistory
        who (nativeHistoryToFOSG g horizon h) := by
  apply Subtype.ext
  simp [nativeReachableInfoToFOSG, Machine.RoundView.reachableInfoStateOfHistory,
    GameTheory.FOSG.reachableInfoStateOfHistory]

@[simp] theorem fosgReachableInfoToNative_of_history
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)) :
    fosgReachableInfoToNative g horizon who
        (((eventGraphFOSGView g).toBoundedFOSG horizon).reachableInfoStateOfHistory
          who h) =
      (eventGraphRoundView g).reachableInfoStateOfHistory horizon who
        (fosgHistoryToNative g horizon h) := by
  apply Subtype.ext
  simp [fosgReachableInfoToNative, Machine.RoundView.reachableInfoStateOfHistory,
    GameTheory.FOSG.reachableInfoStateOfHistory]

@[simp] theorem fosgReachableInfoToNative_nativeReachableInfoToFOSG
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (info : (eventGraphRoundView g).ReachableInfoState horizon who) :
    fosgReachableInfoToNative g horizon who
        (nativeReachableInfoToFOSG g horizon who info) = info := by
  apply Subtype.ext
  simp [nativeReachableInfoToFOSG, fosgReachableInfoToNative]

@[simp] theorem nativeReachableInfoToFOSG_fosgReachableInfoToNative
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (info : ((eventGraphFOSGView g).toBoundedFOSG horizon).ReachableInfoState who) :
    nativeReachableInfoToFOSG g horizon who
        (fosgReachableInfoToNative g horizon who info) = info := by
  apply Subtype.ext
  simp [nativeReachableInfoToFOSG, fosgReachableInfoToNative]

/-! ## Strategy transport -/

set_option linter.flexible false in
theorem availableMoves_nativeToFOSG
    (g : WFProgram P L) (horizon : Nat)
    (h : (eventGraphRoundView g).BoundedHistory horizon) (who : P) :
    ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMoves
        (nativeHistoryToFOSG g horizon h) who =
      (eventGraphRoundView g).boundedAvailableMoves horizon h who := by
  ext move
  change ((eventGraphFOSGView g).toBoundedFOSG horizon).locallyLegalAtState
      (nativeHistoryToFOSG g horizon h).lastState who move ↔
    (eventGraphRoundView g).boundedLocallyLegalAtState horizon h.lastState who move
  rw [nativeHistoryToFOSG_lastState]
  cases move with
  | none =>
      simp [Machine.RoundView.boundedLocallyLegalAtState,
        GameTheory.FOSG.locallyLegalAtState, eventGraphRoundView,
        eventGraphFOSGView, EventGraph.toRoundView, EventGraph.toFOSGView,
        Machine.RoundView.boundedActive, Machine.FOSGView.boundedActive]
  | some _action =>
      simp [Machine.RoundView.boundedLocallyLegalAtState,
        GameTheory.FOSG.locallyLegalAtState, eventGraphRoundView,
        eventGraphFOSGView, EventGraph.toRoundView, EventGraph.toFOSGView,
        Machine.RoundView.boundedActive, Machine.FOSGView.boundedActive,
        Machine.RoundView.boundedAvailableActions,
        Machine.FOSGView.boundedAvailableActions]
      intro _hactive
      rfl

theorem availableMoves_fosgToNative
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History))
    (who : P) :
    (eventGraphRoundView g).boundedAvailableMoves horizon
        (fosgHistoryToNative g horizon h) who =
      ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who := by
  have hEq :=
    availableMoves_nativeToFOSG g horizon
      (fosgHistoryToNative g horizon h) who
  simpa using hEq.symm

noncomputable def nativePureStrategyToFOSG
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (σ : (eventGraphRoundView g).BoundedPureStrategy horizon who) :
    (eventGraphFOSGView g).BoundedPureStrategy horizon who := by
  refine ⟨fun info =>
    σ.1 (fosgReachableInfoToNative g horizon who info), ?_⟩
  intro h
  have hσ := σ.2 (fosgHistoryToNative g horizon h)
  rw [← availableMoves_fosgToNative g horizon h who]
  simpa using hσ

noncomputable def fosgPureStrategyToNative
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (σ : (eventGraphFOSGView g).BoundedPureStrategy horizon who) :
    (eventGraphRoundView g).BoundedPureStrategy horizon who := by
  refine ⟨fun info =>
    σ.1 (nativeReachableInfoToFOSG g horizon who info), ?_⟩
  intro h
  have hσ := σ.2 (nativeHistoryToFOSG g horizon h)
  rw [← availableMoves_nativeToFOSG g horizon h who]
  simpa using hσ

noncomputable def nativeBehavioralStrategyToFOSG
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (σ : (eventGraphRoundView g).BoundedBehavioralStrategy horizon who) :
    (eventGraphFOSGView g).BoundedBehavioralStrategy horizon who := by
  refine ⟨fun info =>
    σ.1 (fosgReachableInfoToNative g horizon who info), ?_⟩
  intro h move hmove
  have hmove' :
      move ∈
        (σ.1 ((eventGraphRoundView g).reachableInfoStateOfHistory horizon who
          (fosgHistoryToNative g horizon h))).support := by
    simpa using hmove
  have hσ := σ.2 (fosgHistoryToNative g horizon h) hmove'
  rw [← availableMoves_fosgToNative g horizon h who]
  simpa using hσ

noncomputable def fosgBehavioralStrategyToNative
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (σ : (eventGraphFOSGView g).BoundedBehavioralStrategy horizon who) :
    (eventGraphRoundView g).BoundedBehavioralStrategy horizon who := by
  refine ⟨fun info =>
    σ.1 (nativeReachableInfoToFOSG g horizon who info), ?_⟩
  intro h move hmove
  have hmove' :
      move ∈
        (σ.1 (((eventGraphFOSGView g).toBoundedFOSG horizon).reachableInfoStateOfHistory
          who (nativeHistoryToFOSG g horizon h))).support := by
    simpa using hmove
  have hσ := σ.2 (nativeHistoryToFOSG g horizon h) hmove'
  rw [← availableMoves_nativeToFOSG g horizon h who]
  simpa using hσ

noncomputable def nativePureProfileToFOSG
    (g : WFProgram P L) (horizon : Nat)
    (π : (eventGraphRoundView g).BoundedPureProfile horizon) :
    (eventGraphFOSGView g).BoundedPureProfile horizon :=
  fun who => nativePureStrategyToFOSG g horizon who (π who)

noncomputable def fosgPureProfileToNative
    (g : WFProgram P L) (horizon : Nat)
    (π : (eventGraphFOSGView g).BoundedPureProfile horizon) :
    (eventGraphRoundView g).BoundedPureProfile horizon :=
  fun who => fosgPureStrategyToNative g horizon who (π who)

noncomputable def nativeBehavioralProfileToFOSG
    (g : WFProgram P L) (horizon : Nat)
    (β : (eventGraphRoundView g).BoundedBehavioralProfile horizon) :
    (eventGraphFOSGView g).BoundedBehavioralProfile horizon :=
  fun who => nativeBehavioralStrategyToFOSG g horizon who (β who)

noncomputable def fosgBehavioralProfileToNative
    (g : WFProgram P L) (horizon : Nat)
    (β : (eventGraphFOSGView g).BoundedBehavioralProfile horizon) :
    (eventGraphRoundView g).BoundedBehavioralProfile horizon :=
  fun who => fosgBehavioralStrategyToNative g horizon who (β who)

@[simp] theorem nativePureStrategyToFOSG_apply
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (σ : (eventGraphRoundView g).BoundedPureStrategy horizon who)
    (info : ((eventGraphFOSGView g).toBoundedFOSG horizon).ReachableInfoState who) :
    (nativePureStrategyToFOSG g horizon who σ).1 info =
      σ.1 (fosgReachableInfoToNative g horizon who info) := rfl

@[simp] theorem fosgPureStrategyToNative_apply
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (σ : (eventGraphFOSGView g).BoundedPureStrategy horizon who)
    (info : (eventGraphRoundView g).ReachableInfoState horizon who) :
    (fosgPureStrategyToNative g horizon who σ).1 info =
      σ.1 (nativeReachableInfoToFOSG g horizon who info) := rfl

@[simp] theorem nativeBehavioralStrategyToFOSG_apply
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (σ : (eventGraphRoundView g).BoundedBehavioralStrategy horizon who)
    (info : ((eventGraphFOSGView g).toBoundedFOSG horizon).ReachableInfoState who) :
    (nativeBehavioralStrategyToFOSG g horizon who σ).1 info =
      σ.1 (fosgReachableInfoToNative g horizon who info) := rfl

@[simp] theorem fosgBehavioralStrategyToNative_apply
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (σ : (eventGraphFOSGView g).BoundedBehavioralStrategy horizon who)
    (info : (eventGraphRoundView g).ReachableInfoState horizon who) :
    (fosgBehavioralStrategyToNative g horizon who σ).1 info =
      σ.1 (nativeReachableInfoToFOSG g horizon who info) := rfl

@[simp] theorem fosgPureStrategyToNative_nativePureStrategyToFOSG
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (σ : (eventGraphRoundView g).BoundedPureStrategy horizon who) :
    fosgPureStrategyToNative g horizon who
        (nativePureStrategyToFOSG g horizon who σ) = σ := by
  apply Subtype.ext
  funext info
  simp [nativePureStrategyToFOSG, fosgPureStrategyToNative]

@[simp] theorem nativePureStrategyToFOSG_fosgPureStrategyToNative
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (σ : (eventGraphFOSGView g).BoundedPureStrategy horizon who) :
    nativePureStrategyToFOSG g horizon who
        (fosgPureStrategyToNative g horizon who σ) = σ := by
  apply Subtype.ext
  funext info
  simp [nativePureStrategyToFOSG, fosgPureStrategyToNative]

@[simp] theorem fosgBehavioralStrategyToNative_nativeBehavioralStrategyToFOSG
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (σ : (eventGraphRoundView g).BoundedBehavioralStrategy horizon who) :
    fosgBehavioralStrategyToNative g horizon who
        (nativeBehavioralStrategyToFOSG g horizon who σ) = σ := by
  apply Subtype.ext
  funext info
  simp [nativeBehavioralStrategyToFOSG, fosgBehavioralStrategyToNative]

@[simp] theorem nativeBehavioralStrategyToFOSG_fosgBehavioralStrategyToNative
    (g : WFProgram P L) (horizon : Nat) (who : P)
    (σ : (eventGraphFOSGView g).BoundedBehavioralStrategy horizon who) :
    nativeBehavioralStrategyToFOSG g horizon who
        (fosgBehavioralStrategyToNative g horizon who σ) = σ := by
  apply Subtype.ext
  funext info
  simp [nativeBehavioralStrategyToFOSG, fosgBehavioralStrategyToNative]

noncomputable def pureStrategyEquiv
    (g : WFProgram P L) (horizon : Nat) (who : P) :
    (eventGraphRoundView g).BoundedPureStrategy horizon who ≃
      (eventGraphFOSGView g).BoundedPureStrategy horizon who where
  toFun := nativePureStrategyToFOSG g horizon who
  invFun := fosgPureStrategyToNative g horizon who
  left_inv := fosgPureStrategyToNative_nativePureStrategyToFOSG g horizon who
  right_inv := nativePureStrategyToFOSG_fosgPureStrategyToNative g horizon who

noncomputable def behavioralStrategyEquiv
    (g : WFProgram P L) (horizon : Nat) (who : P) :
    (eventGraphRoundView g).BoundedBehavioralStrategy horizon who ≃
      (eventGraphFOSGView g).BoundedBehavioralStrategy horizon who where
  toFun := nativeBehavioralStrategyToFOSG g horizon who
  invFun := fosgBehavioralStrategyToNative g horizon who
  left_inv := fosgBehavioralStrategyToNative_nativeBehavioralStrategyToFOSG g horizon who
  right_inv := nativeBehavioralStrategyToFOSG_fosgBehavioralStrategyToNative g horizon who

/-! ## Execution laws -/

theorem terminal_nativeToFOSG
    (g : WFProgram P L) (horizon : Nat)
    (h : (eventGraphRoundView g).BoundedHistory horizon) :
    ((eventGraphFOSGView g).toBoundedFOSG horizon).terminal
        (nativeHistoryToFOSG g horizon h).lastState ↔
      (eventGraphRoundView g).boundedTerminal horizon h.lastState := by
  change ((eventGraphMachine g).terminal
        (nativeHistoryToFOSG g horizon h).lastState.state ∨
      horizon ≤ (nativeHistoryToFOSG g horizon h).lastState.depth) ↔
    ((eventGraphMachine g).terminal h.lastState.state ∨
      horizon ≤ h.lastState.depth)
  simp [nativeHistoryToFOSG_lastState g horizon h]

theorem terminal_fosgToNative
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)) :
    (eventGraphRoundView g).boundedTerminal horizon
        (fosgHistoryToNative g horizon h).lastState ↔
      ((eventGraphFOSGView g).toBoundedFOSG horizon).terminal
        h.lastState := by
  change ((eventGraphMachine g).terminal
        (fosgHistoryToNative g horizon h).lastState.state ∨
      horizon ≤ (fosgHistoryToNative g horizon h).lastState.depth) ↔
    ((eventGraphMachine g).terminal h.lastState.state ∨
      horizon ≤ h.lastState.depth)
  simp [fosgHistoryToNative_lastState g horizon h]

theorem active_nativeToFOSG
    (g : WFProgram P L) (horizon : Nat)
    (h : (eventGraphRoundView g).BoundedHistory horizon) :
    ((eventGraphFOSGView g).toBoundedFOSG horizon).active
        (nativeHistoryToFOSG g horizon h).lastState =
      (eventGraphRoundView g).boundedActive horizon h.lastState := by
  change (if horizon ≤ (nativeHistoryToFOSG g horizon h).lastState.depth then
      ∅ else (programEventGraph g).roundActive
        (nativeHistoryToFOSG g horizon h).lastState.state) =
    (if horizon ≤ h.lastState.depth then ∅ else
      (programEventGraph g).roundActive h.lastState.state)
  simp [nativeHistoryToFOSG_lastState g horizon h]

theorem active_fosgToNative
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)) :
    (eventGraphRoundView g).boundedActive horizon
        (fosgHistoryToNative g horizon h).lastState =
      ((eventGraphFOSGView g).toBoundedFOSG horizon).active h.lastState := by
  change (if horizon ≤ (fosgHistoryToNative g horizon h).lastState.depth then
      ∅ else (programEventGraph g).roundActive
        (fosgHistoryToNative g horizon h).lastState.state) =
    (if horizon ≤ h.lastState.depth then ∅ else
      (programEventGraph g).roundActive h.lastState.state)
  simp [fosgHistoryToNative_lastState g horizon h]

theorem availableActions_nativeToFOSG
    (g : WFProgram P L) (horizon : Nat)
    (h : (eventGraphRoundView g).BoundedHistory horizon) (who : P) :
    ((eventGraphFOSGView g).toBoundedFOSG horizon).availableActions
        (nativeHistoryToFOSG g horizon h).lastState who =
      (eventGraphRoundView g).boundedAvailableActions horizon
        h.lastState who := by
  ext action
  change (action ∈
      (if horizon ≤ (nativeHistoryToFOSG g horizon h).lastState.depth then
        ∅ else (programEventGraph g).roundAvailable
          (nativeHistoryToFOSG g horizon h).lastState.state who)) ↔
    action ∈
      (if horizon ≤ h.lastState.depth then ∅ else
        (programEventGraph g).roundAvailable h.lastState.state who)
  rw [nativeHistoryToFOSG_lastState g horizon h]
  exact Iff.rfl

theorem availableActions_fosgToNative
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History))
    (who : P) :
    (eventGraphRoundView g).boundedAvailableActions horizon
        (fosgHistoryToNative g horizon h).lastState who =
      ((eventGraphFOSGView g).toBoundedFOSG horizon).availableActions
        h.lastState who := by
  ext action
  change (action ∈
      (if horizon ≤ (fosgHistoryToNative g horizon h).lastState.depth then
        ∅ else (programEventGraph g).roundAvailable
          (fosgHistoryToNative g horizon h).lastState.state who)) ↔
    action ∈
      (if horizon ≤ h.lastState.depth then ∅ else
        (programEventGraph g).roundAvailable h.lastState.state who)
  rw [fosgHistoryToNative_lastState g horizon h]
  exact Iff.rfl

noncomputable def nativeLegalActionToFOSG
    (g : WFProgram P L) (horizon : Nat)
    (h : (eventGraphRoundView g).BoundedHistory horizon)
    (a : (eventGraphRoundView g).BoundedLegalAction horizon h.lastState) :
    (((eventGraphFOSGView g).toBoundedFOSG horizon).LegalAction
      (nativeHistoryToFOSG g horizon h).lastState) := by
  refine ⟨a.1, ?_⟩
  rcases a.2 with ⟨hterm, hlocal⟩
  refine ⟨?_, ?_⟩
  · intro ht
    exact hterm ((terminal_nativeToFOSG g horizon h).1 ht)
  · intro who
    have hloc := hlocal who
    cases hmove : a.1 who with
    | none =>
        have hnot :
            who ∉ (eventGraphRoundView g).boundedActive horizon
              h.lastState := by
          simpa [Machine.RoundView.boundedLocallyLegalAtState, hmove]
            using hloc
        simpa [GameTheory.FOSG.locallyLegalAtState, hmove,
          active_nativeToFOSG g horizon h] using hnot
    | some choice =>
        have hpair :
            who ∈ (eventGraphRoundView g).boundedActive horizon h.lastState ∧
              choice ∈
                (eventGraphRoundView g).boundedAvailableActions horizon
                  h.lastState who := by
          simpa [Machine.RoundView.boundedLocallyLegalAtState, hmove]
            using hloc
        simpa [GameTheory.FOSG.locallyLegalAtState, hmove,
          active_nativeToFOSG g horizon h,
          availableActions_nativeToFOSG g horizon h who] using hpair

noncomputable def fosgLegalActionToNative
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History))
    (a : (((eventGraphFOSGView g).toBoundedFOSG horizon).LegalAction
      h.lastState)) :
    (eventGraphRoundView g).BoundedLegalAction horizon
      (fosgHistoryToNative g horizon h).lastState := by
  refine ⟨a.1, ?_⟩
  rcases a.2 with ⟨hterm, hlocal⟩
  refine ⟨?_, ?_⟩
  · intro ht
    exact hterm ((terminal_fosgToNative g horizon h).1 ht)
  · intro who
    have hloc := hlocal who
    cases hmove : a.1 who with
    | none =>
        have hnot :
            who ∉ ((eventGraphFOSGView g).toBoundedFOSG horizon).active
              h.lastState := by
          simpa [GameTheory.FOSG.locallyLegalAtState, hmove] using hloc
        simpa [Machine.RoundView.boundedLocallyLegalAtState, hmove,
          active_fosgToNative g horizon h] using hnot
    | some choice =>
        have hpair :
            who ∈ ((eventGraphFOSGView g).toBoundedFOSG horizon).active
                h.lastState ∧
              choice ∈
                ((eventGraphFOSGView g).toBoundedFOSG horizon).availableActions
                  h.lastState who := by
          simpa [GameTheory.FOSG.locallyLegalAtState, hmove] using hloc
        simpa [Machine.RoundView.boundedLocallyLegalAtState, hmove,
          active_fosgToNative g horizon h,
          availableActions_fosgToNative g horizon h who] using hpair

noncomputable def nativeLegalActionToFOSGOfFOSGHistory
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History))
    (a : (eventGraphRoundView g).BoundedLegalAction horizon
      (fosgHistoryToNative g horizon h).lastState) :
    (((eventGraphFOSGView g).toBoundedFOSG horizon).LegalAction
      h.lastState) := by
  refine ⟨a.1, ?_⟩
  rcases a.2 with ⟨hterm, hlocal⟩
  refine ⟨?_, ?_⟩
  · intro ht
    exact hterm ((terminal_fosgToNative g horizon h).2 ht)
  · intro who
    have hloc := hlocal who
    cases hmove : a.1 who with
    | none =>
        have hnot :
            who ∉ (eventGraphRoundView g).boundedActive horizon
              (fosgHistoryToNative g horizon h).lastState := by
          simpa [Machine.RoundView.boundedLocallyLegalAtState, hmove]
            using hloc
        simpa [GameTheory.FOSG.locallyLegalAtState, hmove,
          active_fosgToNative g horizon h] using hnot
    | some choice =>
        have hpair :
            who ∈ (eventGraphRoundView g).boundedActive horizon
                (fosgHistoryToNative g horizon h).lastState ∧
              choice ∈
                (eventGraphRoundView g).boundedAvailableActions horizon
                  (fosgHistoryToNative g horizon h).lastState who := by
          simpa [Machine.RoundView.boundedLocallyLegalAtState, hmove]
            using hloc
        simpa [GameTheory.FOSG.locallyLegalAtState, hmove,
          active_fosgToNative g horizon h,
          availableActions_fosgToNative g horizon h who] using hpair

noncomputable def fosgLegalActionToNativeOfNativeHistory
    (g : WFProgram P L) (horizon : Nat)
    (h : (eventGraphRoundView g).BoundedHistory horizon)
    (a : (((eventGraphFOSGView g).toBoundedFOSG horizon).LegalAction
      (nativeHistoryToFOSG g horizon h).lastState)) :
    (eventGraphRoundView g).BoundedLegalAction horizon h.lastState := by
  refine ⟨a.1, ?_⟩
  rcases a.2 with ⟨hterm, hlocal⟩
  refine ⟨?_, ?_⟩
  · intro ht
    exact hterm ((terminal_nativeToFOSG g horizon h).2 ht)
  · intro who
    have hloc := hlocal who
    cases hmove : a.1 who with
    | none =>
        have hnot :
            who ∉ ((eventGraphFOSGView g).toBoundedFOSG horizon).active
              (nativeHistoryToFOSG g horizon h).lastState := by
          simpa [GameTheory.FOSG.locallyLegalAtState, hmove] using hloc
        simpa [Machine.RoundView.boundedLocallyLegalAtState, hmove,
          active_nativeToFOSG g horizon h] using hnot
    | some choice =>
        have hpair :
            who ∈ ((eventGraphFOSGView g).toBoundedFOSG horizon).active
                (nativeHistoryToFOSG g horizon h).lastState ∧
              choice ∈
                ((eventGraphFOSGView g).toBoundedFOSG horizon).availableActions
                  (nativeHistoryToFOSG g horizon h).lastState who := by
          simpa [GameTheory.FOSG.locallyLegalAtState, hmove] using hloc
        simpa [Machine.RoundView.boundedLocallyLegalAtState, hmove,
          active_nativeToFOSG g horizon h,
          availableActions_nativeToFOSG g horizon h who] using hpair

@[simp] theorem nativeLegalActionToFOSG_inverse_at_nativeHistory
    (g : WFProgram P L) (horizon : Nat)
    (h : (eventGraphRoundView g).BoundedHistory horizon)
    (a : (((eventGraphFOSGView g).toBoundedFOSG horizon).LegalAction
      (nativeHistoryToFOSG g horizon h).lastState)) :
    nativeLegalActionToFOSG g horizon h
        (fosgLegalActionToNativeOfNativeHistory g horizon h a) = a := by
  apply Subtype.ext
  rfl

@[simp] theorem fosgLegalActionToNativeOfNativeHistory_inverse
    (g : WFProgram P L) (horizon : Nat)
    (h : (eventGraphRoundView g).BoundedHistory horizon)
    (a : (eventGraphRoundView g).BoundedLegalAction horizon h.lastState) :
    fosgLegalActionToNativeOfNativeHistory g horizon h
        (nativeLegalActionToFOSG g horizon h a) = a := by
  apply Subtype.ext
  rfl

@[simp] theorem nativeLegalActionToFOSGOfFOSGHistory_inverse
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History))
    (a : (((eventGraphFOSGView g).toBoundedFOSG horizon).LegalAction
      h.lastState)) :
    nativeLegalActionToFOSGOfFOSGHistory g horizon h
        (fosgLegalActionToNative g horizon h a) = a := by
  apply Subtype.ext
  rfl

@[simp] theorem fosgLegalActionToNative_inverse
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History))
    (a : (eventGraphRoundView g).BoundedLegalAction horizon
      (fosgHistoryToNative g horizon h).lastState) :
    fosgLegalActionToNative g horizon h
        (nativeLegalActionToFOSGOfFOSGHistory g horizon h a) = a := by
  apply Subtype.ext
  rfl

theorem jointActionDist_nativeToFOSG
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (β : (eventGraphRoundView g).BoundedBehavioralProfile horizon)
    (h : (eventGraphRoundView g).BoundedHistory horizon)
    (a : JointAction (eventGraphRoundView g).Act) :
    ((eventGraphFOSGView g).toBoundedFOSG horizon).jointActionDist
        (nativeBehavioralProfileToFOSG g horizon β).extend
        (nativeHistoryToFOSG g horizon h) a =
      (eventGraphRoundView g).jointActionDist horizon β h a := by
  classical
  rw [Machine.RoundView.jointActionDist_apply]
  rw [GameTheory.FOSG.jointActionDist_apply]
  apply Finset.prod_congr rfl
  intro who _
  change (((nativeBehavioralProfileToFOSG g horizon β who).1).extend
      ((nativeHistoryToFOSG g horizon h).playerView who)) (a who) =
    ((β who).1 ((eventGraphRoundView g).reachableInfoStateOfHistory horizon who h)) (a who)
  rw [GameTheory.FOSG.ReachableBehavioralStrategy.extend_apply_history]
  change ((β who).1 (fosgReachableInfoToNative g horizon who
      (((eventGraphFOSGView g).toBoundedFOSG horizon).reachableInfoStateOfHistory
        who (nativeHistoryToFOSG g horizon h)))) (a who) =
    ((β who).1 ((eventGraphRoundView g).reachableInfoStateOfHistory horizon who h)) (a who)
  rw [← nativeReachableInfoToFOSG_of_history g horizon who h]
  simp

theorem jointActionDist_fosgToNative
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (β : (eventGraphFOSGView g).BoundedBehavioralProfile horizon)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History))
    (a : JointAction (eventGraphRoundView g).Act) :
    (eventGraphRoundView g).jointActionDist horizon
        (fosgBehavioralProfileToNative g horizon β)
        (fosgHistoryToNative g horizon h) a =
      ((eventGraphFOSGView g).toBoundedFOSG horizon).jointActionDist
        β.extend h a := by
  classical
  rw [Machine.RoundView.jointActionDist_apply]
  rw [GameTheory.FOSG.jointActionDist_apply]
  apply Finset.prod_congr rfl
  intro who _
  change ((β who).1 (nativeReachableInfoToFOSG g horizon who
        ((eventGraphRoundView g).reachableInfoStateOfHistory horizon who
          (fosgHistoryToNative g horizon h)))) (a who) =
    ((β.extend who).1 (h.playerView who)) (a who)
  rw [← fosgReachableInfoToNative_of_history g horizon who h]
  simp [GameTheory.FOSG.ReachableLegalBehavioralProfile.extend]

theorem legalActionLaw_nativeToFOSG
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (β : (eventGraphRoundView g).BoundedBehavioralProfile horizon)
    (h : (eventGraphRoundView g).BoundedHistory horizon)
    (hterm :
      ¬ (eventGraphRoundView g).boundedTerminal horizon h.lastState) :
    PMF.map (nativeLegalActionToFOSG g horizon h)
        ((eventGraphRoundView g).legalActionLaw horizon β h hterm) =
      ((eventGraphFOSGView g).toBoundedFOSG horizon).legalActionLaw
        (nativeBehavioralProfileToFOSG g horizon β).extend
        (nativeHistoryToFOSG g horizon h)
        (by simpa using hterm) := by
  classical
  apply PMF.ext
  intro a
  rw [PMF.map_apply]
  rw [tsum_fintype]
  trans (eventGraphRoundView g).legalActionLaw horizon β h hterm
        (fosgLegalActionToNativeOfNativeHistory g horizon h a)
  · rw [Fintype.sum_eq_single
      (fosgLegalActionToNativeOfNativeHistory g horizon h a)]
    · have hinv :
          a = nativeLegalActionToFOSG g horizon h
            (fosgLegalActionToNativeOfNativeHistory g horizon h a) :=
        (nativeLegalActionToFOSG_inverse_at_nativeHistory
          g horizon h a).symm
      rw [hinv]
      simp
    · intro b hb
      by_cases heq : a = nativeLegalActionToFOSG g horizon h b
      · exfalso
        apply hb
        apply Subtype.ext
        exact (congrArg Subtype.val heq).symm
      · rw [if_neg heq]
  · rw [Machine.RoundView.legalActionLaw_apply]
    rw [GameTheory.FOSG.legalActionLaw_apply]
    exact (jointActionDist_nativeToFOSG g horizon β h a.1).symm

theorem legalActionLaw_fosgToNative
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (β : (eventGraphFOSGView g).BoundedBehavioralProfile horizon)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History))
    (hterm :
      ¬ ((eventGraphFOSGView g).toBoundedFOSG horizon).terminal h.lastState) :
    PMF.map (fosgLegalActionToNative g horizon h)
        (((eventGraphFOSGView g).toBoundedFOSG horizon).legalActionLaw
          β.extend h hterm) =
      (eventGraphRoundView g).legalActionLaw horizon
        (fosgBehavioralProfileToNative g horizon β)
        (fosgHistoryToNative g horizon h)
        (by
          intro ht
          exact hterm ((terminal_fosgToNative g horizon h).1 ht)) := by
  classical
  apply PMF.ext
  intro a
  rw [PMF.map_apply]
  rw [tsum_fintype]
  trans ((eventGraphFOSGView g).toBoundedFOSG horizon).legalActionLaw
        β.extend h hterm
        (nativeLegalActionToFOSGOfFOSGHistory g horizon h a)
  · rw [Fintype.sum_eq_single
      (nativeLegalActionToFOSGOfFOSGHistory g horizon h a)]
    · have hinv :
          a = fosgLegalActionToNative g horizon h
            (nativeLegalActionToFOSGOfFOSGHistory g horizon h a) := by
        exact (fosgLegalActionToNative_inverse g horizon h a).symm
      rw [hinv]
      simp
    · intro b hb
      by_cases heq : a = fosgLegalActionToNative g horizon h b
      · exfalso
        apply hb
        apply Subtype.ext
        exact (congrArg Subtype.val heq).symm
      · rw [if_neg heq]
  · rw [GameTheory.FOSG.legalActionLaw_apply]
    rw [Machine.RoundView.legalActionLaw_apply]
    exact (jointActionDist_fosgToNative g horizon β h a.1).symm

theorem boundedTransition_nativeToFOSG
    (g : WFProgram P L) (horizon : Nat)
    (h : (eventGraphRoundView g).BoundedHistory horizon)
    (a : (eventGraphRoundView g).BoundedLegalAction horizon h.lastState) :
    ((eventGraphFOSGView g).toBoundedFOSG horizon).transition
        (nativeHistoryToFOSG g horizon h).lastState
        (nativeLegalActionToFOSG g horizon h a) =
      (eventGraphRoundView g).boundedTransition horizon h.lastState a := by
  rw [Machine.FOSGView.toBoundedFOSG_transition,
    Machine.RoundView.boundedTransition]
  have hsucc :
      (fun next =>
          (nativeHistoryToFOSG g horizon h).lastState.succ
            (Nat.lt_of_not_ge
              (fun hle =>
                (nativeLegalActionToFOSG g horizon h a).2.1
                  (Or.inr hle)))
            next) =
        (fun next =>
          h.lastState.succ
            (Nat.lt_of_not_ge
              (fun hle => a.2.1 (Or.inr hle)))
            next) := by
    funext next
    apply Machine.BoundedState.ext <;>
      simp [nativeHistoryToFOSG_lastState g horizon h]
  have hraw :
      (eventGraphFOSGView g).transition
          (nativeHistoryToFOSG g horizon h).lastState.state
          ((eventGraphFOSGView g).boundedActionToAction horizon
            (nativeHistoryToFOSG g horizon h).lastState
            (nativeLegalActionToFOSG g horizon h a)) =
        (eventGraphRoundView g).transition h.lastState.state
          ((eventGraphRoundView g).boundedActionToAction horizon
            h.lastState a) := by
    change
      (programEventGraph g).roundTransition
          (nativeHistoryToFOSG g horizon h).lastState.state
          (nativeLegalActionToFOSG g horizon h a).1 =
      (programEventGraph g).roundTransition h.lastState.state a.1
    simp [nativeLegalActionToFOSG, nativeHistoryToFOSG_lastState g horizon h]
  rw [hsucc, hraw]

theorem nativeHistoryToFOSG_snoc
    (g : WFProgram P L) (horizon : Nat)
    (h : (eventGraphRoundView g).BoundedHistory horizon)
    (a : (eventGraphRoundView g).BoundedLegalAction horizon h.lastState)
    (dst : (eventGraphMachine g).BoundedState horizon)
    (hsupp :
      (eventGraphRoundView g).boundedTransition horizon h.lastState a dst ≠ 0) :
    nativeHistoryToFOSG g horizon (h.snoc a dst hsupp) =
      (nativeHistoryToFOSG g horizon h).snoc
        (nativeLegalActionToFOSG g horizon h a) dst
        (by
          rw [boundedTransition_nativeToFOSG g horizon h a]
          exact hsupp) := by
  apply GameTheory.FOSG.History.ext
  simp [nativeHistoryToFOSG, Machine.RoundView.BoundedHistory.snoc,
    GameTheory.FOSG.History.snoc, nativeStepToFOSG,
    nativeLegalActionToFOSG]
  constructor
  · exact (nativeHistoryToFOSG_lastState g horizon h).symm
  · apply (Subtype.heq_iff_coe_eq ?_).2
    · rfl
    · intro joint
      constructor
      · intro hlegal
        exact (nativeLegalActionToFOSG g horizon h ⟨joint, hlegal⟩).2
      · intro hlegal
        exact (fosgLegalActionToNativeOfNativeHistory g horizon h
          ⟨joint, hlegal⟩).2

theorem nativeHistoryToFOSG_extendByOutcome
    (g : WFProgram P L) (horizon : Nat)
    (h : (eventGraphRoundView g).BoundedHistory horizon)
    (a : (eventGraphRoundView g).BoundedLegalAction horizon h.lastState)
    (dst : (eventGraphMachine g).BoundedState horizon) :
    nativeHistoryToFOSG g horizon
        (h.extendByOutcome a dst) =
      (nativeHistoryToFOSG g horizon h).extendByOutcome
        (nativeLegalActionToFOSG g horizon h a) dst := by
  by_cases hsupp :
      (eventGraphRoundView g).boundedTransition horizon h.lastState a dst = 0
  · have hzero :
        ((eventGraphFOSGView g).toBoundedFOSG horizon).transition
            (nativeHistoryToFOSG g horizon h).lastState
            (nativeLegalActionToFOSG g horizon h a) dst = 0 := by
      rw [boundedTransition_nativeToFOSG g horizon h a]
      exact hsupp
    rw [GameTheory.FOSG.History.extendByOutcome_of_no_support
      (h := nativeHistoryToFOSG g horizon h)
      (a := nativeLegalActionToFOSG g horizon h a)
      (dst := dst) hzero]
    simp [Machine.RoundView.BoundedHistory.extendByOutcome, hsupp]
  · have hsuppF :
        ((eventGraphFOSGView g).toBoundedFOSG horizon).transition
            (nativeHistoryToFOSG g horizon h).lastState
            (nativeLegalActionToFOSG g horizon h a) dst ≠ 0 := by
      rw [boundedTransition_nativeToFOSG g horizon h a]
      exact hsupp
    rw [GameTheory.FOSG.History.extendByOutcome_of_support
      (h := nativeHistoryToFOSG g horizon h)
      (a := nativeLegalActionToFOSG g horizon h a)
      (dst := dst) hsuppF]
    simp [Machine.RoundView.BoundedHistory.extendByOutcome, hsupp]
    exact nativeHistoryToFOSG_snoc g horizon h a dst hsupp

/-! ## Execution laws -/

theorem runDistFrom_nativeToFOSG
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (β : (eventGraphRoundView g).BoundedBehavioralProfile horizon) :
    ∀ (n : Nat) (h : (eventGraphRoundView g).BoundedHistory horizon),
      PMF.map (nativeHistoryToFOSG g horizon)
        (Machine.RoundView.BoundedHistory.runDistFrom
          (view := eventGraphRoundView g) (horizon := horizon) β n h) =
        GameTheory.FOSG.History.runDistFrom
          ((eventGraphFOSGView g).toBoundedFOSG horizon)
          (nativeBehavioralProfileToFOSG g horizon β).extend n
          (nativeHistoryToFOSG g horizon h)
  | 0, h => by
      rw [Machine.RoundView.BoundedHistory.runDistFrom_zero]
      rw [GameTheory.FOSG.History.runDistFrom_zero]
      rw [PMF.pure_map]
  | n + 1, h => by
      let BFOSG := (eventGraphFOSGView g).toBoundedFOSG horizon
      by_cases hterm :
          (eventGraphRoundView g).boundedTerminal horizon h.lastState
      · have htermF : BFOSG.terminal (nativeHistoryToFOSG g horizon h).lastState :=
          (terminal_nativeToFOSG g horizon h).2 hterm
        rw [Machine.RoundView.BoundedHistory.runDistFrom_succ_terminal
          (view := eventGraphRoundView g) (horizon := horizon) β n h hterm]
        rw [GameTheory.FOSG.History.runDistFrom_succ_terminal
          (G := BFOSG) (nativeBehavioralProfileToFOSG g horizon β).extend
          n (nativeHistoryToFOSG g horizon h) htermF]
        rw [PMF.pure_map]
      · have htermF :
            ¬ BFOSG.terminal (nativeHistoryToFOSG g horizon h).lastState := by
          intro ht
          exact hterm ((terminal_nativeToFOSG g horizon h).1 ht)
        rw [Machine.RoundView.BoundedHistory.runDistFrom_succ_nonterminal
          (view := eventGraphRoundView g) (horizon := horizon) β n h hterm]
        rw [GameTheory.FOSG.History.runDistFrom_succ_nonterminal
          (G := BFOSG) (nativeBehavioralProfileToFOSG g horizon β).extend
          n (nativeHistoryToFOSG g horizon h) htermF]
        rw [PMF.map_bind]
        conv_lhs =>
          arg 2
          intro action
          rw [PMF.map_bind]
          arg 2
          intro dst
          rw [runDistFrom_nativeToFOSG g horizon β n
            (h.extendByOutcome action dst)]
          rw [nativeHistoryToFOSG_extendByOutcome g horizon h action dst]
        rw [← legalActionLaw_nativeToFOSG g horizon β h hterm]
        rw [PMF.bind_map]
        congr
        funext action
        simp only [Function.comp_apply, BFOSG]
        rw [boundedTransition_nativeToFOSG g horizon h action]

theorem runDist_nativeToFOSG
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (β : (eventGraphRoundView g).BoundedBehavioralProfile horizon)
    (steps : Nat) :
    PMF.map (nativeHistoryToFOSG g horizon)
        ((eventGraphRoundView g).runDist horizon steps β) =
      ((eventGraphFOSGView g).toBoundedFOSG horizon).runDist steps
        (nativeBehavioralProfileToFOSG g horizon β).extend := by
  simpa [Machine.RoundView.runDist, GameTheory.FOSG.runDist,
    Machine.RoundView.BoundedHistory.nil, GameTheory.FOSG.History.nil,
    nativeHistoryToFOSG] using
    runDistFrom_nativeToFOSG g horizon β steps
      (Machine.RoundView.BoundedHistory.nil (eventGraphRoundView g) horizon)

@[simp] theorem boundedHistoryOutcome_nativeHistoryToFOSG
    (g : WFProgram P L) (horizon : Nat)
    (h : (eventGraphRoundView g).BoundedHistory horizon) :
    (eventGraphFOSGView g).boundedHistoryOutcome horizon
        (nativeHistoryToFOSG g horizon h) =
      (eventGraphMachine g).outcome h.lastState.state := by
  simp [Machine.FOSGView.boundedHistoryOutcome]

theorem boundedOutcomeFromBehavioral_nativeToFOSG
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (β : (eventGraphRoundView g).BoundedBehavioralProfile horizon)
    (steps : Nat) :
    (eventGraphFOSGView g).boundedOutcomeFromBehavioral horizon
        (nativeBehavioralProfileToFOSG g horizon β) steps =
      (eventGraphRoundView g).boundedOutcomeFromBehavioral horizon β steps := by
  let nativeRun :=
    (eventGraphRoundView g).runDist horizon steps β
  let observeNative :
      (eventGraphRoundView g).BoundedHistory horizon →
        (eventGraphMachine g).Outcome :=
    fun h => (eventGraphMachine g).outcome h.lastState.state
  calc
    (eventGraphFOSGView g).boundedOutcomeFromBehavioral horizon
        (nativeBehavioralProfileToFOSG g horizon β) steps =
      PMF.map ((eventGraphFOSGView g).boundedHistoryOutcome horizon)
        (((eventGraphFOSGView g).toBoundedFOSG horizon).runDist steps
          (nativeBehavioralProfileToFOSG g horizon β).extend) := by
          rfl
    _ = PMF.map ((eventGraphFOSGView g).boundedHistoryOutcome horizon)
        (PMF.map (nativeHistoryToFOSG g horizon) nativeRun) := by
          rw [← runDist_nativeToFOSG g horizon β steps]
    _ = PMF.map observeNative nativeRun := by
          rw [PMF.map_comp]
          have hobs :
              ((eventGraphFOSGView g).boundedHistoryOutcome horizon ∘
                  nativeHistoryToFOSG g horizon) = observeNative := by
            funext h
            simp [observeNative]
          rw [hobs]
    _ = (eventGraphRoundView g).boundedOutcomeFromBehavioral horizon β steps := by
          rw [Machine.RoundView.boundedOutcomeFromBehavioral,
            Machine.RoundView.boundedBlockTraceFromBehavioral]
          rw [PMF.map_comp]
          have hobs :
              ((fun trace : (eventGraphMachine g).BlockTrace =>
                  (eventGraphMachine g).outcome trace.2) ∘
                (eventGraphRoundView g).boundedHistoryTrace horizon) =
                (fun h : (eventGraphRoundView g).BoundedHistory horizon =>
                  (eventGraphMachine g).outcome h.lastState.state) := by
            funext h
            rfl
          rw [hobs]

theorem legalPureToBehavioral_nativeToFOSG_agree
    (g : WFProgram P L) (horizon : Nat)
    (π : (eventGraphRoundView g).BoundedPureProfile horizon)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History))
    (who : P) :
    ((nativeBehavioralProfileToFOSG g horizon
          ((eventGraphRoundView g).legalPureToBehavioral horizon π)).extend).toProfile
        who (h.playerView who) =
      (((eventGraphFOSGView g).toBoundedFOSG horizon).legalPureToBehavioral
          (nativePureProfileToFOSG g horizon π).extend).toProfile
        who (h.playerView who) := by
  change
    ((nativeBehavioralProfileToFOSG g horizon
          ((eventGraphRoundView g).legalPureToBehavioral horizon π) who).1).extend
        (h.playerView who) =
      PMF.pure (((nativePureProfileToFOSG g horizon π who).1).extend
        (h.playerView who))
  rw [GameTheory.FOSG.ReachableBehavioralStrategy.extend_apply_history]
  rw [GameTheory.FOSG.ReachablePureStrategy.extend_apply_history]
  simp [nativeBehavioralProfileToFOSG, nativeBehavioralStrategyToFOSG,
    Machine.RoundView.legalPureToBehavioral, Machine.RoundView.pureToBehavioral,
    Machine.RoundView.BoundedPureProfile.toProfile,
    nativePureProfileToFOSG, nativePureStrategyToFOSG]
  rfl

theorem boundedOutcomeFromPure_nativeToFOSG
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (π : (eventGraphRoundView g).BoundedPureProfile horizon)
    (steps : Nat) :
    (eventGraphFOSGView g).boundedOutcomeFromPure horizon
        (nativePureProfileToFOSG g horizon π) steps =
      (eventGraphRoundView g).boundedOutcomeFromPure horizon π steps := by
  let βN := (eventGraphRoundView g).legalPureToBehavioral horizon π
  let βF := nativeBehavioralProfileToFOSG g horizon βN
  let σF :=
    ((eventGraphFOSGView g).toBoundedFOSG horizon).legalPureToBehavioral
      (nativePureProfileToFOSG g horizon π).extend
  have hrun :
      ((eventGraphFOSGView g).toBoundedFOSG horizon).runDist steps σF =
        ((eventGraphFOSGView g).toBoundedFOSG horizon).runDist steps βF.extend := by
    apply GameTheory.FOSG.runDist_congr
    intro h who
    exact (legalPureToBehavioral_nativeToFOSG_agree g horizon π h who).symm
  calc
    (eventGraphFOSGView g).boundedOutcomeFromPure horizon
        (nativePureProfileToFOSG g horizon π) steps =
      PMF.map ((eventGraphFOSGView g).boundedHistoryOutcome horizon)
        (((eventGraphFOSGView g).toBoundedFOSG horizon).runDist steps σF) := by
          rfl
    _ = (eventGraphFOSGView g).boundedOutcomeFromBehavioral horizon βF steps := by
          rw [hrun]
          rfl
    _ = (eventGraphRoundView g).boundedOutcomeFromBehavioral horizon βN steps :=
          boundedOutcomeFromBehavioral_nativeToFOSG g horizon βN steps
    _ = (eventGraphRoundView g).boundedOutcomeFromPure horizon π steps := by
          rfl

end NativeFOSG

end Vegas
