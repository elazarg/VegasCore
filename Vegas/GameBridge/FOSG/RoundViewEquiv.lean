import Vegas.GameBridge.FOSG.FromRoundView

/-!
# Round-view/FOSG equivalence

The FOSG presentation of a `Machine.RoundView` uses the same bounded states,
legal joint actions, and transition kernels as the native round view.  This
file records the proof-facing translations between the two history and
strategy surfaces.
-/

namespace Vegas

open GameTheory

namespace Machine
namespace RoundView

variable {Player : Type} [DecidableEq Player]
variable {M : Machine Player}

namespace ToFOSG

variable (view : M.RoundView) (horizon : Nat) (cutoff : Payoff Player)

/-! ## Steps and histories -/

/-- Repackage one native bounded step as a FOSG step. -/
noncomputable def stepOfBoundedStep
    (step : view.BoundedStep horizon) :
    (view.toFOSG horizon cutoff).Step := by
  refine ⟨step.src, step.act, step.dst, ?_⟩
  simpa [toFOSG] using step.support

/-- Repackage one FOSG step as a native bounded step. -/
noncomputable def boundedStepOfStep
    (step : (view.toFOSG horizon cutoff).Step) :
    view.BoundedStep horizon := by
  refine ⟨step.src, step.act, step.dst, ?_⟩
  simpa [toFOSG] using step.support

@[simp] theorem boundedStepOfStep_stepOfBoundedStep
    (step : view.BoundedStep horizon) :
    boundedStepOfStep view horizon cutoff
        (stepOfBoundedStep view horizon cutoff step) = step := by
  cases step
  simp [stepOfBoundedStep, boundedStepOfStep]

@[simp] theorem stepOfBoundedStep_boundedStepOfStep
    (step : (view.toFOSG horizon cutoff).Step) :
    stepOfBoundedStep view horizon cutoff
        (boundedStepOfStep view horizon cutoff step) = step := by
  cases step
  simp [stepOfBoundedStep, boundedStepOfStep]

@[simp] theorem stepOfBoundedStep_src
    (step : view.BoundedStep horizon) :
    (stepOfBoundedStep view horizon cutoff step).src = step.src := rfl

@[simp] theorem stepOfBoundedStep_dst
    (step : view.BoundedStep horizon) :
    (stepOfBoundedStep view horizon cutoff step).dst = step.dst := rfl

theorem stepChainOfBoundedStepChain :
    ∀ {start : M.BoundedState horizon}
      {steps : List (view.BoundedStep horizon)},
      view.StepChainFrom horizon start steps →
      (view.toFOSG horizon cutoff).StepChainFrom start
        (steps.map (stepOfBoundedStep view horizon cutoff))
  | _start, [], _hchain => by
      trivial
  | _start, _step :: _steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      exact
        ⟨by simpa using hsrc,
          stepChainOfBoundedStepChain htail⟩

theorem boundedStepChainOfStepChain :
    ∀ {start : M.BoundedState horizon}
      {steps : List ((view.toFOSG horizon cutoff).Step)},
      (view.toFOSG horizon cutoff).StepChainFrom start steps →
      view.StepChainFrom horizon start
        (steps.map (boundedStepOfStep view horizon cutoff))
  | _start, [], _hchain => by
      trivial
  | _start, _step :: _steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      exact
        ⟨by simpa using hsrc,
          boundedStepChainOfStepChain htail⟩

theorem lastStateFrom_map_stepOfBoundedStep :
    ∀ {start : M.BoundedState horizon}
      (steps : List (view.BoundedStep horizon)),
      (view.toFOSG horizon cutoff).lastStateFrom start
          (steps.map (stepOfBoundedStep view horizon cutoff)) =
        view.lastStateFrom horizon start steps
  | _start, [] => by
      simp [FOSG.lastStateFrom, lastStateFrom]
  | _start, step :: steps => by
      simpa [FOSG.lastStateFrom, lastStateFrom, stepOfBoundedStep] using
        lastStateFrom_map_stepOfBoundedStep (start := step.dst) steps

theorem lastStateFrom_map_boundedStepOfStep :
    ∀ {start : M.BoundedState horizon}
      (steps : List ((view.toFOSG horizon cutoff).Step)),
      view.lastStateFrom horizon start
          (steps.map (boundedStepOfStep view horizon cutoff)) =
        (view.toFOSG horizon cutoff).lastStateFrom start steps
  | _start, [] => by
      simp [FOSG.lastStateFrom, lastStateFrom]
  | _start, step :: steps => by
      simpa [FOSG.lastStateFrom, lastStateFrom, boundedStepOfStep] using
        lastStateFrom_map_boundedStepOfStep (start := step.dst) steps

/-- Translate a native bounded history to the FOSG history surface. -/
noncomputable def historyOfBoundedHistory
    (h : view.BoundedHistory horizon) :
    (view.toFOSG horizon cutoff).History where
  steps := h.steps.map (stepOfBoundedStep view horizon cutoff)
  chain := by
    exact stepChainOfBoundedStepChain view horizon cutoff h.chain

/-- Translate a FOSG history back to the native bounded-history surface. -/
noncomputable def boundedHistoryOfHistory
    (h : (view.toFOSG horizon cutoff).History) :
    view.BoundedHistory horizon where
  steps := h.steps.map (boundedStepOfStep view horizon cutoff)
  chain := by
    exact boundedStepChainOfStepChain view horizon cutoff h.chain

@[simp] theorem historyOfBoundedHistory_steps
    (h : view.BoundedHistory horizon) :
    (historyOfBoundedHistory view horizon cutoff h).steps =
      h.steps.map (stepOfBoundedStep view horizon cutoff) := rfl

@[simp] theorem boundedHistoryOfHistory_steps
    (h : (view.toFOSG horizon cutoff).History) :
    (boundedHistoryOfHistory view horizon cutoff h).steps =
      h.steps.map (boundedStepOfStep view horizon cutoff) := rfl

@[simp] theorem historyOfBoundedHistory_lastState
    (h : view.BoundedHistory horizon) :
    (historyOfBoundedHistory view horizon cutoff h).lastState =
      h.lastState := by
  simp [historyOfBoundedHistory, BoundedHistory.lastState,
    FOSG.History.lastState, lastStateFrom_map_stepOfBoundedStep]

@[simp] theorem boundedHistoryOfHistory_lastState
    (h : (view.toFOSG horizon cutoff).History) :
    (boundedHistoryOfHistory view horizon cutoff h).lastState =
      h.lastState := by
  simp [boundedHistoryOfHistory, BoundedHistory.lastState,
    FOSG.History.lastState, lastStateFrom_map_boundedStepOfStep]

@[simp] theorem boundedHistoryOfHistory_historyOfBoundedHistory
    (h : view.BoundedHistory horizon) :
    boundedHistoryOfHistory view horizon cutoff
        (historyOfBoundedHistory view horizon cutoff h) = h := by
  apply BoundedHistory.ext
  change List.map (boundedStepOfStep view horizon cutoff)
      (List.map (stepOfBoundedStep view horizon cutoff) h.steps) = h.steps
  rw [List.map_map]
  induction h.steps with
  | nil => rfl
  | cons step steps ih =>
      simp [ih]

@[simp] theorem historyOfBoundedHistory_boundedHistoryOfHistory
    (h : (view.toFOSG horizon cutoff).History) :
    historyOfBoundedHistory view horizon cutoff
        (boundedHistoryOfHistory view horizon cutoff h) = h := by
  apply FOSG.History.ext
  change List.map (stepOfBoundedStep view horizon cutoff)
      (List.map (boundedStepOfStep view horizon cutoff) h.steps) = h.steps
  rw [List.map_map]
  induction h.steps with
  | nil => rfl
  | cons step steps ih =>
      simp [ih]

/-! ## Player information states -/

/-- Translate a native player-visible event to the corresponding FOSG event. -/
def playerEventOfPlayerEvent (player : Player) :
    PlayerEvent view player →
      FOSG.PlayerEvent (view.toFOSG horizon cutoff) player
  | .act action => .act action
  | .obs priv pub => .obs priv pub

/-- Translate a FOSG player-visible event to the native event. -/
def playerEventOfFOSGPlayerEvent (player : Player) :
    FOSG.PlayerEvent (view.toFOSG horizon cutoff) player →
      PlayerEvent view player
  | .act action => .act action
  | .obs priv pub => .obs priv pub

@[simp] theorem playerEventOfFOSGPlayerEvent_playerEventOfPlayerEvent
    (player : Player) (event : PlayerEvent view player) :
    playerEventOfFOSGPlayerEvent view horizon cutoff player
        (playerEventOfPlayerEvent view horizon cutoff player event) =
      event := by
  cases event <;> rfl

@[simp] theorem playerEventOfPlayerEvent_playerEventOfFOSGPlayerEvent
    (player : Player)
    (event : FOSG.PlayerEvent (view.toFOSG horizon cutoff) player) :
    playerEventOfPlayerEvent view horizon cutoff player
        (playerEventOfFOSGPlayerEvent view horizon cutoff player event) =
      event := by
  cases event <;> rfl

/-- Translate a native information state to the FOSG surface. -/
def infoOfInfo (player : Player) (info : view.InfoState player) :
    (view.toFOSG horizon cutoff).InfoState player :=
  info.map (playerEventOfPlayerEvent view horizon cutoff player)

/-- Translate a FOSG information state to the native surface. -/
def infoOfFOSGInfo (player : Player)
    (info : (view.toFOSG horizon cutoff).InfoState player) :
    view.InfoState player :=
  info.map (playerEventOfFOSGPlayerEvent view horizon cutoff player)

@[simp] theorem infoOfFOSGInfo_infoOfInfo
    (player : Player) (info : view.InfoState player) :
    infoOfFOSGInfo view horizon cutoff player
        (infoOfInfo view horizon cutoff player info) = info := by
  unfold infoOfInfo infoOfFOSGInfo
  change List.map (playerEventOfFOSGPlayerEvent view horizon cutoff player)
      (List.map (playerEventOfPlayerEvent view horizon cutoff player) info) =
    info
  rw [List.map_map]
  induction info with
  | nil => rfl
  | cons event events ih =>
      simp [ih]

@[simp] theorem infoOfInfo_infoOfFOSGInfo
    (player : Player)
    (info : (view.toFOSG horizon cutoff).InfoState player) :
    infoOfInfo view horizon cutoff player
        (infoOfFOSGInfo view horizon cutoff player info) = info := by
  unfold infoOfInfo infoOfFOSGInfo
  change List.map (playerEventOfPlayerEvent view horizon cutoff player)
      (List.map (playerEventOfFOSGPlayerEvent view horizon cutoff player)
        info) = info
  rw [List.map_map]
  induction info with
  | nil => rfl
  | cons event events ih =>
      simp [ih]

theorem step_playerViewOfBoundedStep
    (step : view.BoundedStep horizon) (player : Player) :
    FOSG.Step.playerView
        (stepOfBoundedStep view horizon cutoff step) player =
      (step.playerView player).map
        (playerEventOfPlayerEvent view horizon cutoff player) := by
  cases step with
  | mk src act dst support =>
      cases hact : (act : JointAction view.Act) player with
      | none =>
          simp [stepOfBoundedStep, playerEventOfPlayerEvent,
            FOSG.Step.playerView, BoundedStep.playerView,
            FOSG.Step.ownAction?, BoundedStep.ownAction?,
            hact, FOSG.Step.privateObs, FOSG.Step.publicObs,
            BoundedStep.privateObs, BoundedStep.publicObs, toFOSG]
      | some action =>
          simp [stepOfBoundedStep, playerEventOfPlayerEvent,
            FOSG.Step.playerView, BoundedStep.playerView,
            FOSG.Step.ownAction?, BoundedStep.ownAction?,
            hact, FOSG.Step.privateObs, FOSG.Step.publicObs,
            BoundedStep.privateObs, BoundedStep.publicObs, toFOSG]

theorem boundedStep_playerViewOfStep
    (step : (view.toFOSG horizon cutoff).Step) (player : Player) :
    (boundedStepOfStep view horizon cutoff step).playerView player =
      (FOSG.Step.playerView step player).map
        (playerEventOfFOSGPlayerEvent view horizon cutoff player) := by
  cases step with
  | mk src act dst support =>
      cases hact : (act : JointAction view.Act) player with
      | none =>
          simp [boundedStepOfStep, playerEventOfFOSGPlayerEvent,
            FOSG.Step.playerView, BoundedStep.playerView,
            FOSG.Step.ownAction?, BoundedStep.ownAction?,
            hact, FOSG.Step.privateObs, FOSG.Step.publicObs,
            BoundedStep.privateObs, BoundedStep.publicObs, toFOSG]
      | some action =>
          simp [boundedStepOfStep, playerEventOfFOSGPlayerEvent,
            FOSG.Step.playerView, BoundedStep.playerView,
            FOSG.Step.ownAction?, BoundedStep.ownAction?,
            hact, FOSG.Step.privateObs, FOSG.Step.publicObs,
            BoundedStep.privateObs, BoundedStep.publicObs, toFOSG]

theorem playerViewFrom_historyOfBoundedHistory
    (player : Player) :
    ∀ (steps : List (view.BoundedStep horizon)),
      FOSG.History.playerViewFrom
          (G := view.toFOSG horizon cutoff) player
          (steps.map (stepOfBoundedStep view horizon cutoff)) =
        infoOfInfo view horizon cutoff player
          (BoundedHistory.playerViewFrom
            (view := view) (horizon := horizon) player steps)
  | [] => by
      simp [FOSG.History.playerViewFrom,
        BoundedHistory.playerViewFrom, infoOfInfo]
  | step :: steps => by
      simp [FOSG.History.playerViewFrom,
        BoundedHistory.playerViewFrom,
        step_playerViewOfBoundedStep view horizon cutoff step player,
        playerViewFrom_historyOfBoundedHistory player steps,
        infoOfInfo, List.map_append]

theorem playerViewFrom_boundedHistoryOfHistory
    (player : Player) :
    ∀ (steps : List ((view.toFOSG horizon cutoff).Step)),
      BoundedHistory.playerViewFrom
          (view := view) (horizon := horizon) player
          (steps.map (boundedStepOfStep view horizon cutoff)) =
        infoOfFOSGInfo view horizon cutoff player
          (FOSG.History.playerViewFrom
            (G := view.toFOSG horizon cutoff) player steps)
  | [] => by
      simp [FOSG.History.playerViewFrom,
        BoundedHistory.playerViewFrom, infoOfFOSGInfo]
  | step :: steps => by
      simp [FOSG.History.playerViewFrom,
        BoundedHistory.playerViewFrom,
        boundedStep_playerViewOfStep view horizon cutoff step player,
        playerViewFrom_boundedHistoryOfHistory player steps,
        infoOfFOSGInfo, List.map_append]

@[simp] theorem historyOfBoundedHistory_playerView
    (h : view.BoundedHistory horizon) (player : Player) :
    (historyOfBoundedHistory view horizon cutoff h).playerView player =
      infoOfInfo view horizon cutoff player (h.playerView player) := by
  simpa [historyOfBoundedHistory, BoundedHistory.playerView,
    FOSG.History.playerView] using
    playerViewFrom_historyOfBoundedHistory
      (view := view) (horizon := horizon) (cutoff := cutoff)
      player h.steps

@[simp] theorem boundedHistoryOfHistory_playerView
    (h : (view.toFOSG horizon cutoff).History) (player : Player) :
    (boundedHistoryOfHistory view horizon cutoff h).playerView player =
      infoOfFOSGInfo view horizon cutoff player (h.playerView player) := by
  simpa [boundedHistoryOfHistory, BoundedHistory.playerView,
    FOSG.History.playerView] using
    playerViewFrom_boundedHistoryOfHistory
      (view := view) (horizon := horizon) (cutoff := cutoff)
      player h.steps

/-! ## Reachable information states and strategies -/

/-- Translate a reachable native information state to the FOSG surface. -/
noncomputable def reachableInfoOfInfo
    (player : Player) (info : view.ReachableInfoState horizon player) :
    (view.toFOSG horizon cutoff).ReachableInfoState player := by
  refine ⟨infoOfInfo view horizon cutoff player info.1, ?_⟩
  rcases info.2 with ⟨h, hinfo⟩
  refine ⟨historyOfBoundedHistory view horizon cutoff h, ?_⟩
  simp [hinfo]

/-- Translate a reachable FOSG information state to the native surface. -/
noncomputable def infoOfReachableInfo
    (player : Player)
    (info : (view.toFOSG horizon cutoff).ReachableInfoState player) :
    view.ReachableInfoState horizon player := by
  refine ⟨infoOfFOSGInfo view horizon cutoff player info.1, ?_⟩
  rcases info.2 with ⟨h, hinfo⟩
  refine ⟨boundedHistoryOfHistory view horizon cutoff h, ?_⟩
  simp [hinfo]

@[simp] theorem reachableInfoOfInfo_of_history
    (player : Player) (h : view.BoundedHistory horizon) :
    reachableInfoOfInfo view horizon cutoff player
        (view.reachableInfoStateOfHistory horizon player h) =
      (view.toFOSG horizon cutoff).reachableInfoStateOfHistory
        player (historyOfBoundedHistory view horizon cutoff h) := by
  apply Subtype.ext
  simp [reachableInfoOfInfo, reachableInfoStateOfHistory,
    FOSG.reachableInfoStateOfHistory]

@[simp] theorem infoOfReachableInfo_of_history
    (player : Player) (h : (view.toFOSG horizon cutoff).History) :
    infoOfReachableInfo view horizon cutoff player
        ((view.toFOSG horizon cutoff).reachableInfoStateOfHistory player h) =
      view.reachableInfoStateOfHistory horizon player
        (boundedHistoryOfHistory view horizon cutoff h) := by
  apply Subtype.ext
  simp [infoOfReachableInfo, reachableInfoStateOfHistory,
    FOSG.reachableInfoStateOfHistory]

@[simp] theorem infoOfReachableInfo_reachableInfoOfInfo
    (player : Player) (info : view.ReachableInfoState horizon player) :
    infoOfReachableInfo view horizon cutoff player
        (reachableInfoOfInfo view horizon cutoff player info) = info := by
  apply Subtype.ext
  simp [reachableInfoOfInfo, infoOfReachableInfo]

@[simp] theorem reachableInfoOfInfo_infoOfReachableInfo
    (player : Player)
    (info : (view.toFOSG horizon cutoff).ReachableInfoState player) :
    reachableInfoOfInfo view horizon cutoff player
        (infoOfReachableInfo view horizon cutoff player info) = info := by
  apply Subtype.ext
  simp [reachableInfoOfInfo, infoOfReachableInfo]

theorem availableMoves_historyOfBoundedHistory
    (h : view.BoundedHistory horizon) (player : Player) :
    (view.toFOSG horizon cutoff).availableMoves
        (historyOfBoundedHistory view horizon cutoff h) player =
      view.boundedAvailableMoves horizon h player := by
  ext move
  change (view.toFOSG horizon cutoff).locallyLegalAtState
      (historyOfBoundedHistory view horizon cutoff h).lastState player move ↔
    view.boundedLocallyLegalAtState horizon h.lastState player move
  rw [historyOfBoundedHistory_lastState]
  cases move <;> simp [toFOSG, FOSG.locallyLegalAtState,
    boundedLocallyLegalAtState]

theorem availableMoves_boundedHistoryOfHistory
    (h : (view.toFOSG horizon cutoff).History) (player : Player) :
    view.boundedAvailableMoves horizon
        (boundedHistoryOfHistory view horizon cutoff h) player =
      (view.toFOSG horizon cutoff).availableMoves h player := by
  have hEq :=
    availableMoves_historyOfBoundedHistory
      (view := view) (horizon := horizon) (cutoff := cutoff)
      (boundedHistoryOfHistory view horizon cutoff h) player
  simpa using hEq.symm

/-- Translate a legal native behavioral strategy to a legal reachable FOSG
behavioral strategy. -/
noncomputable def behavioralStrategyOfBoundedBehavioralStrategy
    (player : Player)
    (strategy : view.BoundedBehavioralStrategy horizon player) :
    (view.toFOSG horizon cutoff).ReachableLegalBehavioralStrategy player := by
  refine ⟨fun info =>
    strategy.1 (infoOfReachableInfo view horizon cutoff player info), ?_⟩
  intro h move hmove
  have hmoveNative :
      move ∈
        (strategy.1
          (view.reachableInfoStateOfHistory horizon player
            (boundedHistoryOfHistory view horizon cutoff h))).support := by
    simpa using hmove
  have hlegal :=
    strategy.2 (boundedHistoryOfHistory view horizon cutoff h) hmoveNative
  rwa [availableMoves_boundedHistoryOfHistory
    (view := view) (horizon := horizon) (cutoff := cutoff) h player] at hlegal

/-- Translate a legal reachable FOSG behavioral strategy to the native surface. -/
noncomputable def boundedBehavioralStrategyOfBehavioralStrategy
    (player : Player)
    (strategy :
      (view.toFOSG horizon cutoff).ReachableLegalBehavioralStrategy player) :
    view.BoundedBehavioralStrategy horizon player := by
  refine ⟨fun info =>
    strategy.1 (reachableInfoOfInfo view horizon cutoff player info), ?_⟩
  intro h move hmove
  have hmoveFOSG :
      move ∈
        (strategy.1
          ((view.toFOSG horizon cutoff).reachableInfoStateOfHistory player
            (historyOfBoundedHistory view horizon cutoff h))).support := by
    simpa using hmove
  have hlegal :=
    strategy.2 (historyOfBoundedHistory view horizon cutoff h) hmoveFOSG
  rwa [availableMoves_historyOfBoundedHistory
    (view := view) (horizon := horizon) (cutoff := cutoff) h player] at hlegal

noncomputable def behavioralProfileOfBoundedBehavioralProfile
    (profile : view.BoundedBehavioralProfile horizon) :
    (view.toFOSG horizon cutoff).ReachableLegalBehavioralProfile :=
  fun player =>
    behavioralStrategyOfBoundedBehavioralStrategy
      view horizon cutoff player (profile player)

noncomputable def boundedBehavioralProfileOfBehavioralProfile
    (profile :
      (view.toFOSG horizon cutoff).ReachableLegalBehavioralProfile) :
    view.BoundedBehavioralProfile horizon :=
  fun player =>
    boundedBehavioralStrategyOfBehavioralStrategy
      view horizon cutoff player (profile player)

noncomputable def boundedBehavioralProfileOfLegalBehavioralProfile
    (profile : (view.toFOSG horizon cutoff).LegalBehavioralProfile) :
    view.BoundedBehavioralProfile horizon :=
  boundedBehavioralProfileOfBehavioralProfile view horizon cutoff
    (fun player => (profile player).restrictReachable)

@[simp] theorem
    boundedBehavioralStrategyOfBehavioralStrategy_behavioralStrategyOfBoundedBehavioralStrategy
    (player : Player)
    (strategy : view.BoundedBehavioralStrategy horizon player) :
    boundedBehavioralStrategyOfBehavioralStrategy view horizon cutoff player
        (behavioralStrategyOfBoundedBehavioralStrategy
          view horizon cutoff player strategy) = strategy := by
  apply Subtype.ext
  funext info
  simp [behavioralStrategyOfBoundedBehavioralStrategy,
    boundedBehavioralStrategyOfBehavioralStrategy]

@[simp] theorem
    behavioralStrategyOfBoundedBehavioralStrategy_boundedBehavioralStrategyOfBehavioralStrategy
    (player : Player)
    (strategy :
      (view.toFOSG horizon cutoff).ReachableLegalBehavioralStrategy player) :
    behavioralStrategyOfBoundedBehavioralStrategy view horizon cutoff player
        (boundedBehavioralStrategyOfBehavioralStrategy
          view horizon cutoff player strategy) = strategy := by
  apply Subtype.ext
  funext info
  simp [behavioralStrategyOfBoundedBehavioralStrategy,
    boundedBehavioralStrategyOfBehavioralStrategy]

theorem jointActionDist_historyOfBoundedHistory
    [Fintype Player] [∀ player, Fintype (Option (view.Act player))]
    (profile : view.BoundedBehavioralProfile horizon)
    (h : view.BoundedHistory horizon)
    (action : JointAction view.Act) :
    (view.toFOSG horizon cutoff).jointActionDist
        (behavioralProfileOfBoundedBehavioralProfile
          view horizon cutoff profile).extend
        (historyOfBoundedHistory view horizon cutoff h) action =
      view.jointActionDist horizon profile h action := by
  classical
  rw [FOSG.jointActionDist_apply]
  rw [jointActionDist_apply]
  apply Finset.prod_congr rfl
  intro player _hm
  change (((behavioralProfileOfBoundedBehavioralProfile
        view horizon cutoff profile player).1).extend
      ((historyOfBoundedHistory view horizon cutoff h).playerView player))
      (action player) =
    ((profile player).1
      (view.reachableInfoStateOfHistory horizon player h)) (action player)
  rw [FOSG.ReachableBehavioralStrategy.extend_apply_history]
  simp [behavioralProfileOfBoundedBehavioralProfile,
    behavioralStrategyOfBoundedBehavioralStrategy]

open Classical in
theorem runDist_restrictLegalBehavioralProfile
    [Fintype Player] [∀ player, Fintype (Option (view.Act player))]
    (profile : (view.toFOSG horizon cutoff).LegalBehavioralProfile)
    (steps : Nat) :
    (view.toFOSG horizon cutoff).runDist steps
        (behavioralProfileOfBoundedBehavioralProfile view horizon cutoff
          (boundedBehavioralProfileOfLegalBehavioralProfile
          view horizon cutoff profile)).extend =
      (view.toFOSG horizon cutoff).runDist steps profile := by
  classical
  apply FOSG.runDist_congr
  intro h player
  change
    (((behavioralProfileOfBoundedBehavioralProfile view horizon cutoff
          (boundedBehavioralProfileOfLegalBehavioralProfile
            view horizon cutoff profile) player).1).extend
        (h.playerView player)) =
      (profile player).1 (h.playerView player)
  rw [FOSG.ReachableBehavioralStrategy.extend_apply_history]
  simp [behavioralProfileOfBoundedBehavioralProfile,
    boundedBehavioralProfileOfLegalBehavioralProfile,
    boundedBehavioralProfileOfBehavioralProfile,
    behavioralStrategyOfBoundedBehavioralStrategy,
    boundedBehavioralStrategyOfBehavioralStrategy,
    FOSG.LegalBehavioralStrategy.restrictReachable,
    FOSG.BehavioralStrategy.restrictReachable]

/-! ## One-step execution laws -/

theorem terminal_historyOfBoundedHistory
    (h : view.BoundedHistory horizon) :
    (view.toFOSG horizon cutoff).terminal
        (historyOfBoundedHistory view horizon cutoff h).lastState ↔
      view.boundedTerminal horizon h.lastState := by
  change view.boundedTerminal horizon
      (historyOfBoundedHistory view horizon cutoff h).lastState ↔
    view.boundedTerminal horizon h.lastState
  rw [historyOfBoundedHistory_lastState]

theorem terminal_boundedHistoryOfHistory
    (h : (view.toFOSG horizon cutoff).History) :
    view.boundedTerminal horizon
        (boundedHistoryOfHistory view horizon cutoff h).lastState ↔
      (view.toFOSG horizon cutoff).terminal h.lastState := by
  change view.boundedTerminal horizon
      (boundedHistoryOfHistory view horizon cutoff h).lastState ↔
    view.boundedTerminal horizon h.lastState
  rw [boundedHistoryOfHistory_lastState]

/-- Repackage a legal native bounded action at a translated history as a FOSG
legal action. -/
noncomputable def legalActionOfBoundedLegalAction
    (h : view.BoundedHistory horizon)
    (action : view.BoundedLegalAction horizon h.lastState) :
    (view.toFOSG horizon cutoff).LegalAction
      (historyOfBoundedHistory view horizon cutoff h).lastState := by
  refine ⟨action.1, ?_⟩
  change JointActionLegal view.Act (view.boundedActive horizon)
    (view.boundedTerminal horizon) (view.boundedAvailableActions horizon)
    (historyOfBoundedHistory view horizon cutoff h).lastState action.1
  rw [historyOfBoundedHistory_lastState]
  exact action.2

/-- Repackage a legal FOSG action at a translated history as a native bounded
legal action. -/
noncomputable def boundedLegalActionOfLegalAction
    (h : (view.toFOSG horizon cutoff).History)
    (action : (view.toFOSG horizon cutoff).LegalAction h.lastState) :
    view.BoundedLegalAction horizon
      (boundedHistoryOfHistory view horizon cutoff h).lastState := by
  refine ⟨action.1, ?_⟩
  have hlegal :
      JointActionLegal view.Act (view.boundedActive horizon)
        (view.boundedTerminal horizon) (view.boundedAvailableActions horizon)
        h.lastState action.1 := by
    simpa [toFOSG] using action.2
  change JointActionLegal view.Act (view.boundedActive horizon)
    (view.boundedTerminal horizon) (view.boundedAvailableActions horizon)
    (boundedHistoryOfHistory view horizon cutoff h).lastState action.1
  rw [boundedHistoryOfHistory_lastState]
  exact hlegal

/-- Repackage a legal FOSG action over a native translated history back to the
native action surface. -/
noncomputable def boundedLegalActionOfLegalActionAtBoundedHistory
    (h : view.BoundedHistory horizon)
    (action :
      (view.toFOSG horizon cutoff).LegalAction
        (historyOfBoundedHistory view horizon cutoff h).lastState) :
    view.BoundedLegalAction horizon h.lastState := by
  refine ⟨action.1, ?_⟩
  have hlegal :
      JointActionLegal view.Act (view.boundedActive horizon)
        (view.boundedTerminal horizon) (view.boundedAvailableActions horizon)
        (historyOfBoundedHistory view horizon cutoff h).lastState
        action.1 := by
    simpa [toFOSG] using action.2
  simpa [historyOfBoundedHistory_lastState] using hlegal

@[simp] theorem legalActionOfBoundedLegalAction_inverse_at_boundedHistory
    (h : view.BoundedHistory horizon)
    (action :
      (view.toFOSG horizon cutoff).LegalAction
        (historyOfBoundedHistory view horizon cutoff h).lastState) :
    legalActionOfBoundedLegalAction view horizon cutoff h
        (boundedLegalActionOfLegalActionAtBoundedHistory
          view horizon cutoff h action) = action := by
  apply Subtype.ext
  rfl

@[simp] theorem boundedLegalActionOfLegalActionAtBoundedHistory_inverse
    (h : view.BoundedHistory horizon)
    (action : view.BoundedLegalAction horizon h.lastState) :
    boundedLegalActionOfLegalActionAtBoundedHistory view horizon cutoff h
        (legalActionOfBoundedLegalAction view horizon cutoff h action) =
      action := by
  apply Subtype.ext
  rfl

theorem legalActionLaw_historyOfBoundedHistory
    [Fintype Player] [∀ player, Fintype (Option (view.Act player))]
    (profile : view.BoundedBehavioralProfile horizon)
    (h : view.BoundedHistory horizon)
    (hterm : ¬ view.boundedTerminal horizon h.lastState) :
    PMF.map (legalActionOfBoundedLegalAction view horizon cutoff h)
        (view.legalActionLaw horizon profile h hterm) =
      (view.toFOSG horizon cutoff).legalActionLaw
        (behavioralProfileOfBoundedBehavioralProfile
          view horizon cutoff profile).extend
        (historyOfBoundedHistory view horizon cutoff h)
        (by
          intro ht
          exact hterm
            ((terminal_historyOfBoundedHistory
              (view := view) (horizon := horizon) (cutoff := cutoff) h).1 ht)) := by
  classical
  apply PMF.ext
  intro action
  rw [PMF.map_apply, tsum_fintype]
  trans view.legalActionLaw horizon profile h hterm
      (boundedLegalActionOfLegalActionAtBoundedHistory
        view horizon cutoff h action)
  · rw [Fintype.sum_eq_single
      (boundedLegalActionOfLegalActionAtBoundedHistory
        view horizon cutoff h action)]
    · have hinv :
          action =
            legalActionOfBoundedLegalAction view horizon cutoff h
              (boundedLegalActionOfLegalActionAtBoundedHistory
                view horizon cutoff h action) := by
        exact
          (legalActionOfBoundedLegalAction_inverse_at_boundedHistory
            (view := view) (horizon := horizon) (cutoff := cutoff) h action).symm
      rw [hinv]
      simp
    · intro other hne
      by_cases heq :
          action =
            legalActionOfBoundedLegalAction view horizon cutoff h other
      · exfalso
        apply hne
        apply Subtype.ext
        exact (congrArg Subtype.val heq).symm
      · rw [if_neg heq]
  · rw [legalActionLaw_apply]
    rw [FOSG.legalActionLaw_apply]
    exact
      (jointActionDist_historyOfBoundedHistory
        (view := view) (horizon := horizon) (cutoff := cutoff)
        profile h action.1).symm

theorem transition_historyOfBoundedHistory
    (h : view.BoundedHistory horizon)
    (action : view.BoundedLegalAction horizon h.lastState) :
    (view.toFOSG horizon cutoff).transition
        (historyOfBoundedHistory view horizon cutoff h).lastState
        (legalActionOfBoundedLegalAction view horizon cutoff h action) =
      view.boundedTransition horizon h.lastState action := by
  convert
    (rfl :
      view.boundedTransition horizon h.lastState action =
        view.boundedTransition horizon h.lastState action) using 2
  · exact historyOfBoundedHistory_lastState
      (view := view) (horizon := horizon) (cutoff := cutoff) h
  · apply (Subtype.heq_iff_coe_eq ?_).2
    · rfl
    · intro joint
      unfold FOSG.legal
      change JointActionLegal view.Act (view.boundedActive horizon)
          (view.boundedTerminal horizon) (view.boundedAvailableActions horizon)
          (historyOfBoundedHistory view horizon cutoff h).lastState joint ↔
        JointActionLegal view.Act (view.boundedActive horizon)
          (view.boundedTerminal horizon) (view.boundedAvailableActions horizon)
          h.lastState joint
      rw [historyOfBoundedHistory_lastState]

/-- Translation commutes with appending one supported native bounded step. -/
theorem historyOfBoundedHistory_snoc
    (h : view.BoundedHistory horizon)
    (action : view.BoundedLegalAction horizon h.lastState)
    (dst : M.BoundedState horizon)
    (hsupp :
      view.boundedTransition horizon h.lastState action dst ≠ 0) :
    historyOfBoundedHistory view horizon cutoff (h.snoc action dst hsupp) =
      (historyOfBoundedHistory view horizon cutoff h).snoc
        (legalActionOfBoundedLegalAction view horizon cutoff h action) dst
        (by
          rw [transition_historyOfBoundedHistory
            (view := view) (horizon := horizon) (cutoff := cutoff) h action]
          exact hsupp) := by
  apply FOSG.History.ext
  simp only [historyOfBoundedHistory_steps, BoundedHistory.steps_snoc,
    List.map_append, List.map_cons, List.map_nil, FOSG.History.steps_snoc,
    List.append_cancel_left_eq, List.cons.injEq, and_true,
    stepOfBoundedStep, legalActionOfBoundedLegalAction, FOSG.Step.mk.injEq]
  constructor
  · exact (historyOfBoundedHistory_lastState
      (view := view) (horizon := horizon) (cutoff := cutoff) h).symm
  · apply (Subtype.heq_iff_coe_eq ?_).2
    · rfl
    · intro joint
      unfold FOSG.legal
      change JointActionLegal view.Act (view.boundedActive horizon)
          (view.boundedTerminal horizon) (view.boundedAvailableActions horizon)
          h.lastState joint ↔
        JointActionLegal view.Act (view.boundedActive horizon)
          (view.boundedTerminal horizon) (view.boundedAvailableActions horizon)
          (historyOfBoundedHistory view horizon cutoff h).lastState joint
      rw [historyOfBoundedHistory_lastState]

theorem historyOfBoundedHistory_extendByOutcome
    (h : view.BoundedHistory horizon)
    (action : view.BoundedLegalAction horizon h.lastState)
    (dst : M.BoundedState horizon) :
    historyOfBoundedHistory view horizon cutoff
        (h.extendByOutcome action dst) =
      (historyOfBoundedHistory view horizon cutoff h).extendByOutcome
        (legalActionOfBoundedLegalAction view horizon cutoff h action) dst := by
  by_cases hsupp :
      view.boundedTransition horizon h.lastState action dst = 0
  · have hzero :
        (view.toFOSG horizon cutoff).transition
            (historyOfBoundedHistory view horizon cutoff h).lastState
            (legalActionOfBoundedLegalAction view horizon cutoff h action)
            dst = 0 := by
      rw [transition_historyOfBoundedHistory
        (view := view) (horizon := horizon) (cutoff := cutoff) h action]
      exact hsupp
    rw [FOSG.History.extendByOutcome_of_no_support
      (h := historyOfBoundedHistory view horizon cutoff h)
      (a := legalActionOfBoundedLegalAction view horizon cutoff h action)
      (dst := dst) hzero]
    simp [BoundedHistory.extendByOutcome, hsupp]
  · have hsuppF :
        (view.toFOSG horizon cutoff).transition
            (historyOfBoundedHistory view horizon cutoff h).lastState
            (legalActionOfBoundedLegalAction view horizon cutoff h action)
            dst ≠ 0 := by
      rw [transition_historyOfBoundedHistory
        (view := view) (horizon := horizon) (cutoff := cutoff) h action]
      exact hsupp
    rw [FOSG.History.extendByOutcome_of_support
      (h := historyOfBoundedHistory view horizon cutoff h)
      (a := legalActionOfBoundedLegalAction view horizon cutoff h action)
      (dst := dst) hsuppF]
    rw [BoundedHistory.extendByOutcome_of_support
      (h := h) (action := action) (dst := dst) hsupp]
    exact historyOfBoundedHistory_snoc
      (view := view) (horizon := horizon) (cutoff := cutoff)
      h action dst hsupp

theorem historyOfBoundedHistory_snoc_utility
    (h : view.BoundedHistory horizon)
    (action : view.BoundedLegalAction horizon h.lastState)
    (dst : M.BoundedState horizon)
    (support : view.boundedTransition horizon h.lastState action dst ≠ 0)
    (player : Player) :
    (historyOfBoundedHistory view horizon cutoff
        (h.snoc action dst support)).utility player =
      (historyOfBoundedHistory view horizon cutoff h).utility player +
        terminalReward view horizon cutoff h.lastState action dst player := by
  rw [historyOfBoundedHistory_snoc
    (view := view) (horizon := horizon) (cutoff := cutoff)
    h action dst support]
  simp [toFOSG, terminalReward]

theorem historyOfBoundedHistory_appendStep_utility
    (h : view.BoundedHistory horizon)
    (step : view.BoundedStep horizon)
    (hsrc : step.src = h.lastState)
    (player : Player) :
    (historyOfBoundedHistory view horizon cutoff
        (h.appendStep step hsrc)).utility player =
      (historyOfBoundedHistory view horizon cutoff h).utility player +
        terminalReward view horizon cutoff step.src step.act step.dst player := by
  simp [historyOfBoundedHistory, BoundedHistory.appendStep,
    FOSG.History.utility, FOSG.History.rewardSum,
    FOSG.History.rewardSumFrom_append_singleton, stepOfBoundedStep,
    toFOSG, terminalReward]

theorem historyOfBoundedHistory_utility_of_nonterminal
    (h : view.BoundedHistory horizon)
    (hnot : ¬ view.boundedTerminal horizon h.lastState)
    (player : Player) :
    (historyOfBoundedHistory view horizon cutoff h).utility player = 0 := by
  cases h with
  | mk steps chain =>
      induction steps using List.reverseRecOn with
      | nil =>
          simp [historyOfBoundedHistory,
            FOSG.History.utility, FOSG.History.rewardSum]
      | append_singleton steps step ih =>
          let hprefix : view.BoundedHistory horizon :=
            { steps := steps
              chain := Machine.RoundView.StepChainFrom.left
                (view := view) (steps₁ := steps) (steps₂ := [step]) chain }
          have hright :
              view.StepChainFrom horizon
                (view.lastStateFrom horizon
                  (Machine.BoundedState.init M horizon) steps)
                [step] :=
            Machine.RoundView.StepChainFrom.right
              (view := view) (steps₁ := steps) (steps₂ := [step]) chain
          have hsrc : step.src = hprefix.lastState := by
            simpa [hprefix, BoundedHistory.lastState,
              Machine.RoundView.StepChainFrom] using hright.1
          let hfull : view.BoundedHistory horizon :=
            hprefix.appendStep step hsrc
          have hEq :
              ({ steps := steps ++ [step], chain := chain } :
                  view.BoundedHistory horizon) = hfull := by
            ext
            rfl
          have hnotPrefix :
              ¬ view.boundedTerminal horizon hprefix.lastState := by
            intro hterm
            exact step.act.2.1 (by simpa [hsrc] using hterm)
          have hnotDst :
              ¬ view.boundedTerminal horizon step.dst := by
            intro hterm
            exact hnot (by simpa [hEq, hfull] using hterm)
          rw [hEq]
          rw [historyOfBoundedHistory_appendStep_utility
            (view := view) (horizon := horizon) (cutoff := cutoff)
            hprefix step hsrc player]
          rw [ih hprefix.chain hnotPrefix]
          simp [terminalReward, hnotDst]

theorem historyOfBoundedHistory_utility_of_terminal
    (hinit : ¬ view.boundedTerminal horizon (Machine.BoundedState.init M horizon))
    (h : view.BoundedHistory horizon)
    (hterm : view.boundedTerminal horizon h.lastState)
    (player : Player) :
    (historyOfBoundedHistory view horizon cutoff h).utility player =
      optionOutcomeUtility M cutoff (M.outcome h.lastState.state) player := by
  cases h with
  | mk steps chain =>
      induction steps using List.reverseRecOn with
      | nil =>
          exfalso
          exact hinit (by simpa [BoundedHistory.lastState] using hterm)
      | append_singleton steps step _ih =>
          let hprefix : view.BoundedHistory horizon :=
            { steps := steps
              chain := Machine.RoundView.StepChainFrom.left
                (view := view) (steps₁ := steps) (steps₂ := [step]) chain }
          have hright :
              view.StepChainFrom horizon
                (view.lastStateFrom horizon
                  (Machine.BoundedState.init M horizon) steps)
                [step] :=
            Machine.RoundView.StepChainFrom.right
              (view := view) (steps₁ := steps) (steps₂ := [step]) chain
          have hsrc : step.src = hprefix.lastState := by
            simpa [hprefix, BoundedHistory.lastState,
              Machine.RoundView.StepChainFrom] using hright.1
          let hfull : view.BoundedHistory horizon :=
            hprefix.appendStep step hsrc
          have hEq :
              ({ steps := steps ++ [step], chain := chain } :
                  view.BoundedHistory horizon) = hfull := by
            ext
            rfl
          have hnotPrefix :
              ¬ view.boundedTerminal horizon hprefix.lastState := by
            intro hterm
            exact step.act.2.1 (by simpa [hsrc] using hterm)
          have htermDst :
              view.boundedTerminal horizon step.dst := by
            simpa [hEq, hfull] using hterm
          rw [hEq]
          rw [historyOfBoundedHistory_appendStep_utility
            (view := view) (horizon := horizon) (cutoff := cutoff)
            hprefix step hsrc player]
          rw [historyOfBoundedHistory_utility_of_nonterminal
            (view := view) (horizon := horizon) (cutoff := cutoff)
            hprefix hnotPrefix player]
          simp [terminalReward, htermDst, hfull]

theorem historyOfBoundedHistory_utility_of_runDist_support_at_horizon
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (hinit : ¬ view.boundedTerminal horizon (Machine.BoundedState.init M horizon))
    (profile : view.BoundedBehavioralProfile horizon)
    (h : view.BoundedHistory horizon)
    (hsupport : h ∈ (view.runDist horizon horizon profile).support)
    (player : Player) :
    (historyOfBoundedHistory view horizon cutoff h).utility player =
      optionOutcomeUtility M cutoff (M.outcome h.lastState.state) player := by
  exact
    historyOfBoundedHistory_utility_of_terminal
      (view := view) (horizon := horizon) (cutoff := cutoff)
      hinit h
      (view.runDist_support_terminal_at_horizon
        horizon profile h hsupport)
      player

open Classical in
theorem runDistFrom_historyOfBoundedHistory
    [Fintype Player] [∀ player, Fintype (Option (view.Act player))]
    (profile : view.BoundedBehavioralProfile horizon) :
    ∀ (n : Nat) (h : view.BoundedHistory horizon),
      PMF.map (historyOfBoundedHistory view horizon cutoff)
        (BoundedHistory.runDistFrom view horizon profile n h) =
        FOSG.History.runDistFrom (view.toFOSG horizon cutoff)
          (behavioralProfileOfBoundedBehavioralProfile
            view horizon cutoff profile).extend n
          (historyOfBoundedHistory view horizon cutoff h)
  | 0, h => by
      rw [BoundedHistory.runDistFrom_zero]
      rw [FOSG.History.runDistFrom_zero]
      rw [PMF.pure_map]
  | n + 1, h => by
      classical
      let G := view.toFOSG horizon cutoff
      let fosgProfile :=
        (behavioralProfileOfBoundedBehavioralProfile
          view horizon cutoff profile).extend
      by_cases hterm : view.boundedTerminal horizon h.lastState
      · have htermF :
            G.terminal (historyOfBoundedHistory view horizon cutoff h).lastState :=
          (terminal_historyOfBoundedHistory
            (view := view) (horizon := horizon) (cutoff := cutoff) h).2 hterm
        rw [BoundedHistory.runDistFrom_succ_terminal
          (view := view) (horizon := horizon) profile n h hterm]
        rw [FOSG.History.runDistFrom_succ_terminal
          (G := G) fosgProfile n
          (historyOfBoundedHistory view horizon cutoff h) htermF]
        rw [PMF.pure_map]
      · have htermF :
            ¬ G.terminal
              (historyOfBoundedHistory view horizon cutoff h).lastState := by
          intro ht
          exact hterm
            ((terminal_historyOfBoundedHistory
              (view := view) (horizon := horizon) (cutoff := cutoff) h).1 ht)
        rw [BoundedHistory.runDistFrom_succ_nonterminal
          (view := view) (horizon := horizon) profile n h hterm]
        rw [FOSG.History.runDistFrom_succ_nonterminal
          (G := G) fosgProfile n
          (historyOfBoundedHistory view horizon cutoff h) htermF]
        rw [PMF.map_bind]
        conv_lhs =>
          arg 2
          intro action
          rw [PMF.map_bind]
          arg 2
          intro dst
          rw [runDistFrom_historyOfBoundedHistory profile n
            (h.extendByOutcome action dst)]
          rw [historyOfBoundedHistory_extendByOutcome
            (view := view) (horizon := horizon) (cutoff := cutoff)
            h action dst]
        rw [← legalActionLaw_historyOfBoundedHistory
          (view := view) (horizon := horizon) (cutoff := cutoff)
          profile h hterm]
        rw [PMF.bind_map]
        congr
        funext action
        simp only [Function.comp_apply, G, fosgProfile]
        rw [transition_historyOfBoundedHistory
          (view := view) (horizon := horizon) (cutoff := cutoff)
          h action]

open Classical in
theorem runDist_historyOfBoundedHistory
    [Fintype Player] [∀ player, Fintype (Option (view.Act player))]
    (profile : view.BoundedBehavioralProfile horizon)
    (steps : Nat) :
    PMF.map (historyOfBoundedHistory view horizon cutoff)
        (view.runDist horizon steps profile) =
      (view.toFOSG horizon cutoff).runDist steps
        (behavioralProfileOfBoundedBehavioralProfile
          view horizon cutoff profile).extend := by
  simpa [runDist, FOSG.runDist, BoundedHistory.nil,
    FOSG.History.nil, historyOfBoundedHistory] using
    runDistFrom_historyOfBoundedHistory
      (view := view) (horizon := horizon) (cutoff := cutoff)
      profile steps (BoundedHistory.nil view horizon)

open Classical in
theorem runDist_eq_map_boundedBehavioralProfileOfLegalBehavioralProfile
    [Fintype Player] [∀ player, Fintype (Option (view.Act player))]
    (profile : (view.toFOSG horizon cutoff).LegalBehavioralProfile)
    (steps : Nat) :
    (view.toFOSG horizon cutoff).runDist steps profile =
      PMF.map (historyOfBoundedHistory view horizon cutoff)
        (view.runDist horizon steps
          (boundedBehavioralProfileOfLegalBehavioralProfile
            view horizon cutoff profile)) := by
  classical
  rw [← runDist_restrictLegalBehavioralProfile
    (view := view) (horizon := horizon) (cutoff := cutoff) profile steps]
  exact
    (runDist_historyOfBoundedHistory
      (view := view) (horizon := horizon) (cutoff := cutoff)
      (boundedBehavioralProfileOfLegalBehavioralProfile
        view horizon cutoff profile) steps).symm

/-- Kernel game induced by the bounded FOSG presentation at its native
horizon.  Outcomes are realized FOSG histories. -/
noncomputable def historyKernelGame
    [Fintype Player] [∀ player, Fintype (Option (view.Act player))] :
    KernelGame Player := by
  classical
  exact (view.toFOSG horizon cutoff).toKernelGameAtHorizon horizon

open Classical in
@[simp] theorem historyKernelGame_outcomeKernel
    [Fintype Player] [∀ player, Fintype (Option (view.Act player))]
    (profile : (historyKernelGame view horizon cutoff).Profile) :
    (historyKernelGame view horizon cutoff).outcomeKernel profile =
      (view.toFOSG horizon cutoff).runDist horizon profile := rfl

open Classical in
theorem historyKernelGame_outcomeKernel_eq_map_runDist
    [Fintype Player] [∀ player, Fintype (Option (view.Act player))]
    (profile : view.BoundedBehavioralProfile horizon) :
    (historyKernelGame view horizon cutoff).outcomeKernel
        (behavioralProfileOfBoundedBehavioralProfile
          view horizon cutoff profile).extend =
      PMF.map (historyOfBoundedHistory view horizon cutoff)
        (view.runDist horizon horizon profile) := by
  rw [historyKernelGame_outcomeKernel]
  exact
    (runDist_historyOfBoundedHistory
      (view := view) (horizon := horizon) (cutoff := cutoff)
      profile horizon).symm

/-- Kernel game induced by the bounded FOSG presentation, with outcomes still
realized FOSG histories but utility read from the final native machine state.

This is the payoff-facing FOSG history surface for machine semantics.  It does
not use cumulative FOSG transition rewards, so zero-step terminal runs receive
the same payoff as the native machine. -/
noncomputable def machinePayoffHistoryKernelGame
    [Fintype Player] [∀ player, Fintype (Option (view.Act player))] :
    KernelGame Player := by
  classical
  let G := view.toFOSG horizon cutoff
  exact
    { Strategy := fun player => G.LegalBehavioralStrategy player
      Outcome := G.History
      utility := fun h =>
        optionOutcomeUtility M cutoff (M.outcome h.lastState.state)
      outcomeKernel := fun profile => G.runDist horizon profile }

open Classical in
@[simp] theorem machinePayoffHistoryKernelGame_outcomeKernel
    [Fintype Player] [∀ player, Fintype (Option (view.Act player))]
    (profile : (machinePayoffHistoryKernelGame view horizon cutoff).Profile) :
    (machinePayoffHistoryKernelGame view horizon cutoff).outcomeKernel profile =
      (view.toFOSG horizon cutoff).runDist horizon profile := rfl

@[simp] theorem machinePayoffHistoryKernelGame_utility
    [Fintype Player] [∀ player, Fintype (Option (view.Act player))]
    (h : (machinePayoffHistoryKernelGame view horizon cutoff).Outcome)
    (player : Player) :
    (machinePayoffHistoryKernelGame view horizon cutoff).utility h player =
      optionOutcomeUtility M cutoff (M.outcome h.lastState.state) player := rfl

open Classical in
theorem machinePayoffHistoryKernelGame_outcomeKernel_eq_map_runDist
    [Fintype Player] [∀ player, Fintype (Option (view.Act player))]
    (profile : view.BoundedBehavioralProfile horizon) :
    (machinePayoffHistoryKernelGame view horizon cutoff).outcomeKernel
        (behavioralProfileOfBoundedBehavioralProfile
          view horizon cutoff profile).extend =
      PMF.map (historyOfBoundedHistory view horizon cutoff)
        (view.runDist horizon horizon profile) := by
  rw [machinePayoffHistoryKernelGame_outcomeKernel]
  exact
    (runDist_historyOfBoundedHistory
      (view := view) (horizon := horizon) (cutoff := cutoff)
      profile horizon).symm

end ToFOSG
end RoundView
end Machine

end Vegas
