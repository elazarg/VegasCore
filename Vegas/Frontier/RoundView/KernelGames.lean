import Vegas.Frontier.RoundView.Bounded

/-!
# Completed and frontier kernel games

The `CompletedFrontier*` and `Frontier*KernelGame` namespaces: outcome-kernel
support and the exposed pure/behavioral kernel-game surfaces.
-/

namespace Vegas

namespace ToEventGraph

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Pure-strategy frontier game with the impossible cutoff branch erased from
the exposed kernel-game outcome type. -/
structure CompletedFrontierPureKernelGame
    (compiled : CompiledProgram P L)
    (presentation : EventGraph.CheckpointPresentation compiled.graph) where
  semantics : FrontierRoundSemantics compiled presentation
  nodeFintype :
    (node : Fin compiled.graph.nodeCount) →
      Fintype (L.Val (compiled.graph.nodeRow node).ty)

namespace CompletedFrontierPureKernelGame

variable {compiled : CompiledProgram P L}
variable {presentation : EventGraph.CheckpointPresentation compiled.graph}

noncomputable def view
    (completed : CompletedFrontierPureKernelGame compiled presentation) :
    (PrimitiveMachine compiled).RoundView :=
  frontierRoundView compiled presentation completed.semantics

@[reducible] private noncomputable def optionalMoveFintype
    (completed : CompletedFrontierPureKernelGame compiled presentation) :
    ∀ player, Fintype (Option ((view completed).Act player)) := by
  classical
  letI :
      ∀ node : Fin compiled.graph.nodeCount,
        Fintype (L.Val (compiled.graph.nodeRow node).ty) :=
    completed.nodeFintype
  intro player
  dsimp [view, frontierRoundView, EventGraph.frontierRoundView]
  infer_instance

private noncomputable instance instOptionalMoveFintype
    (completed : CompletedFrontierPureKernelGame compiled presentation) :
    ∀ player, Fintype (Option ((view completed).Act player)) :=
  optionalMoveFintype completed

noncomputable def optionOutcomeKernel
    (completed : CompletedFrontierPureKernelGame compiled presentation) :
    (∀ player, (view completed).BoundedPureStrategy
      (completionBound compiled) player) →
      PMF (Option (PrimitiveMachine compiled).Outcome) :=
  by
    classical
    letI := optionalMoveFintype completed
    exact fun σ =>
      (view completed).boundedOutcomeFromPure
        (completionBound compiled) σ (completionBound compiled)

theorem optionOutcomeKernel_support_some
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (σ :
      ∀ player, (view completed).BoundedPureStrategy
        (completionBound compiled) player)
    {result : Option (PrimitiveMachine compiled).Outcome}
    (hsupport :
      result ∈ (completed.optionOutcomeKernel σ).support) :
    ∃ outcome, result = some outcome := by
  classical
  letI :
      ∀ player,
        Fintype (Option
          ((frontierRoundView compiled presentation completed.semantics).Act
            player)) :=
    optionalMoveFintype completed
  simpa [optionOutcomeKernel, view] using
    FrontierRoundSemantics.boundedOutcomeFromPure_support_some_completionBound
      completed.semantics σ hsupport

/-- Concrete-outcome kernel game associated with a completed pure frontier
game. The option-valued bounded kernel is total by
`optionOutcomeKernel_support_some`; `eraseNonePMF` removes the impossible
`none` branch. -/
noncomputable def game
    (completed : CompletedFrontierPureKernelGame compiled presentation) :
    KernelGame P := by
  classical
  letI := optionalMoveFintype completed
  exact
    { Strategy := fun player =>
        (view completed).BoundedPureStrategy
          (completionBound compiled) player
      Outcome := (PrimitiveMachine compiled).Outcome
      utility := (PrimitiveMachine compiled).utility
      outcomeKernel := fun σ =>
        eraseNonePMF (completed.optionOutcomeKernel σ)
          (fun result hresult =>
            completed.optionOutcomeKernel_support_some σ hresult) }

theorem none_not_mem_outcomeKernel_support
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (σ : completed.game.Profile) :
    none ∉ (completed.optionOutcomeKernel σ).support := by
  intro hnone
  rcases completed.optionOutcomeKernel_support_some σ hnone with
    ⟨outcome, houtcome⟩
  cases houtcome

/-- The completed pure-strategy game erases only the impossible cutoff branch:
concrete outcome support is exactly option-outcome support at `some`. -/
theorem outcomeKernel_support_iff
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (σ : completed.game.Profile)
    (outcome : (PrimitiveMachine compiled).Outcome) :
    outcome ∈ (completed.game.outcomeKernel σ).support ↔
      some outcome ∈ (completed.optionOutcomeKernel σ).support := by
  classical
  change
    outcome ∈
        (eraseNonePMF (completed.optionOutcomeKernel σ)
          (fun result hresult =>
            completed.optionOutcomeKernel_support_some σ hresult)).support ↔
      some outcome ∈ (completed.optionOutcomeKernel σ).support
  exact mem_support_eraseNonePMF_iff

/-- Pointwise kernel correspondence for completed pure-strategy games: erasing
the cutoff branch leaves exactly the probability mass at `some outcome`. -/
theorem outcomeKernel_apply
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (σ : completed.game.Profile)
    (outcome : (PrimitiveMachine compiled).Outcome) :
    completed.game.outcomeKernel σ outcome =
      completed.optionOutcomeKernel σ (some outcome) := by
  classical
  change
    eraseNonePMF (completed.optionOutcomeKernel σ)
        (fun result hresult =>
          completed.optionOutcomeKernel_support_some σ hresult) outcome =
      completed.optionOutcomeKernel σ (some outcome)
  exact eraseNonePMF_apply outcome

/-- Utility distributions agree between the concrete completed pure-strategy
game and the option-valued bounded game for any cutoff policy. -/
theorem utilityDistribution_eq_optionUtilityDistribution
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (σ : completed.game.Profile) (who : P) (cutoff : Payoff P) :
    PMF.map (fun outcome => (PrimitiveMachine compiled).utility outcome who)
        (completed.game.outcomeKernel σ) =
      PMF.map
        (fun result =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine compiled) cutoff result who)
        (completed.optionOutcomeKernel σ) := by
  classical
  change
    PMF.map (fun outcome => (PrimitiveMachine compiled).utility outcome who)
      (eraseNonePMF (completed.optionOutcomeKernel σ)
        (fun result hresult =>
          completed.optionOutcomeKernel_support_some σ hresult)) =
      PMF.map
        (fun result =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine compiled) cutoff result who)
        (completed.optionOutcomeKernel σ)
  convert
    eraseNonePMF_map
      (dist := completed.optionOutcomeKernel σ)
      (htotal := fun result hresult =>
        completed.optionOutcomeKernel_support_some σ hresult)
      (f := fun outcome =>
        (PrimitiveMachine compiled).utility outcome who)
      (fallback := cutoff who) using 2
  funext result
  cases result <;> rfl

/-- Expected utility in the concrete completed pure-strategy game agrees with
the option-valued bounded game for any cutoff policy, because `none` has zero
support. -/
theorem eu_eq_optionKernel_expect
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (σ : completed.game.Profile) (who : P) (cutoff : Payoff P) {C : ℝ}
    (hbd :
      ∀ outcome, |(PrimitiveMachine compiled).utility outcome who| ≤ C) :
    completed.game.eu σ who =
      Math.Probability.expect (completed.optionOutcomeKernel σ)
        (fun result =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine compiled) cutoff result who) := by
  classical
  change
    Math.Probability.expect
      (eraseNonePMF (completed.optionOutcomeKernel σ)
        (fun result hresult =>
          completed.optionOutcomeKernel_support_some σ hresult))
      (fun outcome => (PrimitiveMachine compiled).utility outcome who) =
      Math.Probability.expect (completed.optionOutcomeKernel σ)
        (fun result =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine compiled) cutoff result who)
  convert
    eraseNonePMF_expect
      (dist := completed.optionOutcomeKernel σ)
      (htotal := fun result hresult =>
        completed.optionOutcomeKernel_support_some σ hresult)
      (utility := fun outcome =>
        (PrimitiveMachine compiled).utility outcome who)
      (cutoff := cutoff who)
      hbd using 2
  funext result
  cases result <;> rfl

/-- Event batches extracted from a completed pure-strategy bounded history are
available primitive machine batches. -/
theorem boundedHistory_eventBatches_availableRun
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (history : (view completed).BoundedHistory (completionBound compiled)) :
    (PrimitiveMachine compiled).AvailableRunBatchesFrom
      ((Machine.BoundedState.init
        (PrimitiveMachine compiled) (completionBound compiled)).state)
      ((view completed).boundedHistoryEventBatches
        (completionBound compiled) history)
      history.lastState.state := by
  exact
    FrontierRoundSemantics.boundedHistory_eventBatches_availableRun
      completed.semantics history

/-- A supported completed pure-strategy outcome is backed by a supported
bounded frontier history with an available primitive batch run, terminal graph
state, and matching primitive-machine outcome. -/
theorem outcomeKernel_support_history
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (σ : completed.game.Profile)
    {outcome : (PrimitiveMachine compiled).Outcome}
    (hsupport : outcome ∈ (completed.game.outcomeKernel σ).support) :
    ∃ history : (view completed).BoundedHistory (completionBound compiled),
      history ∈
        ((view completed).runDist
          (completionBound compiled) (completionBound compiled)
          ((view completed).legalPureToBehavioral
            (completionBound compiled) σ)).support ∧
      EventGraph.Terminal compiled.graph history.lastState.state.1 ∧
      (PrimitiveMachine compiled).outcome history.lastState.state =
        some outcome ∧
      (PrimitiveMachine compiled).AvailableRunBatchesFrom
        ((Machine.BoundedState.init
          (PrimitiveMachine compiled) (completionBound compiled)).state)
        ((view completed).boundedHistoryEventBatches
          (completionBound compiled) history)
        history.lastState.state := by
  classical
  letI :
      ∀ node : Fin compiled.graph.nodeCount,
        Fintype (L.Val (compiled.graph.nodeRow node).ty) :=
    completed.nodeFintype
  letI :
      ∀ player,
        Fintype (Option
          ((frontierRoundView compiled presentation completed.semantics).Act
            player)) := by
    intro player
    dsimp [frontierRoundView, EventGraph.frontierRoundView]
    infer_instance
  have hsome :
      some outcome ∈ (completed.optionOutcomeKernel σ).support :=
    (completed.outcomeKernel_support_iff σ outcome).1 hsupport
  simpa [optionOutcomeKernel, view] using
    FrontierRoundSemantics.boundedOutcomeFromPure_support_history_completionBound
      completed.semantics σ hsome

/-- Every supported completed pure-strategy frontier round strictly advances
the completed-node downset. -/
theorem boundedStep_done_ssubset
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (step : (view completed).BoundedStep (completionBound compiled)) :
    step.src.state.1.done ⊂ step.dst.state.1.done :=
  FrontierRoundSemantics.boundedStep_done_ssubset
    completed.semantics step

/-- A completed pure-strategy history with one round per graph node is
terminal. -/
theorem boundedHistory_terminal_of_length_completionBound
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (history : (view completed).BoundedHistory (completionBound compiled))
    (hlen : history.steps.length = completionBound compiled) :
    EventGraph.Terminal compiled.graph history.lastState.state.1 :=
  FrontierRoundSemantics.boundedHistory_terminal_of_length_completionBound
    completed.semantics history hlen

/-- The completed pure-strategy history induces a checkpoint history for the
attached presentation. -/
noncomputable def boundedHistory_checkpointHistory
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (history : (view completed).BoundedHistory (completionBound compiled)) :
    presentation.History
      ((Machine.BoundedState.init
        (PrimitiveMachine compiled) (completionBound compiled)).state)
      history.lastState.state :=
  FrontierRoundSemantics.boundedHistory_checkpointHistory
    completed.semantics history

/-- The checkpoint history induced by a completed pure-strategy history has the
same public observations as the frontier-round history. -/
theorem boundedHistory_checkpointHistory_publicView
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (history : (view completed).BoundedHistory (completionBound compiled)) :
    (completed.boundedHistory_checkpointHistory history).publicView =
      history.publicView := by
  exact
    FrontierRoundSemantics.boundedHistory_checkpointHistory_publicView
      completed.semantics history

/-- The checkpoint history induced by a completed pure-strategy history has the
same per-player checkpoint observations as the frontier-round information
state. -/
theorem boundedHistory_checkpointHistory_playerView
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (history : (view completed).BoundedHistory (completionBound compiled))
    (player : P) :
    (completed.boundedHistory_checkpointHistory history).playerView player =
      (Machine.RoundView.InfoState.observationEvents
        (history.playerView player)).map Prod.fst := by
  exact
    FrontierRoundSemantics.boundedHistory_checkpointHistory_playerView
      completed.semantics history player

end CompletedFrontierPureKernelGame

/-- Behavioral-strategy frontier game with the impossible cutoff branch erased
from the exposed kernel-game outcome type. -/
structure CompletedFrontierBehavioralKernelGame
    (compiled : CompiledProgram P L)
    (presentation : EventGraph.CheckpointPresentation compiled.graph) where
  semantics : FrontierRoundSemantics compiled presentation
  nodeFintype :
    (node : Fin compiled.graph.nodeCount) →
      Fintype (L.Val (compiled.graph.nodeRow node).ty)

namespace CompletedFrontierBehavioralKernelGame

variable {compiled : CompiledProgram P L}
variable {presentation : EventGraph.CheckpointPresentation compiled.graph}

noncomputable def view
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation) :
    (PrimitiveMachine compiled).RoundView :=
  frontierRoundView compiled presentation completed.semantics

@[reducible] private noncomputable def optionalMoveFintype
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation) :
    ∀ player, Fintype (Option ((view completed).Act player)) := by
  classical
  letI :
      ∀ node : Fin compiled.graph.nodeCount,
        Fintype (L.Val (compiled.graph.nodeRow node).ty) :=
    completed.nodeFintype
  intro player
  dsimp [view, frontierRoundView, EventGraph.frontierRoundView]
  infer_instance

private noncomputable instance instOptionalMoveFintype
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation) :
    ∀ player, Fintype (Option ((view completed).Act player)) :=
  optionalMoveFintype completed

noncomputable def optionOutcomeKernel
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation) :
    (∀ player, (view completed).BoundedBehavioralStrategy
      (completionBound compiled) player) →
      PMF (Option (PrimitiveMachine compiled).Outcome) :=
  by
    classical
    letI := optionalMoveFintype completed
    exact fun σ =>
      (view completed).boundedOutcomeFromBehavioral
        (completionBound compiled) σ (completionBound compiled)

theorem optionOutcomeKernel_support_some
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (σ :
      ∀ player, (view completed).BoundedBehavioralStrategy
        (completionBound compiled) player)
    {result : Option (PrimitiveMachine compiled).Outcome}
    (hsupport :
      result ∈ (completed.optionOutcomeKernel σ).support) :
    ∃ outcome, result = some outcome := by
  classical
  letI :
      ∀ player,
        Fintype (Option
          ((frontierRoundView compiled presentation completed.semantics).Act
            player)) :=
    optionalMoveFintype completed
  simpa [optionOutcomeKernel, view] using
    FrontierRoundSemantics.boundedOutcomeFromBehavioral_support_some_completionBound
      completed.semantics σ hsupport

/-- Concrete-outcome kernel game associated with a completed behavioral
frontier game. The option-valued bounded kernel is total by
`optionOutcomeKernel_support_some`; `eraseNonePMF` removes the impossible
`none` branch. -/
noncomputable def game
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation) :
    KernelGame P := by
  classical
  letI := optionalMoveFintype completed
  exact
    { Strategy := fun player =>
        (view completed).BoundedBehavioralStrategy
          (completionBound compiled) player
      Outcome := (PrimitiveMachine compiled).Outcome
      utility := (PrimitiveMachine compiled).utility
      outcomeKernel := fun σ =>
        eraseNonePMF (completed.optionOutcomeKernel σ)
          (fun result hresult =>
            completed.optionOutcomeKernel_support_some σ hresult) }

theorem none_not_mem_outcomeKernel_support
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (σ : completed.game.Profile) :
    none ∉ (completed.optionOutcomeKernel σ).support := by
  intro hnone
  rcases completed.optionOutcomeKernel_support_some σ hnone with
    ⟨outcome, houtcome⟩
  cases houtcome

/-- The completed behavioral-strategy game erases only the impossible cutoff
branch: concrete outcome support is exactly option-outcome support at `some`. -/
theorem outcomeKernel_support_iff
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (σ : completed.game.Profile)
    (outcome : (PrimitiveMachine compiled).Outcome) :
    outcome ∈ (completed.game.outcomeKernel σ).support ↔
      some outcome ∈ (completed.optionOutcomeKernel σ).support := by
  classical
  change
    outcome ∈
        (eraseNonePMF (completed.optionOutcomeKernel σ)
          (fun result hresult =>
            completed.optionOutcomeKernel_support_some σ hresult)).support ↔
      some outcome ∈ (completed.optionOutcomeKernel σ).support
  exact mem_support_eraseNonePMF_iff

/-- Pointwise kernel correspondence for completed behavioral-strategy games:
erasing the cutoff branch leaves exactly the probability mass at
`some outcome`. -/
theorem outcomeKernel_apply
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (σ : completed.game.Profile)
    (outcome : (PrimitiveMachine compiled).Outcome) :
    completed.game.outcomeKernel σ outcome =
      completed.optionOutcomeKernel σ (some outcome) := by
  classical
  change
    eraseNonePMF (completed.optionOutcomeKernel σ)
        (fun result hresult =>
          completed.optionOutcomeKernel_support_some σ hresult) outcome =
      completed.optionOutcomeKernel σ (some outcome)
  exact eraseNonePMF_apply outcome

/-- Utility distributions agree between the concrete completed behavioral
game and the option-valued bounded game for any cutoff policy. -/
theorem utilityDistribution_eq_optionUtilityDistribution
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (σ : completed.game.Profile) (who : P) (cutoff : Payoff P) :
    PMF.map (fun outcome => (PrimitiveMachine compiled).utility outcome who)
        (completed.game.outcomeKernel σ) =
      PMF.map
        (fun result =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine compiled) cutoff result who)
        (completed.optionOutcomeKernel σ) := by
  classical
  change
    PMF.map (fun outcome => (PrimitiveMachine compiled).utility outcome who)
      (eraseNonePMF (completed.optionOutcomeKernel σ)
        (fun result hresult =>
          completed.optionOutcomeKernel_support_some σ hresult)) =
      PMF.map
        (fun result =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine compiled) cutoff result who)
        (completed.optionOutcomeKernel σ)
  convert
    eraseNonePMF_map
      (dist := completed.optionOutcomeKernel σ)
      (htotal := fun result hresult =>
        completed.optionOutcomeKernel_support_some σ hresult)
      (f := fun outcome =>
        (PrimitiveMachine compiled).utility outcome who)
      (fallback := cutoff who) using 2
  funext result
  cases result <;> rfl

/-- Expected utility in the concrete completed behavioral-strategy game agrees
with the option-valued bounded game for any cutoff policy, because `none` has
zero support. -/
theorem eu_eq_optionKernel_expect
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (σ : completed.game.Profile) (who : P) (cutoff : Payoff P) {C : ℝ}
    (hbd :
      ∀ outcome, |(PrimitiveMachine compiled).utility outcome who| ≤ C) :
    completed.game.eu σ who =
      Math.Probability.expect (completed.optionOutcomeKernel σ)
        (fun result =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine compiled) cutoff result who) := by
  classical
  change
    Math.Probability.expect
      (eraseNonePMF (completed.optionOutcomeKernel σ)
        (fun result hresult =>
          completed.optionOutcomeKernel_support_some σ hresult))
      (fun outcome => (PrimitiveMachine compiled).utility outcome who) =
      Math.Probability.expect (completed.optionOutcomeKernel σ)
        (fun result =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine compiled) cutoff result who)
  convert
    eraseNonePMF_expect
      (dist := completed.optionOutcomeKernel σ)
      (htotal := fun result hresult =>
        completed.optionOutcomeKernel_support_some σ hresult)
      (utility := fun outcome =>
        (PrimitiveMachine compiled).utility outcome who)
      (cutoff := cutoff who)
      hbd using 2
  funext result
  cases result <;> rfl

/-- Event batches extracted from a completed behavioral-strategy bounded
history are available primitive machine batches. -/
theorem boundedHistory_eventBatches_availableRun
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (history : (view completed).BoundedHistory (completionBound compiled)) :
    (PrimitiveMachine compiled).AvailableRunBatchesFrom
      ((Machine.BoundedState.init
        (PrimitiveMachine compiled) (completionBound compiled)).state)
      ((view completed).boundedHistoryEventBatches
        (completionBound compiled) history)
      history.lastState.state := by
  exact
    FrontierRoundSemantics.boundedHistory_eventBatches_availableRun
      completed.semantics history

/-- A supported completed behavioral-strategy outcome is backed by a supported
bounded frontier history with an available primitive batch run, terminal graph
state, and matching primitive-machine outcome. -/
theorem outcomeKernel_support_history
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (σ : completed.game.Profile)
    {outcome : (PrimitiveMachine compiled).Outcome}
    (hsupport : outcome ∈ (completed.game.outcomeKernel σ).support) :
    ∃ history : (view completed).BoundedHistory (completionBound compiled),
      history ∈
        ((view completed).runDist
          (completionBound compiled) (completionBound compiled) σ).support ∧
      EventGraph.Terminal compiled.graph history.lastState.state.1 ∧
      (PrimitiveMachine compiled).outcome history.lastState.state =
        some outcome ∧
      (PrimitiveMachine compiled).AvailableRunBatchesFrom
        ((Machine.BoundedState.init
          (PrimitiveMachine compiled) (completionBound compiled)).state)
        ((view completed).boundedHistoryEventBatches
          (completionBound compiled) history)
        history.lastState.state := by
  classical
  letI :
      ∀ node : Fin compiled.graph.nodeCount,
        Fintype (L.Val (compiled.graph.nodeRow node).ty) :=
    completed.nodeFintype
  letI :
      ∀ player,
        Fintype (Option
          ((frontierRoundView compiled presentation completed.semantics).Act
            player)) := by
    intro player
    dsimp [frontierRoundView, EventGraph.frontierRoundView]
    infer_instance
  have hsome :
      some outcome ∈ (completed.optionOutcomeKernel σ).support :=
    (completed.outcomeKernel_support_iff σ outcome).1 hsupport
  simpa [optionOutcomeKernel, view] using
    FrontierRoundSemantics.boundedOutcomeFromBehavioral_support_history_completionBound
      completed.semantics σ hsome

/-- Every supported completed behavioral-strategy frontier round strictly
advances the completed-node downset. -/
theorem boundedStep_done_ssubset
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (step : (view completed).BoundedStep (completionBound compiled)) :
    step.src.state.1.done ⊂ step.dst.state.1.done :=
  FrontierRoundSemantics.boundedStep_done_ssubset
    completed.semantics step

/-- A completed behavioral-strategy history with one round per graph node is
terminal. -/
theorem boundedHistory_terminal_of_length_completionBound
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (history : (view completed).BoundedHistory (completionBound compiled))
    (hlen : history.steps.length = completionBound compiled) :
    EventGraph.Terminal compiled.graph history.lastState.state.1 :=
  FrontierRoundSemantics.boundedHistory_terminal_of_length_completionBound
    completed.semantics history hlen

/-- The completed behavioral-strategy history induces a checkpoint history for
the attached presentation. -/
noncomputable def boundedHistory_checkpointHistory
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (history : (view completed).BoundedHistory (completionBound compiled)) :
    presentation.History
      ((Machine.BoundedState.init
        (PrimitiveMachine compiled) (completionBound compiled)).state)
      history.lastState.state :=
  FrontierRoundSemantics.boundedHistory_checkpointHistory
    completed.semantics history

/-- The checkpoint history induced by a completed behavioral-strategy history
has the same public observations as the frontier-round history. -/
theorem boundedHistory_checkpointHistory_publicView
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (history : (view completed).BoundedHistory (completionBound compiled)) :
    (completed.boundedHistory_checkpointHistory history).publicView =
      history.publicView := by
  exact
    FrontierRoundSemantics.boundedHistory_checkpointHistory_publicView
      completed.semantics history

/-- The checkpoint history induced by a completed behavioral-strategy history
has the same per-player checkpoint observations as the frontier-round
information state. -/
theorem boundedHistory_checkpointHistory_playerView
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (history : (view completed).BoundedHistory (completionBound compiled))
    (player : P) :
    (completed.boundedHistory_checkpointHistory history).playerView player =
      (Machine.RoundView.InfoState.observationEvents
        (history.playerView player)).map Prod.fst := by
  exact
    FrontierRoundSemantics.boundedHistory_checkpointHistory_playerView
      completed.semantics history player

end CompletedFrontierBehavioralKernelGame

/-- Default pure-strategy frontier game for a finite checked program. The
exposed `.game` has concrete outcomes, not optional outcomes. -/
noncomputable def canonicalFrontierPureKernelGame
    (program : WFProgram P L) [FiniteDomains program] :
    CompletedFrontierPureKernelGame (ToEventGraph.compile program.core)
      (frontierPresentation
        (ToEventGraph.compile program.core)
        (ToEventGraph.compile_guardLive program)) := by
  classical
  let compiled := ToEventGraph.compile program.core
  let presentation :=
    frontierPresentation compiled
      (ToEventGraph.compile_guardLive program)
  let semantics :=
    canonicalFrontierRoundSemantics compiled
      (ToEventGraph.compile_guardLive program)
  letI :
      ∀ node : Fin compiled.graph.nodeCount,
        Fintype (L.Val (compiled.graph.nodeRow node).ty) :=
    ToEventGraph.compile_nodeFintype program
  exact
    { semantics := semantics
      nodeFintype := ToEventGraph.compile_nodeFintype program }

/-- Default behavioral-strategy frontier game for a finite checked program.
The exposed `.game` has concrete outcomes, not optional outcomes. -/
noncomputable def canonicalFrontierBehavioralKernelGame
    (program : WFProgram P L) [FiniteDomains program] :
    CompletedFrontierBehavioralKernelGame (ToEventGraph.compile program.core)
      (frontierPresentation
        (ToEventGraph.compile program.core)
        (ToEventGraph.compile_guardLive program)) := by
  classical
  let compiled := ToEventGraph.compile program.core
  let presentation :=
    frontierPresentation compiled
      (ToEventGraph.compile_guardLive program)
  let semantics :=
    canonicalFrontierRoundSemantics compiled
      (ToEventGraph.compile_guardLive program)
  letI :
      ∀ node : Fin compiled.graph.nodeCount,
        Fintype (L.Val (compiled.graph.nodeRow node).ty) :=
    ToEventGraph.compile_nodeFintype program
  exact
    { semantics := semantics
      nodeFintype := ToEventGraph.compile_nodeFintype program }

/-- A supported default pure frontier transition lands at an internal-closed
checkpoint. -/
theorem canonicalFrontierPureKernelGame_transition_support_closed
    (program : WFProgram P L) [FiniteDomains program]
    {state dst : (PrimitiveMachine (ToEventGraph.compile program.core)).State}
    (action :
      {a : JointAction (FrontierAct (ToEventGraph.compile program.core)) //
        JointActionLegal
          (FrontierAct (ToEventGraph.compile program.core))
          (frontierActive (ToEventGraph.compile program.core))
          (PrimitiveMachine (ToEventGraph.compile program.core)).terminal
          (frontierAvailableActions (ToEventGraph.compile program.core))
          state a})
    (hsupport :
      (canonicalFrontierPureKernelGame program).semantics.transition
        state action dst ≠ 0) :
    EventGraph.readyInternalNodes
        (ToEventGraph.compile program.core).graph dst.1 = ∅ := by
  simpa [canonicalFrontierPureKernelGame] using
    canonicalFrontierRoundSemantics_transition_support_closed
      (ToEventGraph.compile program.core)
      (ToEventGraph.compile_guardLive program)
      action hsupport

/-- A supported default behavioral frontier transition lands at an
internal-closed checkpoint. -/
theorem canonicalFrontierBehavioralKernelGame_transition_support_closed
    (program : WFProgram P L) [FiniteDomains program]
    {state dst : (PrimitiveMachine (ToEventGraph.compile program.core)).State}
    (action :
      {a : JointAction (FrontierAct (ToEventGraph.compile program.core)) //
        JointActionLegal
          (FrontierAct (ToEventGraph.compile program.core))
          (frontierActive (ToEventGraph.compile program.core))
          (PrimitiveMachine (ToEventGraph.compile program.core)).terminal
          (frontierAvailableActions (ToEventGraph.compile program.core))
          state a})
    (hsupport :
      (canonicalFrontierBehavioralKernelGame program).semantics.transition
        state action dst ≠ 0) :
    EventGraph.readyInternalNodes
        (ToEventGraph.compile program.core).graph dst.1 = ∅ := by
  simpa [canonicalFrontierBehavioralKernelGame] using
    canonicalFrontierRoundSemantics_transition_support_closed
      (ToEventGraph.compile program.core)
      (ToEventGraph.compile_guardLive program)
      action hsupport

namespace FrontierPureKernelGame

variable {compiled : CompiledProgram P L}
variable {presentation : EventGraph.CheckpointPresentation compiled.graph}

/-- The round view certified by this pure-strategy kernel game. -/
noncomputable def view
    (game : FrontierPureKernelGame compiled presentation) :
    (PrimitiveMachine compiled).RoundView :=
  frontierRoundView compiled presentation game.semantics

/-- Event batches extracted from a certified pure-strategy bounded history are
available primitive machine batches. -/
theorem boundedHistory_eventBatches_availableRun
    (game : FrontierPureKernelGame compiled presentation)
    (history : game.view.BoundedHistory game.horizon) :
    (PrimitiveMachine compiled).AvailableRunBatchesFrom
      ((Machine.BoundedState.init
        (PrimitiveMachine compiled) game.horizon).state)
      (game.view.boundedHistoryEventBatches game.horizon history)
      history.lastState.state := by
  exact
    FrontierRoundSemantics.boundedHistory_eventBatches_availableRun
      game.semantics history

/-- Every supported bounded frontier round of this pure-strategy game strictly
advances the completed-node downset. -/
theorem boundedStep_done_ssubset
    (game : FrontierPureKernelGame compiled presentation)
    (step : game.view.BoundedStep game.horizon) :
    step.src.state.1.done ⊂ step.dst.state.1.done :=
  FrontierRoundSemantics.boundedStep_done_ssubset
    game.semantics step

/-- A pure-strategy game history with one round per graph node is terminal. -/
theorem boundedHistory_terminal_of_length_completionBound
    (game : FrontierPureKernelGame compiled presentation)
    (history : game.view.BoundedHistory game.horizon)
    (hlen : history.steps.length = completionBound compiled) :
    EventGraph.Terminal compiled.graph history.lastState.state.1 :=
  FrontierRoundSemantics.boundedHistory_terminal_of_length_completionBound
    game.semantics history hlen

/-- The bounded strategic history of this pure-strategy game induces a
checkpoint history for the attached presentation. -/
noncomputable def boundedHistory_checkpointHistory
    (game : FrontierPureKernelGame compiled presentation)
    (history : game.view.BoundedHistory game.horizon) :
    presentation.History
      ((Machine.BoundedState.init
        (PrimitiveMachine compiled) game.horizon).state)
      history.lastState.state :=
  FrontierRoundSemantics.boundedHistory_checkpointHistory
    game.semantics history

/-- The checkpoint history induced by a certified pure-strategy history has
the same public observations as the frontier-round history. -/
theorem boundedHistory_checkpointHistory_publicView
    (game : FrontierPureKernelGame compiled presentation)
    (history : game.view.BoundedHistory game.horizon) :
    (game.boundedHistory_checkpointHistory history).publicView =
      history.publicView := by
  exact
    FrontierRoundSemantics.boundedHistory_checkpointHistory_publicView
      game.semantics history

/-- The checkpoint history induced by a certified pure-strategy history has
the same per-player checkpoint observations as the frontier-round information
state. -/
theorem boundedHistory_checkpointHistory_playerView
    (game : FrontierPureKernelGame compiled presentation)
    (history : game.view.BoundedHistory game.horizon)
    (player : P) :
    (game.boundedHistory_checkpointHistory history).playerView player =
      (Machine.RoundView.InfoState.observationEvents
        (history.playerView player)).map Prod.fst := by
  exact
    FrontierRoundSemantics.boundedHistory_checkpointHistory_playerView
      game.semantics history player

end FrontierPureKernelGame

namespace FrontierBehavioralKernelGame

variable {compiled : CompiledProgram P L}
variable {presentation : EventGraph.CheckpointPresentation compiled.graph}

/-- The round view certified by this behavioral-strategy kernel game. -/
noncomputable def view
    (game : FrontierBehavioralKernelGame compiled presentation) :
    (PrimitiveMachine compiled).RoundView :=
  frontierRoundView compiled presentation game.semantics

/-- Event batches extracted from a certified behavioral-strategy bounded
history are available primitive machine batches. -/
theorem boundedHistory_eventBatches_availableRun
    (game : FrontierBehavioralKernelGame compiled presentation)
    (history : game.view.BoundedHistory game.horizon) :
    (PrimitiveMachine compiled).AvailableRunBatchesFrom
      ((Machine.BoundedState.init
        (PrimitiveMachine compiled) game.horizon).state)
      (game.view.boundedHistoryEventBatches game.horizon history)
      history.lastState.state := by
  exact
    FrontierRoundSemantics.boundedHistory_eventBatches_availableRun
      game.semantics history

/-- Every supported bounded frontier round of this behavioral-strategy game
strictly advances the completed-node downset. -/
theorem boundedStep_done_ssubset
    (game : FrontierBehavioralKernelGame compiled presentation)
    (step : game.view.BoundedStep game.horizon) :
    step.src.state.1.done ⊂ step.dst.state.1.done :=
  FrontierRoundSemantics.boundedStep_done_ssubset
    game.semantics step

/-- A behavioral-strategy game history with one round per graph node is
terminal. -/
theorem boundedHistory_terminal_of_length_completionBound
    (game : FrontierBehavioralKernelGame compiled presentation)
    (history : game.view.BoundedHistory game.horizon)
    (hlen : history.steps.length = completionBound compiled) :
    EventGraph.Terminal compiled.graph history.lastState.state.1 :=
  FrontierRoundSemantics.boundedHistory_terminal_of_length_completionBound
    game.semantics history hlen

/-- The bounded strategic history of this behavioral-strategy game induces a
checkpoint history for the attached presentation. -/
noncomputable def boundedHistory_checkpointHistory
    (game : FrontierBehavioralKernelGame compiled presentation)
    (history : game.view.BoundedHistory game.horizon) :
    presentation.History
      ((Machine.BoundedState.init
        (PrimitiveMachine compiled) game.horizon).state)
      history.lastState.state :=
  FrontierRoundSemantics.boundedHistory_checkpointHistory
    game.semantics history

/-- The checkpoint history induced by a certified behavioral-strategy history
has the same public observations as the frontier-round history. -/
theorem boundedHistory_checkpointHistory_publicView
    (game : FrontierBehavioralKernelGame compiled presentation)
    (history : game.view.BoundedHistory game.horizon) :
    (game.boundedHistory_checkpointHistory history).publicView =
      history.publicView := by
  exact
    FrontierRoundSemantics.boundedHistory_checkpointHistory_publicView
      game.semantics history

/-- The checkpoint history induced by a certified behavioral-strategy history
has the same per-player checkpoint observations as the frontier-round
information state. -/
theorem boundedHistory_checkpointHistory_playerView
    (game : FrontierBehavioralKernelGame compiled presentation)
    (history : game.view.BoundedHistory game.horizon)
    (player : P) :
    (game.boundedHistory_checkpointHistory history).playerView player =
      (Machine.RoundView.InfoState.observationEvents
        (history.playerView player)).map Prod.fst := by
  exact
    FrontierRoundSemantics.boundedHistory_checkpointHistory_playerView
      game.semantics history player

end FrontierBehavioralKernelGame


end ToEventGraph

end Vegas
