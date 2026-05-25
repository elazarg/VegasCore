import Vegas.Core.ToEventGraph.RoundView
import Vegas.Machine.Kuhn

/-!
# Kuhn-facing facts for compiled event graphs

The generic Kuhn proof adapter lives at `Machine.RoundView`.  This module
records the event-graph facts needed to instantiate that adapter for compiled
frontier games.
-/

namespace Vegas

namespace ToEventGraph

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Compiled frontier round views have observable menus. -/
theorem frontierRoundView_menusObservable
    (compiled : CompiledProgram P L)
    (presentation : EventGraph.CheckpointPresentation compiled.graph)
    (semantics : FrontierRoundSemantics compiled presentation)
    (horizon : Nat) :
    (frontierRoundView compiled presentation semantics).MenusObservable
      horizon :=
  EventGraph.frontierRoundView_menusObservable
    (primitiveMachineSpec compiled) presentation semantics horizon

/-- The canonical completed pure frontier game has observable menus at its
completion horizon. -/
theorem canonicalFrontierPure_menusObservable
    (program : WFProgram P L) [FiniteDomains program] :
    ((canonicalFrontierPureKernelGame program).view).MenusObservable
      (completionBound (compile program.core)) := by
  simpa [CompletedFrontierPureKernelGame.view,
    canonicalFrontierPureKernelGame] using
    frontierRoundView_menusObservable
      (compile program.core)
      (frontierPresentation
        (compile program.core)
        (compile_guardLive program))
      (canonicalFrontierRoundSemantics
        (compile program.core)
        (compile_guardLive program))
      (completionBound (compile program.core))

/-- The canonical completed behavioral frontier game has observable menus at
its completion horizon. -/
theorem canonicalFrontierBehavioral_menusObservable
    (program : WFProgram P L) [FiniteDomains program] :
    ((canonicalFrontierBehavioralKernelGame program).view).MenusObservable
      (completionBound (compile program.core)) := by
  simpa [CompletedFrontierBehavioralKernelGame.view,
    canonicalFrontierBehavioralKernelGame] using
    frontierRoundView_menusObservable
      (compile program.core)
      (frontierPresentation
        (compile program.core)
        (compile_guardLive program))
      (canonicalFrontierRoundSemantics
        (compile program.core)
        (compile_guardLive program))
      (completionBound (compile program.core))

structure CompletedFrontierKuhnGames
    (compiled : CompiledProgram P L)
    (presentation : EventGraph.CheckpointPresentation compiled.graph) where
  semantics : FrontierRoundSemantics compiled presentation
  nodeFintype :
    (node : Fin compiled.graph.nodeCount) →
      Fintype (L.Val (compiled.graph.nodeRow node).ty)
  fieldFintype :
    (field : Fin compiled.graph.fieldCount) →
      Fintype (L.Val (compiled.graph.fieldRow field).ty)

namespace CompletedFrontierKuhnGames

variable {compiled : CompiledProgram P L}
variable {presentation : EventGraph.CheckpointPresentation compiled.graph}

noncomputable def pure
    (games : CompletedFrontierKuhnGames compiled presentation) :
    CompletedFrontierPureKernelGame compiled presentation where
  semantics := games.semantics
  nodeFintype := games.nodeFintype

noncomputable def behavioral
    (games : CompletedFrontierKuhnGames compiled presentation) :
    CompletedFrontierBehavioralKernelGame compiled presentation where
  semantics := games.semantics
  nodeFintype := games.nodeFintype

noncomputable def view
    (games : CompletedFrontierKuhnGames compiled presentation) :
    (PrimitiveMachine compiled).RoundView :=
  frontierRoundView compiled presentation games.semantics

/-- The native frontier round view keeps an operational replay certificate for
every supported strategic transition. -/
theorem view_operationallyCertified
    (games : CompletedFrontierKuhnGames compiled presentation) :
    games.view.OperationallyCertified :=
  FrontierRoundSemantics.view_operationallyCertified games.semantics

@[reducible]
noncomputable def kuhnOptionalMoveFintype
    (games : CompletedFrontierKuhnGames compiled presentation) :
    ∀ player, Fintype (Option ((games.view).Act player)) := by
  classical
  letI :
      ∀ node : Fin compiled.graph.nodeCount,
        Fintype (L.Val (compiled.graph.nodeRow node).ty) :=
    games.nodeFintype
  intro player
  dsimp [view, frontierRoundView, EventGraph.frontierRoundView]
  infer_instance

noncomputable instance instKuhnOptionalMoveFintype
    (games : CompletedFrontierKuhnGames compiled presentation)
    (player : P) :
    Fintype (Option ((games.view).Act player)) :=
  games.kuhnOptionalMoveFintype player

/-- Completed frontier pure games have finite pure-strategy carriers when
graph field and node value domains are finite. This is the finite analysis
surface used before transporting results to behavioral strategies by Kuhn. -/
@[reducible]
noncomputable def pureStrategyFintype
    (games : CompletedFrontierKuhnGames compiled presentation)
    (player : P) :
    Fintype (games.pure.game.Strategy player) := by
  classical
  let horizon := completionBound compiled
  let view := games.view
  letI :
      ∀ node : Fin compiled.graph.nodeCount,
        Fintype (L.Val (compiled.graph.nodeRow node).ty) :=
    games.nodeFintype
  letI :
      ∀ field : Fin compiled.graph.fieldCount,
        Fintype (L.Val (compiled.graph.fieldRow field).ty) :=
    games.fieldFintype
  letI : Fintype (EventGraph.PublicObservation compiled.graph) :=
    inferInstance
  letI : Fintype (EventGraph.Observation compiled.graph player) :=
    inferInstance
  letI : Fintype (EventGraph.FrontierAction compiled.graph player) :=
    inferInstance
  letI :
      Fintype
        ((EventGraph.PrimitiveMachineOf
          (primitiveMachineSpec compiled)).Public) := by
    dsimp [EventGraph.PrimitiveMachineOf, primitiveMachineSpec,
      EventGraph.ToMachine.primitiveMachine]
    infer_instance
  letI :
      Fintype
        ((EventGraph.PrimitiveMachineOf
          (primitiveMachineSpec compiled)).Obs player) := by
    dsimp [EventGraph.PrimitiveMachineOf, primitiveMachineSpec,
      EventGraph.ToMachine.primitiveMachine]
    infer_instance
  letI : Fintype (view.Act player) := by
    dsimp [view, CompletedFrontierKuhnGames.view, frontierRoundView,
      EventGraph.frontierRoundView]
    infer_instance
  letI : Fintype (Option (view.Act player)) := inferInstance
  letI : Fintype (Machine.RoundView.PlayerEvent view player) :=
    Machine.RoundView.PlayerEvent.instFintype
  letI : Fintype (view.ReachableInfoState horizon player) :=
    view.instFintypeReachableInfoStateOfFinitePlayerEvent horizon player
  change
    Fintype
      { σ : view.ReachableInfoState horizon player →
            Option (view.Act player) //
        view.IsLegalReachablePureStrategy horizon player σ }
  infer_instance

/-- Finiteness property for the Kuhn adapter information states of a completed
frontier game.  This is proved from the finite graph observation/action
surface, not from finiteness of the raw machine state. -/
def KuhnInfoFinite
    (games : CompletedFrontierKuhnGames compiled presentation)
    (horizon : Nat)
    (hMenus : games.view.MenusObservable horizon) : Prop :=
  ∀ player,
    Finite (((games.view).kuhnModel horizon hMenus).InfoState player)

/-- Completed frontier Kuhn games have finite Kuhn information states whenever
the graph field and node value domains are finite. -/
noncomputable def kuhnInfoFinite
    (games : CompletedFrontierKuhnGames compiled presentation)
    (horizon : Nat)
    (hMenus : games.view.MenusObservable horizon) :
    games.KuhnInfoFinite horizon hMenus := by
  classical
  intro player
  let view := games.view
  letI :
      ∀ node : Fin compiled.graph.nodeCount,
        Fintype (L.Val (compiled.graph.nodeRow node).ty) :=
    games.nodeFintype
  letI :
      ∀ field : Fin compiled.graph.fieldCount,
        Fintype (L.Val (compiled.graph.fieldRow field).ty) :=
    games.fieldFintype
  letI : Fintype (EventGraph.PublicObservation compiled.graph) :=
    inferInstance
  letI : Fintype (EventGraph.Observation compiled.graph player) :=
    inferInstance
  letI : Fintype (EventGraph.FrontierAction compiled.graph player) :=
    inferInstance
  letI :
      Fintype
        ((EventGraph.PrimitiveMachineOf
          (primitiveMachineSpec compiled)).Public) := by
    dsimp [EventGraph.PrimitiveMachineOf, primitiveMachineSpec,
      EventGraph.ToMachine.primitiveMachine]
    infer_instance
  letI :
      Fintype
        ((EventGraph.PrimitiveMachineOf
          (primitiveMachineSpec compiled)).Obs player) := by
    dsimp [EventGraph.PrimitiveMachineOf, primitiveMachineSpec,
      EventGraph.ToMachine.primitiveMachine]
    infer_instance
  letI :
      Fintype (view.Act player) := by
    dsimp [view, CompletedFrontierKuhnGames.view, frontierRoundView,
      EventGraph.frontierRoundView]
    infer_instance
  letI : Fintype (Machine.RoundView.PlayerEvent view player) := by
    exact Machine.RoundView.PlayerEvent.instFintype
  letI : Fintype (view.ReachableInfoState horizon player) :=
    view.instFintypeReachableInfoStateOfFinitePlayerEvent horizon player
  simpa [KuhnInfoFinite, Machine.RoundView.kuhnModel, view]
    using (Finite.of_fintype (view.ReachableInfoState horizon player))

/-- Canonical behavioral completed-frontier profile realizing a product-mixed
pure profile under the Kuhn mixed-to-behavioral construction. -/
noncomputable def mixedPureToBehavioralProfile_of_menus
    (games : CompletedFrontierKuhnGames compiled presentation)
    (hMenus : games.view.MenusObservable (completionBound compiled))
    (mixed : ∀ player, PMF (games.pure.game.Strategy player)) :
    games.behavioral.game.Profile := by
  classical
  let horizon := completionBound compiled
  let view := games.view
  let mixedView : ∀ player, PMF (view.BoundedPureStrategy horizon player) := by
    simpa [pure, CompletedFrontierPureKernelGame.game,
      CompletedFrontierPureKernelGame.view, view, horizon] using mixed
  letI : ∀ player, Fintype (Option (view.Act player)) :=
    games.kuhnOptionalMoveFintype
  letI :
      ∀ player,
        Finite ((view.kuhnModel horizon hMenus).InfoState player) :=
    games.kuhnInfoFinite horizon hMenus
  simpa [behavioral, CompletedFrontierBehavioralKernelGame.game,
    CompletedFrontierBehavioralKernelGame.view, view, horizon] using
    view.mixedPureToBehavioralProfile horizon hMenus mixedView

/-- Mixed-to-behavioral outcome-kernel realization for completed frontier
games whose strategic views are the same frontier round view, using the
canonical mixed-to-behavioral profile. -/
theorem mixedPureToBehavioralOutcomeKernel_eq_of_menus
    (games : CompletedFrontierKuhnGames compiled presentation)
    (hMenus : games.view.MenusObservable (completionBound compiled))
    (mixed : ∀ player, PMF (games.pure.game.Strategy player)) :
    games.behavioral.game.outcomeKernel
        (games.mixedPureToBehavioralProfile_of_menus hMenus mixed) =
      (Math.PMFProduct.pmfPi mixed).bind
        (fun pureProfile => games.pure.game.outcomeKernel pureProfile) := by
  classical
  let horizon := completionBound compiled
  let view := games.view
  let mixedView : ∀ player, PMF (view.BoundedPureStrategy horizon player) := by
    simpa [pure, CompletedFrontierPureKernelGame.game,
      CompletedFrontierPureKernelGame.view, view, horizon] using mixed
  letI : ∀ player, Fintype (Option (view.Act player)) :=
    games.kuhnOptionalMoveFintype
  letI :
      ∀ player,
        Finite (((view).kuhnModel horizon hMenus).InfoState player) :=
    games.kuhnInfoFinite horizon hMenus
  let behavioralProfile : view.BoundedBehavioralProfile horizon :=
    view.mixedPureToBehavioralProfile horizon hMenus mixedView
  have hbehavioral :
      view.boundedOutcomeFromBehavioral horizon behavioralProfile horizon =
        (Math.PMFProduct.pmfPi mixedView).bind
          (fun pureProfile =>
            view.boundedOutcomeFromPure horizon pureProfile horizon) := by
    simpa [view, horizon] using
      view.mixedPureToBehavioralProfile_optionOutcome
        horizon horizon hMenus mixedView
  apply PMF.ext
  intro outcome
  have hpoint :
      (view.boundedOutcomeFromBehavioral horizon behavioralProfile horizon)
          (some outcome) =
        ((Math.PMFProduct.pmfPi mixed).bind
          (fun pureProfile =>
            view.boundedOutcomeFromPure horizon pureProfile horizon))
          (some outcome) :=
    by
      have hpointView :=
        congrArg (fun dist : PMF (Option (PrimitiveMachine compiled).Outcome) =>
          dist (some outcome)) hbehavioral
      simpa [mixedView, pure, CompletedFrontierPureKernelGame.game,
        CompletedFrontierPureKernelGame.view, view, horizon] using hpointView
  calc
    games.behavioral.game.outcomeKernel
        (games.mixedPureToBehavioralProfile_of_menus hMenus mixed) outcome
        =
      (view.boundedOutcomeFromBehavioral horizon behavioralProfile horizon)
        (some outcome) := by
          simpa [behavioral, CompletedFrontierBehavioralKernelGame.game,
            CompletedFrontierBehavioralKernelGame.optionOutcomeKernel,
            CompletedFrontierBehavioralKernelGame.view,
            mixedPureToBehavioralProfile_of_menus, behavioralProfile,
            mixedView, view, horizon] using
            games.behavioral.outcomeKernel_apply
              (games.mixedPureToBehavioralProfile_of_menus hMenus mixed)
              outcome
    _ =
      ((Math.PMFProduct.pmfPi mixed).bind
        (fun pureProfile =>
          view.boundedOutcomeFromPure horizon pureProfile horizon))
        (some outcome) := hpoint
    _ =
      ((Math.PMFProduct.pmfPi mixed).bind
        (fun pureProfile => games.pure.game.outcomeKernel pureProfile))
        outcome := by
          rw [PMF.bind_apply, PMF.bind_apply]
          apply tsum_congr
          intro pureProfile
          congr 1
          simpa [pure, CompletedFrontierPureKernelGame.optionOutcomeKernel,
            CompletedFrontierPureKernelGame.view, view, horizon] using
            (games.pure.outcomeKernel_apply pureProfile outcome).symm

open Classical in
/-- Product mixed pure-strategy deviation induced by one completed behavioral
frontier strategy. -/
noncomputable def behavioralStrategyToMixedPure
    (games : CompletedFrontierKuhnGames compiled presentation)
    (hMenus : games.view.MenusObservable (completionBound compiled))
    (who : P)
    (deviation : games.behavioral.game.Strategy who) :
    PMF (games.pure.game.Strategy who) := by
  classical
  let horizon := completionBound compiled
  let view := games.view
  letI : ∀ player, Fintype (Option (view.Act player)) :=
    games.kuhnOptionalMoveFintype
  letI :
      ∀ player,
        Finite ((view.kuhnModel horizon hMenus).InfoState player) :=
    games.kuhnInfoFinite horizon hMenus
  let deviationView : view.BoundedBehavioralStrategy horizon who := by
    simpa [behavioral, CompletedFrontierBehavioralKernelGame.game,
      CompletedFrontierBehavioralKernelGame.view, view, horizon] using
      deviation
  simpa [pure, CompletedFrontierPureKernelGame.game,
    CompletedFrontierPureKernelGame.view, view, horizon] using
    view.behavioralStrategyToMixedPure horizon hMenus who deviationView

open Classical in
/-- Canonical mixed-to-behavioral unilateral-deviation law for completed
frontier games. -/
theorem mixedPureToBehavioralUnilateralDeviationOutcomeKernel_eq_of_menus
    (games : CompletedFrontierKuhnGames compiled presentation)
    (hMenus : games.view.MenusObservable (completionBound compiled))
    (mixed : ∀ player, PMF (games.pure.game.Strategy player))
    (who : P)
    (deviation : games.behavioral.game.Strategy who) :
    let mixedDeviation :=
      games.behavioralStrategyToMixedPure hMenus who deviation
    games.behavioral.game.outcomeKernel
        (Function.update
          (games.mixedPureToBehavioralProfile_of_menus hMenus mixed)
          who deviation) =
      (Math.PMFProduct.pmfPi
        (Function.update mixed who mixedDeviation)).bind
        (fun pureProfile => games.pure.game.outcomeKernel pureProfile) := by
  classical
  let horizon := completionBound compiled
  let view := games.view
  letI : ∀ player, Fintype (Option (view.Act player)) :=
    games.kuhnOptionalMoveFintype
  letI :
      ∀ player,
        Finite ((view.kuhnModel horizon hMenus).InfoState player) :=
    games.kuhnInfoFinite horizon hMenus
  let mixedView : ∀ player, PMF (view.BoundedPureStrategy horizon player) := by
    simpa [pure, CompletedFrontierPureKernelGame.game,
      CompletedFrontierPureKernelGame.view, view, horizon] using mixed
  let deviationView : view.BoundedBehavioralStrategy horizon who := by
    simpa [behavioral, CompletedFrontierBehavioralKernelGame.game,
      CompletedFrontierBehavioralKernelGame.view, view, horizon] using
      deviation
  let mixedDeviationView :=
    view.behavioralStrategyToMixedPure horizon hMenus who deviationView
  let mixedDeviation :=
    games.behavioralStrategyToMixedPure hMenus who deviation
  have hmixedDeviation :
      mixedDeviation = mixedDeviationView := by
    simp [mixedDeviation, behavioralStrategyToMixedPure, mixedDeviationView,
      deviationView, pure, CompletedFrontierPureKernelGame.game,
      CompletedFrontierPureKernelGame.view, view, horizon]
  have hOption :
      view.boundedOutcomeFromBehavioral horizon
          (Function.update
            (view.mixedPureToBehavioralProfile horizon hMenus mixedView)
            who deviationView) horizon =
        (Math.PMFProduct.pmfPi
          (Function.update mixedView who mixedDeviationView)).bind
          (fun pureProfile =>
            view.boundedOutcomeFromPure horizon pureProfile horizon) := by
    simpa [view, horizon, mixedDeviationView] using
      view.mixedPureToBehavioralProfile_unilateral_deviation_optionOutcome
        horizon horizon hMenus mixedView who deviationView
  apply PMF.ext
  intro outcome
  have hpoint :
      (view.boundedOutcomeFromBehavioral horizon
          (Function.update
            (view.mixedPureToBehavioralProfile horizon hMenus mixedView)
            who deviationView) horizon) (some outcome) =
        ((Math.PMFProduct.pmfPi
          (Function.update mixedView who mixedDeviationView)).bind
          (fun pureProfile =>
            view.boundedOutcomeFromPure horizon pureProfile horizon))
          (some outcome) :=
    congrArg (fun dist : PMF (Option (PrimitiveMachine compiled).Outcome) =>
      dist (some outcome)) hOption
  calc
    games.behavioral.game.outcomeKernel
        (Function.update
          (games.mixedPureToBehavioralProfile_of_menus hMenus mixed)
          who deviation) outcome
        =
      (view.boundedOutcomeFromBehavioral horizon
        (Function.update
          (view.mixedPureToBehavioralProfile horizon hMenus mixedView)
          who deviationView) horizon) (some outcome) := by
          simpa [behavioral, CompletedFrontierBehavioralKernelGame.game,
            CompletedFrontierBehavioralKernelGame.optionOutcomeKernel,
            CompletedFrontierBehavioralKernelGame.view,
            mixedPureToBehavioralProfile_of_menus, mixedView,
            deviationView, view, horizon] using
            games.behavioral.outcomeKernel_apply
              (Function.update
                (games.mixedPureToBehavioralProfile_of_menus hMenus mixed)
                who deviation) outcome
    _ =
      ((Math.PMFProduct.pmfPi
        (Function.update mixedView who mixedDeviationView)).bind
        (fun pureProfile =>
          view.boundedOutcomeFromPure horizon pureProfile horizon))
        (some outcome) := hpoint
    _ =
      ((Math.PMFProduct.pmfPi
        (Function.update mixed who mixedDeviation)).bind
        (fun pureProfile => games.pure.game.outcomeKernel pureProfile))
        outcome := by
          rw [PMF.bind_apply, PMF.bind_apply]
          apply tsum_congr
          intro pureProfile
          congr 1
          simpa [mixedView, mixedDeviation, hmixedDeviation,
            pure, CompletedFrontierPureKernelGame.optionOutcomeKernel,
            CompletedFrontierPureKernelGame.view, view, horizon] using
            (games.pure.outcomeKernel_apply pureProfile outcome).symm

/-- Mixed-to-behavioral outcome-kernel realizability for completed frontier
games. -/
theorem mixedPureToBehavioralOutcomeKernel_of_menus
    (games : CompletedFrontierKuhnGames compiled presentation)
    (hMenus : games.view.MenusObservable (completionBound compiled))
    (mixed : ∀ player, PMF (games.pure.game.Strategy player)) :
    ∃ behavioralProfile : games.behavioral.game.Profile,
      games.behavioral.game.outcomeKernel behavioralProfile =
        (Math.PMFProduct.pmfPi mixed).bind
          (fun pureProfile => games.pure.game.outcomeKernel pureProfile) :=
  ⟨games.mixedPureToBehavioralProfile_of_menus hMenus mixed,
    games.mixedPureToBehavioralOutcomeKernel_eq_of_menus hMenus mixed⟩

/-- Behavioral-to-correlated-pure outcome-kernel realization for completed
frontier game pairs, stated for behavioral profiles represented in the Kuhn
adapter. The resulting distribution is over pure profiles jointly, not over
independent per-player mixed strategies. -/
theorem adapterBehavioralToCorrelatedPureOutcomeKernel
    (games : CompletedFrontierKuhnGames compiled presentation)
    (hMenus : games.view.MenusObservable (completionBound compiled))
    (adapterBehavioral :
      (games.view.kuhnModel
        (completionBound compiled) hMenus).BehavioralProfile) :
    ∃ correlated : PMF games.pure.game.Profile,
      games.behavioral.game.outcomeKernel
          (by
            simpa [behavioral, CompletedFrontierBehavioralKernelGame.game,
              CompletedFrontierBehavioralKernelGame.view, view] using
              games.view.behavioralProfileOfKuhn
                (completionBound compiled) hMenus adapterBehavioral) =
        correlated.bind fun pureProfile =>
          games.pure.game.outcomeKernel pureProfile := by
  classical
  let horizon := completionBound compiled
  let view := games.view
  letI : ∀ player, Fintype (Option (view.Act player)) :=
    games.kuhnOptionalMoveFintype
  letI :
      ∀ player,
        Finite ((view.kuhnModel horizon hMenus).InfoState player) :=
    games.kuhnInfoFinite horizon hMenus
  have hOption :
      ∃ correlatedView : PMF (view.BoundedPureProfile horizon),
        view.boundedOutcomeFromBehavioral horizon
            (view.behavioralProfileOfKuhn horizon hMenus adapterBehavioral)
            horizon =
          correlatedView.bind fun pureProfile =>
            view.boundedOutcomeFromPure horizon pureProfile horizon := by
    simpa [view, horizon] using
      view.kuhn_adapterBehavioral_to_correlated_pure_optionOutcome
        horizon horizon hMenus adapterBehavioral
  rcases hOption with ⟨correlatedView, hcorrelated⟩
  let correlatedGame : PMF games.pure.game.Profile := by
    simpa [pure, CompletedFrontierPureKernelGame.game,
      CompletedFrontierPureKernelGame.view, view, horizon] using
      correlatedView
  refine ⟨correlatedGame, ?_⟩
  apply PMF.ext
  intro outcome
  let behavioralProfile : games.behavioral.game.Profile := by
    simpa [behavioral, CompletedFrontierBehavioralKernelGame.game,
      CompletedFrontierBehavioralKernelGame.view, view, horizon] using
      view.behavioralProfileOfKuhn horizon hMenus adapterBehavioral
  have hpoint :
      (view.boundedOutcomeFromBehavioral horizon
          (view.behavioralProfileOfKuhn horizon hMenus adapterBehavioral)
          horizon) (some outcome) =
        (correlatedView.bind fun pureProfile =>
          view.boundedOutcomeFromPure horizon pureProfile horizon)
          (some outcome) :=
    congrArg (fun dist : PMF (Option (PrimitiveMachine compiled).Outcome) =>
      dist (some outcome)) hcorrelated
  calc
    games.behavioral.game.outcomeKernel behavioralProfile outcome
        =
      (view.boundedOutcomeFromBehavioral horizon
          (view.behavioralProfileOfKuhn horizon hMenus adapterBehavioral)
          horizon) (some outcome) := by
          simpa [behavioral, CompletedFrontierBehavioralKernelGame.game,
            CompletedFrontierBehavioralKernelGame.optionOutcomeKernel,
            CompletedFrontierBehavioralKernelGame.view, behavioralProfile,
            view, horizon] using
            games.behavioral.outcomeKernel_apply behavioralProfile outcome
    _ =
      (correlatedView.bind fun pureProfile =>
        view.boundedOutcomeFromPure horizon pureProfile horizon)
        (some outcome) := hpoint
    _ =
      (correlatedGame.bind fun pureProfile =>
        games.pure.game.outcomeKernel pureProfile) outcome := by
          rw [PMF.bind_apply, PMF.bind_apply]
          apply tsum_congr
          intro pureProfile
          congr 1
          simpa [correlatedGame, pure,
            CompletedFrontierPureKernelGame.optionOutcomeKernel,
            CompletedFrontierPureKernelGame.view, view, horizon] using
            (games.pure.outcomeKernel_apply pureProfile outcome).symm

/-- Behavioral-to-correlated-pure outcome-kernel realization for completed
frontier game pairs, stated for native behavioral profiles of the completed
behavioral game. -/
theorem behavioralToCorrelatedPureOutcomeKernel
    (games : CompletedFrontierKuhnGames compiled presentation)
    (hMenus : games.view.MenusObservable (completionBound compiled))
    (behavioralProfile : games.behavioral.game.Profile) :
    ∃ correlated : PMF games.pure.game.Profile,
      games.behavioral.game.outcomeKernel behavioralProfile =
        correlated.bind fun pureProfile =>
          games.pure.game.outcomeKernel pureProfile := by
  classical
  let horizon := completionBound compiled
  let view := games.view
  letI : ∀ player, Fintype (Option (view.Act player)) :=
    games.kuhnOptionalMoveFintype
  letI :
      ∀ player,
        Finite ((view.kuhnModel horizon hMenus).InfoState player) :=
    games.kuhnInfoFinite horizon hMenus
  let behavioralView : view.BoundedBehavioralProfile horizon := by
    simpa [behavioral, CompletedFrontierBehavioralKernelGame.game,
      CompletedFrontierBehavioralKernelGame.view, view, horizon] using
      behavioralProfile
  have hOption :
      ∃ correlatedView : PMF (view.BoundedPureProfile horizon),
        view.boundedOutcomeFromBehavioral horizon behavioralView horizon =
          correlatedView.bind fun pureProfile =>
            view.boundedOutcomeFromPure horizon pureProfile horizon := by
    simpa [view, horizon] using
      view.kuhn_behavioral_to_correlated_pure_optionOutcome
        horizon horizon hMenus behavioralView
  rcases hOption with ⟨correlatedView, hcorrelated⟩
  let correlatedGame : PMF games.pure.game.Profile := by
    simpa [pure, CompletedFrontierPureKernelGame.game,
      CompletedFrontierPureKernelGame.view, view, horizon] using
      correlatedView
  refine ⟨correlatedGame, ?_⟩
  apply PMF.ext
  intro outcome
  have hpoint :
      (view.boundedOutcomeFromBehavioral horizon behavioralView horizon)
          (some outcome) =
        (correlatedView.bind fun pureProfile =>
          view.boundedOutcomeFromPure horizon pureProfile horizon)
          (some outcome) :=
    congrArg (fun dist : PMF (Option (PrimitiveMachine compiled).Outcome) =>
      dist (some outcome)) hcorrelated
  calc
    games.behavioral.game.outcomeKernel behavioralProfile outcome
        =
      (view.boundedOutcomeFromBehavioral horizon behavioralView horizon)
        (some outcome) := by
          simpa [behavioral, CompletedFrontierBehavioralKernelGame.game,
            CompletedFrontierBehavioralKernelGame.optionOutcomeKernel,
            CompletedFrontierBehavioralKernelGame.view, behavioralView,
            view, horizon] using
            games.behavioral.outcomeKernel_apply behavioralProfile outcome
    _ =
      (correlatedView.bind fun pureProfile =>
        view.boundedOutcomeFromPure horizon pureProfile horizon)
        (some outcome) := hpoint
    _ =
      (correlatedGame.bind fun pureProfile =>
        games.pure.game.outcomeKernel pureProfile) outcome := by
          rw [PMF.bind_apply, PMF.bind_apply]
          apply tsum_congr
          intro pureProfile
          congr 1
          simpa [correlatedGame, pure,
            CompletedFrontierPureKernelGame.optionOutcomeKernel,
            CompletedFrontierPureKernelGame.view, view, horizon] using
            (games.pure.outcomeKernel_apply pureProfile outcome).symm

open Classical in
/-- Product mixed pure-strategy profile induced by a completed behavioral
frontier profile. This is the behavioral-to-product-mixed direction of Kuhn;
unlike `behavioralToCorrelatedPureOutcomeKernel`, the result is independent across
players. -/
noncomputable def behavioralToMixedPure
    (games : CompletedFrontierKuhnGames compiled presentation)
    (hMenus : games.view.MenusObservable (completionBound compiled))
    (behavioralProfile : games.behavioral.game.Profile) :
    ∀ player, PMF (games.pure.game.Strategy player) := by
  classical
  let horizon := completionBound compiled
  let view := games.view
  letI : ∀ player, Fintype (Option (view.Act player)) :=
    games.kuhnOptionalMoveFintype
  letI :
      ∀ player,
        Finite ((view.kuhnModel horizon hMenus).InfoState player) :=
    games.kuhnInfoFinite horizon hMenus
  letI :
      ∀ player,
        Fintype ((view.kuhnModel horizon hMenus).InfoState player) :=
    fun player => Fintype.ofFinite _
  let behavioralView : view.BoundedBehavioralProfile horizon := by
    simpa [behavioral, CompletedFrontierBehavioralKernelGame.game,
      CompletedFrontierBehavioralKernelGame.view, view, horizon] using
      behavioralProfile
  simpa [pure, CompletedFrontierPureKernelGame.game,
    CompletedFrontierPureKernelGame.view, view, horizon] using
    view.behavioralToMixedPure horizon hMenus behavioralView

/-- Behavioral strategies can be realized by the induced product mixed pure
strategy profile with the same completed-game outcome kernel. This is the
Nash-relevant Kuhn direction: the output is a product mixed profile, not a
correlated distribution over full pure profiles. -/
theorem behavioralToProductMixedOutcomeKernel
    (games : CompletedFrontierKuhnGames compiled presentation)
    (hMenus : games.view.MenusObservable (completionBound compiled))
    (behavioralProfile : games.behavioral.game.Profile) :
    games.behavioral.game.outcomeKernel behavioralProfile =
      (Math.PMFProduct.pmfPi
        (games.behavioralToMixedPure hMenus behavioralProfile)).bind
        fun pureProfile =>
          games.pure.game.outcomeKernel pureProfile := by
  classical
  let horizon := completionBound compiled
  let view := games.view
  letI : ∀ player, Fintype (Option (view.Act player)) :=
    games.kuhnOptionalMoveFintype
  letI :
      ∀ player,
        Finite ((view.kuhnModel horizon hMenus).InfoState player) :=
    games.kuhnInfoFinite horizon hMenus
  letI :
      ∀ player,
        Fintype ((view.kuhnModel horizon hMenus).InfoState player) :=
    fun player => Fintype.ofFinite _
  let behavioralView : view.BoundedBehavioralProfile horizon := by
    simpa [behavioral, CompletedFrontierBehavioralKernelGame.game,
      CompletedFrontierBehavioralKernelGame.view, view, horizon] using
      behavioralProfile
  let mixedView :
      ∀ player, PMF (view.BoundedPureStrategy horizon player) :=
    view.behavioralToMixedPure horizon hMenus behavioralView
  have hOption :
      view.boundedOutcomeFromBehavioral horizon behavioralView horizon =
        (Math.PMFProduct.pmfPi mixedView).bind fun pureProfile =>
          view.boundedOutcomeFromPure horizon pureProfile horizon := by
    simpa [view, horizon, mixedView] using
      view.kuhn_behavioral_to_mixedPure_optionOutcome
        horizon horizon hMenus behavioralView
  apply PMF.ext
  intro outcome
  have hpoint :
      (view.boundedOutcomeFromBehavioral horizon behavioralView horizon)
          (some outcome) =
        ((Math.PMFProduct.pmfPi mixedView).bind fun pureProfile =>
          view.boundedOutcomeFromPure horizon pureProfile horizon)
          (some outcome) :=
    congrArg (fun dist : PMF (Option (PrimitiveMachine compiled).Outcome) =>
      dist (some outcome)) hOption
  calc
    games.behavioral.game.outcomeKernel behavioralProfile outcome
        =
      (view.boundedOutcomeFromBehavioral horizon behavioralView horizon)
        (some outcome) := by
          simpa [behavioral, CompletedFrontierBehavioralKernelGame.game,
            CompletedFrontierBehavioralKernelGame.optionOutcomeKernel,
            CompletedFrontierBehavioralKernelGame.view, behavioralView,
            view, horizon] using
            games.behavioral.outcomeKernel_apply behavioralProfile outcome
    _ =
      ((Math.PMFProduct.pmfPi mixedView).bind fun pureProfile =>
        view.boundedOutcomeFromPure horizon pureProfile horizon)
        (some outcome) := hpoint
    _ =
      ((Math.PMFProduct.pmfPi
        (games.behavioralToMixedPure hMenus behavioralProfile)).bind
        fun pureProfile =>
          games.pure.game.outcomeKernel pureProfile) outcome := by
          rw [PMF.bind_apply, PMF.bind_apply]
          apply tsum_congr
          intro pureProfile
          congr 1
          simpa [behavioralToMixedPure, mixedView, pure,
            CompletedFrontierPureKernelGame.optionOutcomeKernel,
            CompletedFrontierPureKernelGame.view, view, horizon] using
            (games.pure.outcomeKernel_apply pureProfile outcome).symm

/-- Completed frontier games satisfy the generic two-direction Kuhn
outcome-equality schema: behavioral profiles induce product mixed pure
profiles with the same outcome kernel, and every product mixed pure profile is
realizable by some behavioral profile with the same outcome kernel. -/
theorem completeOutcomeKuhn
    (games : CompletedFrontierKuhnGames compiled presentation)
    (hMenus : games.view.MenusObservable (completionBound compiled)) :
    GameTheory.Theorems.KuhnCompleteViaOutcome
      games.behavioral.game.Profile
      (∀ player, PMF (games.pure.game.Strategy player))
      games.pure.game.Profile
      games.pure.game.Outcome
      (fun behavioralProfile =>
        Math.PMFProduct.pmfPi
          (games.behavioralToMixedPure hMenus behavioralProfile))
      Math.PMFProduct.pmfPi
      games.behavioral.game.outcomeKernel
      games.pure.game.outcomeKernel := by
  constructor
  · intro behavioralProfile
    exact (games.behavioralToProductMixedOutcomeKernel
      hMenus behavioralProfile).symm
  · intro mixed
    exact games.mixedPureToBehavioralOutcomeKernel_of_menus hMenus mixed

end CompletedFrontierKuhnGames

/-- Default paired pure/behavioral completed frontier games for Kuhn-facing
semantic statements.  The pair shares one frontier presentation and one round
semantics. -/
noncomputable def canonicalFrontierKuhnGames
    (program : WFProgram P L) [FiniteDomains program] :
    CompletedFrontierKuhnGames (compile program.core)
      (frontierPresentation
        (compile program.core)
        (compile_guardLive program)) where
  semantics :=
    canonicalFrontierRoundSemantics
      (compile program.core)
      (compile_guardLive program)
  nodeFintype := compile_nodeFintype program
  fieldFintype := compile_fieldFintype program

/-- The canonical paired completed frontier games have observable menus at
their completion horizon. -/
theorem canonicalFrontierKuhnGames_menusObservable
    (program : WFProgram P L) [FiniteDomains program] :
    ((canonicalFrontierKuhnGames program).view).MenusObservable
      (completionBound (compile program.core)) := by
  simpa [CompletedFrontierKuhnGames.view, canonicalFrontierKuhnGames] using
    frontierRoundView_menusObservable
      (compile program.core)
      (frontierPresentation
        (compile program.core)
        (compile_guardLive program))
      (canonicalFrontierRoundSemantics
        (compile program.core)
        (compile_guardLive program))
      (completionBound (compile program.core))

/-- Protocol-level product-mixed-pure to behavioral realizability property for
the canonical completed frontier games. -/
def MixedPureToBehavioralOutcomeKernelRealizable
    (program : WFProgram P L) [FiniteDomains program] : Prop :=
  ∀ mixed :
      ∀ player,
        PMF (((canonicalFrontierKuhnGames program).pure.game).Strategy player),
    ∃ behavioral :
      ((canonicalFrontierKuhnGames program).behavioral.game).Profile,
      ((canonicalFrontierKuhnGames program).behavioral.game).outcomeKernel
          behavioral =
        (Math.PMFProduct.pmfPi mixed).bind
          (fun pure =>
            ((canonicalFrontierKuhnGames program).pure.game).outcomeKernel
              pure)

/-- Canonical completed frontier games satisfy product-mixed-pure to
behavioral Kuhn realizability. Finite adapter information states, local support,
and adapter/native run adequacy are generic consequences of the compiled
frontier round view. -/
theorem MixedPureToBehavioralOutcomeKernelRealizable.ofMenus
    (program : WFProgram P L) [FiniteDomains program]
    (hMenus :
      ((canonicalFrontierKuhnGames program).view).MenusObservable
        (completionBound (compile program.core))) :
    MixedPureToBehavioralOutcomeKernelRealizable program := by
  intro mixed
  exact
    (canonicalFrontierKuhnGames program).mixedPureToBehavioralOutcomeKernel_of_menus
      hMenus mixed

theorem MixedPureToBehavioralOutcomeKernelRealizable.canonical
    (program : WFProgram P L) [FiniteDomains program] :
    MixedPureToBehavioralOutcomeKernelRealizable program :=
  MixedPureToBehavioralOutcomeKernelRealizable.ofMenus program
    (canonicalFrontierKuhnGames_menusObservable program)

/-- Canonical completed frontier behavioral games have an equivalent
correlated pure-profile outcome kernel. This direction uses finite graph
action/observation alphabets and the generic no-repeat theorem for native
round views; it does not require the locality/perfect-recall obligation used
by the mixed-to-behavioral direction. -/
theorem behavioralToCorrelatedPureOutcomeKernel
    (program : WFProgram P L) [FiniteDomains program]
    (behavioralProfile :
      ((canonicalFrontierKuhnGames program).behavioral.game).Profile) :
    ∃ correlated :
        PMF ((canonicalFrontierKuhnGames program).pure.game).Profile,
      ((canonicalFrontierKuhnGames program).behavioral.game).outcomeKernel
          behavioralProfile =
        correlated.bind fun pureProfile =>
          ((canonicalFrontierKuhnGames program).pure.game).outcomeKernel
            pureProfile := by
  exact
    (canonicalFrontierKuhnGames program)
      |>.behavioralToCorrelatedPureOutcomeKernel
        (canonicalFrontierKuhnGames_menusObservable program)
        behavioralProfile

/-- Canonical completed frontier behavioral games induce product mixed
pure-strategy profiles with the same outcome kernel. -/
theorem behavioralToProductMixedOutcomeKernel
    (program : WFProgram P L) [FiniteDomains program]
    (behavioralProfile :
      ((canonicalFrontierKuhnGames program).behavioral.game).Profile) :
    ((canonicalFrontierKuhnGames program).behavioral.game).outcomeKernel
        behavioralProfile =
      (Math.PMFProduct.pmfPi
        ((canonicalFrontierKuhnGames program).behavioralToMixedPure
          (canonicalFrontierKuhnGames_menusObservable program)
          behavioralProfile)).bind fun pureProfile =>
        ((canonicalFrontierKuhnGames program).pure.game).outcomeKernel
          pureProfile := by
  exact
    (canonicalFrontierKuhnGames program)
      |>.behavioralToProductMixedOutcomeKernel
        (canonicalFrontierKuhnGames_menusObservable program)
        behavioralProfile

/-- Canonical completed frontier games satisfy the generic two-direction Kuhn
outcome-equality schema. -/
theorem completeOutcomeKuhn
    (program : WFProgram P L) [FiniteDomains program] :
    GameTheory.Theorems.KuhnCompleteViaOutcome
      ((canonicalFrontierKuhnGames program).behavioral.game).Profile
      (∀ player,
        PMF (((canonicalFrontierKuhnGames program).pure.game).Strategy player))
      ((canonicalFrontierKuhnGames program).pure.game).Profile
      ((canonicalFrontierKuhnGames program).pure.game).Outcome
      (fun behavioralProfile =>
        Math.PMFProduct.pmfPi
          ((canonicalFrontierKuhnGames program).behavioralToMixedPure
            (canonicalFrontierKuhnGames_menusObservable program)
            behavioralProfile))
      Math.PMFProduct.pmfPi
      ((canonicalFrontierKuhnGames program).behavioral.game).outcomeKernel
      ((canonicalFrontierKuhnGames program).pure.game).outcomeKernel :=
  (canonicalFrontierKuhnGames program)
    |>.completeOutcomeKuhn
      (canonicalFrontierKuhnGames_menusObservable program)

end ToEventGraph

end Vegas
