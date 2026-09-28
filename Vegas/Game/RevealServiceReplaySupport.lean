/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceReplayContinuation

/-! # Every legal public-replay history has a retained counterpart

Support witnesses use the actual response-menu evaluators. They do not assume
that the target history is reached by an equilibrium, or that watcher response
records are hidden from the watcher.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (watcher : Player)
  (reveals : setup.program.RevealOnly)
  (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
  (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)

private def sourceProfile
    (target : Profile ((replayMenu setup leaks bounds watcher).information
      (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).behavioralSignature) :
    Profile (information setup leaks bounds watcher).behavioralSignature := by
  classical
  intro who info
  by_cases watches : who = watcher
  · exact (menu setup leaks bounds watcher).uniformPolicy (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher) who info
  · refine (target who info).map fun choice => ⟨choice.1, ?_⟩
    cases info with
    | none => exact choice.2
    | some data =>
      obtain ⟨response, allowed, chosen⟩ := choice.2
      refine ⟨response, ?_, chosen⟩
      simpa only [replayMenu, ite_eq_right watches, Finset.union_empty] using allowed

private theorem sourceProfile_ordinary
    (target : Profile ((replayMenu setup leaks bounds watcher).information
      (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).behavioralSignature)
    (who : Player) (ordinary : who ≠ watcher)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    (menu setup leaks bounds watcher).decodeProfile (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher)
        (sourceProfile setup leaks bounds watcher target) who past view =
      (replayMenu setup leaks bounds watcher).decodeProfile (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher) target who past view := by
  classical
  simp only [ReactiveApplication.ResponseMenu.decodeProfile, ReactiveApplication.decodePolicy,
    ReactiveApplication.ResponseMenu.embedPolicy, sourceProfile, dite_eq_right ordinary,
    FinDist.map_comp]
  rfl

include reveals observer openable in
private theorem successor_counterpart
    (source : Profile (information setup leaks bounds watcher).behavioralSignature)
    (target : Profile ((replayMenu setup leaks bounds watcher).information
      (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).behavioralSignature)
    (history : (protocol setup leaks bounds watcher).History)
    (remaining : Nat) (actor : Option Player)
    (first second : (application setup leaks).Execution)
    (current : history.state = some ⟨remaining, actor, first⟩)
    (same : ReplayAgreement setup leaks watcher first second)
    (ordinaryLaw : ∀ who, actor = some who → who ≠ watcher →
      (replayMenu setup leaks bounds watcher).decodeProfile (initialLaw setup)
          (horizon setup watcher) (scheduler setup leaks watcher) target who
          (second.recall who) (second.observe (application setup leaks) who) =
        (menu setup leaks bounds watcher).decodeProfile (initialLaw setup)
          (horizon setup watcher) (scheduler setup leaks watcher) source who
          (first.recall who) (first.observe (application setup leaks) who))
    (next : (application setup leaks).ProtocolState)
    (supported : next ∈ ((application setup leaks).controlStep (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)
      ((replayMenu setup leaks bounds watcher).decodeProfile (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher) target)
      (some ⟨remaining, actor, second⟩)).support) :
    ∃ (nextHistory : (protocol setup leaks bounds watcher).History),
      ∃ count nextActor left right,
      nextHistory.state = some ⟨count, nextActor, left⟩ ∧
      next = some ⟨count, nextActor, right⟩ ∧ ReplayAgreement setup leaks watcher left right := by
  classical
  let app := application setup leaks
  let sourceMenu := menu setup leaks bounds watcher
  let firstPlayers := sourceMenu.decodeProfile (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) source
  let sourceStep := app.controlStep (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) firstPlayers (some ⟨remaining, actor, first⟩)
  let matched (state : app.ProtocolState) : Prop :=
    ∃ count nextActor left right,
      some ⟨count, nextActor, left⟩ ∈ sourceStep.support ∧
      state = some ⟨count, nextActor, right⟩ ∧ ReplayAgreement setup leaks watcher left right
  have coupling := replay_control_bind_eq setup leaks bounds watcher reveals observer openable
    source target history remaining actor first second current same ordinaryLaw
    (fun _ => FinDist.pure true) (fun state => FinDist.pure (decide (matched state)))
    (by
      intro count nextActor left right reached related
      have witness : matched (some ⟨count, nextActor, right⟩) :=
        ⟨count, nextActor, left, right, reached, rfl, related⟩
      rw [decide_eq_true witness])
  rw [FinDist.bind_const, ← FinDist.map_eq_bind] at coupling
  have inMap : decide (matched next) ∈
      (FinDist.pure true).support := by
    rw [coupling, FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  have witness : matched next := of_decide_eq_true (FinDist.mem_support_pure.mp inMap)
  obtain ⟨count, nextActor, left, right, reached, nextEq, related⟩ := witness
  have prefixLaw := sourceMenu.run_map_controlSteps (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) source 1 history
  simp only [Function.iterate_one, FinDist.pure_bind, current] at prefixLaw
  have sourceReach : some ⟨count, nextActor, left⟩ ∈
      (((information setup leaks bounds watcher).runBehavioralFrom source 1 history).map
        History.state).support := by
    rw [prefixLaw]
    exact reached
  obtain ⟨nextHistory, _, nextState⟩ := FinDist.support_map .. ▸ sourceReach
  exact ⟨nextHistory, count, nextActor, left, right, nextState, nextEq, related⟩


include reveals observer openable in
private theorem supported_counterpart
    (target : Profile ((replayMenu setup leaks bounds watcher).information
      (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).behavioralSignature)
    (fuel : Nat)
    (history : ((replayMenu setup leaks bounds watcher).protocol
      (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).History)
    (supported : history ∈ (((replayMenu setup leaks bounds watcher).information
      (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).runBehavioral
        target fuel).support) :
    history.state = none ∨
      ∃ (original : (protocol setup leaks bounds watcher).History),
        ∃ count actor first second, original.state = some ⟨count, actor, first⟩ ∧
          history.state = some ⟨count, actor, second⟩ ∧
          ReplayAgreement setup leaks watcher first second := by
  classical
  let app := application setup leaks
  let sourceMenu := menu setup leaks bounds watcher
  let targetMenu := replayMenu setup leaks bounds watcher
  let initial := initialLaw setup
  let count := horizon setup watcher
  let service := scheduler setup leaks watcher
  let source := sourceProfile setup leaks bounds watcher target
  let targetModel := targetMenu.information initial count service
  let sourceModel := sourceMenu.information initial count service
  let firstPlayers := sourceMenu.decodeProfile initial count service source
  let secondPlayers := targetMenu.decodeProfile initial count service target
  induction fuel generalizing history with
  | zero =>
      have equal : history = (targetMenu.protocol initial count service).initHistory :=
        FinDist.mem_support_pure.mp supported
      exact Or.inl (congrArg History.state equal)
  | succ fuel ih =>
      change history ∈ (targetModel.runBehavioralFrom target (fuel + 1)
        (targetMenu.protocol initial count service).initHistory).support at supported
      rw [targetModel.runBehavioralFrom_add, FinDist.support_bind] at supported
      obtain ⟨prior, reached, moved⟩ := Set.mem_iUnion₂.mp supported
      have targetStep := targetMenu.run_map_controlSteps initial count service target 1 prior
      simp only [Function.iterate_one, FinDist.pure_bind] at targetStep
      have stateSupport : history.state ∈
          (app.controlStep initial count service secondPlayers prior.state).support := by
        rw [← targetStep, FinDist.support_map]
        exact ⟨history, moved, rfl⟩
      rcases ih prior reached with uninitialized | related
      · rw [uninitialized] at stateSupport
        have initialStep (players : Player → app.Policy) :
            app.controlStep initial count service players none =
              initial.map (fun state => some ⟨count, none,
                ReactiveApplication.Execution.initial app state⟩) := by
          simp only [ReactiveApplication.controlStep, ReactiveApplication.actor,
            Option.bind_none, ReactiveApplication.transition, FinDist.map_eq_bind]
          rfl
        rw [initialStep, FinDist.support_map] at stateSupport
        obtain ⟨state, stateSupported, stateEq⟩ := stateSupport
        have sourceStep := sourceMenu.run_map_controlSteps initial count service source 1
          (sourceMenu.protocol initial count service).initHistory
        simp only [Function.iterate_one, FinDist.pure_bind] at sourceStep
        change (sourceModel.runBehavioral source 1).map History.state =
          app.controlStep initial count service firstPlayers none at sourceStep
        rw [initialStep] at sourceStep
        have inSource : some ⟨count, none, ReactiveApplication.Execution.initial app state⟩ ∈
            ((sourceModel.runBehavioral source 1).map History.state).support := by
          rw [sourceStep, FinDist.support_map]
          exact ⟨state, stateSupported, rfl⟩
        obtain ⟨original, _, originalState⟩ := FinDist.support_map .. ▸ inSource
        refine Or.inr ⟨original, count, none, _, _, originalState, stateEq.symm, ?_⟩
        exact ReplayAgreement.refl _ (by simp [ReactiveApplication.Execution.initial,
          MessageNetwork.empty])
      · obtain ⟨original, remaining, actor, first, second, originalState, priorState, same⟩ :=
          related
        rw [priorState] at stateSupport
        apply Or.inr
        exact successor_counterpart setup leaks bounds watcher reveals observer openable
          source target original remaining actor first second originalState same
          (by
            intro who _ ordinary
            rw [← same.recall who ordinary, ← same.observe who]
            exact (sourceProfile_ordinary setup leaks bounds watcher target who ordinary _ _).symm)
          history.state stateSupport

include reveals observer openable in
/-- Every legal history, including zero-probability equilibrium histories,
has an actual original-menu history with the same application, public data,
ordinary-player information, and live pending packets. -/
theorem replay_history_counterpart
    (history : ((replayMenu setup leaks bounds watcher).protocol
      (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).History)
    (control : (application setup leaks).Control) (state : history.state = some control) :
    ∃ (original : (protocol setup leaks bounds watcher).History),
      ∃ first, original.state = some ⟨control.remaining, control.actor, first⟩ ∧
        ReplayAgreement setup leaks watcher first control.execution := by
  let replayed := replayMenu setup leaks bounds watcher
  let reference := replayed.uniformAssessment (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)
  have reached := (replayed.uniform_fullyMixed (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)).history_supported history.trace
  rcases supported_counterpart setup leaks bounds watcher reveals observer openable
      reference.strategy history.trace.length history reached with absent | present
  · rw [state] at absent
    cases absent
  · obtain ⟨original, remaining, actor, first, second, originalState, targetState, related⟩ :=
      present
    have equal := Option.some.inj (state.symm.trans targetState)
    subst control
    exact ⟨original, first, originalState, related⟩

end Vegas
