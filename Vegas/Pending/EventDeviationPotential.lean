/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPotential
import Vegas.Pending.EventInvariant

/-! # Canonical continuations against a unilateral native deviation

Only prescribed players' cached samples constrain the graph continuation.
The focal player's cache is arbitrary private implementation state: its graph
policy must instead be extracted from effective semantic decisions.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Retain only actions remembered at events not owned by the focal player. -/
def State.opponentMemory (state : State graph) (focal : Player) : RememberedActions graph :=
  fun event => if graph.actor? event = some focal then none else state.remembered event

/-- The graph profile contains the proposed backtranslation at the focal
coordinate; arbitrary native focal caches cannot override that coordinate. -/
def State.deviationContinuation (state : State graph)
    (profile : graph.BehavioralProfile) (focal : Player) : FinDist graph.SemanticKey :=
  graph.canonicalContinuation (graph.memoizedProfile profile (state.opponentMemory focal))
    state.config

theorem State.deviationContinuation_initial (inputs : graph.Inputs)
    (profile : graph.BehavioralProfile) (focal : Player) :
    (State.initial inputs).deviationContinuation profile focal =
      graph.canonicalContinuation profile (Config.initial inputs) := by
  unfold deviationContinuation
  apply graph.canonicalContinuation_congr_on_unfinished
  intro event unfinished who actor observation
  rw [normalizePolicy_memoizedProfile]
  simp [memoizedProfile, opponentMemory, State.initial]

theorem State.deviationContinuation_terminal (state : State graph)
    (profile : graph.BehavioralProfile) (focal : Player)
    (terminal : state.config.cut.Terminal) :
    state.deviationContinuation profile focal = FinDist.pure (graph.semanticKey state.config) :=
  (graph.canonicalContinuation_terminal _ state.config terminal).symm

/-- Only graph state and unfinished prescribed caches enter the continuation;
packet pools, receipts, candidate catalogues, and completed caches do not. -/
theorem State.deviationContinuation_congr (before after : State graph)
    (profile : graph.BehavioralProfile) (focal : Player)
    (config : before.config = after.config)
    (memory : ∀ event, event ∉ before.config.cut.completed →
      graph.actor? event ≠ some focal → before.remembered event = after.remembered event) :
    before.deviationContinuation profile focal = after.deviationContinuation profile focal := by
  unfold deviationContinuation
  rw [← config]
  apply graph.canonicalContinuation_memoized_congr_on_unfinished
  intro event unfinished
  unfold opponentMemory
  split
  · rfl
  · rename_i other
    exact memory event unfinished other

/-- Arbitrary focal preparation and first-write memory are irrelevant to the
continuation, even when they precede readiness or disagree with later packets. -/
theorem privateStep_focal_deviationContinuation (state : State graph)
    (profile : graph.BehavioralProfile) (focal : Player) (command : PrivateCommand graph) :
    (privateStep state focal command).deviationContinuation profile focal =
      state.deviationContinuation profile focal := by
  have memory : (privateStep state focal command).opponentMemory focal =
      state.opponentMemory focal := by
    funext event
    unfold State.opponentMemory
    by_cases owned : graph.actor? event = some focal
    · simp only [owned, ↓reduceIte]
    · simp only [owned, ↓reduceIte]
      cases command with
      | prepare serial raw => rfl
      | remember query action =>
          by_cases queryOwned : graph.actor? query = some focal
          · simp only [privateStep, dite_eq_left queryOwned]
            cases remembered : state.remembered query with
            | some value => rfl
            | none =>
                simp only
                apply Function.update_of_ne
                intro equal
                exact owned (equal ▸ queryOwned)
          · rw [privateStep, dite_eq_right queryOwned]
  unfold State.deviationContinuation
  rw [memory, (privateStep_facts state focal command).1]

/-- None of the focal player's native commands completes a graph event by
itself. Submission and replay remain observable, but preserve this potential. -/
theorem playerStep_focal_deviationContinuation (runtime : EventGraphRuntime graph)
    (profile : graph.BehavioralProfile) (focal : Player)
    (execution : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand) :
    (runtime.application.playerStep focal execution command).bind
        (fun next => next.native.application.deviationContinuation profile focal) =
      execution.native.application.deviationContinuation profile focal := by
  cases command with
  | privateCommand command =>
      rw [runtime.application.playerStep_private_eq, FinDist.pure_bind]
      exact privateStep_focal_deviationContinuation execution.native.application profile
        focal command
  | submit payload =>
      rw [runtime.application.playerStep_submit_eq, FinDist.pure_bind]
      rfl
  | replay id =>
      simp only [MessageApplication.playerStep, MessageApplication.PlayerCommand.toAction,
        MessageApplication.advance, MessageApplication.step, FinDist.pure_bind]
  | wait =>
      simp only [MessageApplication.playerStep, MessageApplication.PlayerCommand.toAction,
        MessageApplication.advance, FinDist.pure_bind]

/-- Sampling an unchanged opponent's previously unremembered ready action
preserves the deviation continuation in expectation. Partial staging can
therefore persist across service blocks without redrawing that action. -/
theorem playerStep_opponent_remember_deviationContinuation
    (runtime : EventGraphRuntime graph) (ordered : graph.BarrierOrdered)
    (profile : graph.BehavioralProfile) (focal owner : Player) (other : owner ≠ focal)
    (execution : runtime.application.PolicyExecution) (event : graph.EventId)
    (ready : execution.native.application.config.cut.Ready event)
    (actor : graph.actor? event = some owner)
    (empty : execution.native.application.remembered event = none) :
    ((graph.normalizePolicy owner (profile owner) event actor
      (graph.playerObserve owner execution.native.application.config)).bind fun action =>
        (runtime.application.playerStep owner execution
          (.privateCommand (.remember event action))).bind fun next =>
            next.native.application.deviationContinuation profile focal) =
      execution.native.application.deviationContinuation profile focal := by
  have notFocal : graph.actor? event ≠ some focal := by
    rw [actor]
    exact fun same => other (Option.some.inj same)
  have emptyOther : execution.native.application.opponentMemory focal event = none := by
    simp only [State.opponentMemory, ite_eq_right notFocal, empty]
  change _ = graph.canonicalContinuation
    (graph.memoizedProfile profile (execution.native.application.opponentMemory focal))
      execution.native.application.config
  rw [ordered.canonicalContinuation_remember profile
    (execution.native.application.opponentMemory focal) execution.native.application.config
    event ready owner actor emptyOther]
  apply FinDist.bind_congr
  intro action _
  rw [runtime.application.playerStep_private_eq, FinDist.pure_bind]
  change (privateStep execution.native.application owner
    (.remember event action)).deviationContinuation profile focal = _
  simp only [privateStep, dite_eq_left actor, empty, State.deviationContinuation]
  congr 2
  funext query
  by_cases same : query = event
  · subst query
    simp [State.opponentMemory, notFocal]
  · simp [State.opponentMemory, Function.update_of_ne same]

/-- A prescribed cached action exposes its exact graph step even if its
private staging was split over several service blocks. -/
theorem State.deviationContinuation_opponent_step (state : State graph)
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (focal owner : Player) (other : owner ≠ focal)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (actor : graph.actor? event = some owner) (action : graph.Action event)
    (saved : state.remembered event = some action) :
    state.deviationContinuation profile focal =
      (state.config.step event ready action).bind fun config =>
        ({ state with config } : State graph).deviationContinuation profile focal := by
  have savedOther : state.opponentMemory focal event = some action := by
    simp only [State.opponentMemory, actor, Option.some.injEq, other, ↓reduceIte, saved]
  exact ordered.canonicalContinuation_memoized_step profile (state.opponentMemory focal)
    state.config event ready owner actor action savedOther

/-- Once the backtranslated policy selects an effective focal action, its
semantic step preserves the continuation exactly. This is a local policy
matching premise, not an assumed whole-run simulation. -/
theorem State.deviationContinuation_focal_step (state : State graph)
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile) (focal : Player)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (actor : graph.actor? event = some focal) (action : graph.Action event)
    (selected : graph.normalizePolicy focal (profile focal) event actor
      (graph.playerObserve focal state.config) = FinDist.pure action) :
    state.deviationContinuation profile focal =
      (state.config.step event ready action).bind fun config =>
        ({ state with config } : State graph).deviationContinuation profile focal := by
  unfold State.deviationContinuation
  rw [← ordered.normalizedThenCanonical_eq _ state.config event ready]
  unfold normalizedThenCanonical normalizedPolicyStep
  split
  · rename_i who owned
    have same : who = focal := Option.some.inj (owned.symm.trans actor)
    subst who
    rw [normalizePolicy_memoizedProfile]
    simp only [memoizedProfile, State.opponentMemory, actor, ↓reduceIte, selected,
      FinDist.pure_bind]
    rfl
  · rename_i ownerless
    simp [actor] at ownerless

/-- A supported strategic completion conserves the continuation when its
effective action matches the focal policy or the prescribed owner's saved
sample. This applies equally to packet acceptance and deadline resolution. -/
theorem State.deviationContinuation_eq_of_effective_step (before after : State graph)
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (focal owner : Player) (event : graph.EventId)
    (ready : before.config.cut.Ready event) (actor : graph.actor? event = some owner)
    (action : graph.Action event)
    (member : after.config ∈ (before.config.step event ready action).support)
    (memory : after.remembered = before.remembered)
    (focalAction : owner = focal →
      ∀ (owned : graph.actor? event = some focal),
        graph.normalizePolicy focal (profile focal) event owned
          (graph.playerObserve focal before.config) = FinDist.pure action)
    (opponentAction : owner ≠ focal → before.remembered event = some action) :
    after.deviationContinuation profile focal = before.deviationContinuation profile focal := by
  have law : before.deviationContinuation profile focal =
      (before.config.step event ready action).bind fun config =>
        ({ before with config } : State graph).deviationContinuation profile focal := by
    by_cases same : owner = focal
    · subst owner
      exact before.deviationContinuation_focal_step ordered profile focal event ready actor
        action (focalAction rfl actor)
    · exact before.deviationContinuation_opponent_step ordered profile focal owner same event
        ready actor action (opponentAction same)
  rw [before.config.step_eq_pure_of_actor event ready action owner actor after.config member,
    FinDist.pure_bind] at law
  rw [law]
  exact after.deviationContinuation_congr { before with config := after.config }
    profile focal rfl (fun _ _ _ => congrFun memory _)

/-- A native chance trigger retains the graph's chance kernel in the
deviation continuation. No strategic player chooses the random result. -/
theorem environmentStep_sample_deviationContinuation (runtime : EventGraphRuntime graph)
    (state : State graph) (ordered : graph.BarrierOrdered)
    (profile : graph.BehavioralProfile) (focal : Player) (event : graph.EventId) :
    (environmentStep runtime state (.executeSample event)).bind
      (fun next => next.deviationContinuation profile focal) =
        state.deviationContinuation profile focal := by
  by_cases ready : state.config.cut.Ready event
  · cases view : nodeView graph event with
    | bind owner payload outputEq codeEq | resolve owner payload binding checks outputEq codeEq =>
        rw [environmentStep_executeSample_of_nonsample runtime state event ready
          (by intro ty law outputEq' codeEq'; simp [view]), FinDist.pure_bind]
    | sample payload law outputEq codeEq =>
        have actor : graph.actor? event = none := by
          have castActor := EventCode.actor_cast outputEq (graph.nodes event)
          rw [codeEq] at castActor
          exact castActor.symm
        rw [environmentStep_executeSample_eq runtime state event ready payload law
          outputEq codeEq view, FinDist.bind_map]
        change (state.config.step event ready
          (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)).bind
            (graph.canonicalContinuation
              (graph.memoizedProfile profile (state.opponentMemory focal))) = _
        have actionEq : cast (congrArg EventField.Action outputEq.symm) PUnit.unit =
            EventCode.actionOfActorNone (graph.nodes event) actor := by
          have singleton : Subsingleton (graph.Action event) := by
            change Subsingleton (graph.outputLayout event).Action
            rw [outputEq]
            infer_instance
          exact @Subsingleton.elim _ singleton _ _
        rw [actionEq]
        have law := ordered.normalizedThenCanonical_eq
          (graph.memoizedProfile profile (state.opponentMemory focal)) state.config event ready
        unfold normalizedThenCanonical normalizedPolicyStep at law
        split at law
        · rename_i who owned
          simp [actor] at owned
        · exact law
  · rw [environmentStep_executeSample_of_not_ready runtime state event ready, FinDist.pure_bind]

/-- Service announcements and clock increments have no semantic effect before
the separate expiry instructions run. -/
theorem environmentStep_tick_deviationContinuation (runtime : EventGraphRuntime graph)
    (state : State graph) (profile : graph.BehavioralProfile) (focal : Player) :
    (environmentStep runtime state .advanceClock).bind
      (fun next => next.deviationContinuation profile focal) =
        state.deviationContinuation profile focal := by
  rw [environmentStep, FinDist.pure_bind]
  rfl

theorem environmentStep_grant_deviationContinuation (runtime : EventGraphRuntime graph)
    (state : State graph) (profile : graph.BehavioralProfile) (focal : Player)
    (event : graph.EventId) :
    (environmentStep runtime state (.grant event)).bind
      (fun next => next.deviationContinuation profile focal) =
        state.deviationContinuation profile focal := by
  rw [environmentStep, FinDist.pure_bind]
  rfl

end Vegas.EventGraphRuntime
