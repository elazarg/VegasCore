/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.MemoizedPolicy
import Vegas.Pending.EventPolicyBlock
import Vegas.Pending.EventInvariant

/-! # Canonical continuations for partly prescribed play

A predicate `prescribed` marks the players whose native policies are the
compiled graph policies. Only their cached samples constrain the graph
continuation. Every other player's cache is arbitrary private implementation
state: its graph policy must instead be matched at effective semantic
decisions. A unilateral deviation marks every player except the deviator;
honest play marks every player.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every owner of `event`, if it has one, is prescribed. -/
def PrescribedEvent (graph : Vegas.EventGraph Player L) (prescribed : Player → Prop)
    (event : graph.EventId) : Prop :=
  ∀ owner, graph.actor? event = some owner → prescribed owner

end Vegas.EventGraph

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- A private command changes remembered actions only at events its author
owns. -/
theorem privateStep_remembered_of_not_owned (state : State graph) (who : Player)
    (command : PrivateCommand graph) (event : graph.EventId)
    (foreign : graph.actor? event ≠ some who) :
    (privateStep state who command).remembered event = state.remembered event := by
  cases command with
  | prepare serial raw => rfl
  | remember query action =>
      by_cases owned : graph.actor? query = some who
      · have different : event ≠ query := fun same => foreign (same ▸ owned)
        cases remembered : state.remembered query <;>
          simp [privateStep, owned, remembered, Function.update_of_ne different]
      · simp [privateStep, owned]

/-- Retain only actions remembered at prescribed players' events. -/
def State.prescribedMemory (state : State graph) (prescribed : Player → Prop)
    [DecidablePred prescribed] : RememberedActions graph :=
  fun event => match graph.actor? event with
    | some owner => if prescribed owner then state.remembered event else none
    | none => state.remembered event

/-- The graph profile supplies the policies of players who are not prescribed;
their native caches cannot override those coordinates. -/
def State.prescribedContinuation (state : State graph)
    (profile : graph.BehavioralProfile) (prescribed : Player → Prop)
    [DecidablePred prescribed] : PMF graph.SemanticKey :=
  graph.canonicalContinuation (graph.memoizedProfile profile (state.prescribedMemory prescribed))
    state.config

section Prescribed

variable (prescribed : Player → Prop) [DecidablePred prescribed]

theorem State.prescribedContinuation_initial (inputs : graph.Inputs)
    (profile : graph.BehavioralProfile) :
    (State.initial inputs).prescribedContinuation profile prescribed =
      graph.canonicalContinuation profile (Config.initial inputs) := by
  unfold prescribedContinuation
  apply graph.canonicalContinuation_congr_on_unfinished
  intro event unfinished who actor observation
  rw [normalizePolicy_memoizedProfile]
  simp [memoizedProfile, prescribedMemory, actor, State.initial]

theorem State.prescribedContinuation_terminal (state : State graph)
    (profile : graph.BehavioralProfile) (terminal : state.config.cut.Terminal) :
    state.prescribedContinuation profile prescribed = PMF.pure (graph.semanticKey state.config) :=
  (graph.canonicalContinuation_terminal _ state.config terminal).symm

/-- Only graph state and unfinished prescribed caches enter the continuation;
packet pools, receipts, candidate catalogues, and completed caches do not. -/
theorem State.prescribedContinuation_congr (before after : State graph)
    (profile : graph.BehavioralProfile)
    (config : before.config = after.config)
    (memory : ∀ event, event ∉ before.config.cut.completed →
      graph.PrescribedEvent prescribed event → before.remembered event = after.remembered event) :
    before.prescribedContinuation profile prescribed =
      after.prescribedContinuation profile prescribed := by
  unfold prescribedContinuation
  rw [← config]
  apply graph.canonicalContinuation_memoized_congr_on_unfinished
  intro event unfinished
  unfold prescribedMemory
  cases actor : graph.actor? event with
  | none =>
      exact memory event unfinished (fun owner owned => by simp [actor] at owned)
  | some owner =>
      by_cases prescribedOwner : prescribed owner
      · simp only [prescribedOwner, ↓reduceIte]
        refine memory event unfinished (fun other owned => ?_)
        rw [actor] at owned
        cases owned
        exact prescribedOwner
      · simp only [prescribedOwner, ↓reduceIte]

/-- Arbitrary preparation and first-write memory by a player who is not
prescribed are irrelevant to the continuation, even when they precede
readiness or disagree with later packets. -/
theorem privateStep_free_prescribedContinuation (state : State graph)
    (profile : graph.BehavioralProfile) (who : Player) (free : ¬ prescribed who)
    (command : PrivateCommand graph) :
    (privateStep state who command).prescribedContinuation profile prescribed =
      state.prescribedContinuation profile prescribed := by
  apply State.prescribedContinuation_congr prescribed _ _ profile
    (privateStep_facts state who command).1
  intro event _ prescribedEvent
  exact privateStep_remembered_of_not_owned state who command event
    (fun owned => free (prescribedEvent who owned))

/-- None of a free player's native commands completes a graph event by
itself. Submission and replay remain observable, but preserve this potential. -/
theorem playerStep_free_prescribedContinuation (runtime : EventGraphRuntime graph)
    (profile : graph.BehavioralProfile) (who : Player) (free : ¬ prescribed who)
    (execution : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand) :
    (runtime.application.playerStep who execution command).bind
        (fun next => next.native.application.prescribedContinuation profile prescribed) =
      execution.native.application.prescribedContinuation profile prescribed := by
  cases command with
  | privateCommand command =>
      rw [runtime.application.playerStep_private_eq, PMF.pure_bind]
      exact privateStep_free_prescribedContinuation prescribed execution.native.application
        profile who free command
  | submit payload =>
      rw [runtime.application.playerStep_submit_eq, PMF.pure_bind]
      rfl
  | replay id =>
      simp only [MessageApplication.playerStep, MessageApplication.PlayerCommand.toAction,
        MessageApplication.advance, MessageApplication.step, PMF.pure_bind]
  | wait =>
      simp only [MessageApplication.playerStep, MessageApplication.PlayerCommand.toAction,
        MessageApplication.advance, PMF.pure_bind]

/-- Sampling a prescribed player's previously unremembered ready action
preserves the continuation in expectation. Partial staging can therefore
persist across service blocks without redrawing that action. -/
theorem playerStep_prescribed_remember_prescribedContinuation
    (runtime : EventGraphRuntime graph) (ordered : graph.BarrierOrdered)
    (profile : graph.BehavioralProfile) (owner : Player) (prescribedOwner : prescribed owner)
    (execution : runtime.application.PolicyExecution) (event : graph.EventId)
    (ready : execution.native.application.config.cut.Ready event)
    (actor : graph.actor? event = some owner)
    (empty : execution.native.application.remembered event = none) :
    ((graph.normalizePolicy owner (profile owner) event actor
      (graph.playerObserve owner execution.native.application.config)).bind fun action =>
        (runtime.application.playerStep owner execution
          (.privateCommand (.remember event action))).bind fun next =>
            next.native.application.prescribedContinuation profile prescribed) =
      execution.native.application.prescribedContinuation profile prescribed := by
  have emptyPrescribed : execution.native.application.prescribedMemory prescribed event = none := by
    simp only [State.prescribedMemory, actor, prescribedOwner, ↓reduceIte, empty]
  change _ = graph.canonicalContinuation
    (graph.memoizedProfile profile (execution.native.application.prescribedMemory prescribed))
      execution.native.application.config
  rw [ordered.canonicalContinuation_remember profile
    (execution.native.application.prescribedMemory prescribed) execution.native.application.config
    event ready owner actor emptyPrescribed]
  apply bind_congr_on_support _
  intro action _
  rw [runtime.application.playerStep_private_eq, PMF.pure_bind]
  change (privateStep execution.native.application owner
    (.remember event action)).prescribedContinuation profile prescribed = _
  simp only [privateStep, dite_eq_left actor, empty, State.prescribedContinuation]
  congr 2
  funext query
  by_cases same : query = event
  · subst query
    simp [State.prescribedMemory, actor, prescribedOwner]
  · simp [State.prescribedMemory, Function.update_of_ne same]

/-- A prescribed cached action exposes its exact graph step even if its
private staging was split over several service blocks. -/
theorem State.prescribedContinuation_prescribed_step (state : State graph)
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (owner : Player) (prescribedOwner : prescribed owner)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (actor : graph.actor? event = some owner) (action : graph.Action event)
    (saved : state.remembered event = some action) :
    state.prescribedContinuation profile prescribed =
      (state.config.step event ready action).bind fun config =>
        ({ state with config } : State graph).prescribedContinuation profile prescribed := by
  have savedPrescribed : state.prescribedMemory prescribed event = some action := by
    simp only [State.prescribedMemory, actor, prescribedOwner, ↓reduceIte, saved]
  exact ordered.canonicalContinuation_memoized_step profile (state.prescribedMemory prescribed)
    state.config event ready owner actor action savedPrescribed

/-- Once the profile selects an effective action of a free player, its
semantic step preserves the continuation exactly. This is a local policy
matching premise, not an assumed whole-run simulation. -/
theorem State.prescribedContinuation_free_step (state : State graph)
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (owner : Player) (free : ¬ prescribed owner)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (actor : graph.actor? event = some owner) (action : graph.Action event)
    (selected : graph.normalizePolicy owner (profile owner) event actor
      (graph.playerObserve owner state.config) = PMF.pure action) :
    state.prescribedContinuation profile prescribed =
      (state.config.step event ready action).bind fun config =>
        ({ state with config } : State graph).prescribedContinuation profile prescribed := by
  unfold State.prescribedContinuation
  rw [← ordered.normalizedThenCanonical_eq _ state.config event ready]
  unfold normalizedThenCanonical normalizedPolicyStep
  split
  · rename_i who owned
    have same : who = owner := Option.some.inj (owned.symm.trans actor)
    subst who
    rw [normalizePolicy_memoizedProfile]
    simp only [memoizedProfile, State.prescribedMemory, actor, free, ↓reduceIte, selected,
      PMF.pure_bind]
    rfl
  · rename_i ownerless
    simp [actor] at ownerless

/-- A supported strategic completion conserves the continuation when its
effective action matches the profile of a free owner or the prescribed owner's
saved sample. This applies equally to packet acceptance and deadline
resolution. -/
theorem State.prescribedContinuation_eq_of_effective_step (before after : State graph)
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (owner : Player) (event : graph.EventId)
    (ready : before.config.cut.Ready event) (actor : graph.actor? event = some owner)
    (action : graph.Action event)
    (member : after.config ∈ (before.config.step event ready action).support)
    (memory : after.remembered = before.remembered)
    (freeAction : ¬ prescribed owner →
      graph.normalizePolicy owner (profile owner) event actor
        (graph.playerObserve owner before.config) = PMF.pure action)
    (prescribedAction : prescribed owner → before.remembered event = some action) :
    after.prescribedContinuation profile prescribed =
      before.prescribedContinuation profile prescribed := by
  have law : before.prescribedContinuation profile prescribed =
      (before.config.step event ready action).bind fun config =>
        ({ before with config } : State graph).prescribedContinuation profile prescribed := by
    by_cases prescribedOwner : prescribed owner
    · exact before.prescribedContinuation_prescribed_step prescribed ordered profile owner
        prescribedOwner event ready actor action (prescribedAction prescribedOwner)
    · exact before.prescribedContinuation_free_step prescribed ordered profile owner
        prescribedOwner event ready actor action (freeAction prescribedOwner)
  rw [before.config.step_eq_pure_of_actor event ready action owner actor after.config member,
    PMF.pure_bind] at law
  rw [law]
  exact after.prescribedContinuation_congr prescribed { before with config := after.config }
    profile rfl (fun _ _ _ => congrFun memory _)

/-- A native chance trigger retains the graph's chance kernel in the
continuation. No strategic player chooses the random result. -/
theorem environmentStep_sample_prescribedContinuation (runtime : EventGraphRuntime graph)
    (state : State graph) (ordered : graph.BarrierOrdered)
    (profile : graph.BehavioralProfile) (event : graph.EventId) :
    (environmentStep runtime state (.executeSample event)).bind
      (fun next => next.prescribedContinuation profile prescribed) =
        state.prescribedContinuation profile prescribed := by
  by_cases ready : state.config.cut.Ready event
  · cases view : nodeView graph event with
    | bind owner payload outputEq codeEq | resolve owner payload binding checks outputEq codeEq =>
        rw [environmentStep_executeSample_of_nonsample runtime state event ready
          (by intro ty law outputEq' codeEq'; simp [view]), PMF.pure_bind]
    | sample payload law outputEq codeEq =>
        have actor : graph.actor? event = none := by
          have castActor := EventCode.actor_cast outputEq (graph.nodes event)
          rw [codeEq] at castActor
          exact castActor.symm
        rw [environmentStep_executeSample_eq runtime state event ready payload law
          outputEq codeEq view, PMF.bind_map]
        change (state.config.step event ready
          (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)).bind
            (graph.canonicalContinuation
              (graph.memoizedProfile profile (state.prescribedMemory prescribed))) = _
        have actionEq : cast (congrArg EventField.Action outputEq.symm) PUnit.unit =
            EventCode.actionOfActorNone (graph.nodes event) actor := by
          have singleton : Subsingleton (graph.Action event) := by
            change Subsingleton (graph.outputLayout event).Action
            rw [outputEq]
            infer_instance
          exact @Subsingleton.elim _ singleton _ _
        rw [actionEq]
        have law := ordered.normalizedThenCanonical_eq
          (graph.memoizedProfile profile (state.prescribedMemory prescribed)) state.config event
            ready
        unfold normalizedThenCanonical normalizedPolicyStep at law
        split at law
        · rename_i who owned
          simp [actor] at owned
        · exact law
  · rw [environmentStep_executeSample_of_not_ready runtime state event ready, PMF.pure_bind]

/-- Service announcements and clock increments have no semantic effect before
the separate expiry instructions run. -/
theorem environmentStep_tick_prescribedContinuation (runtime : EventGraphRuntime graph)
    (state : State graph) (profile : graph.BehavioralProfile) :
    (environmentStep runtime state .advanceClock).bind
      (fun next => next.prescribedContinuation profile prescribed) =
        state.prescribedContinuation profile prescribed := by
  rw [environmentStep, PMF.pure_bind]
  rfl

theorem environmentStep_grant_prescribedContinuation (runtime : EventGraphRuntime graph)
    (state : State graph) (profile : graph.BehavioralProfile) (event : graph.EventId) :
    (environmentStep runtime state (.grant event)).bind
      (fun next => next.prescribedContinuation profile prescribed) =
        state.prescribedContinuation profile prescribed := by
  rw [environmentStep, PMF.pure_bind]
  rfl

end Prescribed

end Vegas.EventGraphRuntime
