/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.CanonicalStep
import Vegas.EventGraph.OwnedStep
import Vegas.EventGraph.Sequential
import Vegas.Pending.ExclusionCompletion
import Vegas.Pending.ReactiveAcceptedOutput

/-! # Policy continuation through automatic default completion

On the sequential graph, automatic service executes precisely the next
mechanical instruction of the ordinary policy runner. It retains every typed
cell, actual decision and public default event, without querying a callback.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.State

open EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- One automatic completion preserves the complete remaining execution law
of every graph profile on the sequential specialization. -/
theorem completeAutomatic_runPlan_canonical (graph : Vegas.EventGraph Player L)
    (profile : graph.sequentialize.BehavioralProfile) (state : State graph.sequentialize)
    (event : graph.sequentialize.EventId) (eligible : state.AutomaticReady event) :
    graph.sequentialize.runPlan
        (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler)
        state.config.remaining state.config =
      graph.sequentialize.runPlan
        (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler)
        (state.completeAutomatic event eligible).config.remaining
        (state.completeAutomatic event eligible).config := by
  obtain ⟨owner, acting, inactive⟩ := eligible.owned
  obtain ⟨action, supported⟩ := state.completeAutomatic_step event eligible
  obtain ⟨next, law⟩ := state.config.step_eq_pure_of_actor event eligible.1 action owner acting
  have exactLaw : state.config.step event eligible.1 action =
      PMF.pure (state.completeAutomatic event eligible).config := by
    rw [law, PMF.mem_support_pure_iff] at supported
    simpa only [supported] using law
  have progress := state.completeAutomatic_progress event eligible
  have least : ∀ other, other ∉ state.config.cut.completed → event.val ≤ other.val :=
    fun _ unfinished => EventOrder.Cut.ready_le_unfinished state.config.cut eligible.1 unfinished
  calc
    _ = graph.sequentialize.runPlan
          (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler)
          ((state.completeAutomatic event eligible).config.remaining + 1) state.config :=
      congrArg (fun fuel => graph.sequentialize.runPlan
        (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler)
          fuel state.config) progress.symm
    _ = _ := by
      rw [graph.sequentialize.runPlan_canonical_defaulted profile _ state.config event eligible.1
        least owner acting inactive action, exactLaw, PMF.pure_bind]

/-- Bounded automatic draining preserves the complete remaining execution law.
The profile is arbitrary and the native state need not be initialized. -/
theorem drain_runPlan_canonical (graph : Vegas.EventGraph Player L)
    (profile : graph.sequentialize.BehavioralProfile) (state : State graph.sequentialize) :
    graph.sequentialize.runPlan
        (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler)
        state.config.remaining state.config =
      graph.sequentialize.runPlan
        (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler)
        state.drain.config.remaining state.drain.config := by
  symm
  exact drainFuel_induction (fun current => graph.sequentialize.runPlan
      (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler)
      current.config.remaining current.config = graph.sequentialize.runPlan
        (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler)
        state.config.remaining state.config)
    (fun before event eligible previous =>
      (completeAutomatic_runPlan_canonical graph profile before event eligible).symm.trans previous)
    state.config.remaining state rfl

/-- A probabilistic native transition may drain its automatic completions
before continuing the ordinary graph runner, with the same full result law. -/
theorem drain_bind_runPlan_canonical (graph : Vegas.EventGraph Player L)
    (profile : graph.sequentialize.BehavioralProfile) (law : PMF (State graph.sequentialize)) :
    (law.map State.drain).bind (fun state => graph.sequentialize.runPlan
      (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler)
      state.config.remaining state.config) =
    law.bind (fun state => graph.sequentialize.runPlan
      (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler)
      state.config.remaining state.config) := by
  rw [PMF.bind_map]
  apply bind_congr_on_support _
  intro state _
  exact (drain_runPlan_canonical graph profile state).symm

end Vegas.EventGraphRuntime.State

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Acceptance has the ordinary full continuation law of its certified graph completion.
Automatic default service may advance several instructions before that continuation starts. -/
theorem AcceptanceWitness.reactive_runPlan (graph : Vegas.EventGraph Player L)
    (runtime : EventGraphRuntime graph.sequentialize)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    (profile : graph.sequentialize.BehavioralProfile)
    {event : graph.sequentialize.EventId}
    {message : Message Player (WitnessedPacket graph.sequentialize)}
    {sent : graph.sequentialize.Config} {action : graph.sequentialize.Action event}
    {output : (graph.sequentialize.outputLayout event).Value}
    {state next : State graph.sequentialize}
    (witness : AcceptanceWitness event message sent action output state)
    (sameConfig : state.config = sent)
    (accepted : (runtime.reactiveApplication leaks).handle state message = some next) :
    ∃ ready : sent.cut.Ready event, sent.actualDecision event action = some action ∧
      graph.sequentialize.runPlan
          (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler)
          next.config.remaining next.config =
        graph.sequentialize.runPlan
          (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler)
          (sent.complete event ready action output).remaining
          (sent.complete event ready action output) := by
  obtain ⟨native, handled, nextEq⟩ := reactiveHandle_call accepted
  obtain ⟨ready, recorded, completed⟩ := witness.complete runtime sameConfig handled
  refine ⟨ready, recorded, ?_⟩
  rw [← nextEq]
  simpa only [completed] using (State.drain_runPlan_canonical graph profile native).symm

end Vegas.EventGraphRuntime
