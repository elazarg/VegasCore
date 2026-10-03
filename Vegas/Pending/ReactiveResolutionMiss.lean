/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDecisionMiss

/-! # Actual missed resolutions retain publication failure

Only due strategic expiry creates a public missed-event marker. At a
resolution it stores publication failure; every later raw transition retains
that actual typed output. The marker is not inferred from watcher evidence.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Every actually marked publication has its immutable failure output. -/
def State.ResolutionMissesFail (state : State graph) : Prop :=
  ∀ event payload (layout : graph.outputLayout event = .publication payload),
    event ∈ state.missedEvents →
      (⟨.inr event, layout⟩ : FieldRef graph.layout (.publication payload)).get?
        state.config.store = some .failure

/-- Actual submission, inclusion, sampling and expiry preserve the typed
failure belonging to a missed resolution. -/
theorem reactiveResolutionMissesFail (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    (runtime.reactiveApplication leaks).Invariant State.ResolutionMissesFail where
  submit state who material valid := by
    intro event payload layout missed
    have same := runtime.reactive_respond_application leaks
      (.initial (runtime.reactiveApplication leaks) state) who ⟨some material⟩
    have marked := congrArg PublicView.missedEvents same.2
    change ((runtime.reactiveApplication leaks).submit state who material).missedEvents =
      state.missedEvents at marked
    exact same.1 ▸ valid event payload layout (marked ▸ missed)
  handle state message next valid accepted := by
    intro event payload layout missed
    rw [handle_missedEvents runtime state next ⟨message.id, message.payload.call⟩
      (reactiveHandle_call accepted)] at missed
    let ref : FieldRef graph.layout (.publication payload) := ⟨.inr event, layout⟩
    exact ref.get?_preserved state.config.store next.config.store
      (handle_store_of_some runtime state next ⟨message.id, message.payload.call⟩
        (reactiveHandle_call accepted)) .failure (valid event payload layout missed)
  environment state command next valid reached := by
    intro event payload layout missed
    by_cases prior : event ∈ state.missedEvents
    · let ref : FieldRef graph.layout (.publication payload) := ⟨.inr event, layout⟩
      exact ref.get?_preserved state.config.store next.config.store
        (environmentStep_store_of_some runtime state next command reached) .failure
          (valid event payload layout prior)
    · obtain ⟨rfl, ready, ⟨entered, activated, due⟩, strategic⟩ :=
        environmentStep_new_missedEvent runtime state next command reached event prior missed
      cases node : nodeView graph event with
      | sample ty law outputEq codeEq =>
          exact (strategic ((EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
            (congrArg EventCode.actor codeEq))).elim
      | bind owner ty outputEq codeEq =>
          have impossible := outputEq.symm.trans layout
          cases impossible
      | resolve owner ty binding checks outputEq codeEq =>
          have same := EventField.publication.inj (outputEq.symm.trans layout)
          subst payload
          change next ∈ (environmentStep runtime state (.expire event)).support at reached
          rw [environmentStep_expire_resolve_eq runtime state event ready entered activated due
            owner ty binding checks outputEq codeEq node, PMF.mem_support_pure_iff _ _] at reached
          subst next
          simp only [State.markMissed_config, State.complete, FieldRef.get?, Config.store,
            Config.complete_output_same]
          have cancel {α β : Type} (same : α = β) (value : β) :
              cast (congrArg Option same) (some (cast same.symm value)) = some value := by
            cases same
            rfl
          exact cancel (congrArg EventField.Value layout) .failure

/-- Arbitrary initialized raw histories give marked resolutions their actual
typed failure, including after further deviating responses. -/
theorem resolutionMissesFail_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {control : (runtime.reactiveApplication leaks).Control}
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control)) :
    control.execution.application.ResolutionMissesFail :=
  (runtime.reactiveResolutionMissesFail leaks).history (inputs.map State.initial) horizon
    scheduler (by
      intro state supported
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      intro event payload layout missed
      exact (Finset.notMem_empty event missed).elim) trace

end Vegas.EventGraphRuntime
