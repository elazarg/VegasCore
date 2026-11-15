module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.RankedConfig

@[expose] public section

/-! # Canonical replay of actual event records

Actor-local seriality lets every actual terminal graph path be replayed in rank order.
The replay fixes the recorded action at each event, retaining binding omissions and
mechanical completions. Its chance outcomes remain supported because declared reads
cannot be reordered across their producers. This is an ex-post reachability theorem;
the replay profile need not be selected uniformly across traces or private inputs.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Replay the actual recorded action when it exists, and otherwise use a harmless fallback. -/
private def recordedProfile (final : graph.Config) : graph.BehavioralProfile := by
  classical
  exact fun owner event actor _ _ =>
    if found : ∃ action : graph.Action event, ∃ default : Option Player,
        (⟨event, some action, default⟩ : graph.Completion) ∈ final.history then
      PMF.pure found.choose
    else PMF.pure ((graph.nodes event).failureAction owner actor)

private theorem recordedProfile_at_record (final : graph.Config) (owner : Player)
    (event : graph.EventId) (actor : graph.actor? event = some owner)
    (observation : graph.PlayerObservation owner) (active : owner ∉ observation.defaulted)
    (action : graph.Action event) (default : Option Player)
    (member : (⟨event, some action, default⟩ : graph.Completion) ∈ final.history) :
    graph.recordedProfile final owner event actor observation active = PMF.pure action := by
  classical
  have found : ∃ action : graph.Action event, ∃ default : Option Player,
      (⟨event, some action, default⟩ : graph.Completion) ∈ final.history :=
    ⟨action, default, member⟩
  unfold recordedProfile
  rw [dite_eq_left found]
  congr 1
  obtain ⟨chosenDefault, chosenMember⟩ := found.choose_spec
  have chosenRecord := (completionOf_eq_some_iff final event
    ⟨event, some found.choose, chosenDefault⟩).mpr ⟨chosenMember, rfl⟩
  have actualRecord := (completionOf_eq_some_iff final event
    ⟨event, some action, default⟩).mpr ⟨member, rfl⟩
  have same := Option.some.inj (chosenRecord.symm.trans actualRecord)
  cases same
  rfl

private theorem ActorSerial.readyIndependent_recordedProfile
    (serial : graph.ActorSerial) (final : graph.Config) :
    ReadyIndependent (graph.recordedProfile final) := by
  classical
  exact serial.readyIndependent_of_eventLaws (fun owner event actor =>
    if found : ∃ action : graph.Action event, ∃ default : Option Player,
        (⟨event, some action, default⟩ : graph.Completion) ∈ final.history then
      PMF.pure found.choose
    else PMF.pure ((graph.nodes event).failureAction owner actor))

private theorem recordedProfile_eventStep_of_step (final before after : graph.Config)
    (later : after.history.IsPrefix final.history)
    (event : graph.EventId) (ready : before.cut.Ready event) (action : graph.Action event)
    (moved : after ∈ (before.step event ready action).support) :
    after ∈ (eventStep (graph.recordedProfile final) before event ready).support := by
  classical
  unfold eventStep
  rw [PMF.support_bind]
  simp only [Set.mem_iUnion]
  cases owned : (graph.nodes event).actor with
  | none =>
      refine ⟨EventCode.actionOfActorNone (graph.nodes event) owned, ?_, ?_⟩
      · rw [actionLaw_of_ownerless _ _ owned]
        simp
      · simpa only [(graph.nodes event).action_eq_of_actor_none owned
          (EventCode.actionOfActorNone (graph.nodes event) owned) action] using moved
  | some owner =>
      rw [actionLaw_of_actor _ _ owned]
      by_cases inactive : owner ∈ before.defaulted
      · rw [dite_eq_left inactive]
        refine ⟨(graph.nodes event).failureAction owner owned, by simp, ?_⟩
        rwa [before.step_eq_of_defaulted event ready owner owned inactive
          ((graph.nodes event).failureAction owner owned) action]
      · rw [dite_eq_right inactive]
        obtain ⟨value, _output, history⟩ := before.step_completion event ready action after moved
        have member : EventGraph.completion graph event (some action) value ∈ final.history := by
          apply later.subset
          rw [history, before.actualDecision_of_active event owner owned inactive action]
          simp
        have policy := recordedProfile_at_record final owner event owned
          (graph.playerObserve owner before) inactive action
          ((graph.nodes event).defaultEvent action value) member
        rw [policy]
        exact ⟨action, by simp, moved⟩

private theorem ReadyIndependent.canonicalLaw_mem_of_eventStep {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (before after : graph.Config)
    (event : graph.EventId) (ready : before.cut.Ready event)
    (moved : after ∈ (eventStep profile before event ready).support)
    (key : graph.order.Cut × Store graph.layout × (graph.EventId → Option graph.Completion))
    (member : key ∈ (canonicalLaw profile after).support) :
    key ∈ (canonicalLaw profile before).support := by
  rw [← independent.eventStep_bind_canonicalLaw before.remaining before rfl event ready,
    PMF.support_bind]
  exact Set.mem_iUnion.mpr ⟨after, Set.mem_iUnion.mpr ⟨moved, member⟩⟩

private theorem ActorSerial.runKey_mem_recorded_canonicalLaw
    (serial : graph.ActorSerial) (before final : graph.Config)
    (path : Relation.ReflTransGen Config.Step before final) (terminal : final.cut.Terminal) :
    runKey final ∈ (canonicalLaw (graph.recordedProfile final) before).support := by
  have independent := serial.readyIndependent_recordedProfile final
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl =>
      have empty := (final.terminal_iff_remaining_zero).mp terminal
      simp [canonicalLaw, empty, EventGraph.runPlan]
  | @head before middle moved rest ih =>
      obtain ⟨event, ready, action, supported⟩ := moved
      apply independent.canonicalLaw_mem_of_eventStep before middle event ready
        (recordedProfile_eventStep_of_step final before middle
          (Config.Step.path_history_prefix rest) event ready action supported) (runKey final) ih

/-- Every reachable terminal record table admits its literal source-ranked execution. -/
private theorem ActorSerial.rankedConfig_mem_canonical
    (serial : graph.ActorSerial) (inputs : graph.Inputs) (final : graph.Config)
    (reach : final.Reachable inputs) (terminal : final.cut.Terminal) :
    rankedConfig final terminal ∈
      (graph.sequentialize.runPolicies graph.sequentialize.canonicalScheduler
        (graph.recordedProfile final) inputs).support := by
  have path : Relation.ReflTransGen Config.Step (Config.initial inputs) final := by
    clear terminal
    induction reach with
    | initial => exact .refl
    | step previous event ready action next member ih =>
        exact ih.tail ⟨event, ready, action, member⟩
  have supported := serial.runKey_mem_recorded_canonicalLaw
    (Config.initial inputs) final path terminal
  change runKey final ∈
    ((graph.runPolicies graph.canonicalScheduler (graph.recordedProfile final) inputs).map
      runKey).support at supported
  rw [← canonical_fromSequential_config_law graph (graph.recordedProfile final) inputs,
    PMF.map_comp, PMF.support_map] at supported
  obtain ⟨ordered, orderedSupported, same⟩ := supported
  have orderedReach := graph.sequentialize.run_reachable inputs
    (graph.sequentialize.policyPlan (graph.recordedProfile final)
      graph.sequentialize.canonicalScheduler) ordered orderedSupported
  have orderedTerminal := graph.sequentialize.runPolicies_terminal
    graph.sequentialize.canonicalScheduler (graph.recordedProfile final) inputs
    ordered orderedSupported
  have recast : rankedConfig final terminal = ordered := by
    have congr := rankedConfig_congr same.symm terminal orderedTerminal
    exact congr.trans (rankedConfig_fromSequentialConfig orderedReach orderedTerminal)
  exact recast.symm ▸ orderedSupported

/-- Every actual terminal record table is supported by some canonical profile.
The profile is chosen after the trace; no behavioral law is asserted. -/
theorem ActorSerial.exists_canonical_replay
    (serial : graph.ActorSerial) (inputs : graph.Inputs) (final : graph.Config)
    (reach : final.Reachable inputs) (terminal : final.cut.Terminal) :
    ∃ profile : graph.sequentialize.BehavioralProfile,
      rankedConfig final terminal ∈
        (graph.sequentialize.runPolicies graph.sequentialize.canonicalScheduler profile
          inputs).support :=
  ⟨graph.recordedProfile final, serial.rankedConfig_mem_canonical inputs final reach terminal⟩

/-- Rank reconstruction of an actual terminal path is genuinely reachable under the
sequential dependencies. Actions, omissions, outputs and per-event defaults are unchanged. -/
theorem ActorSerial.rankedConfig_reachable
    (serial : graph.ActorSerial) (inputs : graph.Inputs) (final : graph.Config)
    (reach : final.Reachable inputs) (terminal : final.cut.Terminal) :
    Config.Reachable (graph := graph.sequentialize) inputs (rankedConfig final terminal) := by
  obtain ⟨profile, supported⟩ := serial.exists_canonical_replay inputs final reach terminal
  exact graph.sequentialize.run_reachable inputs
    (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler) _ supported

end Vegas.EventGraph
