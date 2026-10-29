/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PublicFailureEvidence

/-! # Native public default provenance

Default status comes from the graph public record. Inherited defaults account
for a saved source frontier; every later default has an owned public failure
witness. Native admission, chance, expiry and automatic service preserve this
same invariant.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Exact public failure provenance relative to an inherited source frontier. -/
structure ExclusionEvidence (low : Nat) (inherited : Finset Player)
    (state : State graph) : Prop where
  receipts : state.ReceiptsComplete
  below : ∀ event : graph.EventId, event.val < low → event ∈ state.config.cut.completed
  defaulted : ∀ owner, owner ∈ state.config.defaulted ↔ owner ∈ inherited ∨
    ∃ event : graph.EventId, low ≤ event.val ∧ graph.actor? event = some owner ∧
      state.PublicFailure event

namespace ExclusionEvidence

variable {low : Nat} {inherited : Finset Player} {state : State graph}

/-- At a saved prefix every current default belongs to the inherited set. -/
theorem of_rank_cut (receipts : state.ReceiptsComplete)
    (atPrefix : ∀ event : graph.EventId, event ∈ state.config.cut.completed ↔ event.val < low)
    (defaults : state.config.defaulted = inherited) : ExclusionEvidence low inherited state := by
  refine ⟨receipts, fun event lower => (atPrefix event).mpr lower, fun owner => ?_⟩
  rw [defaults]
  constructor
  · exact Or.inl
  · rintro (member | ⟨event, lower, _acting, failed⟩)
    · exact member
    · have earlier := (atPrefix event).mp failed.completed
      omega

private theorem advance (valid : ExclusionEvidence low inherited state)
    (next : State graph) (step : CompletionStep state next)
    (newEvidence : ∀ event, event ∉ state.config.cut.completed →
      next.PublicFailure event → ∀ owner, graph.actor? event = some owner →
        owner ∈ next.config.defaulted)
    (newMembers : ∀ owner ∈ next.config.defaulted, owner ∈ state.config.defaulted ∨
      ∃ event, low ≤ event.val ∧ graph.actor? event = some owner ∧ next.PublicFailure event) :
    ExclusionEvidence low inherited next := by
  refine ⟨valid.receipts.step step, ?_, fun owner => ⟨?_, ?_⟩⟩
  · intro event lower
    exact step.completed_mono (valid.below event lower)
  · intro member
    rcases newMembers owner member with previous | witness
    · rcases (valid.defaulted owner).mp previous with inheritedOwner |
        ⟨query, lower, acting, failed⟩
      · exact Or.inl inheritedOwner
      · exact Or.inr ⟨query, lower, acting,
          (step.publicFailure_iff_of_completed failed.completed).mpr failed⟩
    · exact Or.inr witness
  · rintro (inheritedOwner | ⟨query, lower, acting, failed⟩)
    · exact step.defaulted_mono ((valid.defaulted owner).mpr (Or.inl inheritedOwner))
    · by_cases completed : query ∈ state.config.cut.completed
      · apply step.defaulted_mono
        exact (valid.defaulted owner).mpr (Or.inr ⟨query, lower, acting,
          (step.publicFailure_iff_of_completed completed).mp failed⟩)
      · exact newEvidence query completed failed owner acting

open Classical in
private theorem advance_owned (valid : ExclusionEvidence low inherited state)
    (next : State graph) (step : CompletionStep state next) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (action : graph.Action event)
    (supported : next.config ∈ (state.config.step event ready action).support)
    (owner : Player) (acting : graph.actor? event = some owner)
    (defaults : next.config.defaulted =
      if next.PublicFailure event then insert owner state.config.defaulted
        else state.config.defaulted) : ExclusionEvidence low inherited next := by
  classical
  apply valid.advance next step ?_ ?_
  · intro query unfinished failed who owned
    have same := State.completed_event_eq_of_step supported unfinished failed.completed
    subst query
    have ownerEq : owner = who := Option.some.inj (acting.symm.trans owned)
    cases ownerEq
    rw [defaults, ite_eq_left failed]
    exact Finset.mem_insert_self _ _
  · intro who member
    rw [defaults] at member
    by_cases failed : next.PublicFailure event
    · rw [ite_eq_left failed, Finset.mem_insert] at member
      rcases member with rfl | prior
      · right
        refine ⟨event, ?_, acting, failed⟩
        by_contra lower
        exact ready.1 (valid.below event (by omega))
      · exact Or.inl prior
    · exact Or.inl (by simpa only [ite_eq_right failed] using member)

private theorem publication_completion_failure (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (disclose : Bool) (result : PublicationResult (L.Val payload)) :
    (state.complete event ready (cast (congrArg EventField.Action outputEq.symm) disclose)
      (cast (congrArg EventField.Value outputEq.symm) result)).PublicFailure event ↔
        result.isFailure = true := by
  cases result <;>
    simp [State.PublicFailure, PublicView.missedBinding, outputEq, State.publicationFailed,
      node, State.complete, Config.complete, PublicationResult.isFailure]

/-- Accepted bindings remain opaque admissions; accepted publication failure records its owner. -/
theorem handle (valid : ExclusionEvidence low inherited state)
    (runtime : EventGraphRuntime graph) (message : Message Player (Payload graph))
    (next : State graph) (accepted : EventGraphRuntime.handle runtime state message = some next) :
    ExclusionEvidence low inherited next := by
  classical
  have footprint := completionStep_handle runtime state next message accepted
  obtain ⟨event, named, ready, action, supported⟩ :=
    handle_config_mem_step runtime state next message accepted
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [EventGraphRuntime.handle] at accepted
  | commitment actual candidate =>
      have same : actual = event := Option.some.inj named
      subst event
      obtain ⟨_active, _ready, _timely, owner, payload, outputEq, codeEq, node, _sender,
        _handleOwner, _vacant, _unused, nextEq⟩ :=
        (handle_commitment_iff runtime state next id actual candidate).mp accepted
      have acting : graph.actor? actual = some owner :=
        (EventCode.actor_cast outputEq (graph.nodes actual)).symm.trans
          (congrArg EventCode.actor codeEq)
      have noFailure : ¬ next.PublicFailure actual := by
        rintro (missed | publication)
        · have receipt : next.publicView.accepted (.inr actual) = some candidate := by
            rw [nextEq]
            exact Function.update_self _ _ _
          rw [next.publicView.missedBinding_of_accepted actual candidate receipt] at missed
          cases missed
        · simp only [State.publicationFailed, node, Bool.false_eq_true] at publication
      have defaults : next.config.defaulted = state.config.defaulted := by
        rw [nextEq]
        change (state.config.complete actual _ _ _).defaults.defaulted =
          state.config.defaults.defaulted
        rw [Config.complete_defaults, state.config.completion_bind_some_defaultEvent actual
          owner payload outputEq codeEq]
        rfl
      apply valid.advance_owned next footprint actual ready action supported owner acting
      simpa only [ite_eq_right noFailure] using defaults
  | opening actual candidate raw =>
      have same : actual = event := Option.some.inj named
      subst event
      obtain ⟨_active, _ready, _timely, owner, payload, binding, checks, outputEq, codeEq,
        value, result, node, _sender, _handleOwner, _associated, _rawEq, _verified,
        _stored, _resolved, nextEq⟩ :=
        (handle_opening_iff runtime state next id actual candidate raw).mp accepted
      have acting : graph.actor? actual = some owner :=
        (EventCode.actor_cast outputEq (graph.nodes actual)).symm.trans
          (congrArg EventCode.actor codeEq)
      have failed : next.PublicFailure actual ↔ result.isFailure = true := by
        rw [nextEq]
        exact publication_completion_failure state actual _ owner payload binding checks
          outputEq codeEq node true result
      apply valid.advance_owned next footprint actual ready action supported owner acting
      rw [failed, nextEq]
      change (state.config.complete actual _ _ _).defaults.defaulted = _
      rw [Config.complete_defaults, state.config.completion_resolve_defaultEvent actual owner
        payload binding checks outputEq codeEq]
      cases result <;> by_cases inactive : owner ∈ state.config.defaults.defaulted <;>
        simp_all [Config.defaulted, PublicationResult.isFailure]

/-- A public-silent native update with the same graph configuration preserves evidence. -/
theorem sameConfig {before after : State graph}
    (valid : ExclusionEvidence low inherited before)
    (step : CompletionStep before after) (same : after.config = before.config) :
    ExclusionEvidence low inherited after := by
  apply valid.advance after step ?_ ?_
  · intro event unfinished failed _owner _acting
    exact (unfinished (same ▸ failed.completed)).elim
  · intro owner member
    exact Or.inl (same ▸ member)

/-- Automatic failure cannot default an owner who was active before the step. -/
theorem completeAutomatic (valid : ExclusionEvidence low inherited state)
    (event : graph.EventId) (eligible : state.AutomaticReady event) :
    ExclusionEvidence low inherited (state.completeAutomatic event eligible) := by
  obtain ⟨owner, acting, inactive⟩ := eligible.owned
  obtain ⟨action, supported⟩ := state.completeAutomatic_step event eligible
  have footprint : CompletionStep state (state.completeAutomatic event eligible) :=
    State.completeFailure_completionStep state event eligible.1 acting
  apply valid.advance (state.completeAutomatic event eligible) footprint ?_ ?_
  · intro query unfinished failed who owned
    have same := State.completed_event_eq_of_step supported unfinished failed.completed
    subst query
    have ownerEq : owner = who := Option.some.inj (acting.symm.trans owned)
    rw [state.completeAutomatic_defaulted event eligible]
    exact ownerEq ▸ inactive
  · intro who member
    rw [state.completeAutomatic_defaulted event eligible] at member
    exact Or.inl member

/-- Bounded automatic service preserves exact native failure provenance. -/
theorem drainFuel (fuel : Nat) (valid : ExclusionEvidence low inherited state) :
    ExclusionEvidence low inherited (State.drainFuel fuel state) :=
  State.drainFuel_induction (ExclusionEvidence low inherited)
    (fun _ event eligible previous => previous.completeAutomatic event eligible) fuel state valid

/-- Full automatic service preserves exact native failure provenance. -/
theorem drain (valid : ExclusionEvidence low inherited state) :
    ExclusionEvidence low inherited state.drain := valid.drainFuel _

/-- At the initial frontier, every default has an owned public failure witness. -/
theorem defaulted_zero {state : State graph}
    (valid : ExclusionEvidence 0 ∅ state) (owner : Player) :
    owner ∈ state.config.defaulted ↔
      ∃ event, graph.actor? event = some owner ∧ state.PublicFailure event := by
  simpa only [Finset.notMem_empty, false_or, Nat.zero_le, true_and] using valid.defaulted owner

/-- Initial graph state has no default or public failure evidence. -/
theorem initial (inputs : graph.Inputs) : ExclusionEvidence 0 ∅ (State.initial inputs) := by
  refine ⟨State.ReceiptsComplete.initial inputs, fun event lower => by omega, fun owner => ?_⟩
  constructor
  · intro member
    change owner ∈ (∅ : Finset Player) at member
    exact (Finset.notMem_empty _ member).elim
  · rintro (inherited | ⟨event, _lower, _acting, failed⟩)
    · exact (Finset.notMem_empty _ inherited).elim
    · have impossible := failed.completed
      change event ∈ (∅ : Finset graph.EventId) at impossible
      exact (Finset.notMem_empty _ impossible).elim

/-- A private submission changes neither graph defaults nor public receipt provenance. -/
theorem submit (valid : ExclusionEvidence low inherited state)
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (submission : WitnessedSubmission graph) :
    ExclusionEvidence low inherited ((runtime.reactiveApplication leaks).submit state who
      submission) := by
  have publicEq := reactiveApplication_submit_publicView runtime leaks state who submission
  have configEq : ((runtime.reactiveApplication leaks).submit state who submission).config =
      state.config := by
    change (submitStep (submission.call.register state who) who _).config = _
    rw [submitStep_config, (submission.call.register_facts who state).1]
  apply valid.sameConfig _ configEq
  exact Or.inl ⟨configEq, congrArg PublicView.accepted publicEq,
    congrArg PublicView.activatedAt publicEq⟩

private theorem completeFailure_defaulted (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (owner : Player)
    (acting : graph.actor? event = some owner) :
    (state.completeFailure event ready).config.defaulted = insert owner state.config.defaulted := by
  cases node : nodeView graph event with
  | bind actor payload outputEq codeEq =>
      have actorEq : graph.actor? event = some actor :=
        (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
          (congrArg EventCode.actor codeEq)
      have same := Option.some.inj (actorEq.symm.trans acting)
      subst actor
      simp only [State.completeFailure, node, State.complete]
      change (state.config.complete event ready _ _).defaults.defaulted = _
      rw [Config.complete_defaults, state.config.completion_bind_none_defaultEvent event owner
        payload outputEq codeEq]
      by_cases inactive : owner ∈ state.config.defaults.defaulted <;>
        simp_all [Config.defaulted]
  | resolve actor payload binding checks outputEq codeEq =>
      have actorEq : graph.actor? event = some actor :=
        (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
          (congrArg EventCode.actor codeEq)
      have same := Option.some.inj (actorEq.symm.trans acting)
      subst actor
      simp only [State.completeFailure, node, State.complete]
      change (state.config.complete event ready _ _).defaults.defaulted = _
      rw [Config.complete_defaults, state.config.completion_resolve_defaultEvent event owner
        payload binding checks outputEq codeEq]
      by_cases inactive : owner ∈ state.config.defaults.defaulted <;>
        simp_all [Config.defaulted, PublicationResult.isFailure]
  | sample payload law outputEq codeEq =>
      have ownerless : graph.actor? event = none :=
        (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
          (congrArg EventCode.actor codeEq)
      rw [ownerless] at acting
      cases acting

/-- An actual owned failure records its owner in the authoritative default history. -/
theorem completeFailure (valid : ExclusionEvidence low inherited state)
    (event : graph.EventId) (ready : state.config.cut.Ready event) (owner : Player)
    (acting : graph.actor? event = some owner) :
    ExclusionEvidence low inherited (state.completeFailure event ready) := by
  classical
  obtain ⟨action, supported⟩ := state.completeFailure_step event ready acting
  apply valid.advance_owned _ (State.completeFailure_completionStep state event ready acting)
    event ready action supported owner acting
  rw [ite_eq_left (State.completeFailure_publicFailure state valid.receipts event ready acting)]
  exact completeFailure_defaulted state event ready owner acting

private theorem expired_eq_completeFailure (runtime : EventGraphRuntime graph)
    (native next : State graph) (event : graph.EventId)
    (reached : next ∈ (environmentStep runtime native (.expire event)).support)
    (changed : next.config ≠ native.config) (owner : Player)
    (acting : graph.actor? event = some owner) :
    ∃ ready : native.config.cut.Ready event, next = native.completeFailure event ready := by
  obtain same | ⟨ready, action, member⟩ :=
    environmentStep_expire_config_eq_or_mem_step runtime native next event reached
  · exact (changed same).elim
  have due : ∃ entered, native.activatedAt event = some entered ∧
      runtime.deadline event ≤ native.clock - entered := by
    cases activated : native.activatedAt event with
    | none =>
        rw [environmentStep_expire_of_not_activated runtime _ event ready activated,
          PMF.mem_support_pure_iff] at reached
        exact (changed (by rw [reached])).elim
    | some entered =>
        by_cases late : runtime.deadline event ≤ native.clock - entered
        · exact ⟨entered, rfl, late⟩
        · rw [environmentStep_expire_of_not_due runtime _ event ready entered activated late,
            PMF.mem_support_pure_iff] at reached
          exact (changed (by rw [reached])).elim
  obtain ⟨entered, activated, late⟩ := due
  refine ⟨ready, ?_⟩
  cases node : nodeView graph event with
  | sample payload law outputEq codeEq =>
      have ownerless : graph.actor? event = none :=
        (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
          (congrArg EventCode.actor codeEq)
      rw [ownerless] at acting
      cases acting
  | bind actor payload outputEq codeEq =>
      rw [environmentStep_expire_bind_eq runtime native event ready entered activated late actor
        payload outputEq codeEq node, PMF.mem_support_pure_iff] at reached
      simpa only [State.completeFailure, node] using reached
  | resolve actor payload binding checks outputEq codeEq =>
      rw [environmentStep_expire_resolve_eq runtime native event ready entered activated late
        actor payload binding checks outputEq codeEq node, PMF.mem_support_pure_iff] at reached
      simpa only [State.completeFailure, node] using reached

private theorem defaulted_of_ownerless_step (before after : graph.Config)
    (event : graph.EventId) (ready : before.cut.Ready event) (action : graph.Action event)
    (supported : after ∈ (before.step event ready action).support)
    (ownerless : graph.actor? event = none) : after.defaulted = before.defaulted := by
  change (graph.nodes event).actor = none at ownerless
  have noDecision : before.actualDecision event action = none := by
    simp only [Config.actualDecision, EventCode.actualDecision, ownerless]
  rw [Config.step, PMF.support_map] at supported
  obtain ⟨value, _chosen, rfl⟩ := supported
  change (before.complete event ready action value).defaults.defaulted = before.defaults.defaulted
  rw [Config.complete_defaults, noDecision]
  rfl

/-- Native chance, clocks and expiry preserve exact public failure provenance. -/
theorem environmentStep (valid : ExclusionEvidence low inherited state)
    (runtime : EventGraphRuntime graph) (command : EnvironmentCommand graph) (next : State graph)
    (reached : next ∈ (EventGraphRuntime.environmentStep runtime state command).support) :
    ExclusionEvidence low inherited next := by
  have footprint := completionStep_environmentStep runtime state next command reached
  cases command with
  | advanceClock =>
      simp only [EventGraphRuntime.environmentStep, PMF.mem_support_pure_iff] at reached
      subst next
      exact valid.sameConfig footprint rfl
  | executeSample event =>
      obtain ⟨_clock, cases⟩ :=
        environmentStep_executeSample_config_activated runtime state next event reached
      rcases cases with same | ⟨ready, action, supported, _activated⟩
      · exact valid.sameConfig footprint same.1
      · cases node : nodeView graph event with
        | bind owner payload outputEq codeEq =>
            rw [environmentStep_executeSample_of_nonsample runtime state event ready
              (by intros; simp [node]), PMF.mem_support_pure_iff] at reached
            subst next
            exact valid
        | resolve owner payload binding checks outputEq codeEq =>
            rw [environmentStep_executeSample_of_nonsample runtime state event ready
              (by intros; simp [node]), PMF.mem_support_pure_iff] at reached
            subst next
            exact valid
        | sample payload law outputEq codeEq =>
            have ownerless : graph.actor? event = none :=
              (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
                (congrArg EventCode.actor codeEq)
            have defaults := defaulted_of_ownerless_step state.config next.config event ready
              action supported ownerless
            apply valid.advance next footprint ?_ ?_
            · intro query unfinished failed _owner _acting
              have same := State.completed_event_eq_of_step supported unfinished failed.completed
              subst query
              rw [ownerless] at _acting
              cases _acting
            · intro owner member
              exact Or.inl (defaults ▸ member)
  | expire event =>
      by_cases same : next.config = state.config
      · exact valid.sameConfig footprint same
      · obtain _same | ⟨ready, action, supported⟩ :=
          environmentStep_expire_config_eq_or_mem_step runtime state next event reached
        · exact (same _same).elim
        · cases actor : graph.actor? event with
          | some owner =>
              obtain ⟨ready, rfl⟩ :=
                expired_eq_completeFailure runtime state next event reached same owner actor
              exact valid.completeFailure event ready owner actor
          | none =>
              have defaults := defaulted_of_ownerless_step state.config next.config event ready
                action supported actor
              apply valid.advance next footprint ?_ ?_
              · intro query unfinished failed _owner _acting
                have eq := State.completed_event_eq_of_step supported unfinished failed.completed
                subst query
                rw [actor] at _acting
                cases _acting
              · intro owner member
                exact Or.inl (defaults ▸ member)

/-- Included authenticated packets are followed by the same native automatic service. -/
theorem reactiveHandle (valid : ExclusionEvidence low inherited state)
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (message : Message Player (WitnessedPacket graph)) (next : State graph)
    (accepted : (runtime.reactiveApplication leaks).handle state message = some next) :
    ExclusionEvidence low inherited next := by
  obtain ⟨native, handled, rfl⟩ := reactiveHandle_call accepted
  exact (valid.handle runtime _ native handled).drain

/-- Environment service and automatic service preserve the same native evidence invariant. -/
theorem environment (valid : ExclusionEvidence low inherited state)
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (command : EnvironmentCommand graph) (next : State graph)
    (reached : next ∈ ((runtime.reactiveApplication leaks).environment state command).support) :
    ExclusionEvidence low inherited next := by
  change next ∈ ((EventGraphRuntime.environmentStep runtime state command).map State.drain).support
    at reached
  obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ reached
  exact (valid.environmentStep runtime command native moved).drain

/-- Every operation preserves the same native evidence invariant. -/
theorem invariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    (runtime.reactiveApplication leaks).Invariant (ExclusionEvidence low inherited) where
  submit _state who submission valid := valid.submit runtime leaks who submission
  handle _state message next valid accepted :=
    valid.reactiveHandle runtime leaks message next accepted
  environment _state command next valid reached :=
    valid.environment runtime leaks command next reached

/-- Every initialized native history has exact public default provenance. -/
theorem history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {state : (runtime.reactiveApplication leaks).ProtocolState}
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace state) :
    ReactiveApplication.stateInvariant (ExclusionEvidence 0 ∅) state := by
  apply (invariant runtime leaks).history (inputs.map State.initial) horizon scheduler ?_ trace
  intro state supported
  obtain ⟨input, _member, rfl⟩ := PMF.support_map .. ▸ supported
  exact initial input

/-- At native histories public default membership is exactly owned public failure. -/
theorem history_defaulted_iff (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {state : (runtime.reactiveApplication leaks).ProtocolState}
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace state) :
    ReactiveApplication.stateInvariant (fun state : State graph => ∀ owner,
      owner ∈ state.config.defaulted ↔
        ∃ event, graph.actor? event = some owner ∧ state.PublicFailure event) state := by
  have valid := history runtime leaks inputs horizon scheduler trace
  cases state with
  | none => trivial
  | some control => exact fun owner => valid.defaulted_zero owner

end ExclusionEvidence
end Vegas.EventGraphRuntime
