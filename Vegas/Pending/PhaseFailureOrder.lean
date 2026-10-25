/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseFailureCoverage

/-! # Source-ordered suppression of an excluded player's later publications -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace RecoveryState

/-- A completed publication of an inherited excluded owner, or following an
earlier public failure of the same owner, is itself publicly failed. -/
def OrderedPublicFailures (low : Nat) (inherited : Finset Player)
    (state : RecoveryState graph) : Prop :=
  ∀ event owner, low ≤ event.val → (graph.outputLayout event).IsPublication →
    graph.actor? event = some owner → event ∈ state.native.config.cut.completed →
    (owner ∈ inherited ∨ ∃ prior : graph.EventId,
      low ≤ prior.val ∧ prior.val < event.val ∧ graph.actor? prior = some owner ∧
        state.native.PublicFailure prior) → state.native.PublicFailure event

omit [DecidableEq Player] in
theorem orderedPublicFailures_of_prefix (low : Nat) (inherited : Finset Player)
    (state : RecoveryState graph) (atPrefix : state.native.config.cut.IsPrefix low) :
    state.OrderedPublicFailures low inherited := by
  intro event _ lower _ _ completed _
  have earlier := (atPrefix.2 event).mp completed
  omega

omit [DecidableEq Player] in
theorem OrderedPublicFailures.copy {low : Nat} {inherited : Finset Player}
    {before after : RecoveryState graph} (valid : before.OrderedPublicFailures low inherited)
    (config : after.native.config = before.native.config)
    (accepted : after.native.accepted = before.native.accepted) :
    after.OrderedPublicFailures low inherited := by
  intro event owner lower publication acting completed reason
  apply (State.PublicFailure.congr event (by rw [config]) (by rw [config])
    (congrFun accepted _)).mpr
  apply valid event owner lower publication acting (config ▸ completed)
  rcases reason with member | ⟨prior, lower, earlier, acting, failed⟩
  · exact Or.inl member
  · exact Or.inr ⟨prior, lower, earlier, acting,
      (State.PublicFailure.congr prior (by rw [config]) (by rw [config])
        (congrFun accepted _)).mp failed⟩

/-- A native completion respects source-ordered exclusion whenever an event
owned by an already excluded player can only complete as public failure. -/
theorem OrderedPublicFailures.advance {low : Nat} {inherited : Finset Player}
    {state : RecoveryState graph} (valid : state.OrderedPublicFailures low inherited)
    (coverage : state.FailureCoverage) (inherited_le : inherited ⊆ state.excluded)
    (ordered : graph.RevealRelaxedOrdered) (native : State graph) (excluded : Finset Player)
    (step : CompletionStep state.native native)
    (suppressed : ∀ event (ready : state.native.config.cut.Ready event)
      (action : graph.Action event), native.config ∈
        (state.native.config.step event ready action).support → ∀ owner,
      graph.actor? event = some owner → owner ∈ state.excluded → native.PublicFailure event) :
    OrderedPublicFailures low inherited ⟨native, excluded⟩ := by
  rcases step with ⟨config, accepted, _⟩ |
      ⟨changed, ready, action, supported, _, acceptedOnly⟩
  · exact valid.copy config accepted
  intro event owner lower publication acting completed reason
  have unchanged (query : graph.EventId) (different : query ≠ changed) :
      native.PublicFailure query ↔ state.native.PublicFailure query :=
    State.PublicFailure.of_step_of_ne supported
      (fun field different => (acceptedOnly field different).2) different
  by_cases same : event = changed
  · subst event
    apply suppressed changed ready action supported owner acting
    rcases reason with excluded | ⟨prior, _lower, earlier, priorActor, failed⟩
    · exact inherited_le excluded
    · have different : prior ≠ changed := fun equal => by subst prior; omega
      exact coverage.covered prior owner priorActor ((unchanged prior different).mp failed)
  · apply (unchanged event same).mpr
    have previous : event ∈ state.native.config.cut.completed := by
      rw [state.native.config.step_cut changed ready action native.config supported,
        EventOrder.Cut.mem_complete] at completed
      exact completed.resolve_left same
    apply valid event owner lower publication acting previous
    rcases reason with member | ⟨prior, lower, earlier, priorActor, failed⟩
    · exact Or.inl member
    · have different : prior ≠ changed := by
        intro equal
        subst prior
        have barrier : changed ∈ (barrierOrder graph.outputLayout).predecessors event :=
          (mem_barrierOrder graph.outputLayout changed event).mpr
            ⟨earlier, Or.inr (Or.inl publication.isPublic)⟩
        have dependency := ordered event changed barrier
          (IndependentReveals.not_of_actor_eq (priorActor.trans acting.symm))
        exact ready.1 (state.native.config.cut.predecessor_closed previous dependency)
      exact Or.inr ⟨prior, lower, earlier, priorActor, (unchanged prior different).mp failed⟩

theorem OrderedPublicFailures.completeAutomatic {low : Nat} {inherited : Finset Player}
    {state : RecoveryState graph} (valid : state.OrderedPublicFailures low inherited)
    (coverage : state.FailureCoverage) (inherited_le : inherited ⊆ state.excluded)
    (ordered : graph.RevealRelaxedOrdered) (event : graph.EventId)
    (eligible : state.AutomaticReady event) :
    (state.completeAutomatic event eligible).OrderedPublicFailures low inherited := by
  obtain ⟨owner, acting, _⟩ := eligible.owned
  apply valid.advance coverage inherited_le ordered _ _
    (State.completeFailure_completionStep state.native event eligible.1 acting)
  intro query ready action supported actor actingQuery _
  have completed : query ∈
      (state.native.completeFailure event eligible.1).config.cut.completed := by
    rw [state.native.config.step_cut query ready action _ supported,
      EventOrder.Cut.mem_complete]
    exact Or.inl rfl
  obtain ⟨actualAction, actualSupported⟩ :=
    state.native.completeFailure_step event eligible.1 acting
  rw [state.native.config.step_cut event eligible.1 actualAction _ actualSupported,
    EventOrder.Cut.mem_complete] at completed
  have same := completed.resolve_right ready.1
  subst query
  exact State.completeFailure_publicFailure state.native coverage.receipts
    event eligible.1 actingQuery

theorem OrderedPublicFailures.inclusionResult {low : Nat} {inherited : Finset Player}
    {state : RecoveryState graph} (valid : state.OrderedPublicFailures low inherited)
    (coverage : state.FailureCoverage) (inherited_le : inherited ⊆ state.excluded)
    (ordered : graph.RevealRelaxedOrdered) (runtime : EventGraphRuntime graph)
    (message : Message Player (Payload graph)) (native : State graph)
    (permitted : state.excludedCall message.payload = false)
    (handled : EventGraphRuntime.handle runtime state.native message = some native) :
    (state.inclusionResult message.payload native).OrderedPublicFailures low inherited := by
  obtain ⟨event, named, ready, action, supported⟩ :=
    handle_config_mem_step runtime state.native native message handled
  apply valid.advance coverage inherited_le ordered _ _
    (completionStep_handle runtime state.native native message handled)
  intro query queryReady queryAction querySupported owner acting excluded
  have completed : query ∈ native.config.cut.completed := by
    rw [state.native.config.step_cut query queryReady queryAction native.config querySupported,
      EventOrder.Cut.mem_complete]
    exact Or.inl rfl
  have same := State.completed_event_eq_of_step supported queryReady.1 completed
  subst query
  have forbidden : state.excludedCall message.payload = true := by
    simp only [excludedCall, named, excludedEvent, acting, Option.any_some,
      decide_eq_true_eq, excluded]
  cases forbidden.symm.trans permitted

theorem OrderedPublicFailures.environmentResult {low : Nat} {inherited : Finset Player}
    {state : RecoveryState graph} (valid : state.OrderedPublicFailures low inherited)
    (coverage : state.FailureCoverage) (inherited_le : inherited ⊆ state.excluded)
    (ordered : graph.RevealRelaxedOrdered) (runtime : EventGraphRuntime graph)
    (command : EnvironmentCommand graph) (native : State graph)
    (reached : native ∈ (environmentStep runtime state.native command).support) :
    (state.environmentResult command native).OrderedPublicFailures low inherited := by
  apply valid.advance coverage inherited_le ordered _ _
    (completionStep_environmentStep runtime state.native native command reached)
  intro query queryReady queryAction querySupported owner acting _
  have completed : query ∈ native.config.cut.completed := by
    rw [state.native.config.step_cut query queryReady queryAction native.config querySupported,
      EventOrder.Cut.mem_complete]
    exact Or.inl rfl
  have changed : native.config ≠ state.native.config := by
    intro same
    exact queryReady.1 (same ▸ completed)
  cases command with
  | advanceClock =>
      simp only [environmentStep, PMF.mem_support_pure_iff] at reached
      subst native
      exact (changed rfl).elim
  | expire event =>
      rcases environmentStep_expire_config_eq_or_mem_step runtime state.native native event
        reached with same | ⟨ready, action, supported⟩
      · exact (changed same).elim
      · have same := State.completed_event_eq_of_step supported queryReady.1 completed
        subst query
        exact ExclusionEvidence.expire_publicFailure runtime state.native native
          coverage.receipts event reached changed acting
  | executeSample event =>
      rcases (environmentStep_executeSample_config_activated runtime state.native native event
        reached).2 with ⟨same, _⟩ | ⟨ready, action, supported, _⟩
      · exact (changed same).elim
      · have same := State.completed_event_eq_of_step supported queryReady.1 completed
        subst query
        cases view : nodeView graph event with
        | sample payload law outputEq codeEq =>
            have ownerless : graph.actor? event = none :=
              (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
                (congrArg EventCode.actor codeEq)
            cases ownerless.symm.trans acting
        | bind | resolve =>
            have nonsample : ∀ payload law outputEq codeEq,
                nodeView graph event ≠ .sample payload law outputEq codeEq := by
              intro payload law outputEq codeEq same
              rw [view] at same
              cases same
            rw [environmentStep_executeSample_of_nonsample runtime state.native event ready
              nonsample, PMF.mem_support_pure_iff] at reached
            subst native
            exact (changed rfl).elim

end RecoveryState

namespace RuntimePhase

theorem orderedPublicFailures_drainFuel (phase : RuntimePhase graph) (fuel : Nat)
    (low : Nat) (inherited : Finset Player) (state : RecoveryState graph)
    (valid : state.OrderedPublicFailures low inherited) (coverage : state.FailureCoverage)
    (inherited_le : inherited ⊆ state.excluded) (ordered : graph.RevealRelaxedOrdered) :
    (phase.drainFuel fuel state).OrderedPublicFailures low inherited := by
  have preserved := phase.drainFuel_induction (fun next =>
    next.OrderedPublicFailures low inherited ∧ next.FailureCoverage ∧ inherited ⊆ next.excluded)
    (fun before event eligible previous =>
      ⟨previous.1.completeAutomatic previous.2.1 previous.2.2 ordered event eligible.2,
        previous.2.1.completeAutomatic event eligible.2, previous.2.2⟩)
    fuel state ⟨valid, coverage, inherited_le⟩
  exact preserved.1

theorem orderedPublicFailures_drain (phase : RuntimePhase graph) (low : Nat)
    (inherited : Finset Player) (state : RecoveryState graph)
    (valid : state.OrderedPublicFailures low inherited) (coverage : state.FailureCoverage)
    (inherited_le : inherited ⊆ state.excluded) (ordered : graph.RevealRelaxedOrdered) :
    (phase.drain state).OrderedPublicFailures low inherited :=
  phase.orderedPublicFailures_drainFuel _ low inherited state valid coverage inherited_le ordered

end RuntimePhase
end Vegas.EventGraphRuntime
