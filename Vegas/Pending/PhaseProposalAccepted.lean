/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseApplication
import Vegas.Pending.ExclusionPublicRecord

/-! # Actual packet origins of true publication completion actions -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Only a true publication action denotes a disclosure. -/
def publicationDiscloses : (kind : EventField Player L) → kind.Action → Bool
  | .publication _, action => action
  | _, _ => false

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem publicationDiscloses_cast {left right : EventField Player L} (same : left = right)
    (action : left.Action) :
    publicationDiscloses right (cast (congrArg EventField.Action same) action) =
      publicationDiscloses left action := by cases same; rfl

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem publicationDiscloses_binding {kind : EventField Player L} {owner : Player}
    {payload : L.Ty} (typed : kind = .binding owner payload) (action : kind.Action) :
    publicationDiscloses kind action = false := by cases typed; rfl

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem publicationDiscloses_publicData {kind : EventField Player L} {payload : L.Ty}
    (typed : kind = .publicData payload) (action : kind.Action) :
    publicationDiscloses kind action = false := by cases typed; rfl

/-- A true publication completion came from an actual submitted opening.
There is no surviving-owner condition: a rejected guard can exclude the owner
in the very transition that records this true action. -/
def OpeningOrigins (messages : List (Message Player (CommitAttemptPacket graph)))
    (native : EventGraphRuntime.State graph) : Prop :=
  ∀ completion ∈ native.config.history,
    publicationDiscloses (graph.outputLayout completion.event) completion.action = true →
      ∃ message ∈ messages, ∃ candidate raw,
        message.payload.packet.call = .opening completion.event candidate raw

namespace OpeningOrigins

variable {messages : List (Message Player (CommitAttemptPacket graph))}
  {native : EventGraphRuntime.State graph}

omit [DecidableEq Player] in
theorem copy (valid : OpeningOrigins messages native)
    {next : EventGraphRuntime.State graph} (same : next.config.history = native.config.history) :
    OpeningOrigins messages next := by
  intro completion recorded disclosed
  exact valid completion (same ▸ recorded) disclosed

omit [DecidableEq Player] in
theorem mono (valid : OpeningOrigins messages native)
    {more : List (Message Player (CommitAttemptPacket graph))} (included : messages ⊆ more) :
    OpeningOrigins more native := by
  intro completion recorded disclosed
  obtain ⟨message, present, candidate, raw, call⟩ := valid completion recorded disclosed
  exact ⟨message, included present, candidate, raw, call⟩

omit [DecidableEq Player] in
theorem complete_nondisclosing (valid : OpeningOrigins messages native)
    (event : graph.EventId) (ready : native.config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value)
    (silent : publicationDiscloses (graph.outputLayout event) action = false) :
    OpeningOrigins messages (native.complete event ready action value) := by
  intro completion recorded disclosed
  change completion ∈ native.config.history ++ [⟨event, action⟩] at recorded
  rcases List.mem_append.mp recorded with previous | current
  · exact valid completion previous disclosed
  · have same := List.mem_singleton.mp current
    subst completion
    rw [silent] at disclosed
    cases disclosed

omit [DecidableEq Player] in
theorem completeFailure (valid : OpeningOrigins messages native)
    (event : graph.EventId) (ready : native.config.cut.Ready event) :
    OpeningOrigins messages (native.completeFailure event ready) := by
  cases viewed : nodeView graph event with
  | bind owner payload outputEq codeEq =>
      simp only [State.completeFailure, viewed]
      apply valid.complete_nondisclosing
      exact publicationDiscloses_cast outputEq.symm
        (PublicationResult.failure : PublicationResult (L.Val payload))
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [State.completeFailure, viewed]
      apply valid.complete_nondisclosing
      exact publicationDiscloses_cast outputEq.symm false
  | sample payload law outputEq codeEq =>
      simpa only [State.completeFailure, viewed] using valid

omit [DecidableEq Player] in
theorem automatic (valid : OpeningOrigins messages native) (excluded : Finset Player)
    (event : graph.EventId)
    (eligible : (⟨native, excluded⟩ : RecoveryState graph).AutomaticReady event) :
    OpeningOrigins messages
      ((⟨native, excluded⟩ : RecoveryState graph).completeAutomatic event eligible).native :=
  valid.completeFailure event eligible.1

theorem drain (valid : OpeningOrigins messages native) (excluded : Finset Player)
    (phase : RuntimePhase graph) :
    OpeningOrigins messages (phase.drain (⟨native, excluded⟩ : RecoveryState graph)).native := by
  have along : ∀ next,
      Relation.ReflTransGen phase.AutomaticStep (⟨native, excluded⟩ : RecoveryState graph) next →
        OpeningOrigins messages next.native := by
    intro next path
    induction path with
    | refl => exact valid
    | tail _ step ih =>
        obtain ⟨event, eligible, rfl⟩ := step
        exact ih.automatic _ event eligible.2
  exact along _ (phase.drain_trace _)

/-- Every accepting native handler supplies the actual envelope when it adds
a true publication. Malformed calls cannot complete events, and bindings have
no publication action. -/
theorem handle (valid : OpeningOrigins messages native) (runtime : EventGraphRuntime graph)
    (message : Message Player (CommitAttemptPacket graph)) (present : message ∈ messages)
    (next : EventGraphRuntime.State graph)
    (handled : EventGraphRuntime.handle runtime native
      ⟨message.id, message.payload.packet.call⟩ = some next) :
    OpeningOrigins messages next := by
  obtain ⟨event, named, ready, action, supported⟩ :=
    handle_config_mem_step runtime native next ⟨message.id, message.payload.packet.call⟩ handled
  intro completion recorded disclosed
  rw [native.config.step_history event ready action next.config supported] at recorded
  rcases List.mem_append.mp recorded with previous | current
  · exact valid completion previous disclosed
  · have same := List.mem_singleton.mp current
    subst completion
    cases packet : message.payload.packet.call with
    | malformed raw =>
        simp only [packet, Payload.event?] at named
        cases named
    | commitment actual candidate =>
        have eventEq : actual = event :=
          Option.some.inj (by simpa only [packet, Payload.event?] using named)
        subst actual
        rw [packet] at handled
        obtain ⟨_, _, owner, payload, outputEq, _code, _node, _rest⟩ :=
          handle_commitment_conditions runtime native next message.id event candidate handled
        change publicationDiscloses (graph.outputLayout event) action = true at disclosed
        rw [publicationDiscloses_binding outputEq action] at disclosed
        cases disclosed
    | opening actual candidate raw =>
        have eventEq : actual = event :=
          Option.some.inj (by simpa only [packet, Payload.event?] using named)
        exact ⟨message, present, candidate, raw, eventEq ▸ packet⟩

omit [DecidableEq Player] in
theorem step_nondisclosing (valid : OpeningOrigins messages native)
    (event : graph.EventId) (ready : native.config.cut.Ready event) (action : graph.Action event)
    (next : EventGraphRuntime.State graph)
    (supported : next.config ∈ (native.config.step event ready action).support)
    (silent : publicationDiscloses (graph.outputLayout event) action = false) :
    OpeningOrigins messages next := by
  intro completion recorded disclosed
  rw [native.config.step_history event ready action next.config supported] at recorded
  rcases List.mem_append.mp recorded with previous | current
  · exact valid completion previous disclosed
  · have same := List.mem_singleton.mp current
    subst completion
    rw [silent] at disclosed
    cases disclosed

omit [DecidableEq Player] in
theorem environment (valid : OpeningOrigins messages native) (runtime : EventGraphRuntime graph)
    (command : EnvironmentCommand graph) (next : EventGraphRuntime.State graph)
    (reached : next ∈ (environmentStep runtime native command).support) :
    OpeningOrigins messages next := by
  classical
  cases command with
  | advanceClock =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid
  | executeSample event =>
      obtain ⟨_clock, same | ⟨ready, action, supported, _activated⟩⟩ :=
        environmentStep_executeSample_config_activated runtime native next event reached
      · exact valid.copy (congrArg Config.history same.1)
      · cases viewed : nodeView graph event with
        | sample payload law outputEq codeEq =>
            apply valid.step_nondisclosing event ready action next supported
            exact publicationDiscloses_publicData outputEq action
        | bind | resolve =>
            have nonsample : ∀ payload law outputEq codeEq,
                nodeView graph event ≠ .sample payload law outputEq codeEq := by
              intro payload law outputEq codeEq impossible
              rw [viewed] at impossible
              cases impossible
            rw [environmentStep_executeSample_of_nonsample runtime native event ready nonsample,
              PMF.mem_support_pure_iff] at reached
            subst next
            exact valid
  | expire event =>
      by_cases ready : native.config.cut.Ready event
      · cases activated : native.activatedAt event with
        | none =>
            rw [environmentStep_expire_of_not_activated runtime native event ready activated,
              PMF.mem_support_pure_iff] at reached
            subst next
            exact valid
        | some entered =>
            by_cases due : runtime.deadline event ≤ native.clock - entered
            · cases viewed : nodeView graph event with
              | bind owner payload outputEq codeEq =>
                  rw [environmentStep_expire_bind_eq runtime native event ready entered activated
                    due owner payload outputEq codeEq viewed, PMF.mem_support_pure_iff] at reached
                  subst next
                  apply valid.complete_nondisclosing
                  exact publicationDiscloses_cast outputEq.symm
                    (PublicationResult.failure : PublicationResult (L.Val payload))
              | resolve owner payload binding checks outputEq codeEq =>
                  rw [environmentStep_expire_resolve_eq runtime native event ready entered
                    activated due owner payload binding checks outputEq codeEq viewed,
                    PMF.mem_support_pure_iff] at reached
                  subst next
                  apply valid.complete_nondisclosing
                  exact publicationDiscloses_cast outputEq.symm false
              | sample payload law outputEq codeEq =>
                  rw [environmentStep_expire_sample_eq runtime native event ready entered
                    activated due payload law outputEq codeEq viewed,
                    PMF.mem_support_pure_iff] at reached
                  subst next
                  exact valid
            · rw [environmentStep_expire_of_not_due runtime native event ready entered activated
                due, PMF.mem_support_pure_iff] at reached
              subst next
              exact valid
      · rw [environmentStep_expire_of_not_ready runtime native event ready,
          PMF.mem_support_pure_iff] at reached
        subst next
        exact valid

end OpeningOrigins

/-- Normalization retains opening origins through arbitrary drains, retry
restoration and phase advances. Saved and live histories are both tracked. -/
theorem settle_openingOrigins
    (messages : List (Message Player (CommitAttemptPacket graph)))
    (phases : List (RuntimePhase graph)) (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph))
    (saved : OpeningOrigins messages entry.native)
    (active : OpeningOrigins messages current.native) :
    let next := PhaseRuntimeState.settle phases generation entry current retired
    OpeningOrigins messages next.current.native ∧ OpeningOrigins messages next.entry.native := by
  induction phases generalizing generation entry current retired with
  | nil => exact ⟨active, saved⟩
  | cons phase remaining ih =>
      have drained := active.drain current.excluded phase
      have restored : OpeningOrigins messages
          (PhaseRuntimeState.restore entry (phase.drain current)).native := saved.copy rfl
      have rebuilt := restored.drain
        (PhaseRuntimeState.restore entry (phase.drain current)).excluded phase
      simp only [PhaseRuntimeState.settle]
      split
      · split
        · split
          · exact ⟨rebuilt, restored⟩
          · exact ih _ _ _ _ rebuilt rebuilt
        · exact ih _ _ _ _ drained drained
      · exact ⟨drained, saved⟩

end Vegas.EventGraphRuntime.PhaseProposal
