/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseBindingStamp
import Vegas.Pending.PhaseFrontier
import Vegas.Pending.PhaseExclusionEvidence
import Vegas.Pending.AcceptedEventOwnership
import Vegas.Pending.ExclusionNativeFailure
import Interaction.ReactiveNormalHistory

/-! # Authentic attempt stamps of completed events of nonexcluded owners -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A completed owned event is in the saved prefix or has an authentic owner
output in the current attempt. Newly automatic and expired completions belong
to excluded owners, so they do not require a player-authored output. -/
def CompletionStamp
    (outputs : Player → List (Message Player (CommitAttemptPacket graph)))
    (attempt : CommitAttemptId) (state : RecoveryState graph) : Prop :=
  ∀ event owner, graph.actor? event = some owner → event ∈ state.native.config.cut.completed →
    owner ∉ state.excluded →
    event.val < attempt.phase ∨ ∃ message ∈ outputs owner,
      message.sender = owner ∧ message.payload.packet.call.event? graph = some event ∧
        message.payload.attempt = attempt

namespace CompletionStamp

variable {outputs : Player → List (Message Player (CommitAttemptPacket graph))}
  {attempt : CommitAttemptId} {state : RecoveryState graph}

omit [DecidableEq Player] in
theorem copy {next : RecoveryState graph} (valid : CompletionStamp outputs attempt state)
    (config : next.native.config = state.native.config)
    (excluded : next.excluded = state.excluded) :
    CompletionStamp outputs attempt next := by
  simpa only [CompletionStamp, config, excluded] using valid

omit [DecidableEq Player] in
theorem mono {more : Player → List (Message Player (CommitAttemptPacket graph))}
    (valid : CompletionStamp outputs attempt state) (contains : ∀ who, outputs who ⊆ more who) :
    CompletionStamp more attempt state := by
  intro event owner acting completed active
  rcases valid event owner acting completed active with before | ⟨message, member, rest⟩
  · exact Or.inl before
  · exact Or.inr ⟨message, contains owner member, rest⟩

omit [DecidableEq Player] in
theorem of_before (attempt : CommitAttemptId) (state : RecoveryState graph)
    (before : ∀ event, event ∈ state.native.config.cut.completed → event.val < attempt.phase) :
    CompletionStamp outputs attempt state :=
  fun event _owner _acting completed _active => Or.inl (before event completed)

omit [DecidableEq Player] in
theorem completeAutomatic (valid : CompletionStamp outputs attempt state) (event : graph.EventId)
    (eligible : state.AutomaticReady event) :
    CompletionStamp outputs attempt (state.completeAutomatic event eligible) := by
  intro query owner acting completed active
  by_cases previous : query ∈ state.native.config.cut.completed
  · exact valid query owner acting previous active
  · obtain ⟨action, supported⟩ := state.completeAutomatic_step event eligible
    have same := State.completed_event_eq_of_step supported previous completed
    subst query
    obtain ⟨principal, owned, excluded⟩ := eligible.owned
    have ownerEq : principal = owner := Option.some.inj (owned.symm.trans acting)
    exact (active (ownerEq ▸ excluded)).elim

theorem drain (valid : CompletionStamp outputs attempt state) (phase : RuntimePhase graph) :
    CompletionStamp outputs attempt (phase.drain state) := by
  exact phase.drainFuel_induction (CompletionStamp outputs attempt)
    (fun _ event eligible previous => previous.completeAutomatic event eligible.2) _ state valid

/-- Native acceptance authenticates the sender of the uniquely completed
event. The actual issued envelope supplies its unmodified attempt stamp. -/
theorem inclusionResult (valid : CompletionStamp outputs attempt state)
    (runtime : EventGraphRuntime graph)
    (message : Message Player (CommitAttemptPacket graph)) (native : State graph)
    (accepted : handle runtime state.native ⟨message.id, message.payload.packet.call⟩ = some native)
    (sent : message ∈ outputs message.sender) (current : message.payload.attempt = attempt) :
    CompletionStamp outputs attempt (state.inclusionResult message.payload.packet.call native) := by
  intro query owner acting completed active
  by_cases previous : query ∈ state.native.config.cut.completed
  · exact valid query owner acting previous (fun excluded => active
      (state.inclusionResult_excluded_subset _ _ excluded))
  · obtain ⟨event, named, ready, action, supported⟩ :=
      handle_config_mem_step runtime state.native native
        ⟨message.id, message.payload.packet.call⟩ accepted
    have same := State.completed_event_eq_of_step supported previous completed
    subst query
    obtain ⟨actual, addressed, author⟩ := handle_event_actor runtime state.native native
      ⟨message.id, message.payload.packet.call⟩ accepted
    have actualEq : actual = event := Option.some.inj (addressed.symm.trans named)
    subst actual
    have sender : message.sender = owner := Option.some.inj (author.symm.trans acting)
    exact Or.inr ⟨message, sender ▸ sent, sender, named, current⟩

/-- An environment completion of an owned event is an expiry and permanently
excludes that owner. Every nonexcluded owned completion therefore predates it. -/
theorem environmentResult (valid : CompletionStamp outputs attempt state)
    (runtime : EventGraphRuntime graph) (command : EnvironmentCommand graph) (native : State graph)
    (reached : native ∈ (environmentStep runtime state.native command).support) :
    CompletionStamp outputs attempt (state.environmentResult command native) := by
  intro query owner acting completed active
  by_cases previous : query ∈ state.native.config.cut.completed
  · exact valid query owner acting previous (fun excluded => active
      (state.environmentResult_excluded_subset _ _ excluded))
  · cases command with
    | advanceClock =>
        simp only [environmentStep, PMF.mem_support_pure_iff] at reached
        subst native
        exact (previous completed).elim
    | executeSample event =>
        rcases (environmentStep_executeSample_config_activated runtime state.native native event
          reached).2 with ⟨same, _⟩ | ⟨ready, action, supported, _⟩
        · exact (previous (same ▸ completed)).elim
        · have same := State.completed_event_eq_of_step supported previous completed
          subst query
          cases view : nodeView graph event with
          | sample payload law outputEq codeEq =>
              have unowned : graph.actor? event = none :=
                (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
                  (congrArg EventCode.actor codeEq)
              rw [unowned] at acting
              cases acting
          | bind | resolve =>
              have nonsample : ∀ payload law outputEq codeEq,
                  nodeView graph event ≠ .sample payload law outputEq codeEq := by
                intro payload law outputEq codeEq same
                rw [view] at same
                cases same
              rw [environmentStep_executeSample_of_nonsample runtime state.native event ready
                nonsample, PMF.mem_support_pure_iff] at reached
              subst native
              exact (previous completed).elim
    | expire event =>
        rcases environmentStep_expire_config_eq_or_mem_step runtime state.native native event
          reached with same | ⟨ready, action, supported⟩
        · exact (previous (same ▸ completed)).elim
        · have same := State.completed_event_eq_of_step supported previous completed
          subst query
          apply False.elim
          apply active
          change owner ∈ (if event ∉ state.native.config.cut.completed ∧
            event ∈ native.config.cut.completed then
              RecoveryState.excludeEvent state.excluded event else state.excluded)
          change event ∈ native.config.cut.completed at completed
          rw [ite_eq_left ⟨previous, completed⟩]
          simp only [RecoveryState.excludeEvent, acting, Finset.mem_insert_self]

end CompletionStamp

namespace PhaseRuntimeState

/-- Phase-local automatic service, rollback and advancement preserve the
current-attempt provenance of every completed nonexcluded owned event. -/
theorem settle_completionStamp
    (outputs : Player → List (Message Player (CommitAttemptPacket graph)))
    (phases : List (RuntimePhase graph)) (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph))
    (frontier : Frontier
      (⟨phases, generation, entry, current, retired⟩ : PhaseRuntimeState graph))
    (active : CompletionStamp outputs ⟨phaseLow phases, generation⟩ current) :
    CompletionStamp outputs (settle phases generation entry current retired).attempt
      (settle phases generation entry current retired).current := by
  induction phases generalizing generation entry current retired with
  | nil => exact CompletionStamp.of_before _ _ (fun event _ => event.isLt)
  | cons phase remaining ih =>
      have saved := frontier.positioned.1
      have within := phase.drain_within current frontier.positioned.2
      have drained := active.drain phase
      have rebuilt :=
        (CompletionStamp.of_before (outputs := outputs) ⟨phase.low, generation + 1⟩
          (restore entry (phase.drain current)) (fun event completed =>
            (saved.2 event).mp completed)).drain phase
      have advance (next : RecoveryState graph) (archive : List (RetiredCommitAttempt graph))
          (position : next.native.config.cut.IsPrefix phase.high) :
          CompletionStamp outputs (settle remaining generation next next archive).attempt
            (settle remaining generation next next archive).current := by
        have nextPosition := positioned_next phase remaining next frontier.adjacent frontier.last
          position
        apply ih generation next next archive
          ⟨nextPosition.adjacent, nextPosition.last, nextPosition.positioned⟩
        apply CompletionStamp.of_before
        intro event completed
        cases rest : remaining with
        | nil => exact event.isLt
        | cons following tail =>
            have positioned := nextPosition.positioned
            rw [rest] at positioned
            exact (positioned.1.2 event).mp completed
      simp only [settle]
      split
      · rename_i finished
        split
        · rename_i failure
          split
          · exact rebuilt
          · rename_i exhausted
            have restoredWithin := saved.within phase.nonempty.le
            have allExcluded : phase.owners ⊆ (restore entry (phase.drain current)).excluded := by
              intro owner owned
              by_contra outside
              exact exhausted ⟨owner, Finset.mem_sdiff.mpr ⟨owned, outside⟩⟩
            have completed := phase.drain_finished_of_excluded
              (restore entry (phase.drain current)) restoredWithin failure.1 allExcluded
            exact advance _ _ (phase.finished_prefix _ (phase.drain_within _ restoredWithin)
              completed)
        · exact advance _ _ (phase.finished_prefix _ within finished)
      · exact drained

theorem normalize_completionStamp
    (outputs : Player → List (Message Player (CommitAttemptPacket graph)))
    (state : PhaseRuntimeState graph) (frontier : state.Frontier)
    (active : CompletionStamp outputs state.attempt state.current) :
    CompletionStamp outputs state.normalize.attempt state.normalize.current :=
  settle_completionStamp outputs state.phases state.generation state.entry state.current
    state.retired frontier active

end PhaseRuntimeState
end Vegas.EventGraphRuntime
