/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseSingleton

/-! # Rebuilding an excluded singleton preserves its actual native result

The saved frontier is compared with the physical state immediately before its
single automatic completion. Candidate meanings, accepted handles and the clock
are retained exactly; only the completed event's obsolete timer can differ.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace State

omit [DecidableEq Player] in
theorem Invariant.only_ready_activated {state : State graph} {inputs : graph.Inputs}
    (valid : state.Invariant inputs) (event : graph.EventId)
    (unique : ∀ other, state.config.cut.Ready other → other = event)
    (other : graph.EventId) (different : other ≠ event) : state.activatedAt other = none := by
  cases recorded : state.activatedAt other with
  | none => rfl
  | some clock =>
      have ready := ((valid.activated_iff other).mp (by rw [recorded]; rfl)).1
      exact (different (unique other ready)).elim

omit [DecidableEq Player] in
/-- Completing the only potentially activated event erases its prior timer. -/
theorem complete_eq_of_only_current_activated (left right : State graph)
    (event : graph.EventId) (leftReady : left.config.cut.Ready event)
    (rightReady : right.config.cut.Ready event)
    (sameConfig : left.config = right.config) (sameAccepted : left.accepted = right.accepted)
    (sameCandidates : left.candidates = right.candidates) (sameClock : left.clock = right.clock)
    (leftOnly : ∀ other, other ≠ event → left.activatedAt other = none)
    (rightOnly : ∀ other, other ≠ event → right.activatedAt other = none)
    (action : graph.Action event) (value : (graph.outputLayout event).Value) :
    left.complete event leftReady action value = right.complete event rightReady action value := by
  cases left with
  | mk leftConfig leftAccepted leftCandidates leftClock leftActivated =>
      cases right with
      | mk rightConfig rightAccepted rightCandidates rightClock rightActivated =>
          dsimp only at sameConfig sameAccepted sameCandidates sameClock
          cases sameConfig
          cases sameAccepted
          cases sameCandidates
          cases sameClock
          dsimp only at leftOnly rightOnly
          dsimp only [complete]
          congr 1
          funext other
          unfold refreshActivated
          split
          · rename_i nextReady
            have different : other ≠ event := by
              intro same
              subst other
              exact nextReady.1 (by simp [Config.complete])
            rw [leftOnly other different, rightOnly other different]
          · rfl

omit [DecidableEq Player] in
theorem completeFailure_eq_of_only_current_activated (left right : State graph)
    (event : graph.EventId) (leftReady : left.config.cut.Ready event)
    (rightReady : right.config.cut.Ready event) {owner : Player}
    (owned : graph.actor? event = some owner)
    (sameConfig : left.config = right.config) (sameAccepted : left.accepted = right.accepted)
    (sameCandidates : left.candidates = right.candidates) (sameClock : left.clock = right.clock)
    (leftOnly : ∀ other, other ≠ event → left.activatedAt other = none)
    (rightOnly : ∀ other, other ≠ event → right.activatedAt other = none) :
    left.completeFailure event leftReady = right.completeFailure event rightReady := by
  cases view : nodeView graph event with
  | bind owner payload outputEq codeEq | resolve owner payload binding checks outputEq codeEq =>
      simp only [completeFailure, view]
      exact complete_eq_of_only_current_activated left right event leftReady rightReady
        sameConfig sameAccepted sameCandidates sameClock leftOnly rightOnly _ _
  | sample payload law outputEq codeEq =>
      obtain ⟨action, supported⟩ := left.completeFailure_step event leftReady owned
      have progress := left.config.remaining_step event leftReady action _ supported
      simp only [completeFailure, view] at progress
      omega

end State

namespace RuntimePhase

/-- Restoring and draining one excluded event reproduces its actual completed
state when its saved config and associations are the preceding frontier. -/
theorem restore_completeAutomatic (phase : RuntimePhase graph)
    (entry current : RecoveryState graph) {inputs : graph.Inputs}
    (valid : current.native.Invariant inputs) (event : graph.EventId)
    (only : phase.events = {event}) (eligible : current.AutomaticReady event)
    (savedConfig : entry.native.config = current.native.config)
    (savedAccepted : entry.native.accepted = current.native.accepted)
    (unique : ∀ other, current.native.config.cut.Ready other → other = event) :
    phase.drain (PhaseRuntimeState.restore entry (current.completeAutomatic event eligible)) =
      current.completeAutomatic event eligible := by
  let failed := current.completeAutomatic event eligible
  let restored := PhaseRuntimeState.restore entry failed
  have restoredReady : restored.AutomaticReady event := by
    change entry.native.config.cut.Ready event ∧ _
    rw [savedConfig]
    exact eligible
  rw [phase.drain_eq_completeAutomatic_of_singleton restored event only restoredReady]
  have tables := current.native.completeFailure_tables event eligible.1
  obtain ⟨owner, acting, _⟩ := eligible.owned
  have native : restored.native.completeFailure event restoredReady.1 =
      current.native.completeFailure event eligible.1 := by
    apply State.completeFailure_eq_of_only_current_activated restored.native current.native
      event restoredReady.1 eligible.1 acting savedConfig savedAccepted tables.2.1 tables.2.2
    · intro other different
      have absent : ¬ entry.native.config.cut.Ready other := by
        rw [savedConfig]
        exact fun ready => different (unique other ready)
      change State.refreshActivated entry.native.config failed.native.clock
        (fun _ => none) other = none
      simp only [State.refreshActivated, dite_eq_right absent]
    · exact valid.only_ready_activated event unique
  change (⟨restored.native.completeFailure event restoredReady.1, current.excluded⟩ :
      RecoveryState graph) = ⟨current.native.completeFailure event eligible.1, current.excluded⟩
  exact congrArg (fun state => (⟨state, current.excluded⟩ : RecoveryState graph)) native

end RuntimePhase

end Vegas.EventGraphRuntime
