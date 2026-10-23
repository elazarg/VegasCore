/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseBindingForeignMemory

/-! # Logical shadow masks at actual restored frontiers

Candidate meanings belong to permanent physical slots. Logical output and
completion overrides belong only to events present at the current checkpoint;
a retry must discard a canceled producer's override before automatic drain.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

open Classical in
/-- Retain semantic overrides only for an actual completed frontier. Physical
candidate overrides remain literal, including preparations of retired attempts. -/
def restrictCompleted (memory : BindingShadow graph) (completed : Finset graph.EventId) :
    BindingShadow graph :=
  { memory with
    values := fun field => match field with
      | .inl input => memory.values (.inl input)
      | .inr event => if event ∈ completed then memory.values (.inr event) else none
    actions := fun event => if event ∈ completed then memory.actions event else none }

@[simp] theorem restrictCompleted_candidates (memory : BindingShadow graph)
    (completed : Finset graph.EventId) :
    (memory.restrictCompleted completed).candidates = memory.candidates := rfl

theorem restrictCompleted_pending (memory : BindingShadow graph)
    (completed : Finset graph.EventId) (event : graph.EventId) (missing : event ∉ completed) :
    (memory.restrictCompleted completed).values (.inr event) = none ∧
      (memory.restrictCompleted completed).actions event = none := by
  classical
  simp only [restrictCompleted, missing, ite_false, and_self]

/-- Masking cannot change a saved configuration whose completed producers
are retained. In particular, it cannot alter any saved live binding meaning. -/
theorem restrictCompleted_config (memory : BindingShadow graph)
    (completed : Finset graph.EventId) (state : graph.Config)
    (retained : state.cut.completed ⊆ completed) :
    (memory.restrictCompleted completed).config state = memory.config state := by
  classical
  apply Config.ext_fields (left := (memory.restrictCompleted completed).config state)
    (right := memory.config state) rfl rfl
  · funext event
    by_cases present : event ∈ completed
    · simp only [config, restrictCompleted, present, ite_true]
    · have missing : state.outputs event = none := by
        cases stored : state.outputs event with
        | none => rfl
        | some value =>
            exact (present (retained ((state.output_available event).mp
              (by rw [stored]; rfl)))).elim
      simp only [config, missing, Option.map_none]
  · apply List.map_congr_left
    intro entry member
    have present : entry.event ∈ completed := retained
      ((state.history_exact entry.event).mp (List.mem_map.mpr ⟨entry, member, rfl⟩))
    simp only [completion, restrictCompleted, present, ite_true]

/-- The mask retains exactly the same permitted kinds of hidden overrides. -/
theorem OwnBindings.restrictCompleted {memory : BindingShadow graph} {owner : Player}
    (owned : memory.OwnBindings owner) (completed : Finset graph.EventId) :
    (memory.restrictCompleted completed).OwnBindings owner := by
  classical
  constructor
  · intro field present
    cases field with
    | inl input => exact owned.1 _ present
    | inr event =>
        change (if event ∈ completed then memory.values (.inr event) else none).isSome = true
          at present
        by_cases kept : event ∈ completed
        · exact owned.1 _ (by simpa only [kept, ite_true] using present)
        · simp only [kept, ite_false, Option.isSome_none,
            Bool.false_eq_true] at present
  · intro event present
    change (if event ∈ completed then memory.actions event else none).isSome = true at present
    by_cases kept : event ∈ completed
    · exact owned.2 _ (by simpa only [kept, ite_true] using present)
    · simp only [kept, ite_false, Option.isSome_none,
        Bool.false_eq_true] at present

variable [DecidableEq Player]

/-- Only semantic masks change; the current physical catalogue, timers,
accepted handles and unchanged live outputs retain their existing frame. -/
theorem restrictCompleted_native (memory : BindingShadow graph) (owner : Player)
    (completed : Finset graph.EventId) (state : State graph)
    (retained : state.config.cut.completed ⊆ completed) :
    (memory.restrictCompleted completed).native owner state = memory.native owner state := by
  have same := restrictCompleted_config memory completed state.config retained
  unfold native
  rw [same]
  rfl

/-- Apply the logical mask at the actual restoration edge, before rebuilt
excluded events are automatically completed. Physical slot overrides survive. -/
theorem restrictCompleted_restore (memory : BindingShadow graph) (owner : Player)
    (entry current : RecoveryState graph) :
    (memory.restrictCompleted entry.native.config.cut.completed).recovery owner
        (PhaseRuntimeState.restore entry current) =
      PhaseRuntimeState.restore (memory.recovery owner entry) (memory.recovery owner current) := by
  rw [restore_phased]
  apply congrArg (fun native => RecoveryState.mk native current.excluded)
  exact restrictCompleted_native memory owner entry.native.config.cut.completed _
    (fun _ member => member)

/-- Updating a new producer cannot materialize it in the saved checkpoint.
This retains the existing completion proof, without a second replay runner. -/
theorem rememberCompletion_saved (memory : BindingShadow graph) (owner : Player)
    (entry : RecoveryState graph) (event : graph.EventId)
    (missing : event ∉ entry.native.config.cut.completed)
    (action : graph.Action event) (value : (graph.outputLayout event).Value) :
    (memory.rememberCompletion event action value).recovery owner entry =
      memory.recovery owner entry := by
  apply congrArg (fun native => RecoveryState.mk native entry.excluded)
  exact rememberCompletion_native_pending memory owner entry.native event missing action value

/-- A ready producer has no inherited logical override after masking the
actual completed frontier. Its real failure completion therefore commutes. -/
theorem restrictCompleted_completeFailure (memory : BindingShadow graph) (owner : Player)
    (completed : Finset graph.EventId)
    (state : State graph) (event : graph.EventId) (ready : state.config.cut.Ready event) :
    completed ⊆ state.config.cut.completed →
    let masked := memory.restrictCompleted completed
    masked.native owner (state.completeFailure event ready) =
      (masked.native owner state).completeFailure event ready := by
  classical
  intro retained
  dsimp only
  obtain ⟨noValue, noAction⟩ := restrictCompleted_pending memory completed event
    (fun present => ready.1 (retained present))
  cases node : nodeView graph event with
  | bind author payload outputEq codeEq =>
      simp only [State.completeFailure, node]
      exact native_complete_unmodified _ owner state event ready noValue noAction _ _
  | resolve author payload binding checks outputEq codeEq =>
      simp only [State.completeFailure, node]
      exact native_complete_unmodified _ owner state event ready noValue noAction _ _
  | sample payload law outputEq codeEq => simp only [State.completeFailure, node]

/-- Actual excluded-owner service uses the same mask, regardless of the
excluded set. It does not require a clear attempt or an empty retired archive. -/
theorem restrictCompleted_completeAutomatic (memory : BindingShadow graph) (owner : Player)
    (completed : Finset graph.EventId)
    (state : RecoveryState graph) (event : graph.EventId)
    (eligible : state.AutomaticReady event)
    (retained : completed ⊆ state.native.config.cut.completed) :
    let masked := memory.restrictCompleted completed
    masked.recovery owner (state.completeAutomatic event eligible) =
      (masked.recovery owner state).completeAutomatic event eligible := by
  dsimp only
  apply congrArg (fun native => RecoveryState.mk native state.excluded)
  exact restrictCompleted_completeFailure memory owner completed state.native event eligible.1
    retained

end Vegas.EventGraphRuntime.BindingShadow
