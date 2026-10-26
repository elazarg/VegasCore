/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseOwnCommitments
import Vegas.Pending.ReactiveBindingRepair
import Interaction.ReactiveTrafficState

/-! # Public provenance of occupied prepared candidates -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

private theorem submitted_prepared_fresh (state : State graph) (actor observer : Player)
    (material : WitnessedSubmission graph) (serial : Nat) :
    (submitStep (material.call.register state actor) actor material.call.packet).candidates.lookup
        (observer, .prepared serial) = .fresh ↔
      state.candidates.lookup (observer, .prepared serial) = .fresh ∧
        ¬ (actor = observer ∧ ∃ event,
          material.call.packet = .commitment event (observer, .prepared serial)) := by
  by_cases same : observer = actor
  · subst observer
    rw [material.call.candidateAfter_eq]
    cases packet : material.call.packet with
    | commitment event candidate =>
      rcases candidate with ⟨owner, slot⟩
      by_cases owned : owner = actor
      · subst owner
        cases slot with
        | initial input => simp [Submission.candidateAfter, packet]
        | prepared used =>
          by_cases selected : serial = used
          · subst used
            cases meaning : state.candidates.lookup (actor, .prepared serial) <;>
              cases opening : material.call.opening <;>
                simp [Submission.candidateAfter, packet, meaning, opening]
          · simp [Submission.candidateAfter, packet, selected, Ne.symm selected]
      · simp [Submission.candidateAfter, packet, owned]
    | opening | malformed => simp [Submission.candidateAfter, packet]
  · have view := (submitStep_playerView_other (material.call.register state actor) actor observer
      same material.call.packet).trans (material.call.register_other state actor observer same)
    have lookup := congrFun (congrArg PlayerView.candidates view) (.prepared serial)
    change (submitStep (material.call.register state actor) actor
      material.call.packet).candidates.lookup (observer, .prepared serial) =
      state.candidates.lookup (observer, .prepared serial) at lookup
    rw [lookup]
    simp [Ne.symm same]

/-- Freshness is determined by the authenticated commitment handles in the
actual input word; private opening values do not occur in this property. -/
def PhasePreparedInputs (execution : (app).Execution) : Prop :=
  ∀ who serial, execution.application.current.native.candidates.lookup
      (who, .prepared serial) = .fresh ↔
    ¬ ∃ message ∈ execution.network.inputs, message.sender = who ∧
      ∃ event, message.payload.packet.call = .commitment event (who, .prepared serial)

theorem PhasePreparedInputs.respond (execution : (app).Execution)
    (valid : PhasePreparedInputs runtime leaks execution) (actor : Player)
    (response : (app).Action) :
    PhasePreparedInputs runtime leaks (execution.respond (app) actor response) := by
  intro observer serial
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact valid observer serial
  | some material =>
    change (submitStep (material.call.register execution.application.current.native actor) actor
      material.call.packet).candidates.lookup (observer, .prepared serial) = .fresh ↔ _
    rw [submitted_prepared_fresh, valid observer serial]
    have emitted : ((execution.application.submit actor material).emit actor
        (execution.network.known actor) material).packet.call = material.call.packet :=
      phase_emit_call _ _ _ _
    change _ ↔ ¬ ∃ message ∈ execution.network.inputs ++
      [⟨(actor, execution.network.nextSerial actor),
        (execution.application.submit actor material).emit actor
          (execution.network.known actor) material⟩], _
    simp only [List.mem_append, List.mem_singleton, or_and_right,
      exists_or, exists_eq_left, Message.sender, emitted, not_or]

private theorem issued_handle_candidates (execution : (app).Execution)
    (valid : PhaseOwnCommitmentsFixed runtime leaks execution)
    (message : Message Player (CommitAttemptPacket graph))
    (issued : execution.Issued (app) message) (next : PhaseRuntimeState graph)
    (accepted : execution.application.handle runtime message = some next) :
    next.current.native.candidates = execution.application.current.native.candidates := by
  unfold PhaseRuntimeState.handle at accepted
  split at accepted
  · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
    dsimp only [PhaseRuntimeState.normalize]
    rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).2.1]
    change native.candidates = execution.application.current.native.candidates
    cases call : message.payload.packet.call with
    | commitment event candidate =>
      rw [call] at handled
      obtain ⟨tables, _, owned⟩ :=
        handle_commitment_tables runtime _ _ message.id event candidate handled
      obtain ⟨entry, member, material, _sent, emitted, _encoded⟩ := issued
      have output : message ∈ (app).outputs (execution.recall message.sender) :=
        List.mem_filterMap.mpr ⟨entry, member, emitted⟩
      have fixed : execution.application.current.native.candidates.lookup candidate ≠ .fresh := by
        have named : message.payload.packet.call =
            .commitment event (message.sender, candidate.2) := by
          rw [call]
          exact congrArg (Payload.commitment event) (Prod.ext owned rfl)
        have proof := valid message.sender message output event candidate.2 named
        have candidateEq : candidate = (message.sender, candidate.2) := Prod.ext owned rfl
        rw [candidateEq]
        exact proof
      rw [tables]
      exact execution.application.current.native.candidates.freeze_eq_self_of_not_fresh
        candidate fixed
    | opening event candidate raw =>
      exact (handle_resolution_tables runtime _ _ _ (by
        intro event candidate impossible
        change message.payload.packet.call = .commitment event candidate at impossible
        rw [call] at impossible
        cases impossible) handled).2
    | malformed raw => simp [call, handle] at handled
  · cases accepted

private theorem environment_candidates (execution next : (app).Execution)
    (valid : PhaseOwnCommitmentsFixed runtime leaks execution)
    (provenance : execution.Provenance (app)) (command : (app).Command)
    (reached : next ∈ (execution.environmentStep (app) command).support) :
    next.application.current.native.candidates =
      execution.application.current.native.candidates := by
  apply (app).environmentStep_cases execution next command reached
    (predicate := fun _ next => next.application.current.native.candidates =
      execution.application.current.native.candidates)
  · rfl
  · intros; rfl
  · intro id
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    cases found : execution.network.lookup id with
    | none => rfl
    | some message =>
      change (((app).handle execution.application message).getD
        execution.application).current.native.candidates = _
      cases accepted : (app).handle execution.application message with
      | none => rfl
      | some state =>
        exact issued_handle_candidates runtime leaks execution valid message
          (provenance.lookup id message found) state accepted
  · intro command state changed
    change state ∈ (execution.application.environment runtime command).support at changed
    unfold PhaseRuntimeState.environment at changed
    split at changed
    · obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ changed
      dsimp only [PhaseRuntimeState.normalize]
      rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).2.1]
      exact (environmentStep_tables runtime execution.application.current.native native command
        moved).2
    · cases (PMF.mem_support_pure_iff _ _).mp changed
      rfl

/-- The actual input word determines prepared freshness at every initialized
raw history, including arbitrary responses, inclusion and phase rollback. -/
theorem phasePreparedInputs_history (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) :
    ∀ {state} (_trace : ((app).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace state),
      ReactiveApplication.serviceInvariant (PhasePreparedInputs runtime leaks) state := by
  have invariant : (app).ServiceInvariant scheduler (fun execution =>
      PhasePreparedInputs runtime leaks execution ∧
      PhaseOwnCommitmentsFixed runtime leaks execution ∧ execution.Provenance (app)) := {
    respond := fun execution actor action valid =>
      ⟨valid.1.respond runtime leaks execution actor action,
        valid.2.1.respond runtime leaks actor action,
        (app).respond_provenance execution actor action valid.2.2⟩
    environment := by
      intro execution next command valid _ reached
      refine ⟨?_, valid.2.1.environmentStep runtime leaks command reached,
        (app).environment_provenance execution next command valid.2.2 reached⟩
      intro who serial
      rw [environment_candidates runtime leaks execution next valid.2.1 valid.2.2 command reached,
        (app).environmentStep_inputs execution next command reached]
      exact valid.1 who serial }
  intro state trace
  have valid := invariant.history (inputs.map (PhaseRuntimeState.initial plan)) horizon (by
    intro initial supported
    obtain ⟨input, _, rfl⟩ := PMF.support_map .. ▸ supported
    refine ⟨?_, ?_, MessageNetwork.Satisfies.empty⟩
    · intro who serial
      change (PhaseRuntimeState.initial plan input).current.native.candidates.lookup
        (who, .prepared serial) = .fresh ↔ _
      unfold PhaseRuntimeState.initial
      rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).2.1,
        State.initial_candidate input who (.prepared serial)]
      simp [ReactiveApplication.Execution.initial, MessageNetwork.empty]
    · intro who message member
      cases member) trace
  cases state with
  | none => trivial
  | some control => exact valid.1

/-- Equal actual input words give the same canonical physical slot, even
when the two private candidate meanings and source priors differ. -/
theorem reactiveFreshSlot_eq_of_phasePreparedInputs (left right : (app).Execution)
    (first : PhasePreparedInputs runtime leaks left)
    (second : PhasePreparedInputs runtime leaks right)
    (inputs : left.network.inputs = right.network.inputs) (who : Player) :
    reactiveFreshSlot (left.application.current.native.playerView who) =
      reactiveFreshSlot (right.application.current.native.playerView who) := by
  apply reactiveFreshSlot_congr
  intro serial
  change left.application.current.native.candidates.lookup _ = .fresh ↔
    right.application.current.native.candidates.lookup _ = .fresh
  rw [first who serial, second who serial, inputs]

end Vegas.EventGraphRuntime
