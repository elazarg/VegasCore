/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalAcceptedHistory
import Interaction.ReactiveReceipts

/-! # Recorded TRUE native disclosures have actual TRUE physical receipts -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

open scoped Classical in
/-- Literal submitted inputs whose permanent physical receipt is TRUE. -/
def trueReceiptInputs (execution : (app).Execution) :
    List (Message Player (CommitAttemptPacket graph)) :=
  execution.network.inputs.filter fun message => (message.id, true) ∈ execution.receipts

private theorem trueReceiptInputs_mono (before after : (app).Execution)
    (inputs : before.network.inputs ⊆ after.network.inputs)
    (receipts : before.receipts ⊆ after.receipts) :
    trueReceiptInputs runtime leaks before ⊆ trueReceiptInputs runtime leaks after := by
  classical
  intro message member
  obtain ⟨input, accepted⟩ := List.mem_filter.mp member
  exact List.mem_filter.mpr ⟨inputs input,
    by simpa only [decide_eq_true_eq] using receipts (of_decide_eq_true accepted)⟩

/-- Existing opening-origin semantics instantiated with the actual
TRUE-receipted input list. Guard acceptance is not part of this certificate. -/
def OpeningReceiptOrigins (execution : (app).Execution) : Prop :=
  OpeningOrigins (trueReceiptInputs runtime leaks execution)
      execution.application.current.native ∧
    OpeningOrigins (trueReceiptInputs runtime leaks execution)
      execution.application.entry.native

private theorem receiptOrigins_respond (execution : (app).Execution) (owner : Player)
    (response : (app).Action) (valid : OpeningReceiptOrigins runtime leaks execution) :
    OpeningReceiptOrigins runtime leaks (execution.respond app owner response) := by
  have inputs : execution.network.inputs ⊆
      (execution.respond app owner response).network.inputs := by
    cases response with
    | mk transmission => cases transmission with
      | none => exact List.Subset.refl _
      | some material => exact List.subset_append_left _ _
  have more := trueReceiptInputs_mono runtime leaks execution (execution.respond app owner response)
    inputs (by rw [(app).respond_receipts])
  cases response with
  | mk transmission =>
      cases transmission with
      | none => exact ⟨valid.1.mono more, valid.2.mono more⟩
      | some material =>
          refine ⟨(valid.1.mono more).copy ?_, valid.2.mono more⟩
          change (submitStep (material.call.register execution.application.current.native owner)
            owner material.call.packet).config.history = _
          rw [submitStep_config, (material.call.register_facts owner _).1]

private theorem trueReceiptInputs_include_message (execution : (app).Execution)
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (found : execution.network.lookup id = some message) (next : PhaseRuntimeState graph)
    (handled : execution.application.handle runtime message = some next)
    (origins : execution.Provenance app) (recalled : execution.InputRecall app) :
    message ∈ trueReceiptInputs runtime leaks (execution.includePending app id) := by
  classical
  have addressed : message.id = id := by
    simpa only [decide_eq_true_eq] using (List.find?_eq_some_iff_append.mp found).1
  have input := ((app).retained_envelopes_mem_inputs execution origins recalled).lookup
    id message found
  apply List.mem_filter.mpr
  constructor
  · simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found] using input
  · apply decide_eq_true
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, show (app).handle execution.application message = some next from handled,
      Option.isSome_some, addressed]
    exact List.mem_append_right _ (List.mem_singleton_self _)

/-- The original native result of an actual accepting inclusion retains its
TRUE-receipted opening origins before the dispatcher normalizes any phase. -/
theorem OpeningReceiptOrigins.inclusion (execution : (app).Execution)
    (valid : OpeningReceiptOrigins runtime leaks execution)
    (origins : execution.Provenance app) (recalled : execution.InputRecall app)
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (found : execution.network.lookup id = some message) (next : PhaseRuntimeState graph)
    (handled : execution.application.handle runtime message = some next)
    (native : EventGraphRuntime.State graph)
    (accepted : EventGraphRuntime.handle runtime execution.application.current.native
      ⟨message.id, message.payload.packet.call⟩ = some native) :
    OpeningOrigins (trueReceiptInputs runtime leaks (execution.includePending app id)) native := by
  have inputs : (execution.includePending app id).network.inputs = execution.network.inputs := by
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    cases execution.network.lookup id <;> rfl
  have more := trueReceiptInputs_mono runtime leaks execution (execution.includePending app id)
    (by rw [inputs])
    ((app).includePending_receipts_prefix execution id).subset
  exact (valid.1.mono more).handle runtime message
    (trueReceiptInputs_include_message runtime leaks execution id message found next handled
      origins recalled) native accepted

private theorem receiptOrigins_includePending (execution : (app).Execution) (id : MessageId Player)
    (valid : OpeningReceiptOrigins runtime leaks execution)
    (origins : execution.Provenance app) (recalled : execution.InputRecall app) :
    OpeningReceiptOrigins runtime leaks (execution.includePending app id) := by
  classical
  let after := execution.includePending app id
  have inputs : after.network.inputs = execution.network.inputs := by
    unfold after ReactiveApplication.Execution.includePending MessageNetwork.includePending
    cases execution.network.lookup id <;> rfl
  have more := trueReceiptInputs_mono runtime leaks execution after
    (by rw [inputs])
    ((app).includePending_receipts_prefix execution id).subset
  have active := valid.1.mono more
  have saved := valid.2.mono more
  cases found : execution.network.lookup id with
  | none =>
      simp only [OpeningReceiptOrigins, after, ReactiveApplication.Execution.includePending,
        MessageNetwork.includePending, found] at active saved ⊢
      exact ⟨active, saved⟩
  | some message =>
      cases handled : execution.application.handle runtime message with
      | none =>
          simp only [OpeningReceiptOrigins, after, ReactiveApplication.Execution.includePending,
            MessageNetwork.includePending, found,
            show (app).handle execution.application message = none from handled,
            Option.getD_none] at active saved ⊢
          exact ⟨active, saved⟩
      | some next =>
          have present := trueReceiptInputs_include_message runtime leaks execution id message
            found next handled origins recalled
          have actual := handled
          unfold PhaseRuntimeState.handle at handled
          split at handled
          · obtain ⟨native, accepted, rfl⟩ := Option.map_eq_some_iff.mp handled
            have retained := settle_openingOrigins (trueReceiptInputs runtime leaks after)
              execution.application.phases execution.application.generation
              execution.application.entry
              (execution.application.current.inclusionResult message.payload.packet.call native)
              execution.application.retired saved
                (active.handle runtime message present native accepted)
            simpa only [OpeningReceiptOrigins, after, PhaseRuntimeState.normalize,
              ReactiveApplication.Execution.includePending, MessageNetwork.includePending, found,
              show (app).handle execution.application message = some _ from actual,
              Option.getD_some] using retained
          · cases handled

private theorem receiptOrigins_environment (execution next : (app).Execution)
    (command : (app).Command) (valid : OpeningReceiptOrigins runtime leaks execution)
    (origins : execution.Provenance app) (recalled : execution.InputRecall app)
    (reached : next ∈ (execution.environmentStep app command).support) :
    OpeningReceiptOrigins runtime leaks next := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff ..).mp reached
      exact valid
  | activate owner =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨sample, _selected, rfl⟩ := PMF.support_map .. ▸ supported
      exact valid
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff ..).mp reached
      exact receiptOrigins_includePending runtime leaks execution id valid origins recalled
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ (execution.application.environment runtime command).support at changed
      unfold PhaseRuntimeState.environment at changed
      split at changed
      · obtain ⟨native, nativeMoved, rfl⟩ := PMF.support_map .. ▸ changed
        exact settle_openingOrigins (trueReceiptInputs runtime leaks execution) _ _ _ _ _ valid.2
          (valid.1.environment runtime command native nativeMoved)
      · cases (PMF.mem_support_pure_iff ..).mp changed
        exact valid

/-- Every actual TRUE native publication action retains a TRUE physical
opening receipt, even when that same inclusion rejects its semantic guard. -/
theorem openingReceiptOrigins_history (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control)) :
    OpeningReceiptOrigins runtime leaks control.execution := by
  have invariant : (app).ServiceInvariant scheduler (fun execution =>
      OpeningReceiptOrigins runtime leaks execution ∧ execution.Provenance app ∧
        execution.InputRecall app) := {
    respond := fun execution owner action valid =>
      ⟨receiptOrigins_respond runtime leaks execution owner action valid.1,
        (app).respond_provenance execution owner action valid.2.1,
        (app).respond_inputRecall execution owner action valid.2.2⟩
    environment := fun execution next command valid _ reached =>
      ⟨receiptOrigins_environment runtime leaks execution next command valid.1 valid.2.1 valid.2.2
          reached,
        (app).environment_provenance execution next command valid.2.1 reached,
        (app).environment_inputRecall execution next command valid.2.2 reached⟩ }
  exact (invariant.history _ horizon (by
    intro state supported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    refine ⟨?_, MessageNetwork.Satisfies.empty, (app).initial_inputRecall _⟩
    apply settle_openingOrigins
    all_goals intro completion recorded; cases recorded) trace).1

end Vegas.EventGraphRuntime.PhaseProposal
