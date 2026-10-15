/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourcePolicyInformation
import Vegas.Game.CommitRecoveryContinuingProbability
import Vegas.Pending.PhaseClearTraceProgress
import Interaction.ReactiveRecordedResponse

/-! # Nonomitting physical bindings under continuing source strategies -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  (continuing : ∀ who (site : setup.commitRecoveryModel.InformationSite who),
    ∀ choice ∈ (assessment.strategy who site.1).support,
      setup.CommitRecoveryContinues who site.1 choice.1)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (capacity : horizon ≤ bounds.candidateCount)
  (control : (phaseApplication runtime leaks).Control)
  (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
  (who : Player) (active : control.actor = some who)
  (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
  (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
  (request : control.execution.application.SeedRequest who
    ⟨control.execution.application.attempt, event⟩)
  (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
    PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
  (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
  (clear : control.execution.application.current.excluded = ∅)

local notation "app" => phaseApplication runtime leaks
local notation "actual" => phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
  who (control.execution.recall who) (control.execution.observe app who)

include continuing maximal capacity trace active binding request unsent values clear

/-- Every supported physical binding response sends its canonical fresh handle.
The distinct source omission flag is absent at the genuine decoded source site;
an accepted unusable binding still sends a packet. -/
theorem phaseSourcePolicy_binding_emits_of_continuing
    (response : (app).Action) (supported : response ∈ (actual).support) :
    ∃ serial result, serial < horizon ∧
      response = phaseBindingResponse runtime leaks who event payload result serial := by
  classical
  obtain ⟨view, serial, _decoded, played, bounded, law, _result⟩ :=
    phaseSourcePolicy_binding_at_played_information setup mode runtime leaks bounds wellFormed
      assessment who event payload binding (PhaseCount.onePacketMenu runtime leaks bounds) plan
        maximal horizon scheduler capacity control trace active request unsent values clear
  rw [law] at supported
  obtain ⟨choice, chosen, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  let move : Option (CommitRecoveryMove Player L) := choice.1
  have absent : move.elim false (·.missing) = false := by
    cases selected : move with
    | none => rfl
    | some action =>
        exact (continuing who ⟨_, played⟩ choice chosen action selected).1
  refine ⟨serial, (phaseRecoveryBindingData setup mode event who payload binding move).1,
    bounded, ?_⟩
  change phaseRecoveryBindingResponse setup mode runtime leaks who event payload binding serial
    move = phaseBindingResponse runtime leaks who event payload
      (phaseRecoveryBindingData setup mode event who payload binding move).1 serial
  have missing : (phaseRecoveryBindingData setup mode event who payload binding move).2 =
      false := by
    unfold phaseRecoveryBindingData
    rw [absent]
    rfl
  dsimp only [phaseRecoveryBindingResponse]
  rw [missing]
  rfl

/-- A continuing source strategy has exactly zero physical WAIT probability
at every genuine clear unsent binding callback. -/
theorem phaseSourcePolicy_binding_silence_law_of_continuing :
    (actual).map (fun response => response.transmission.isNone) = PMF.pure false := by
  calc
    _ = (actual).map (fun _ => false) := by
      apply map_congr_on_support
      intro response supported
      obtain ⟨serial, result, _bounded, rfl⟩ := phaseSourcePolicy_binding_emits_of_continuing
        setup mode runtime leaks bounds wellFormed assessment continuing plan maximal horizon
          scheduler capacity control trace who active event payload binding request unsent values
            clear response supported
      rfl
    _ = _ := PMF.map_const _ _

omit active request in
/-- At a clear unsent binding, every earlier response to this same physical
request was non-silent. Its supported source law is recovered at the exact
earlier callback and full prior own word, rather than evaluated at today's view. -/
theorem phaseSourcePolicy_no_silent_binding_recall
    (consistent : ReactiveApplication.Policy.Consistent
      (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who)
        (control.execution.recall who))
    (entry : (app).PlayerEntry) (recorded : entry ∈ control.execution.recall who)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 who
      ⟨control.execution.application.attempt, event⟩) :
    entry.action.transmission.isSome = true := by
  classical
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let start := setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)
  obtain ⟨before, prior, isPrefix, acting, viewed, chosen, after, recalled⟩ :=
    menu.recorded_response_supported start horizon scheduler control trace who
      (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who)
        consistent entry recorded
  have publicRequest : PhaseRuntimeState.requests before.execution.application.publicView who
      ⟨control.execution.application.attempt, event⟩ := by
    rw [viewed] at requested
    exact requested
  let inputs := setup.initialLaw.map encodeInputs
  have raw := menu.toRawTrace start horizon scheduler prior
  have nativeTrace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some before) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact raw
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    nativeTrace
  have oldRequest := (PhaseRuntimeState.requests_publicView before.execution.application valid
    who ⟨control.execution.application.attempt, event⟩).mp publicRequest
  have attempts : control.execution.application.attempt = before.execution.application.attempt :=
    oldRequest.1
  have currentRequest : before.execution.application.SeedRequest who
      ⟨before.execution.application.attempt, event⟩ := by
    rw [← attempts]
    exact oldRequest
  have earlierUnsent : ∀ message ∈ (app).outputs (before.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨before.execution.application.attempt, event⟩ := by
    intro message member named
    have retained : message ∈ (app).outputs (control.execution.recall who) := by
      rw [recalled, ReactiveApplication.outputs, List.filterMap_append]
      exact List.mem_append_left _ member
    apply unsent message retained
    rw [attempts]
    exact named
  have earlierClear := (phase_clear_nativeProgress_of_prefix runtime leaks menu start horizon
    scheduler before control prior trace isPrefix clear).1
  obtain ⟨serial, result, _bounded, emitted⟩ := phaseSourcePolicy_binding_emits_of_continuing
    setup mode runtime leaks bounds wellFormed assessment continuing plan maximal horizon
      scheduler capacity before prior who acting event payload binding currentRequest earlierUnsent
        values earlierClear entry.action chosen
  rw [emitted]
  rfl

end Vegas
