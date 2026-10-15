/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseIntendedOpeningSuccess
import Vegas.Game.PhaseContinuingBinding
import Vegas.Pending.PhaseUnsentNativeMemory

/-! # Native compiler freshness from actual nonmissing canonical callbacks -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Every earlier reply to a current unsent opening was an actual non-silent
canonical opening. Guard success is recovered at its genuine earlier history,
with the original complete prior owner words. -/
theorem phaseSourcePolicy_no_silent_opening_recall
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source
      assessment.strategy)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (consistent : ∀ owner, (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      owner).Consistent (control.execution.recall owner))
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (publication : ((serviceGraph setup mode).outputLayout event).IsPublication)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ payload, (serviceGraph setup mode).outputLayout event = .publication payload →
      ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (entry : (phaseApplication runtime leaks).PlayerEntry)
    (recorded : entry ∈ control.execution.recall who)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 who
      ⟨control.execution.application.attempt, event⟩) :
    entry.action.transmission.isSome = true := by
  let app := phaseApplication runtime leaks
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  obtain ⟨before, prior, isPrefix, acting, viewed, chosen, _after, recalled⟩ :=
    menu.recorded_response_supported initial horizon scheduler control trace who
      (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who)
        (consistent who) entry recorded
  have publicRequest : PhaseRuntimeState.requests before.execution.application.publicView who
      ⟨control.execution.application.attempt, event⟩ := by
    rw [viewed] at requested
    exact requested
  have raw := menu.toRawTrace initial horizon scheduler prior
  obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    raw
  have oldRequest := (PhaseRuntimeState.requests_publicView before.execution.application valid who
    ⟨control.execution.application.attempt, event⟩).mp publicRequest
  have attempts : control.execution.application.attempt = before.execution.application.attempt :=
    oldRequest.1
  have request : before.execution.application.SeedRequest who
      ⟨before.execution.application.attempt, event⟩ := by
    rw [← attempts]
    exact oldRequest
  have earlierUnsent : ∀ message ∈ (app).outputs (before.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨before.execution.application.attempt, event⟩ := by
    intro message member named
    apply unsent message
      (by rw [recalled, ReactiveApplication.outputs, List.filterMap_append]
          exact List.mem_append_left _ member)
    rw [attempts]
    exact named
  have earlierClear := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial horizon
    scheduler before control prior trace isPrefix clear).1
  have earlierConsistent : ∀ owner, (phaseSourcePolicy setup mode runtime leaks bounds wellFormed
      assessment owner).Consistent (before.execution.recall owner) := by
    intro owner
    have reaches := menu.reaches_raw initial horizon scheduler isPrefix.reachesWithin
    obtain ⟨suffix, kept⟩ := app.reaches_recall_prefix initial horizon scheduler reaches before
      control rfl rfl owner
    have final := consistent owner
    rw [← kept] at final
    exact final.of_append
  obtain ⟨payload, binding, checks, outputEq, codeEq, node, value, resolved⟩ :=
    phase_ready_publication_success setup mode runtime leaks bounds wellFormed source assessment
      copies plan maximal horizon scheduler prior earlierClear earlierConsistent who event
        request publication
  have stored := EventCode.binding_success_of_resolve_success binding checks true
    before.execution.application.current.native.config.store value resolved
  obtain ⟨candidate, _accepted, law⟩ := phaseSourcePolicy_opening_of_history setup mode runtime
    leaks bounds wellFormed assessment plan inputs horizon scheduler prior who event payload binding
      checks
      outputEq codeEq node request earlierUnsent value stored (values payload outputEq value)
  rw [law, PMF.mem_support_pure_iff] at chosen
  rw [chosen]
  rfl

/-- At an actual clear unsent coordinate, no native compiler memory can suppress
a fresh response. Earlier binding replies use the continuing source support;
earlier opening replies use the actual intended guard calculation. -/
theorem phaseSourcePolicy_unsent_native_fresh
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source
      assessment.strategy)
    (continuing : ∀ who (site : setup.commitRecoveryModel.InformationSite who),
      ∀ choice ∈ (assessment.strategy who site.1).support,
        setup.CommitRecoveryContinues who site.1 choice.1)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount) {control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (consistent : ∀ owner, (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      owner).Consistent (control.execution.recall owner))
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ payload,
      ((serviceGraph setup mode).outputLayout event = .binding who payload ∨
        (serviceGraph setup mode).outputLayout event = .publication payload) →
      ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    runtime.reactiveAlreadySubmitted (PhaseNativeProjection.nativeLeaks leaks plan)
      ((PhaseNativeProjection.execution runtime leaks plan control.execution).recall who)
      event = false ∧
    ∀ intentions, runtime.reactiveAlreadyDecided (PhaseNativeProjection.nativeLeaks leaks plan) who
      ((PhaseNativeProjection.execution runtime leaks plan control.execution).recall who)
      intentions event = false := by
  have fresh := phase_unsent_native_submitted_false runtime leaks bounds plan
    (setup.initialLaw.map encodeInputs) horizon scheduler trace clear who event request unsent
  refine ⟨fresh, fun intentions => ?_⟩
  apply phase_native_decided_false_of_nonsilent_requests runtime leaks bounds plan
    (serviceGraph_revealRelaxedOrdered setup mode) maximal (setup.initialLaw.map encodeInputs)
      horizon scheduler trace clear who event request _ intentions
  intro entry recorded requested
  cases node : nodeView (serviceGraph setup mode) event with
  | bind owner payload outputEq codeEq =>
      have acting : (serviceGraph setup mode).actor? event = some owner :=
        (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
      have same : owner = who := Option.some.inj (acting.symm.trans request.2.2.2.1)
      subst owner
      have sourceTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
          (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
          horizon scheduler).Trace (some control) := by
        have initialEq :
            (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan) =
              setup.initialLaw.map
                (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) :=
          PMF.map_comp encodeInputs setup.initialLaw (PhaseRuntimeState.initial plan)
        exact Eq.mp (congrArg (fun initial =>
          ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
            scheduler).Trace (some control)) initialEq) trace
      exact phaseSourcePolicy_no_silent_binding_recall setup mode runtime leaks bounds wellFormed
        assessment continuing plan maximal horizon scheduler capacity control sourceTrace who event
          payload outputEq unsent (values payload (Or.inl outputEq)) clear (consistent who)
            entry recorded requested
  | resolve owner payload binding checks outputEq codeEq =>
      have publication : ((serviceGraph setup mode).outputLayout event).IsPublication := by
        rw [outputEq]
        trivial
      exact phaseSourcePolicy_no_silent_opening_recall setup mode runtime leaks bounds wellFormed
        source assessment copies plan maximal horizon scheduler trace clear consistent who event
          publication unsent (fun τ typed => values τ (Or.inr typed)) entry recorded requested
  | sample payload distribution outputEq codeEq =>
      have acting : (serviceGraph setup mode).actor? event = none :=
        (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
      have owned := request.2.2.2.1
      rw [acting] at owned
      cases owned

end Vegas
