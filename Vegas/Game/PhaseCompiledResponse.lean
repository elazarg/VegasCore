/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseIntendedBindingResponse
import Vegas.Game.PhaseIntendedOpeningResponse
import Vegas.Game.PhaseCanonicalFreshness
import Vegas.Game.PhaseCompiledSentResponse
import Vegas.Pending.ReactiveOriginalConfig

/-! # Complete canonical and compiled-native local response laws -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (source : ∀ who, setup.intendedModel.BehavioralPolicy who)

local notation "copied" => EventGraph.toModeProfile (toEventGraph setup.program) mode
  (compileEventProfile setup.program (Setup.decodeBehavioralProfile setup
    (CommitmentInterface.values setup.program) (Setup.openingExtension setup source)))

/-- The complete local response law agrees with the native prescribed compiler
at every genuine clear canonical callback. Current source inputs, guarded
opening success and compiler freshness are derived from the same actual history.
The two prior consistency hypotheses are precisely those consumed by the
owning policy-matching history induction. -/
theorem phaseSourcePolicy_prescribed_of_clear_history
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
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
    (phaseConsistent : ∀ owner, (phaseSourcePolicy setup mode runtime leaks bounds wellFormed
      assessment owner).Consistent (control.execution.recall owner))
    (nativeConsistent : ∀ owner,
      (runtime.prescribedReactivePolicy (PhaseNativeProjection.nativeLeaks leaks plan) owner
        (copied owner)).Consistent
          ((PhaseNativeProjection.execution runtime leaks plan control.execution).recall owner))
    (values : ∀ event who payload,
      ((serviceGraph setup mode).outputLayout event = .binding who payload ∨
        (serviceGraph setup mode).outputLayout event = .publication payload) →
      ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (who : Player) (active : control.actor = some who) :
    (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
      (control.execution.recall who)
      (control.execution.observe (phaseApplication runtime leaks) who)).map
        (PhaseNativeProjection.action runtime leaks plan) =
      runtime.prescribedReactivePolicy (PhaseNativeProjection.nativeLeaks leaks plan) who
        (copied who)
        ((PhaseNativeProjection.execution runtime leaks plan control.execution).recall who)
        ((PhaseNativeProjection.execution runtime leaks plan control.execution).observe
          (runtime.reactiveApplication (PhaseNativeProjection.nativeLeaks leaks plan)) who) := by
  classical
  rcases control with ⟨remaining, actor, execution⟩
  cases active
  let nativeLeaks := PhaseNativeProjection.nativeLeaks leaks plan
  let projected := PhaseNativeProjection.execution runtime leaks plan execution
  let actual := phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
    (execution.recall who) (execution.observe (phaseApplication runtime leaks) who)
  let erased := actual.map (PhaseNativeProjection.action runtime leaks plan)
  by_cases selected : ∃ coordinate, execution.application.SeedRequest who coordinate
  · obtain ⟨⟨attempt, event⟩, request⟩ := selected
    have same : attempt = execution.application.attempt := request.1
    subst attempt
    by_cases unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (execution.recall who),
        PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩
    · obtain ⟨fresh, undecided⟩ := phaseSourcePolicy_unsent_native_fresh setup mode runtime leaks
        bounds wellFormed source assessment copies continuing plan maximal horizon scheduler
          capacity trace clear phaseConsistent who event request unsent (values event who)
      have turn := execution.application.current.native.ownTurn_of_ready
        (serviceGraph_revealRelaxedOrdered setup mode) who event
        ((execution.application.current.native.publicView_eventReady event).mpr request.2.2.1)
        request.2.2.2.1
      have selectedTurn := execution.application.current.native.publicView.ownTurn?_of_ownTurn who
        event turn
      rw [runtime.prescribedReactivePolicy_apply]
      change erased = _
      rw [← PMF.bind_const ((runtime.prescribedReactiveImplementation nativeLeaks who
        (copied who)).posterior (projected.recall who)) erased]
      apply bind_congr_on_support
      intro intentions positive
      let defaults : Player → List (Option (serviceGraph setup mode).Completion) := fun owner =>
        ((runtime.prescribedReactiveImplementation nativeLeaks owner (copied owner)).posterior
          (projected.recall owner)).support_nonempty.choose
      let memories := Function.update defaults who intentions
      have supported : ∀ owner, memories owner ∈
          ((runtime.prescribedReactiveImplementation nativeLeaks owner (copied owner)).posterior
            (projected.recall owner)).support := by
        intro owner
        by_cases same : owner = who
        · subst owner
          simpa only [memories, Function.update_self] using positive
        · rw [show memories owner = defaults owner from Function.update_of_ne same _ _]
          exact ((runtime.prescribedReactiveImplementation nativeLeaks owner
            (copied owner)).posterior (projected.recall owner)).support_nonempty.choose_spec
      have focal : memories who = intentions := by
        simp only [memories, Function.update_self]
      rw [← focal]
      change erased = (runtime.prescribedReactiveResponse nativeLeaks who (copied who)
        (projected.recall who) (memories who)
        (projected.observe (runtime.reactiveApplication nativeLeaks) who)).map Prod.fst
      rw [runtime.prescribedReactiveResponse_originalConfig nativeLeaks projected memories who
        (copied who) event selectedTurn fresh (undecided (memories who)) request.2.2.2.1,
        PMF.map_comp]
      change erased = ((serviceGraph setup mode).normalizePolicy who (copied who) event
        request.2.2.2.1 ((serviceGraph setup mode).playerObserve who
          (runtime.originalConfig nativeLeaks projected memories))).map
        (fun action => runtime.reactiveDecision nativeLeaks who event action
          (execution.application.current.native.playerView who))
      cases node : nodeView (serviceGraph setup mode) event with
      | bind owner payload outputEq codeEq =>
          have acting : (serviceGraph setup mode).actor? event = some owner :=
            (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
          have own : owner = who := Option.some.inj (acting.symm.trans request.2.2.2.1)
          subst owner
          obtain ⟨_serial, _bounded, _allocated, law⟩ :=
            phaseSourcePolicy_compiled_binding_of_intended_history setup mode runtime leaks source
              bounds wellFormed assessment copies plan maximal horizon scheduler capacity _ trace
                clear phaseConsistent nativeConsistent memories supported who rfl event payload
                  outputEq request unsent (values event who payload (Or.inl outputEq)) codeEq node
          exact law
      | resolve owner payload binding checks outputEq codeEq =>
          have publication : ((serviceGraph setup mode).outputLayout event).IsPublication := by
            rw [outputEq]
            trivial
          exact phaseSourcePolicy_compiled_opening_of_intended_history setup mode runtime leaks
            source bounds wellFormed assessment copies plan maximal horizon scheduler trace clear
              phaseConsistent who event request publication unsent
                (fun payload typed => values event who payload (Or.inr typed))
                ((serviceGraph setup mode).playerObserve who
                  (runtime.originalConfig nativeLeaks projected memories))
      | sample payload distribution outputEq codeEq =>
          have acting : (serviceGraph setup mode).actor? event = none :=
            (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
          have owned := request.2.2.2.1
          rw [acting] at owned
          cases owned
    · push Not at unsent
      obtain ⟨message, output, named⟩ := unsent
      have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler
        trace
      have recalled := (phaseApplication runtime leaks).history_inputRecall _ horizon scheduler raw
      have emitted := output
      rw [← recalled who] at emitted
      have owner : message.sender = who := of_decide_eq_true (List.mem_filter.mp emitted).2
      obtain ⟨actual, called, equal⟩ := Option.map_eq_some_iff.mp named
      have tag := congrArg CommitAttemptEvent.attempt equal
      have eventEq := congrArg CommitAttemptEvent.event equal
      have sent : PhaseSeedScheduler.ownPacket ⟨execution.application.attempt, event⟩ who
          message = true := decide_eq_true ⟨owner, tag, called.trans (congrArg some eventEq)⟩
      exact phaseSourcePolicy_prescribed_of_sent setup mode runtime leaks bounds wellFormed
        assessment plan (setup.initialLaw.map encodeInputs) horizon scheduler remaining who
          execution trace event request ⟨message, output, sent⟩ (copied who)
  · exact phaseSourcePolicy_prescribed_of_no_request setup mode runtime leaks bounds wellFormed
      assessment plan maximal (setup.initialLaw.map encodeInputs) horizon scheduler remaining who
        execution trace clear (fun coordinate request => selected ⟨coordinate, request⟩)
          (copied who)

end Vegas
