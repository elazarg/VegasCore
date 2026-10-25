/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionStoppedBoundary
import Vegas.Pending.ExclusionFailureOwners
import Vegas.Game.RecoveryNativeComparison
import Vegas.Game.OnePacketRareMainMass
import Vegas.Game.RecoveryForeignFailure
import Vegas.Game.OnePacketDebtRouting
import GameTheoryExtensions.Analysis.Protocol.StoppedExitBound

/-! # Rare first responses of the common native comparison profile -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}

/-- At a clear regular prefix before focal debt, previous source-main foreign
first callbacks prevent the current foreign callback from being a late delivery.
The comparison begins at an actual focal source turn. -/
theorem recovery_nonlate_of_mainActivationTraceAfter
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal owner : Player)
    (different : owner ≠ focal)
    {initial : PMF (RecoveryState (graph setup))}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
    (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
    {horizon : Nat} {scheduler : ((runtime setup).recoveryApplication leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon scheduler delay)
    (timely : (runtime setup).AsyncTimely delay bound)
    (start control : (application setup leaks).Control)
    (startTrace : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace (some start))
    (trace : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace (some control))
    (startPrefix : TracePrefix startTrace trace)
    (current : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source focal trace)
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (main : MainActivationTraceAfter setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source focal
      startTrace.length trace) :
    ¬ LateDelivery setup leaks owner (some (control.execution.recall owner,
      control.execution.observe (application setup leaks) owner)) := by
  let nativeScheduler := RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler
  rintro ⟨past, view, event, same, pending, entry, remembered, activated⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same.symm)
  obtain ⟨point, decoded, intended⟩ :=
    intended_of_clear_regular_notOwes wellFormed source focal trace clear regular notOwed
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
    (bounds.onePacketMenu (runtime setup) leaks) horizon nativeScheduler trace control rfl
  have samePoint := Option.some.inj ((decodedPoint_eq residual).symm.trans decoded)
  subst point
  have submissions := onePacket_ownSubmissionsAtTurn bounds trace residual.checkpoint.ordered _
    residual.decode intended owner
  obtain ⟨before, prior, response, joint, legal, realized, afterPrefix, acting, chosen,
    firstPending, never⟩ := firstActivation_response_prefix_of_recall trace owner event
      ⟨entry, remembered, activated⟩ submissions
  have ready := (control.execution.application.publicView_eventReady event).mp
    (pendingEvent_spec pending).2.1
  have owned := (pendingEvent_spec pending).2.2.1
  have unfinished : event ∉ start.execution.application.config.cut.completed := by
    intro completed
    obtain ⟨value, output⟩ := Option.isSome_iff_exists.mp
      ((start.execution.application.config.output_available event).mpr completed)
    have stored : start.execution.application.config.store (.inr event) = some value := output
    have retained := storedValue_of_tracePrefix startTrace startPrefix (.inr event) value stored
    change control.execution.application.config.outputs event = some value at retained
    exact ready.1 ((control.execution.application.config.output_available event).mp
      (by rw [retained]; rfl))
  have priorPrefix : TracePrefix prior trace :=
    (TracePrefix.extend .refl joint legal realized).trans afterPrefix
  have readyBefore := (before.execution.application.publicView_eventReady event).mp
    (pendingEvent_spec firstPending).2.1
  have future := foreign_ready_prefix_after_ownTurn startTrace prior startPrefix priorPrefix focal
    owner different current event turn owned unfinished readyBefore
  have supportStep := mainActivationStep_of_tracePrefix source focal startTrace.length prior joint
    legal realized afterPrefix main future.length_le
  have first : FirstActivation setup leaks owner (some (before.execution.recall owner,
      before.execution.observe (application setup leaks) owner)) :=
    ⟨before.execution.recall owner, before.execution.observe (application setup leaks) owner, event,
      rfl, firstPending, never⟩
  have supported := supportStep owner acting different first
  rw [chosen, Option.getD_some] at supported
  obtain ⟨earlierClear, earlierRegular, earlierNotOwed⟩ := clear_regular_notOwes_of_tracePrefix
    wellFormed source focal owner different prior trace priorPrefix clear regular notOwed
  obtain ⟨earlyPoint, earlyDecoded, earlyIntended⟩ :=
    intended_of_clear_regular_notOwes wellFormed source focal prior earlierClear earlierRegular
      earlierNotOwed
  have forced : ForcedState setup leaks owner (some before) :=
    (forcedState_iff_decodedPoint before).mpr
      ⟨earlyPoint, earlyDecoded, forcedPoint_of_intended owner earlyIntended⟩
  have ownerNotOwed : ∀ point, decodedPoint setup before.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure owner setup.program point := by
    intro point pointDecoded
    cases Option.some.inj (earlyDecoded.symm.trans pointDecoded)
    exact ProtocolState.Intended.not_owesFailure owner setup.program earlyPoint earlyIntended
  have offered : response ∈ bounds.onePacketActions (runtime setup) leaks owner
      (before.execution.recall owner) (before.execution.observe (application setup leaks) owner) :=
    (chosen ▸ legal.2 owner).2
  have selected : (responseChoice setup leaks bounds (initialLaw setup) horizon nativeScheduler
      owner (some (before.execution.recall owner,
        before.execution.observe (application setup leaks) owner)) response).1 = some response := by
    simp only [responseChoice, dite_eq_left offered]
  have named : (runtime setup).submittedEvent? leaks response = some event := by
    rcases before with ⟨remaining, actor, execution⟩
    dsimp only at acting
    subst actor
    have rawTrace := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
      horizon nativeScheduler prior
    have fits := recovery_firstActivation_inclusionFits initialized nativeLaw opportunity timely
      rawTrace rfl earlierClear event (pendingEvent_spec firstPending).1 never
    obtain ⟨action, material, canonical, sends, _⟩ := honestChoice_canonical_of_debtFree wellFormed
      covers capacity source prior owner forced ownerNotOwed event firstPending bound fits _
      supported
    have responseEq := Option.some.inj (selected.symm.trans canonical)
    rw [responseEq]
    rcases canonical_silentOrNames owner (execution.recall owner)
      (execution.observe (application setup leaks) owner) event action with silent | names
    · rw [sends] at silent
      cases silent
    · exact names
  let recordedEntry := respondEntry setup leaks before.execution owner response
  have initialRecord := recordsEntry_respond before.execution owner response before.remaining none
  have laterRecord : ∀ {state}
      {later : (onePacketProtocol setup leaks bounds horizon nativeScheduler).Trace state},
      TracePrefix (prior.extend joint legal realized) later →
        RecordsEntry setup leaks owner recordedEntry state := by
    intro state later laterPrefix
    induction laterPrefix with
    | refl => exact initialRecord
    | @extend first second earlier isPrefix actions allowed reached ih =>
        exact recordsEntry_transition owner recordedEntry (initialLaw setup) horizon nativeScheduler
          first second actions ih reached
  obtain ⟨earlier, later, split⟩ := laterRecord afterPrefix
  have recorded :
      (runtime setup).eventRecorded leaks (control.execution.recall owner) event = true :=
    ((runtime setup).eventRecorded_iff leaks (control.execution.recall owner) event).mpr
      ⟨recordedEntry, by rw [split]; exact List.mem_append_right _ (List.mem_cons_self ..), named⟩
  rw [(pendingEvent_spec pending).2.2.2] at recorded
  cases recorded

private theorem main_of_no_pending
    (source : setup.intendedModel.BehavioralAssessment)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {remaining : Nat} {owner : Player} {execution : (application setup leaks).Execution}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some owner, execution⟩))
    (point : ProtocolState setup.program)
    (decoded : decodedPoint setup execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point)
    (noPending : pendingEvent setup leaks owner (some (execution.recall owner,
      execution.observe (application setup leaks) owner)) = none)
    (response : (application setup leaks).Action)
    (offered : response ∈ bounds.onePacketActions (runtime setup) leaks owner
      (execution.recall owner) (execution.observe (application setup leaks) owner)) :
    responseChoice setup leaks bounds (initialLaw setup) horizon scheduler owner
      (some (execution.recall owner, execution.observe (application setup leaks) owner)) response ∈
      (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler source owner
        (some (execution.recall owner,
          execution.observe (application setup leaks) owner))).support := by
  have rawTrace := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
    horizon scheduler trace
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
    (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler trace _ rfl
  have samePoint := Option.some.inj ((decodedPoint_eq residual).symm.trans decoded)
  subst point
  have records : ∀ event, execution.application.publicView.ownTurn? owner = some event →
      (runtime setup).eventRecorded leaks (execution.recall owner) event = true := by
    intro event turn
    cases actual : (runtime setup).eventRecorded leaks (execution.recall owner) event with
    | true => rfl
    | false =>
        have pending : pendingEvent setup leaks owner (some (execution.recall owner,
            execution.observe (application setup leaks) owner)) = some event :=
          pendingEvent_of_spec turn actual
        rw [noPending] at pending
        cases pending
  have silent : response.transmission = none := by
    rcases ((bounds.mem_onePacketActions (runtime setup) leaks owner _ _ response).mp
      offered).2 with
      silent | ⟨material, transmits, permitted⟩
    · exact silent
    · exfalso
      have valid := ((countPermits_eq_true_iff _ _).mp permitted).1
      obtain ⟨event, named, _⟩ := (WitnessedPacket.tokenValid_iff _).mp valid
      have submitted : (runtime setup).submittedEvent? leaks response = some event := by
        unfold EventGraphRuntime.submittedEvent?
        rw [transmits]
        exact named
      have atTurn := onePacket_submission_atTurn bounds (failureProfile setup.program) rawTrace
        residual response offered event submitted
      rcases atTurn with turn | owed
      · exact onePacket_recorded_not_offered trace owner event (records event turn) response
          submitted offered
      · exact ProtocolState.Intended.not_owesFailure owner setup.program _ intended
          (owed _ residual.decode)
  have responseEq : response = ⟨none⟩ := by
    cases response
    cases silent
    rfl
  have mainLaw : honestChoice setup leaks bounds (initialLaw setup) horizon scheduler source owner
      (some (execution.recall owner, execution.observe (application setup leaks) owner)) =
      PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler owner
        (some (execution.recall owner, execution.observe (application setup leaks) owner))) := by
    cases turn : execution.application.publicView.ownTurn? owner with
    | none =>
        exact honestChoice_silence_of_noTurn source owner (execution.recall owner)
          (execution.observe (application setup leaks) owner) turn
    | some event =>
        exact honestChoice_silence_of_recorded source trace owner event turn (records event turn)
  rw [mainLaw, responseEq]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

/-- Before the rare marker, a foreign first callback is main by the marker
condition, while every other callback has the main silent response. -/
theorem recovery_response_main_of_mainActivationTraceAfter
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal owner : Player)
    (different : owner ≠ focal)
    {initial : PMF (RecoveryState (graph setup))}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
    (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
    {horizon : Nat} {scheduler : ((runtime setup).recoveryApplication leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon scheduler delay)
    (timely : (runtime setup).AsyncTimely delay bound)
    (start control : (application setup leaks).Control)
    (startTrace : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace (some start))
    (trace : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace (some control))
    (startPrefix : TracePrefix startTrace trace)
    (current : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source focal trace)
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (main : MainActivationTraceAfter setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source focal
      startTrace.length trace)
    (active : control.actor = some owner)
    (joint : Player → Option (application setup leaks).Action)
    (legal : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Legal
        (some control) joint)
    (stepMain : MainActivationStep setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source focal
      (some control) joint) :
    responseChoice setup leaks bounds (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) owner
      (some (control.execution.recall owner,
        control.execution.observe (application setup leaks) owner)) ((joint owner).getD ⟨none⟩) ∈
      (honestChoice setup leaks bounds (initialLaw setup) horizon
        (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source owner
        (some (control.execution.recall owner,
          control.execution.observe (application setup leaks) owner))).support := by
  have nonlate := recovery_nonlate_of_mainActivationTraceAfter wellFormed covers capacity source
    focal owner different initialized nativeLaw opportunity timely start control startTrace trace
    startPrefix current turn clear regular notOwed main
  by_cases first : FirstActivation setup leaks owner (some (control.execution.recall owner,
      control.execution.observe (application setup leaks) owner))
  · exact stepMain owner active different first
  have noPending : pendingEvent setup leaks owner (some (control.execution.recall owner,
      control.execution.observe (application setup leaks) owner)) = none := by
    cases actual : pendingEvent setup leaks owner (some (control.execution.recall owner,
        control.execution.observe (application setup leaks) owner)) with
    | none => rfl
    | some event =>
        exact ((firstActivation_or_lateDelivery actual).elim first nonlate).elim
  obtain ⟨point, decoded, intended⟩ :=
    intended_of_clear_regular_notOwes wellFormed source focal trace clear regular notOwed
  rcases control with ⟨remaining, actor, execution⟩
  dsimp only at active
  subst actor
  have localLegal := legal.2 owner
  cases selected : joint owner with
  | none =>
      rw [selected] at localLegal
      exact (localLegal rfl).elim
  | some response =>
      rw [selected] at localLegal
      simpa only [selected, Option.getD_some] using
        main_of_no_pending source trace point decoded intended noPending response localLegal.2

/-- Before a non-main first callback, an unmarked foreign response preserves
the full source-factor regularity predicate. -/
theorem regularStep_of_mainActivationTraceAfter
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal owner : Player)
    (different : owner ≠ focal)
    {initial : PMF (RecoveryState (graph setup))}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
    (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
    {horizon : Nat} {scheduler : ((runtime setup).recoveryApplication leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon scheduler delay)
    (timely : (runtime setup).AsyncTimely delay bound)
    (start control : (application setup leaks).Control)
    (startTrace : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace (some start))
    (trace : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace (some control))
    (startPrefix : TracePrefix startTrace trace)
    (current : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source focal trace)
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (main : MainActivationTraceAfter setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source focal
      startTrace.length trace)
    (active : control.actor = some owner)
    (joint : Player → Option (application setup leaks).Action)
    (legal : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Legal
        (some control) joint)
    (stepMain : MainActivationStep setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source focal
      (some control) joint)
    (next : (application setup leaks).Control)
    (realized : some next ∈ ((onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).step
        (some control) ⟨joint, legal⟩).support) :
    RegularStep setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source focal
      (some control) joint (some next) := by
  have supported := recovery_response_main_of_mainActivationTraceAfter wellFormed covers capacity
    source focal owner different initialized nativeLaw opportunity timely start control startTrace
    trace
    startPrefix current turn clear regular notOwed main active joint legal stepMain
  rcases control with ⟨remaining, actor, execution⟩
  dsimp only at active
  subst actor
  exact regularStep_of_clear_regular_main wellFormed source focal owner covers
    (by have positive := capacity owner; omega) trace clear regular notOwed joint legal next
    realized
    supported

/-- Actual stopped play keeps regularity whenever no foreign first callback
has left source-main support. Focal actions and the remaining behavioral laws
are arbitrary. Only public-clear prefixes before focal debt use service. -/
theorem recovery_stopped_regular_of_mainActivationTraceAfter
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal : Player)
    {initial : PMF (RecoveryState (graph setup))}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
    (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
    {horizon : Nat} {scheduler : ((runtime setup).recoveryApplication leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon scheduler delay)
    (timely : (runtime setup).AsyncTimely delay bound)
    (certificate : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).WellFoundedHistories)
    (profile : ∀ who, (onePacketModel setup leaks bounds (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).BehavioralPolicy who)
    (extraStop : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).History → Prop)
    (start : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).History)
    (control : (application setup leaks).Control) (state : start.state = some control)
    (current : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? focal = some current)
    (regular : RegularTrace setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source focal
      start.trace) :
    ∀ final ∈ ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).runBehavioralUntil
        certificate profile (fun history =>
          ¬ ReactiveApplication.stateInvariant (app := application setup leaks)
            (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
              history.state ∨
          DecodedState setup leaks (failureProfile setup.program)
            (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history)
        start).support,
      (∃ reached, final.state = some reached) ∧ TracePrefix start.trace final.trace ∧
        (MainActivationTraceAfter setup leaks bounds horizon
          (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source focal
          start.trace.length final.trace →
          RegularTrace setup leaks bounds horizon
            (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source focal
            final.trace) := by
  classical
  rcases start with ⟨startState, startTrace⟩
  change startState = some control at state
  subst startState
  let start : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).History :=
    ⟨some control, startTrace⟩
  let nativeScheduler := RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler
  let model := onePacketModel setup leaks bounds (initialLaw setup) horizon nativeScheduler
  let stopped := fun history :
      (onePacketProtocol setup leaks bounds horizon nativeScheduler).History =>
    ¬ ReactiveApplication.stateInvariant (app := application setup leaks)
      (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
        history.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history
  let property := fun history :
      (onePacketProtocol setup leaks bounds horizon nativeScheduler).History =>
    (∃ reached, history.state = some reached) ∧ TracePrefix start.trace history.trace ∧
      (MainActivationTraceAfter setup leaks bounds horizon nativeScheduler source focal
        start.trace.length history.trace →
        RegularTrace setup leaks bounds horizon nativeScheduler source focal history.trace)
  have initialProperty : property start := ⟨⟨control, rfl⟩, .refl, fun _ => regular⟩
  have preserved : ∀ history, ¬ stopped history →
      ¬ (onePacketProtocol setup leaks bounds horizon nativeScheduler).terminal history.state →
      property history → ∀ next ∈ (model.runBehavioralFrom profile 1 history).support,
        property next := by
    intro history going running valid next supported
    have clear : ReactiveApplication.stateInvariant (app := application setup leaks)
        (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
          history.state := not_not.mp (fun failed => going (Or.inl failed))
    rw [model.runBehavioralFrom_succ_of_not_terminal profile 0 running,
      PMF.mem_support_bind_iff] at supported
    obtain ⟨draw, _chosen, stepped⟩ := supported
    rw [PMF.mem_support_bindOnSupport_iff] at stepped
    obtain ⟨target, realized, reached⟩ := stepped
    change next ∈ (PMF.pure _).support at reached
    rw [PMF.mem_support_pure_iff] at reached
    subst reached
    obtain ⟨before, beforeState⟩ := valid.1
    rcases history with ⟨previous, trace⟩
    change previous = some before at beforeState
    cases beforeState
    obtain ⟨after, afterState, _recall⟩ := (application setup leaks).transition_recall_prefix
      (initialLaw setup) horizon nativeScheduler before target draw.1 realized
    cases afterState
    refine ⟨⟨after, rfl⟩, .extend valid.2.1 draw.1 draw.2 realized, ?_⟩
    intro main
    have beforeMain := main.1
    have beforeRegular := valid.2.2 beforeMain
    refine ⟨beforeRegular, ?_⟩
    cases active : before.actor with
    | none =>
        intro actor acts different
        rw [active] at acts
        cases acts
    | some owner =>
        by_cases same : owner = focal
        · intro actor acts different
          have which := Option.some.inj (active.symm.trans acts)
          exact (different (which.symm.trans same)).elim
        have notOwed : ∀ point,
            decodedPoint setup before.execution.application.config = some point →
            ¬ ProtocolState.OwesFailure focal setup.program point := by
          intro point decoded owed
          apply going
          right
          left
          exact decodedState_of_nativeDecodedState (failureProfile setup.program)
            ⟨some before, trace⟩ decoded owed
        exact regularStep_of_mainActivationTraceAfter wellFormed covers capacity source focal owner
          same initialized nativeLaw opportunity timely control before start.trace trace valid.2.1
          current turn clear beforeRegular notOwed beforeMain active draw.1 draw.2
          (main.2 valid.2.1.length_le) after realized
  exact model.runBehavioralUntil_support_history_closed certificate profile stopped property
    preserved start initialProperty

end Vegas

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler (runtime setup) leaks scheduler
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler

/-- At a represented forced nonlate input, the globally assembled comparison
profile gives a total mass at most square plus scale to every response event
disjoint from source-main support. The original common weights are retained. -/
theorem nativeComparisonStrategy_event_le_of_disjoint_main [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p)) (n : ℕ)
    (who : Player) (info : (application setup leaks).Info)
    (nonlate : ¬ LateDelivery setup leaks who info)
    (occurs : ∃ history : (ReactiveApplication.ResponseMenu.protocol
      (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
        (NativeScheduler)).History, (N).infoOf who history.trace = info)
    (forced : Vegas.forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup)
      horizon (NativeScheduler) who info)
    (event : Set ((N).Choice who info))
    (disjoint : Disjoint
      (honestChoice setup leaks bounds (initialLaw setup) horizon (NativeScheduler) (sequence n)
        who info).support event) :
    (((nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale positive le_one
      weights n who info).toOuterMeasure event).toReal) ≤ (scale n) ^ 2 + scale n := by
  let main := honestChoice setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
    (sequence n) who info
  let law := nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale positive
    le_one weights n who info
  have dominates : ∀ choice, slotRetention (scale n) * (main choice).toReal ≤
      (law choice).toReal := by
    intro choice
    exact onePacketMixture_ge_honest_of_not_late setup leaks bounds horizon (NativeScheduler)
      sequence scale positive le_one n
      (nativeComparisonWeights setup leaks bounds horizon scheduler (weights n)) nonlate occurs
      forced choice
  have close := PMF.WithinTV.of_domination main law (slotRetention (scale n))
    (slotRetention_le_one (positive n).le (le_one n)) dominates
  have zero : main.toOuterMeasure event = 0 :=
    (PMF.toOuterMeasure_apply_eq_zero_iff main event).mpr disjoint
  have comparison := close event
  rw [zero, ENNReal.toReal_zero, zero_sub, abs_neg,
    abs_of_nonneg ENNReal.toReal_nonneg] at comparison
  exact comparison.trans (by
    have lower := slotMainRetention_ge (positive n).le (le_one n)
    change 1 - slotRetention (scale n) ≤ (scale n) ^ 2 + scale n
    have retained : 1 - ((scale n) ^ 2 + scale n) ≤ slotRetention (scale n) := by
      simpa only [slotRetention, mul_assoc] using lower
    linarith)

private theorem responseChoice_getD_eq
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (choice : (N).Choice who (some (past, view))) :
    responseChoice setup leaks bounds (initialLaw setup) horizon (NativeScheduler) who
      (some (past, view)) (choice.1.getD ⟨none⟩) = choice := by
  classical
  rcases choice with ⟨value, allowed⟩
  change ∃ response ∈ bounds.onePacketActions (runtime setup) leaks who past view,
    value = some response at allowed
  obtain ⟨response, offered, rfl⟩ := allowed
  apply Subtype.ext
  simp only [Option.getD_some, responseChoice, dite_eq_left offered]

/-- An actual behavioral step of the same comparison profile, with arbitrary
focal policy, puts at most square plus scale on violating the foreign fresh-main
condition. Idle, focal, and nonfirst callbacks have no such violation. -/
theorem nativeComparison_joint_mainActivation_failure_le [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p)) (n : ℕ)
    (focal : Player) (focalPolicy : (N).BehavioralPolicy focal)
    (control : (application setup leaks).Control)
    (trace : (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).Trace (some control))
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) focal trace)
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (running : ¬ (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).terminal
      (some control)) :
    ((((N).behavioralJoint
      (Function.update (nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale
        positive le_one weights n) focal focalPolicy) trace running).toOuterMeasure
      {draw | ¬ MainActivationStep setup leaks bounds horizon (NativeScheduler) (sequence n) focal
        (some control) draw.1}).toReal) ≤ (scale n) ^ 2 + scale n := by
  classical
  let profile := Function.update (nativeComparisonStrategy setup leaks bounds horizon scheduler
    sequence scale positive le_one weights n) focal focalPolicy
  let jointLaw := (N).behavioralJoint profile trace running
  let bad : Set {joint : Player → Option (application setup leaks).Action //
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).Legal
        (some control) joint} :=
    {draw | ¬ MainActivationStep setup leaks bounds horizon (NativeScheduler) (sequence n)
      focal (some control) draw.1}
  change (jointLaw.toOuterMeasure bad).toReal ≤ _
  by_cases eligible : ∃ owner, control.actor = some owner ∧ owner ≠ focal ∧
      FirstActivation setup leaks owner (some (control.execution.recall owner,
        control.execution.observe (application setup leaks) owner))
  · obtain ⟨owner, active, different, first⟩ := eligible
    let info := some (control.execution.recall owner,
      control.execution.observe (application setup leaks) owner)
    let main := honestChoice setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
      (sequence n) owner info
    let optionBad := {selected : Option (application setup leaks).Action |
      responseChoice setup leaks bounds (initialLaw setup) horizon (NativeScheduler) owner info
        (selected.getD ⟨none⟩) ∉ main.support}
    have infoEq : (N).infoOf owner trace = info := by
      rw [onePacket_infoOf]
      simp only [ReactiveApplication.observe, active, ↓reduceIte, info]
    have marginal : jointLaw.map (fun draw => draw.1 owner) =
        (nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale positive
          le_one
          weights n owner info).map Subtype.val := by
      calc
        jointLaw.map (fun draw => draw.1 owner) =
            (jointLaw.map Subtype.val).map (fun actions => actions owner) :=
          by simp only [PMF.map_comp, Function.comp_def]
        _ = (profile owner ((N).infoOf owner trace)).map Subtype.val := by
          rw [(N).behavioralJoint_map_val, independentProduct_map_eval]
        _ = _ := by
          simpa only [profile, Function.update_of_ne different] using
            congrArg (fun input => (nativeComparisonStrategy setup leaks bounds horizon scheduler
              sequence scale positive le_one weights n owner input).map Subtype.val) infoEq
    have eventEq : bad = (fun draw => draw.1 owner) ⁻¹' optionBad := by
      ext draw
      constructor
      · intro outside supported
        apply outside
        intro actor acts actorDifferent actorFirst
        cases Option.some.inj (active.symm.trans acts)
        exact supported
      · intro outside supported
        exact outside (supported owner active different first)
    have choiceEvent : Subtype.val ⁻¹' optionBad = main.supportᶜ := by
      ext choice
      change (responseChoice setup leaks bounds (initialLaw setup) horizon (NativeScheduler) owner
        info (choice.1.getD ⟨none⟩) ∉ main.support) ↔ choice ∉ main.support
      rw [responseChoice_getD_eq]
    have forced := forcedAgent_of_history (⟨some control, trace⟩)
      (forcedState_of_clear_regular_notOwes wellFormed (sequence n) focal trace clear regular
        notOwed owner)
    rw [infoEq] at forced
    have massEq : (jointLaw.toOuterMeasure bad).toReal =
        ((nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale positive
          le_one weights n owner info).toOuterMeasure main.supportᶜ).toReal := by
      calc
        (jointLaw.toOuterMeasure bad).toReal =
            ((jointLaw.map (fun draw => draw.1 owner)).toOuterMeasure optionBad).toReal := by
          rw [PMF.toOuterMeasure_map_apply, eventEq]
          rfl
        _ = (((nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale positive
            le_one weights n owner info).map Subtype.val).toOuterMeasure optionBad).toReal :=
          congrArg (fun law : PMF (Option (application setup leaks).Action) =>
            (law.toOuterMeasure optionBad).toReal) marginal
        _ = _ := by rw [PMF.toOuterMeasure_map_apply, choiceEvent]
    calc
      (jointLaw.toOuterMeasure bad).toReal = _ := massEq
      _ ≤ _ := nativeComparisonStrategy_event_le_of_disjoint_main setup leaks bounds horizon
        scheduler sequence scale positive le_one weights n owner info
        (not_lateDelivery_of_firstActivation first) ⟨⟨some control, trace⟩, infoEq⟩ forced
        main.supportᶜ disjoint_compl_right
  · have zero : jointLaw.toOuterMeasure bad = 0 :=
      (PMF.toOuterMeasure_apply_eq_zero_iff jointLaw bad).mpr
        (Set.disjoint_left.mpr fun draw _ outside => outside fun owner active different first =>
          (eligible ⟨owner, active, different, first⟩).elim)
    rw [zero, ENNReal.toReal_zero]
    exact add_nonneg (sq_nonneg _) (positive n).le

private theorem oneStep_marker_mass_eq_joint
    (source : setup.intendedModel.BehavioralAssessment) (focal : Player) (cutoff : Nat)
    (profile : ∀ who, (N).BehavioralPolicy who)
    (history : (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History)
    (running : ¬ (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).terminal
      history.state)
    (main : MainActivationTraceAfter setup leaks bounds horizon (NativeScheduler) source focal
      cutoff history.trace) (later : cutoff ≤ history.trace.length) :
    (((N).runBehavioralFrom profile 1 history).toOuterMeasure
      {next | ¬ MainActivationTraceAfter setup leaks bounds horizon (NativeScheduler) source focal
        cutoff next.trace}).toReal =
      (((N).behavioralJoint profile history.trace running).toOuterMeasure
        {draw | ¬ MainActivationStep setup leaks bounds horizon (NativeScheduler) source focal
          history.state draw.1}).toReal := by
  classical
  let mark := fun next : (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History =>
    decide (¬ MainActivationTraceAfter setup leaks bounds horizon (NativeScheduler) source focal
      cutoff next.trace)
  let markStep := fun draw : {joint : Player → Option (application setup leaks).Action //
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).Legal history.state joint} =>
    decide (¬ MainActivationStep setup leaks bounds horizon (NativeScheduler) source focal
      history.state draw.1)
  have mapped : ((N).runBehavioralFrom profile 1 history).map mark =
      ((N).behavioralJoint profile history.trace running).map markStep := by
    rw [(N).runBehavioralFrom_succ_of_not_terminal profile 0 running, PMF.map_bind]
    calc
      _ = ((N).behavioralJoint profile history.trace running).bind
          (fun draw => PMF.pure (markStep draw)) := by
        apply bind_congr_on_support
        intro draw _
        apply map_bindOnSupport_const
        intro target realized
        change (PMF.pure (history.extend draw.2 realized)).map mark = _
        rw [PMF.pure_map]
        apply congrArg PMF.pure
        simp only [mark, markStep, History.extend, MainActivationTraceAfter, main, later,
          true_implies, true_and]
      _ = _ := PMF.bind_pure_comp _ _
  have mass := congrArg (fun law : PMF Bool => (law.toOuterMeasure {true}).toReal) mapped
  have markEvent : mark ⁻¹' {true} = {next | ¬ MainActivationTraceAfter setup leaks bounds
      horizon (NativeScheduler) source focal cutoff next.trace} := by
    ext next
    simp only [Set.mem_preimage, Set.mem_singleton_iff, mark, decide_eq_true_eq, Set.mem_ofPred_eq]
  have stepEvent : markStep ⁻¹' {true} = {draw | ¬ MainActivationStep setup leaks bounds horizon
      (NativeScheduler) source focal history.state draw.1} := by
    ext draw
    simp only [Set.mem_preimage, Set.mem_singleton_iff, markStep, decide_eq_true_eq,
      Set.mem_ofPred_eq]
  calc
    _ = ((((N).runBehavioralFrom profile 1 history).map mark).toOuterMeasure {true}).toReal := by
      rw [PMF.toOuterMeasure_map_apply, markEvent]
    _ = ((((N).behavioralJoint profile history.trace running).map markStep).toOuterMeasure
        {true}).toReal := mass
    _ = _ := by
      rw [PMF.toOuterMeasure_map_apply, stepEvent]
      rfl

/-- Before public exclusion or focal debt, the probability that a foreign first
callback leaves source-main support is bounded by square plus scale times the
actual remaining protocol rank. The focal policy is arbitrary. -/
theorem nativeComparison_marker_mass_le_rank [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p)) (n : ℕ)
    (focal : Player) (focalPolicy : (N).BehavioralPolicy focal)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (timely : (runtime setup).AsyncTimely delay bound)
    (certificate :
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).WellFoundedHistories)
    (extraStop : (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History → Prop)
    (start : (application setup leaks).Control)
    (startTrace :
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).Trace (some start))
    (current : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (regular : RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) focal
      startTrace) :
    (((N).runBehavioralUntil certificate
      (Function.update (nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale
        positive le_one weights n) focal focalPolicy)
      (fun history => ¬ ReactiveApplication.stateInvariant (app := application setup leaks)
        (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
          history.state ∨
        DecodedState setup leaks (failureProfile setup.program)
          (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history)
      ⟨some start, startTrace⟩).toOuterMeasure
      {final | ¬ MainActivationTraceAfter setup leaks bounds horizon (NativeScheduler) (sequence n)
        focal startTrace.length final.trace}).toReal ≤
      ((scale n) ^ 2 + scale n) * (application setup leaks).rank horizon (some start) := by
  classical
  let profile := Function.update (nativeComparisonStrategy setup leaks bounds horizon scheduler
    sequence scale positive le_one weights n) focal focalPolicy
  let stopped := fun history :
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History =>
    ¬ ReactiveApplication.stateInvariant (app := application setup leaks)
      (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
        history.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history
  let marked := {history :
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History |
    ¬ MainActivationTraceAfter setup leaks bounds horizon (NativeScheduler) (sequence n) focal
      startTrace.length history.trace}
  let payoff := fun history => @ite ℝ (history ∈ marked) (Classical.propDecidable _) 1 0
  let inside := fun history :
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History =>
    (∃ reached, history.state = some reached) ∧ TracePrefix startTrace history.trace ∧
      RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) focal history.trace ∧
      MainActivationTraceAfter setup leaks bounds horizon (NativeScheduler) (sequence n) focal
        startTrace.length history.trace
  have initialized : ∀ state ∈ (Initial).support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)) := by
    intro state supported
    obtain ⟨native, nativeSupported, rfl⟩ := PMF.support_map .. ▸ supported
    obtain ⟨inputs, rfl⟩ := serviceInitialLaw_initialized setup native nativeSupported
    exact ⟨inputs, rfl⟩
  have nativeLaw : (Initial).map RecoveryState.native = initialLaw setup := initialLaw_native setup
  have payoffBounded : ∀ history, |payoff history| ≤ 1 := by
    intro history
    dsimp only [payoff]
    split <;> norm_num
  have nonnegative : 0 ≤ (scale n) ^ 2 + scale n := add_nonneg (sq_nonneg _) (positive n).le
  have preserve : ∀ history, inside history → ¬ stopped history →
      ¬ (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).terminal history.state →
      ∀ next ∈ ((N).runBehavioralFrom profile 1 history).support,
      next ∉ marked → inside next := by
    intro history valid going running next supported unmarked
    have clear : ReactiveApplication.stateInvariant (app := application setup leaks)
        (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
          history.state := not_not.mp (fun failed => going (Or.inl failed))
    rw [(N).runBehavioralFrom_succ_of_not_terminal profile 0 running,
      PMF.mem_support_bind_iff] at supported
    obtain ⟨draw, _chosen, stepped⟩ := supported
    rw [PMF.mem_support_bindOnSupport_iff] at stepped
    obtain ⟨target, realized, reached⟩ := stepped
    change next ∈ (PMF.pure _).support at reached
    rw [PMF.mem_support_pure_iff] at reached
    subst reached
    obtain ⟨before, beforeState⟩ := valid.1
    rcases history with ⟨previous, trace⟩
    change previous = some before at beforeState
    cases beforeState
    obtain ⟨after, afterState, _recall⟩ := (application setup leaks).transition_recall_prefix
      (initialLaw setup) horizon (NativeScheduler) before target draw.1 realized
    cases afterState
    have main : MainActivationTraceAfter setup leaks bounds horizon (NativeScheduler) (sequence n)
        focal startTrace.length (trace.extend draw.1 draw.2 realized) := not_not.mp unmarked
    refine ⟨⟨after, rfl⟩, .extend valid.2.1 draw.1 draw.2 realized, ?_, main⟩
    refine ⟨valid.2.2.1, ?_⟩
    cases active : before.actor with
    | none =>
        intro actor acts different
        rw [active] at acts
        cases acts
    | some owner =>
        by_cases same : owner = focal
        · intro actor acts different
          have which := Option.some.inj (active.symm.trans acts)
          exact (different (which.symm.trans same)).elim
        have notOwed : ∀ point,
            decodedPoint setup before.execution.application.config = some point →
            ¬ ProtocolState.OwesFailure focal setup.program point := by
          intro point decoded owed
          exact going (Or.inr (Or.inl (decodedState_of_nativeDecodedState
            (failureProfile setup.program) ⟨some before, trace⟩ decoded owed)))
        exact regularStep_of_mainActivationTraceAfter wellFormed covers capacity (sequence n) focal
          owner same initialized nativeLaw opportunity timely start before startTrace trace
          valid.2.1
          current turn clear valid.2.2.1 notOwed main.1 active draw.1 draw.2
          (main.2 valid.2.1.length_le) after realized
  have futureBound : ∀ history,
      |expect ((N).runBehavioralUntil certificate profile stopped history) payoff| ≤ 1 :=
    fun _ => expect_abs_le_of_bounded zero_le_one payoffBounded
  have estimate := (N).abs_expect_runBehavioralUntil_le_of_exits certificate profile stopped inside
    payoff payoffBounded nonnegative
    (fun history => (application setup leaks).rank horizon history.state)
    (fun history valid _ => by
      have unmarked : history ∉ marked := not_not_intro valid.2.2.2
      simp only [payoff, unmarked, ↓reduceIte])
    (by
      intro history next valid going running member
      obtain ⟨⟨joint, legal, realized⟩, _⟩ :=
        (N).mem_support_runBehavioralFrom_one profile running member
      exact (application setup leaks).rank_step (initialLaw setup) horizon (NativeScheduler)
        history.state next.state joint running realized)
    (by
      intro history valid going running
      obtain ⟨control, controlState⟩ := valid.1
      rcases history with ⟨before, trace⟩
      change before = some control at controlState
      cases controlState
      let history : (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History :=
        ⟨some control, trace⟩
      let step := (N).runBehavioralFrom profile 1 history
      let outside := fun next => if inside next then 0
        else expect ((N).runBehavioralUntil certificate profile stopped next) payoff
      have outsideBound : ∀ next, |outside next| ≤ 1 := by
        intro next
        dsimp only [outside]
        split
        · norm_num
        · exact futureBound next
      have outsideNonnegative : ∀ next, 0 ≤ outside next := by
        intro next
        dsimp only [outside]
        split
        · exact le_rfl
        · apply expect_nonneg
          intro final _
          dsimp only [payoff]
          split <;> norm_num
      have comparison : expect step outside ≤ expect step payoff := by
        apply expect_mono ?_
          (payoffIntegrable_of_bounded step outside outsideBound)
          (payoffIntegrable_of_bounded step payoff payoffBounded)
        intro next member
        dsimp only [outside]
        split
        · dsimp only [payoff]
          split <;> norm_num
        · rename_i outsideNext
          by_cases markedNext : next ∈ marked
          · simpa only [payoff, markedNext, ↓reduceIte] using
              (le_abs_self _).trans (futureBound next)
          · exact (outsideNext (preserve history valid going running next member markedNext)).elim
      have clear : ExclusionEvidence 0 ∅
          (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) :=
        not_not.mp (fun failed => going (Or.inl failed))
      have notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
          ¬ ProtocolState.OwesFailure focal setup.program point := by
        intro point decoded owed
        exact going (Or.inr (Or.inl (decodedState_of_nativeDecodedState
          (failureProfile setup.program) history decoded owed)))
      rw [abs_of_nonneg (expect_nonneg step outside (fun next _ => outsideNonnegative next))]
      calc
        expect step outside ≤ expect step payoff := comparison
        _ = (step.toOuterMeasure marked).toReal := by
          simpa only [payoff] using expect_indicator step marked
        _ = _ := oneStep_marker_mass_eq_joint setup leaks bounds horizon scheduler (sequence n)
          focal startTrace.length profile history running valid.2.2.2 valid.2.1.length_le
        _ ≤ _ := nativeComparison_joint_mainActivation_failure_le setup leaks bounds horizon
          scheduler
          wellFormed sequence scale positive le_one weights n focal focalPolicy control trace clear
          valid.2.2.1 notOwed running)
    ⟨some start, startTrace⟩
    ⟨⟨start, rfl⟩, .refl, regular,
      mainActivationTraceAfter_of_length_le (sequence n) focal startTrace startTrace.length le_rfl⟩
  have indicator := expect_indicator
    ((N).runBehavioralUntil certificate profile stopped ⟨some start, startTrace⟩) marked
  have indicatorAbs := congrArg abs indicator
  rw [abs_of_nonneg ENNReal.toReal_nonneg] at indicatorAbs
  calc
    _ = |expect ((N).runBehavioralUntil certificate profile stopped ⟨some start, startTrace⟩)
        payoff| := by simpa only [payoff] using indicatorAbs.symm
    _ ≤ _ := estimate

/-- A first foreign public failure remembers a future first
activation outside main support. The environment boundary and all prefix
regularity facts come from the actual stopped continuation. -/
theorem recovery_stopped_foreignFailure_marked
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal : Player)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks (Initial) horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks (Initial) horizon scheduler
      bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (certificate : (onePacketProtocol setup leaks bounds horizon
      (NativeScheduler)).WellFoundedHistories)
    (profile : ∀ who, (N).BehavioralPolicy who)
    (extraStop : (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History → Prop)
    (start : (application setup leaks).Control)
    (startTrace :
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).Trace (some start))
    (current : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨start.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon (NativeScheduler) source focal startTrace)
    (final : (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History)
    (supported : final ∈ ((N).runBehavioralUntil certificate profile (fun history =>
      ¬ ReactiveApplication.stateInvariant (app := application setup leaks)
        (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
          history.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history)
      ⟨some start, startTrace⟩).support)
    (finalControl : (application setup leaks).Control) (state : final.state = some finalControl)
    (owner : Player) (different : owner ≠ focal) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (failed : finalControl.execution.application.PublicFailure event) :
    ¬ MainActivationTraceAfter setup leaks bounds horizon (NativeScheduler) source focal
      startTrace.length final.trace := by
  classical
  have initialized : ∀ state ∈ (Initial).support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)) := by
    intro state member
    obtain ⟨native, nativeMember, rfl⟩ := PMF.support_map .. ▸ member
    obtain ⟨inputs, rfl⟩ := serviceInitialLaw_initialized setup native nativeMember
    exact ⟨inputs, rfl⟩
  have boundary := responseMenu_stopped_exclusion_boundary (runtime setup) leaks (initialLaw setup)
    horizon (NativeScheduler) (bounds.onePacketMenu (runtime setup) leaks) certificate profile
    (fun history => DecodedState setup leaks (failureProfile setup.program)
      (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history)
    ⟨some start, startTrace⟩ start rfl clear final supported
  intro main
  have regularFinal := (recovery_stopped_regular_of_mainActivationTraceAfter wellFormed covers
    capacity source focal initialized (initialLaw_native setup) opportunity timely certificate
    profile extraStop ⟨some start, startTrace⟩ start rfl current turn regular final supported).2.2
    main
  rcases final with ⟨finalState, target⟩
  change finalState = some finalControl at state
  subst finalState
  rcases boundary with finalClear | ⟨remaining, execution, prior, command, next, priorClear,
    priorGoing, _chosen, reached, endpoint, startPrefix, targetPrefix⟩
  · have impossible : owner ∈ (∅ : Finset Player) :=
      (finalClear.excluded_zero owner).mpr ⟨event, owned, failed⟩
    exact Finset.notMem_empty owner impossible
  · cases Option.some.inj endpoint
    have beforeRegular := regularTrace_of_tracePrefix source focal targetPrefix regularFinal
    have beforeNotOwed : ∀ point, decodedPoint setup execution.application.config = some point →
        ¬ ProtocolState.OwesFailure focal setup.program point := by
      intro point decoded owed
      apply priorGoing
      left
      exact decodedState_of_nativeDecodedState (failureProfile setup.program)
        ⟨some ⟨remaining + 1, none, execution⟩, prior⟩ decoded owed
    exact recovery_firstForeignFailure_not_mainActivationTraceAfter wellFormed covers capacity
      source focal owner different initialized (initialLaw_native setup) opportunity inclusion
      timely
      start startTrace remaining execution prior startPrefix current event turn priorClear
      beforeRegular beforeNotOwed owned command next reached target targetPrefix failed main

/-- From a clear source turn, actual foreign first failures under the common comparison
profile have probability at most square plus scale times remaining protocol rank.
The focal policy is arbitrary, and the runner stops at focal source debt. -/
theorem nativeComparison_foreign_failure_mass_le_rank [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p)) (n : ℕ)
    (focal : Player) (focalPolicy : (N).BehavioralPolicy focal)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (certificate :
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).WellFoundedHistories)
    (extraStop : (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History → Prop)
    (start : (application setup leaks).Control)
    (startTrace :
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).Trace (some start))
    (current : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨start.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) focal
      startTrace) :
    (((N).runBehavioralUntil certificate
      (Function.update (nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale
        positive le_one weights n) focal focalPolicy)
      (fun history => ¬ ReactiveApplication.stateInvariant (app := application setup leaks)
        (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
          history.state ∨
        DecodedState setup leaks (failureProfile setup.program)
          (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history)
      ⟨some start, startTrace⟩).toOuterMeasure
      {final | ∃ (control : (application setup leaks).Control) (owner : Player)
        (event : (graph setup).EventId), final.state = some control ∧ owner ≠ focal ∧
        (graph setup).actor? event = some owner ∧
          control.execution.application.PublicFailure event}).toReal ≤
      ((scale n) ^ 2 + scale n) * (application setup leaks).rank horizon (some start) := by
  classical
  let profile := Function.update (nativeComparisonStrategy setup leaks bounds horizon scheduler
    sequence scale positive le_one weights n) focal focalPolicy
  let stopped := fun history :
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History =>
    ¬ ReactiveApplication.stateInvariant (app := application setup leaks)
      (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
        history.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history
  let law := (N).runBehavioralUntil certificate profile stopped ⟨some start, startTrace⟩
  let failures := {final :
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History |
    ∃ (control : (application setup leaks).Control) (owner : Player)
      (event : (graph setup).EventId), final.state = some control ∧ owner ≠ focal ∧
      (graph setup).actor? event = some owner ∧ control.execution.application.PublicFailure event}
  let marked := {final :
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History |
    ¬ MainActivationTraceAfter setup leaks bounds horizon (NativeScheduler) (sequence n) focal
      startTrace.length final.trace}
  have subset : failures ∩ law.support ⊆ marked := by
    rintro final ⟨⟨control, owner, event, state, different, owned, failed⟩, supported⟩
    exact recovery_stopped_foreignFailure_marked setup leaks bounds horizon scheduler wellFormed
      covers capacity (sequence n) focal opportunity inclusion timely certificate profile extraStop
      start startTrace current turn clear regular final supported control state owner different
      event
      owned failed
  have mass : law.toOuterMeasure failures ≤ law.toOuterMeasure marked := by
    calc
      _ = law.toOuterMeasure (failures ∩ law.support) := by
        rw [← PMF.toOuterMeasure_apply_inter_support]
      _ ≤ _ := MeasureTheory.measure_mono subset
  calc
    _ = (law.toOuterMeasure failures).toReal := rfl
    _ ≤ (law.toOuterMeasure marked).toReal := ENNReal.toReal_mono (outerMeasure_ne_top _ _) mass
    _ ≤ _ := nativeComparison_marker_mass_le_rank setup leaks bounds horizon scheduler wellFormed
      covers capacity sequence scale positive le_one weights n focal focalPolicy opportunity timely
      certificate extraStop start startTrace current turn regular


private theorem foreign_failure_of_unclear_survival (focal : Player)
    (history : (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History)
    (unclear : ¬ ReactiveApplication.stateInvariant (app := application setup leaks)
      (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
        history.state)
    (survives : focal ∉ nativeFailureOwners (runtime setup) leaks history.state) :
    ∃ (control : (application setup leaks).Control) (owner : Player)
      (event : (graph setup).EventId), history.state = some control ∧ owner ≠ focal ∧
      (graph setup).actor? event = some owner ∧ control.execution.application.PublicFailure event
        := by
  classical
  rcases history with ⟨state, trace⟩
  cases state with
  | none => exact (unclear trivial).elim
  | some control =>
    have receipts := native_receiptsComplete_history (runtime setup) leaks (initialLaw setup)
      (serviceInitialLaw_initialized setup) horizon (NativeScheduler)
      ((bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
        (NativeScheduler) trace)
    have witness : ∃ (owner : Player) (event : (graph setup).EventId),
        (graph setup).actor? event = some owner ∧
          control.execution.application.PublicFailure event := by
      by_contra missing
      apply unclear
      refine ⟨receipts, fun event lower => by omega, fun owner => ⟨?_, ?_⟩⟩
      · intro member
        exact (Finset.notMem_empty owner member).elim
      · rintro (inherited | ⟨event, _lower, owned, failed⟩)
        · exact inherited
        · exact (missing ⟨owner, event, owned, failed⟩).elim
    obtain ⟨owner, event, owned, failed⟩ := witness
    refine ⟨control, owner, event, rfl, ?_, owned, failed⟩
    intro same
    subst owner
    apply survives
    change focal ∈ control.execution.application.failureOwners
    simp only [EventGraphRuntime.State.failureOwners, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨event, owned, failed⟩

/-- The actual foreign first-exit event of the debt-stopped common comparison
profile is bounded by square plus scale times remaining protocol rank. -/
theorem nativeComparison_foreign_exit_mass_le_rank [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p)) (n : ℕ)
    (focal : Player) (focalPolicy : (N).BehavioralPolicy focal)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (certificate :
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).WellFoundedHistories)
    (extraStop : (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History → Prop)
    (start : (application setup leaks).Control)
    (startTrace :
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).Trace (some start))
    (current : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨start.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) focal
      startTrace) :
    (((N).runBehavioralUntil certificate
      (Function.update (nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale
        positive le_one weights n) focal focalPolicy)
      (fun history => ¬ ReactiveApplication.stateInvariant (app := application setup leaks)
        (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
          history.state ∨
        DecodedState setup leaks (failureProfile setup.program)
          (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history)
      ⟨some start, startTrace⟩).toOuterMeasure
      {final | ¬ ReactiveApplication.stateInvariant (app := application setup leaks)
        (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
          final.state ∧
        focal ∉ nativeFailureOwners (runtime setup) leaks final.state}).toReal ≤
      ((scale n) ^ 2 + scale n) * (application setup leaks).rank horizon (some start) := by
  classical
  let profile := Function.update (nativeComparisonStrategy setup leaks bounds horizon scheduler
    sequence scale positive le_one weights n) focal focalPolicy
  let stopped := fun history :
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History =>
    ¬ ReactiveApplication.stateInvariant (app := application setup leaks)
      (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
        history.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history
  let law := (N).runBehavioralUntil certificate profile stopped ⟨some start, startTrace⟩
  let exits := {final :
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History |
    ¬ ReactiveApplication.stateInvariant (app := application setup leaks)
      (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
        final.state ∧
      focal ∉ nativeFailureOwners (runtime setup) leaks final.state}
  let failures := {final :
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History |
    ∃ (control : (application setup leaks).Control) (owner : Player)
      (event : (graph setup).EventId), final.state = some control ∧ owner ≠ focal ∧
      (graph setup).actor? event = some owner ∧ control.execution.application.PublicFailure event}
  have subset : exits ⊆ failures := by
    intro final eligible
    exact foreign_failure_of_unclear_survival setup leaks bounds horizon scheduler focal final
      eligible.1 eligible.2
  have mass : law.toOuterMeasure exits ≤ law.toOuterMeasure failures :=
    MeasureTheory.measure_mono subset
  calc
    _ = (law.toOuterMeasure exits).toReal := rfl
    _ ≤ (law.toOuterMeasure failures).toReal := ENNReal.toReal_mono (outerMeasure_ne_top _ _) mass
    _ ≤ _ := nativeComparison_foreign_failure_mass_le_rank setup leaks bounds horizon scheduler
      wellFormed covers capacity sequence scale positive le_one weights n focal focalPolicy
      opportunity inclusion timely certificate extraStop start startTrace current turn clear regular

end Vegas.RecoveryOnePacket
