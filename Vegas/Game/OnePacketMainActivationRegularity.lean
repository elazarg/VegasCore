/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionStoppedBoundary
import Vegas.Pending.ExclusionFailureOwners
import Vegas.Game.OnePacketRareMainMass
import Vegas.Game.OnePacketForeignFailure
import Vegas.Game.OnePacketDebtRouting
import GameTheoryExtensions.Analysis.Protocol.StoppedExitBound

/-! # Source-main first responses preserve actual counted regularity -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}

/-- At a clear regular prefix before focal debt, previous source-main foreign
first callbacks prevent the current foreign callback from being a late delivery.
The comparison begins at an actual focal source turn. -/
theorem nonlate_of_mainActivationTraceAfter
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal owner : Player)
    (different : owner ≠ focal)
    {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      OpportunityAt runtime leaks control.execution delay)
    (timely : runtime.AsyncTimely delay bound)
    (start control : (application setup runtime leaks).Control)
    (startTrace : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).Trace (some start))
    (trace : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).Trace (some control))
    (startPrefix : TracePrefix startTrace trace)
    (current : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup runtime leaks bounds horizon
      scheduler source focal trace)
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (main : MainActivationTraceAfter setup runtime leaks bounds horizon
      scheduler source focal
      startTrace.length trace) :
    ¬ LateDelivery setup runtime leaks owner (some (control.execution.recall owner,
      control.execution.observe (application setup runtime leaks) owner)) := by
  rintro ⟨past, view, event, same, pending, entry, remembered, activated⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same.symm)
  obtain ⟨point, decoded, intended⟩ :=
    intended_of_clear_regular_notOwes (runtime := runtime) wellFormed source focal trace clear
      regular notOwed
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (runtime := runtime) (failureProfile
    setup.program)
    (bounds.onePacketMenu runtime leaks) horizon scheduler trace control rfl
  have samePoint := Option.some.inj ((decodedPoint_eq residual).symm.trans decoded)
  subst point
  have submissions := onePacket_ownSubmissionsAtTurn (runtime := runtime) bounds trace
    residual.checkpoint.ordered _
    residual.decode intended owner
  obtain ⟨before, prior, response, joint, legal, realized, afterPrefix, acting, chosen,
    firstPending, never⟩ := firstActivation_response_prefix_of_recall (runtime := runtime) trace
      owner event
      ⟨entry, remembered, activated⟩ submissions
  have ready := (control.execution.application.publicView_eventReady event).mp
    (pendingEvent_spec (runtime := runtime) pending).2.1
  have owned := (pendingEvent_spec (runtime := runtime) pending).2.2.1
  have unfinished : event ∉ start.execution.application.config.cut.completed := by
    intro completed
    obtain ⟨value, output⟩ := Option.isSome_iff_exists.mp
      ((start.execution.application.config.output_available event).mpr completed)
    have stored : start.execution.application.config.store (.inr event) = some value := output
    have retained := storedValue_of_tracePrefix (runtime := runtime) startTrace startPrefix (.inr
      event) value stored
    change control.execution.application.config.outputs event = some value at retained
    exact ready.1 ((control.execution.application.config.output_available event).mp
      (by rw [retained]; rfl))
  have priorPrefix : TracePrefix prior trace :=
    (TracePrefix.extend .refl joint legal realized).trans afterPrefix
  have readyBefore := (before.execution.application.publicView_eventReady event).mp
    (pendingEvent_spec (runtime := runtime) firstPending).2.1
  have future := foreign_ready_prefix_after_ownTurn (runtime := runtime) startTrace prior
    startPrefix priorPrefix focal
    owner different current event turn owned unfinished readyBefore
  have supportStep := mainActivationStep_of_tracePrefix (runtime := runtime) source focal
    startTrace.length prior joint
    legal realized afterPrefix main future.length_le
  have first : FirstActivation setup runtime leaks owner (some (before.execution.recall owner,
      before.execution.observe (application setup runtime leaks) owner)) :=
    ⟨before.execution.recall owner, before.execution.observe (application setup runtime leaks)
      owner, event,
      rfl, firstPending, never⟩
  have supported := supportStep owner acting different first
  rw [chosen, Option.getD_some] at supported
  obtain ⟨earlierClear, earlierRegular, earlierNotOwed⟩ := clear_regular_notOwes_of_tracePrefix
    (runtime := runtime)
    wellFormed source focal owner different prior trace priorPrefix clear regular notOwed
  obtain ⟨earlyPoint, earlyDecoded, earlyIntended⟩ :=
    intended_of_clear_regular_notOwes (runtime := runtime) wellFormed source focal prior
      earlierClear earlierRegular
      earlierNotOwed
  have forced : ForcedState setup runtime leaks owner (some before) :=
    (forcedState_iff_decodedPoint (runtime := runtime) before).mpr
      ⟨earlyPoint, earlyDecoded, forcedPoint_of_intended owner earlyIntended⟩
  have ownerNotOwed : ∀ point, decodedPoint setup before.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure owner setup.program point := by
    intro point pointDecoded
    cases Option.some.inj (earlyDecoded.symm.trans pointDecoded)
    exact ProtocolState.Intended.not_owesFailure owner setup.program earlyPoint earlyIntended
  have offered : response ∈ bounds.onePacketActions runtime leaks owner
      (before.execution.recall owner) (before.execution.observe (application setup runtime leaks)
        owner) :=
    (chosen ▸ legal.2 owner).2
  have selected : (responseChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler
      owner (some (before.execution.recall owner,
        before.execution.observe (application setup runtime leaks) owner)) response).1 = some
          response := by
    simp only [responseChoice, dite_eq_left offered]
  have named : runtime.submittedEvent? leaks response = some event := by
    rcases before with ⟨remaining, actor, execution⟩
    dsimp only at acting
    subst actor
    have fits := firstActivation_inclusionFits_of_counted_opportunity setup runtime leaks bounds
      horizon
      scheduler delay bound opportunity timely prior rfl earlierClear event
      (pendingEvent_spec (runtime := runtime) firstPending).1 never
    obtain ⟨action, material, canonical, sends, _⟩ := honestChoice_canonical_of_debtFree (runtime
      := runtime) wellFormed
      covers capacity source prior owner forced ownerNotOwed event firstPending bound fits _
      supported
    have responseEq := Option.some.inj (selected.symm.trans canonical)
    rw [responseEq]
    rcases canonical_silentOrNames (runtime := runtime) owner (execution.recall owner)
      (execution.observe (application setup runtime leaks) owner) event action with silent | names
    · rw [sends] at silent
      cases silent
    · exact names
  let recordedEntry := respondEntry setup runtime leaks before.execution owner response
  have initialRecord := recordsEntry_respond (runtime := runtime) before.execution owner response
    before.remaining none
  have laterRecord : ∀ {state}
      {later : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state},
      TracePrefix (prior.extend joint legal realized) later →
        RecordsEntry setup runtime leaks owner recordedEntry state := by
    intro state later laterPrefix
    induction laterPrefix with
    | refl => exact initialRecord
    | @extend first second earlier isPrefix actions allowed reached ih =>
        exact recordsEntry_transition (runtime := runtime) owner recordedEntry (initialLaw setup)
          horizon scheduler
          first second actions ih reached
  obtain ⟨earlier, later, split⟩ := laterRecord afterPrefix
  have recorded :
      runtime.eventRecorded leaks (control.execution.recall owner) event = true :=
    (runtime.eventRecorded_iff leaks (control.execution.recall owner) event).mpr
      ⟨recordedEntry, by rw [split]; exact List.mem_append_right _ (List.mem_cons_self ..), named⟩
  rw [(pendingEvent_spec (runtime := runtime) pending).2.2.2] at recorded
  cases recorded

private theorem main_of_no_pending
    (source : setup.intendedModel.BehavioralAssessment)
    {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler}
    {remaining : Nat} {owner : Player} {execution : (application setup runtime leaks).Execution}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some owner, execution⟩))
    (point : ProtocolState setup.program)
    (decoded : decodedPoint setup execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point)
    (noPending : pendingEvent setup runtime leaks owner (some (execution.recall owner,
      execution.observe (application setup runtime leaks) owner)) = none)
    (response : (application setup runtime leaks).Action)
    (offered : response ∈ bounds.onePacketActions runtime leaks owner
      (execution.recall owner) (execution.observe (application setup runtime leaks) owner)) :
    responseChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler owner
      (some (execution.recall owner, execution.observe (application setup runtime leaks) owner))
        response ∈
      (honestChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler source owner
        (some (execution.recall owner,
          execution.observe (application setup runtime leaks) owner))).support := by
  have rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
    horizon scheduler trace
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (runtime := runtime) (failureProfile
    setup.program)
    (bounds.onePacketMenu runtime leaks) horizon scheduler trace _ rfl
  have samePoint := Option.some.inj ((decodedPoint_eq residual).symm.trans decoded)
  subst point
  have records : ∀ event, execution.application.publicView.ownTurn? owner = some event →
      runtime.eventRecorded leaks (execution.recall owner) event = true := by
    intro event turn
    cases actual : runtime.eventRecorded leaks (execution.recall owner) event with
    | true => rfl
    | false =>
        have pending : pendingEvent setup runtime leaks owner (some (execution.recall owner,
            execution.observe (application setup runtime leaks) owner)) = some event :=
          pendingEvent_of_spec (runtime := runtime) turn actual
        rw [noPending] at pending
        cases pending
  have silent : response.transmission = none := by
    rcases ((bounds.mem_onePacketActions runtime leaks owner _ _ response).mp
      offered).2 with
      silent | ⟨material, transmits, permitted⟩
    · exact silent
    · exfalso
      have valid := ((countPermits_eq_true_iff _ _).mp permitted).1
      obtain ⟨event, named, _⟩ := (WitnessedPacket.tokenValid_iff _).mp valid
      have submitted : runtime.submittedEvent? leaks response = some event := by
        unfold EventGraphRuntime.submittedEvent?
        rw [transmits]
        exact named
      have atTurn := onePacket_submission_atTurn (runtime := runtime) bounds (failureProfile
        setup.program) rawTrace
        residual response offered event submitted
      rcases atTurn with turn | owed
      · exact onePacket_recorded_not_offered (runtime := runtime) trace owner event (records event
          turn) response
          submitted offered
      · exact ProtocolState.Intended.not_owesFailure owner setup.program _ intended
          (owed _ residual.decode)
  have responseEq : response = ⟨none⟩ := by
    cases response
    cases silent
    rfl
  have mainLaw : honestChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler
    source owner
      (some (execution.recall owner, execution.observe (application setup runtime leaks) owner)) =
      PMF.pure (silenceChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler owner
        (some (execution.recall owner, execution.observe (application setup runtime leaks)
          owner))) := by
    cases turn : execution.application.publicView.ownTurn? owner with
    | none =>
        exact honestChoice_silence_of_noTurn (runtime := runtime) source owner (execution.recall
          owner)
          (execution.observe (application setup runtime leaks) owner) turn
    | some event =>
        exact honestChoice_silence_of_recorded (runtime := runtime) source trace owner event turn
          (records event turn)
  rw [mainLaw, responseEq]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

/-- Before the rare marker, a foreign first callback is main by the marker
condition, while every other callback has the main silent response. -/
theorem response_main_of_mainActivationTraceAfter
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal owner : Player)
    (different : owner ≠ focal)
    {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      OpportunityAt runtime leaks control.execution delay)
    (timely : runtime.AsyncTimely delay bound)
    (start control : (application setup runtime leaks).Control)
    (startTrace : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).Trace (some start))
    (trace : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).Trace (some control))
    (startPrefix : TracePrefix startTrace trace)
    (current : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup runtime leaks bounds horizon
      scheduler source focal trace)
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (main : MainActivationTraceAfter setup runtime leaks bounds horizon
      scheduler source focal
      startTrace.length trace)
    (active : control.actor = some owner)
    (joint : Player → Option (application setup runtime leaks).Action)
    (legal : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).Legal
        (some control) joint)
    (stepMain : MainActivationStep setup runtime leaks bounds horizon
      scheduler source focal
      (some control) joint) :
    responseChoice setup runtime leaks bounds (initialLaw setup) horizon
      scheduler owner
      (some (control.execution.recall owner,
        control.execution.observe (application setup runtime leaks) owner)) ((joint owner).getD
          ⟨none⟩) ∈
      (honestChoice setup runtime leaks bounds (initialLaw setup) horizon
        scheduler source owner
        (some (control.execution.recall owner,
          control.execution.observe (application setup runtime leaks) owner))).support := by
  have nonlate := nonlate_of_mainActivationTraceAfter (runtime := runtime) wellFormed covers
    capacity source
    focal owner different opportunity timely start control startTrace trace
    startPrefix current turn clear regular notOwed main
  by_cases first : FirstActivation setup runtime leaks owner (some (control.execution.recall owner,
      control.execution.observe (application setup runtime leaks) owner))
  · exact stepMain owner active different first
  have noPending : pendingEvent setup runtime leaks owner (some (control.execution.recall owner,
      control.execution.observe (application setup runtime leaks) owner)) = none := by
    cases actual : pendingEvent setup runtime leaks owner (some (control.execution.recall owner,
        control.execution.observe (application setup runtime leaks) owner)) with
    | none => rfl
    | some event =>
        exact ((firstActivation_or_lateDelivery (runtime := runtime) actual).elim first
          nonlate).elim
  obtain ⟨point, decoded, intended⟩ :=
    intended_of_clear_regular_notOwes (runtime := runtime) wellFormed source focal trace clear
      regular notOwed
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
        main_of_no_pending (runtime := runtime) source trace point decoded intended noPending
          response localLegal.2

/-- Before a non-main first callback, an unmarked foreign response preserves
the full source-factor regularity predicate. -/
theorem regularStep_of_native_mainActivationTraceAfter
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal owner : Player)
    (different : owner ≠ focal)
    {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      OpportunityAt runtime leaks control.execution delay)
    (timely : runtime.AsyncTimely delay bound)
    (start control : (application setup runtime leaks).Control)
    (startTrace : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).Trace (some start))
    (trace : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).Trace (some control))
    (startPrefix : TracePrefix startTrace trace)
    (current : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup runtime leaks bounds horizon
      scheduler source focal trace)
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (main : MainActivationTraceAfter setup runtime leaks bounds horizon
      scheduler source focal
      startTrace.length trace)
    (active : control.actor = some owner)
    (joint : Player → Option (application setup runtime leaks).Action)
    (legal : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).Legal
        (some control) joint)
    (stepMain : MainActivationStep setup runtime leaks bounds horizon
      scheduler source focal
      (some control) joint)
    (next : (application setup runtime leaks).Control)
    (realized : some next ∈ ((onePacketProtocol setup runtime leaks bounds horizon
      scheduler).step
        (some control) ⟨joint, legal⟩).support) :
    RegularStep setup runtime leaks bounds horizon
      scheduler source focal
      (some control) joint (some next) := by
  have supported := response_main_of_mainActivationTraceAfter (runtime := runtime) wellFormed
    covers capacity
    source focal owner different opportunity timely start control startTrace
    trace
    startPrefix current turn clear regular notOwed main active joint legal stepMain
  rcases control with ⟨remaining, actor, execution⟩
  dsimp only at active
  subst actor
  exact regularStep_of_clear_regular_main (runtime := runtime) wellFormed source focal owner covers
    (by have positive := capacity owner; omega) trace clear regular notOwed joint legal next
    realized
    supported

/-- Actual stopped play keeps regularity whenever no foreign first callback
has left source-main support. Focal actions and the remaining behavioral laws
are arbitrary. Only public-clear prefixes before focal debt use service. -/
theorem stopped_regular_of_mainActivationTraceAfter
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal : Player)
    {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      OpportunityAt runtime leaks control.execution delay)
    (timely : runtime.AsyncTimely delay bound)
    (certificate : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).WellFoundedHistories)
    (profile : ∀ who, (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralPolicy who)
    (extraStop : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).History → Prop)
    (start : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).History)
    (control : (application setup runtime leaks).Control) (state : start.state = some control)
    (current : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? focal = some current)
    (regular : RegularTrace setup runtime leaks bounds horizon
      scheduler source focal
      start.trace) :
    ∀ final ∈ ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).runBehavioralUntil
        certificate profile (fun history =>
          ¬ ReactiveApplication.stateInvariant (app := application setup runtime leaks)
            (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
              history.state ∨
          DecodedState setup runtime leaks (failureProfile setup.program)
            (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history)
        start).support,
      (∃ reached, final.state = some reached) ∧ TracePrefix start.trace final.trace ∧
        (MainActivationTraceAfter setup runtime leaks bounds horizon
          scheduler source focal
          start.trace.length final.trace →
          RegularTrace setup runtime leaks bounds horizon
            scheduler source focal
            final.trace) := by
  classical
  rcases start with ⟨startState, startTrace⟩
  change startState = some control at state
  subst startState
  let start : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).History :=
    ⟨some control, startTrace⟩
  let model := onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
  let stopped := fun history :
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).History =>
    ¬ ReactiveApplication.stateInvariant (app := application setup runtime leaks)
      (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
        history.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history
  let property := fun history :
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).History =>
    (∃ reached, history.state = some reached) ∧ TracePrefix start.trace history.trace ∧
      (MainActivationTraceAfter setup runtime leaks bounds horizon scheduler source focal
        start.trace.length history.trace →
        RegularTrace setup runtime leaks bounds horizon scheduler source focal history.trace)
  have initialProperty : property start := ⟨⟨control, rfl⟩, .refl, fun _ => regular⟩
  have preserved : ∀ history, ¬ stopped history →
      ¬ (onePacketProtocol setup runtime leaks bounds horizon scheduler).terminal history.state →
      property history → ∀ next ∈ (model.runBehavioralFrom profile 1 history).support,
        property next := by
    intro history going running valid next supported
    have clear : ReactiveApplication.stateInvariant (app := application setup runtime leaks)
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
    obtain ⟨after, afterState, _recall⟩ := (application setup runtime
      leaks).transition_recall_prefix
      (initialLaw setup) horizon scheduler before target draw.1 realized
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
          exact decodedState_of_nativeDecodedState (runtime := runtime) (failureProfile
            setup.program)
            ⟨some before, trace⟩ decoded owed
        exact regularStep_of_native_mainActivationTraceAfter (runtime := runtime) wellFormed
          covers capacity source focal
          owner
          same opportunity timely control before start.trace trace valid.2.1
          current turn clear beforeRegular notOwed beforeMain active draw.1 draw.2
          (main.2 valid.2.1.length_le) after realized
  exact model.runBehavioralUntil_support_history_closed certificate profile stopped property
    preserved start initialProperty

end Vegas
