/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDebtFreeResponse
import Vegas.Game.OnePacketCanonicalSafety
import Vegas.Game.OnePacketClearRegularity
import Vegas.Game.OnePacketDisclosureResolves
import Vegas.Pending.ExclusionAcceptedOutput

/-! # First public failures exclude actual source-main counted responses

The argument depends on the native callback deadline and protected fresh-call
settlement facts. Concrete service contracts are supplied in separate adapters.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime GameTheory.Math.Probability

private theorem isFailure_cast {Player : Type} {L : IExpr}
    {first second : EventGraph.EventField Player L} (same : first = second)
    (value : first.Value) :
    second.IsFailure (cast (congrArg EventGraph.EventField.Value same) value) ↔
      first.IsFailure value := by
  cases same
  rfl

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem resolution_failure_of_intended_impossible
    {bounds : MessageBounds (graph setup)} {horizon : Nat}
    {scheduler : (application setup runtime leaks).Scheduler}
    {control : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    {event : (graph setup).EventId} {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (ready : control.execution.application.config.cut.Ready event)
    {point : ProtocolState setup.program}
    (decoded : decodedPoint setup control.execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point)
    (failed : EventGraph.EventCode.resolveOutput? binding checks true
      control.execution.application.config.store = some .failure) : False := by
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (runtime := runtime)
    (failureProfile setup.program) (bounds.onePacketMenu runtime leaks) horizon scheduler
    trace control rfl
  have pointEq := Option.some.inj ((decodedPoint_eq residual).symm.trans decoded)
  have active : owner ∉ control.execution.application.config.defaulted := by
    rw [defaulted_eq_empty_of_decodedIntended decoded intended]
    exact Finset.notMem_empty _
  have stepEq := control.execution.application.config.step_eq_map_of_code event ready outputEq _
    codeEq true (PMF.pure .failure) (by
      change (EventGraph.EventCode.resolveOutput? binding checks
        (if owner ∈ control.execution.application.config.defaulted then false else true)
        control.execution.application.config.store).map PMF.pure = _
      rw [ite_eq_right active, failed]
      rfl)
  rw [PMF.pure_map] at stepEq
  have member : control.execution.application.config.complete event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
      (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload))) ∈
      (control.execution.application.config.step event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)).support := by
    rw [stepEq]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨successor, reached⟩ := residual.step event ready _ _ member
  rw [pointEq] at reached
  have atEvent : control.execution.application.config.cut.IsPrefix event.val :=
    ⟨event.isLt.le, fun query =>
      setup.eventGraph.sequentialize_mem_completed_iff_lt_of_ready _ ready⟩
  have rankEq := atEvent.unique residual.checkpoint.ordered
  subst rank
  have nextDecoded := successor.decode
  unfold sourceServicePrefix? serviceSourcePrefix? at nextDecoded
  have failedNext := ProtocolState.revealFailed_of_decode_failure setup.program event.val
    (event.val + 1) (ContextRefs.initial setup.context (outputLayout setup.program)) []
    (Revelations.initial setup.context) (outputRef setup.program) _ _ _ _ event.isLt
    (Nat.lt_succ_self _) owner payload outputEq nextDecoded
    ((eventOwner?_eq_actor setup.program event).trans (nodeView_resolve_actor outputEq codeEq))
    (by
      change (control.execution.application.config.complete event ready _ _).outputs event = _
      rw [EventGraph.Config.complete_output_same])
  exact ProtocolState.not_revealFailed_step owner setup.program _ _ _
    (ProtocolState.intendedFor_of_intended owner setup.program point intended)
    (forcedPoint_of_intended owner intended).1
    (decodeEventAction_disclosure_true setup.program event.val event.isLt outputEq)
    reached failedNext

/-- A source-main response cannot precede a public failure when its actual native
callback fits the original deadline and its recorded fresh calls settle. -/
theorem firstResponse_not_main_of_publicFailure_of_settles
    (bounds : MessageBounds (graph setup)) (wellFormed : setup.WellFormed)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal : Player)
    (horizon : Nat) (scheduler : (application setup runtime leaks).Scheduler)
    (bound : (graph setup).EventId → Nat)
    {remaining : Nat} {who : Player} {execution : (application setup runtime leaks).Execution}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (clear : execution.application.config.defaulted = ∅)
    (regular : RegularTrace setup runtime leaks bounds horizon scheduler source focal trace)
    (notOwed : ∀ point, decodedPoint setup execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (event : (graph setup).EventId)
    (pending : pendingEvent setup runtime leaks who (some (execution.recall who,
      execution.observe (application setup runtime leaks) who)) = some event)
    (fits : execution.application.publicView.InclusionFitsDeadline runtime bound event)
    (choice : (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).Choice who
      (some (execution.recall who, execution.observe (application setup runtime leaks) who)))
    (response : (application setup runtime leaks).Action) (selected : choice.1 = some response)
    (after : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, none,
        execution.respond (application setup runtime leaks) who response⟩))
    (next : (application setup runtime leaks).Execution)
    (settles : SettlesFreshCalls setup leaks who event bound next)
    (control : (application setup runtime leaks).Control) (nextExecution : control.execution = next)
    (target : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control)) (isPrefix : TracePrefix after target)
    (failed : next.application.PublicFailure event) :
    choice ∉ (honestChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler source
      who
      (some (execution.recall who, execution.observe (application setup runtime leaks)
        who))).support := by
  intro supported
  obtain ⟨point, decoded, intended⟩ :=
    intended_of_clear_regular_notOwes (runtime := runtime) wellFormed source focal trace clear
      regular notOwed
  have forced : ForcedState setup runtime leaks who (some ⟨remaining, some who, execution⟩) :=
    (forcedState_iff_decodedPoint (runtime := runtime) _).mpr
      ⟨point, decoded, forcedPoint_of_intended who intended⟩
  have responderNotOwed : ∀ found, decodedPoint setup execution.application.config = some found →
      ¬ ProtocolState.OwesFailure who setup.program found := by
    intro found foundDecoded
    have same := Option.some.inj (decoded.symm.trans foundDecoded)
    subst found
    exact ProtocolState.Intended.not_owesFailure who setup.program point intended
  have turn := (pendingEvent_spec (runtime := runtime) pending).1
  obtain ⟨action, material, chosen, submits, bindSuccess⟩ :=
    honestChoice_canonical_of_debtFree (runtime := runtime) wellFormed covers capacity source
      trace who forced
      responderNotOwed event pending bound fits choice supported
  have sameResponse := Option.some.inj (selected.symm.trans chosen)
  subst response
  obtain ⟨output, witness, stored⟩ := canonical_firstResponse_result_of_settles (runtime := runtime)
    bounds horizon scheduler bound trace event turn fits action material submits after control
    target isPrefix next nextExecution settles
  have good : ¬ ((graph setup).outputLayout event).IsFailure output := by
    rcases witness with
      ⟨candidate, owner, payload, layoutEq, _call, _fixed, decision, outputValue⟩ |
      ⟨candidate, raw, owner, payload, binding, checks, outputEq, codeEq, result,
        _call, _node, resolved, _decision, outputValue⟩
    · have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) layoutEq)
          ((graph setup).nodes event) = .bind owner payload := by
        generalize cast (congrArg (EventGraph.EventCode (graph setup).layout) layoutEq)
          ((graph setup).nodes event) = lowered
        cases lowered
        rfl
      obtain ⟨value, succeeds⟩ := bindSuccess owner payload layoutEq codeEq
        (nodeView_eq_bind layoutEq codeEq)
      rw [decision] at succeeds
      have result : next.application.bindingResult candidate payload = .success value := by
        simpa only [cast_cast, cast_eq, Option.some.injEq] using succeeds
      rw [outputValue, isFailure_cast layoutEq.symm, result]
      exact fun impossible => by cases impossible
    · rw [outputValue, isFailure_cast outputEq.symm]
      cases result with
      | success value => exact fun impossible => by cases impossible
      | failure =>
          have ready := (execution.application.publicView_eventReady event).mp
            (PublicView.ownTurn?_spec _ who event turn).1
          exact (resolution_failure_of_intended_impossible trace outputEq codeEq ready decoded
            intended resolved).elim
  have outputStored := (stored failed.completed).1
  have facts := legalFacts setup leaks horizon scheduler control
    ((bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon scheduler target)
  have valid := facts.binding
  rw [nextExecution] at valid
  exact (OutputSucceeded.not_publicFailure ⟨output, outputStored, good⟩ valid) failed


end Vegas
