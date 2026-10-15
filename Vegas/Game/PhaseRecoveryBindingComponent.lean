/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseEventSourceView
import Vegas.Game.CommitRecoveryRestriction
import Vegas.Pending.PhasePreparedOnePacket
import Vegas.Compile.EventGraphBacktranslation

/-! # Actual phased binding components of source recovery assessments

The original source assessment is evaluated at the retained information of the
decoded source view. Accepted unusable bindings emit an actual packet, whereas
the distinct source omission flag emits silence. No source history, posterior
identity or future physical service law is assumed here.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))

/-- Decode the addressed source result and its separate physical omission
flag. Ill-addressed actions are totalized, never used by the legality theorem. -/
def phaseRecoveryBindingData (event : (serviceGraph setup mode).EventId)
    (owner : Player) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (move : Option (CommitRecoveryMove Player L)) : PublicationResult (L.Val payload) × Bool :=
  if move.elim false (·.missing) then (.failure, true) else
    (((move.bind fun action => encodeEventAction? setup.program event action.action).map
      (cast (congrArg EventField.Action outputEq))).getD .failure, false)

/-- Source binding omission waits. A received failed typed binding still emits
its fresh handle, so it is not silently converted into a public omission. -/
def phaseRecoveryBindingResponse (who : Player) (event : (serviceGraph setup mode).EventId)
    (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (serial : Nat) (move : Option (CommitRecoveryMove Player L)) :
    (phaseApplication runtime leaks).Action :=
  let data := phaseRecoveryBindingData setup mode event who payload outputEq move
  if data.2 then ⟨none⟩ else phaseBindingResponse runtime leaks who event payload data.1 serial

/-- One genuine response realizes the original typed result and omission flag
jointly in its actual catalogue and actual transmission decision. -/
theorem phaseRecoveryBindingResponse_result
    (execution : (phaseApplication runtime leaks).Execution) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (serial : Nat)
    (fresh : execution.application.current.native.candidates.lookup (who, .prepared serial) =
      .fresh) (move : Option (CommitRecoveryMove Player L)) :
    let response := phaseRecoveryBindingResponse setup mode runtime leaks who event payload
      outputEq serial move
    let after := execution.respond (phaseApplication runtime leaks) who response
    (after.application.current.native.bindingResult (who, .prepared serial) payload,
      response.transmission.isNone) =
      phaseRecoveryBindingData setup mode event who payload outputEq move := by
  cases move with
  | none =>
      change (_, false) = (_, false)
      exact congrArg (fun result => (result, false))
        (phaseBindingResponse_result runtime leaks execution who event payload .failure
          serial fresh)
  | some move =>
      cases missing : move.missing with
      | false =>
          simp only [phaseRecoveryBindingResponse, phaseRecoveryBindingData, Option.elim_some,
            missing, Bool.false_eq_true, ↓reduceIte]
          exact congrArg (fun result => (result, false))
            (phaseBindingResponse_result runtime leaks execution who event payload _ serial fresh)
      | true =>
          simp only [phaseRecoveryBindingResponse, phaseRecoveryBindingData, Option.elim_some,
            missing, ↓reduceIte]
          change (execution.application.current.native.bindingResult
            (who, .prepared serial) payload, true) = _
          simp only [State.bindingResult, fresh]

/-- Legal auxiliary source choices retain their original declared result and
omission flag, including the distinction between unusable and missing bindings. -/
theorem phaseRecoveryBindingData_faithful
    (wellFormed : setup.WellFormed) (execution : (phaseApplication runtime leaks).Execution)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (view : SourceProgram.ProtocolView who setup.program)
    (decoded : phaseSourceView? setup mode runtime leaks who event
      (execution.observe (phaseApplication runtime leaks) who) = some view)
    (acting : (serviceGraph setup mode).actor? event = some who)
    (choice : setup.commitRecoveryModel.Choice who
      (setup.commitRecoveryInformation wellFormed who (some view))) :
    ∃ move action, choice.1 = some move ∧
      decodeEventAction setup.program event action = some move.action ∧
      phaseRecoveryBindingData setup mode event who payload outputEq choice.1 =
        (cast (congrArg EventField.Action outputEq) action, move.missing) := by
  have actor := (phaseSourceView?_actor setup mode runtime leaks execution who event view
    decoded).trans acting
  have active : setup.commitRecoveryActive who
      (setup.commitRecoveryRetainedInfo wellFormed who (some view)).1 := by
    unfold Setup.commitRecoveryActive
    rw [setup.commitRecoveryRetainedInfo_current, setup.commitRecoveryRetainedInfo_excluded]
    exact ⟨actor, Finset.notMem_empty _⟩
  cases value : choice.1 with
  | none =>
      have inactive := choice.2
      rw [value] at inactive
      exact (inactive active).elim
  | some move =>
      have available := choice.2
      rw [value] at available
      have offered : move ∈
          SourceProgram.ProtocolView.recoveryAvailable who setup.program view := by
        have offeredHere := available.2
        change (setup.commitRecoveryRetainedInfo wellFormed who (some view)).1.1.elim False _
          at offeredHere
        rw [setup.commitRecoveryRetainedInfo_current] at offeredHere
        exact offeredHere
      obtain ⟨action, sent⟩ := phaseSourceView?_available setup mode runtime leaks execution who
        event view decoded move.action offered.1
      refine ⟨move, action, rfl, sent, ?_⟩
      have encoded := encodeEventAction?_decodeEventAction_eq_some setup.program event action
        move.action sent
      cases missing : move.missing with
      | false =>
          simp only [phaseRecoveryBindingData, Option.elim_some, missing,
            Bool.false_eq_true, ↓reduceIte, Option.bind_some, encoded, Option.map_some,
            Option.getD_some]
      | true =>
          have atCommit := phaseSourceView?_atCommit setup mode runtime leaks execution who event
            view decoded who payload outputEq
          have failed := offered.2
          rw [ite_eq_left atCommit] at failed
          have result := decodeEventAction_failure_of_binding setup.program event who payload
            outputEq action move.action sent (failed missing)
          simp only [phaseRecoveryBindingData, Option.elim_some, missing, ↓reduceIte, result]

/-- Evaluate the actual auxiliary source assessment at one retained source
input and encode its whole choice law as physical binding responses. -/
def phaseRecoveryBindingLaw (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (serial : Nat) (view : setup.ProtocolView who) : PMF (phaseApplication runtime leaks).Action :=
  (assessment.strategy who (setup.commitRecoveryInformation wellFormed who view)).map fun choice =>
    phaseRecoveryBindingResponse setup mode runtime leaks who event payload outputEq serial choice.1

section FiniteMenu

variable [Fintype Player] (bounds : MessageBounds (serviceGraph setup mode))

open Classical in
/-- A globally legal actual policy evaluates the source recovery assessment
at the decoded retained information and waits outside its physical menu guard. -/
def phaseRecoveryBindingPolicy (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload) :
    (phaseApplication runtime leaks).Policy := fun past view =>
  match reactiveFreshSlot view.application.1 with
  | none => PMF.pure ⟨none⟩
  | some serial =>
      if ∀ move, phaseRecoveryBindingResponse setup mode runtime leaks who event payload outputEq
          serial move ∈ PhaseCount.onePacketActions runtime leaks bounds who past view then
        phaseRecoveryBindingLaw setup mode runtime leaks wellFormed assessment who event payload
          outputEq serial (phaseSourceView? setup mode runtime leaks who event view)
      else PMF.pure ⟨none⟩

/-- Every globally defined physical input receives a legal one-packet law. -/
theorem phaseRecoveryBindingPolicy_covered (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (phaseRecoveryBindingPolicy setup mode runtime leaks bounds wellFormed
      assessment who event payload outputEq past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  classical
  unfold phaseRecoveryBindingPolicy at supported
  split at supported
  · cases (PMF.mem_support_pure_iff _ _).mp supported
    exact PhaseCount.silence_onePacket runtime leaks bounds who past view
  · split at supported
    · rename_i serial _ covered
      dsimp only [phaseRecoveryBindingLaw] at supported
      obtain ⟨choice, _supported, rfl⟩ := PMF.support_map .. ▸ supported
      exact covered choice.1
    · cases (PMF.mem_support_pure_iff _ _).mp supported
      exact PhaseCount.silence_onePacket runtime leaks bounds who past view

/-- A genuine unsent ready callback realizes the actual auxiliary source
choice law at the decoded retained source information. Both declared result
and physical omission flag are preserved jointly by this concrete response.
Future inclusion, expiry and repeated activation are not identified here. -/
theorem phaseRecoveryBindingPolicy_of_history
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount)
    (control : (phaseApplication runtime leaks).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control)) (acting : control.actor = some who)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    ∃ view serial,
      phaseSourceView? setup mode runtime leaks who event
        (control.execution.observe (phaseApplication runtime leaks) who) = some view ∧
      serial < horizon ∧
      let source := assessment.strategy who
        (setup.commitRecoveryInformation wellFormed who (some view))
      let actual := phaseRecoveryBindingPolicy setup mode runtime leaks bounds wellFormed
        assessment who event payload outputEq (control.execution.recall who)
          (control.execution.observe (phaseApplication runtime leaks) who)
      actual = source.map (fun choice => phaseRecoveryBindingResponse setup mode runtime leaks
        who event payload outputEq serial choice.1) ∧
      actual.map (fun response =>
        let after := control.execution.respond (phaseApplication runtime leaks) who response
        (after.application.current.native.bindingResult (who, .prepared serial) payload,
          response.transmission.isNone)) =
        source.map (fun choice =>
          phaseRecoveryBindingData setup mode event who payload outputEq choice.1) := by
  classical
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have raw := menu.toRawTrace initial horizon scheduler trace
  obtain ⟨serial, bounded, selected⟩ := PhaseCandidates.reactiveFreshSlot_lt_horizon runtime leaks
    plan inputs horizon scheduler control raw who acting
  have fresh := reactiveFreshSlot_spec _ serial selected
  have fixed := phaseOwnCommitmentsFixed_history runtime leaks initial horizon scheduler raw
  have recalled := PhaseCount.countRecall_history runtime leaks raw
  have allowed (result : PublicationResult (L.Val payload)) :
      phaseBindingResponse runtime leaks who event payload result serial ∈
        PhaseCount.onePacketActions runtime leaks bounds who (control.execution.recall who)
          (control.execution.observe (phaseApplication runtime leaks) who) := by
    rw [PhaseCount.mem_onePacketActions]
    exact ⟨phaseBindingResponse_available runtime leaks bounds who _ _ event payload values
      result serial (bounded.trans_le capacity), Or.inr
        (PhaseCount.phaseBindingResponse_permitted runtime leaks control.execution recalled fixed
          who event payload outputEq request unsent result serial fresh)⟩
  have covered (move : Option (CommitRecoveryMove Player L)) :
      phaseRecoveryBindingResponse setup mode runtime leaks who event payload outputEq serial move ∈
        PhaseCount.onePacketActions runtime leaks bounds who (control.execution.recall who)
          (control.execution.observe (phaseApplication runtime leaks) who) := by
    dsimp only [phaseRecoveryBindingResponse]
    split
    · exact PhaseCount.silence_onePacket runtime leaks bounds who _ _
    · exact allowed _
  obtain ⟨view, decoded⟩ := phaseSourceView?_succeeds setup mode runtime leaks control.execution who
    event request.2.2.1 request.2.2.2.1
      (by rw [outputEq]; simp only [EventField.IsPublication, not_false_eq_true])
  refine ⟨view, serial, decoded, bounded, ?_, ?_⟩
  · unfold phaseRecoveryBindingPolicy
    simp only [selected, ite_eq_left covered]
    exact congrArg (phaseRecoveryBindingLaw setup mode runtime leaks wellFormed assessment who
      event payload outputEq serial) decoded
  · have law : phaseRecoveryBindingPolicy setup mode runtime leaks bounds wellFormed assessment
        who event payload outputEq (control.execution.recall who)
          (control.execution.observe (phaseApplication runtime leaks) who) =
      (assessment.strategy who (setup.commitRecoveryInformation wellFormed who (some view))).map
        (fun choice => phaseRecoveryBindingResponse setup mode runtime leaks who event payload
          outputEq serial choice.1) := by
      unfold phaseRecoveryBindingPolicy
      simp only [selected, ite_eq_left covered]
      exact congrArg (phaseRecoveryBindingLaw setup mode runtime leaks wellFormed assessment who
        event payload outputEq serial) decoded
    rw [law, PMF.map_comp]
    apply congrArg (fun f =>
      (assessment.strategy who (setup.commitRecoveryInformation wellFormed who (some view))).map f)
    funext choice
    exact phaseRecoveryBindingResponse_result setup mode runtime leaks control.execution who
      event payload outputEq serial fresh choice.1

end FiniteMenu
end Vegas
