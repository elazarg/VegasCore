/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketStoppedCommitment
import Vegas.Game.OnePacketStoppedAcceptance
import Vegas.Game.OnePacketCommitmentFreshCall

/-! # Source-step laws at counted native event completion -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
  {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
  {bound : (graph setup).EventId → Nat}
  (inclusion : ∀ control : (application setup leaks).Control,
    (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control) →
    ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
    ProtectedInclusionAt (runtime setup) leaks control.execution bound)

local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun state => ExclusionEvidence 0 ∅ (RecoveryState.mk state ∅))

include inclusion in
/-- A protected fixed-value binding has exactly the source step law at its
actual completion boundary, stopped also at first public exclusion. The law
uses counted native service and arbitrary continuation policies. -/
theorem counted_committed_stop_sourceLaw
    (completes : ∀ control : (application setup leaks).Control,
    (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control) →
    ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
    (application setup leaks).terminal (some control) →
    control.execution.application.config.cut.Terminal)
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {who : Player} {entry : (application setup leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {sent : (graph setup).Config} (ready : sent.cut.Ready event) {rank : Nat}
    (ordered : sent.cut.IsPrefix rank) {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    {candidate : Handle (graph setup)} (call : message.payload.call = .commitment event candidate)
    {value : L.Val payload} (action : (graph setup).Action event)
    (successful : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      PublicationResult (L.Val payload)) = .success value)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History) {control : (application setup leaks).Control}
    (current : start.state = some control)
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (invariant : AcceptanceInvariant setup leaks bounds horizon scheduler who entry message event
      sent (some control))
    (atSent : control.execution.application.config = sent)
    (fixed : control.execution.application.candidates.lookup candidate =
      .openable ⟨payload, value⟩)
    (owned : (graph setup).actor? event = some who)
    (fresh : FreshCall setup leaks who event bound entry message)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank sent = some point) :
    ((((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (fun history => LateStopped setup leaks bounds horizon scheduler rank history ∨
          ¬ Clear history.state) start).map
        (fun history => nativeDecodedState setup leaks history.state)) =
      (ProtocolState.step setup.program point
        (fun _ => decodeEventAction setup.program event action)).map some := by
  classical
  let menu := bounds.onePacketMenu (runtime setup) leaks
  obtain ⟨found, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program) menu
    horizon scheduler (current ▸ start.trace) control rfl
  rw [atSent] at residual
  have sameRank := isPrefix_unique residual.checkpoint.ordered ordered
  subst sameRank
  have beforeDecoded : decodedPoint setup sent = some point :=
    (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have acts := (decodedPoint_actor who ready beforeDecoded).trans owned
  obtain ⟨target, stepEq⟩ := ProtocolState.step_eq_pure_of_actor who who setup.program point
    (fun _ => decodeEventAction setup.program event action) acts
  rw [stepEq, PMF.pure_map]
  refine (map_congr_on_support _ (g := fun _ => some target) ?_).trans (PMF.map_const _ _)
  intro stopped supported
  obtain ⟨final, state, compiled, _succeeded⟩ := counted_committed_stop_config
    inclusion completes certificate players ready ordered
    (outputEq := outputEq) codeEq call action successful start current clear invariant atSent
    fixed owned fresh stopped supported
  obtain ⟨before, after, decodedBefore, decodedAfter, reached⟩ :=
    decodedPoint_step residual event ready action _ compiled
  rw [beforeDecoded] at decodedBefore
  cases Option.some.inj decodedBefore
  rw [stepEq, PMF.mem_support_pure_iff] at reached
  subst reached
  rw [state]
  exact decodedAfter


include inclusion in
/-- A count-permitted fixed-value commitment at its actual clear first callback
has exactly the source step law from the resulting response history. Freshness,
the acceptance invariant and pending public clarity are derived from the packet
and the counted native opportunity and inclusion bounds. -/
theorem counted_firstActivation_commitment_sourceLaw
    {delay : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup leaks).Control,
    (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control) →
    ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
    OpportunityAt (runtime setup) leaks control.execution delay)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : ∀ control : (application setup leaks).Control,
    (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control) →
    ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
    (application setup leaks).terminal (some control) →
    control.execution.application.config.cut.Terminal)
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (clear : ExclusionEvidence 0 ∅ (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (response : (application setup leaks).Action)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who
      (execution.recall who) (execution.observe (application setup leaks) who))
    (material : (application setup leaks).Submission)
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    {value : L.Val payload}
    (after : material.call.candidateAfter who
      (execution.observe (application setup leaks) who).application.candidates
      (.prepared serial) = .openable ⟨payload, value⟩)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (current : start.state = some ⟨remaining, none,
      execution.respond (application setup leaks) who response⟩) :
    ((((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (fun history => LateStopped setup leaks bounds horizon scheduler rank history ∨
          ¬ Clear history.state) start).map
        (fun history => nativeDecodedState setup leaks history.state)) =
      (ProtocolState.step setup.program point
        (fun _ => sourceOfValue setup event outputEq value)).map some := by
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have fresh := counted_commitment_freshCall opportunity timely trace
    clear event turn never node response member material sends packet
  obtain ⟨invariant, fixed⟩ := acceptanceInvariant_respond_commitment trace event turn outputEq
    response member material sends packet after (current ▸ start.trace)
  have callEq : (sentEnvelope setup leaks execution who material).payload.call =
      .commitment event (who, .prepared serial) := by
    have evidenceNone := (onePacket_commitment_fresh trace who response member material sends
      packet).2
    rcases material with ⟨call, evidence⟩
    change evidence = .none at evidenceNone
    subst evidenceNone
    unfold sentEnvelope
    rw [reactiveApplication_packet_none]
    exact packet
  have clearAfter : ExclusionEvidence 0 ∅
      (⟨(execution.respond (application setup leaks) who response).application, ∅⟩ :
        RecoveryState (graph setup)) := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => exact clear
    | some submission => exact clear.submit who submission
  let action : (graph setup).Action event :=
    cast (congrArg EventGraph.EventField.Action outputEq.symm)
      (PublicationResult.success value : PublicationResult (L.Val payload))
  have successful : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      PublicationResult (L.Val payload)) = .success value := by
    simp only [action, cast_cast, cast_eq]
  exact counted_committed_stop_sourceLaw inclusion completes certificate
    players ready ordered (outputEq := outputEq) codeEq callEq action successful start current
    clearAfter invariant ((runtime setup).reactive_respond_application leaks execution who _).1
    fixed owned fresh decoded

include inclusion in
/-- A protected recorded opening has exactly its successful disclosure source
step law at the actual completion boundary. Only counted native inclusion and
completion are assumed, with arbitrary continuation policies. -/
theorem counted_disclosed_stop_sourceLaw
    (completes : ∀ control : (application setup leaks).Control,
    (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control) →
    ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
    (application setup leaks).terminal (some control) →
    control.execution.application.config.cut.Terminal)
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {who : Player} {entry : (application setup leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {sent : (graph setup).Config} (ready : sent.cut.Ready event) {rank : Nat}
    (ordered : sent.cut.IsPrefix rank) {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (action : (graph setup).Action event)
    (disclosing : (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) = true)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History) {control : (application setup leaks).Control}
    (current : start.state = some control)
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (invariant : AcceptanceInvariant setup leaks bounds horizon scheduler who entry message event
      sent (some control))
    (atSent : control.execution.application.config = sent)
    (owned : (graph setup).actor? event = some who)
    (fresh : FreshCall setup leaks who event bound entry message)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank sent = some point) :
    ((((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (fun history => LateStopped setup leaks bounds horizon scheduler rank history ∨
          ¬ Clear history.state) start).map
        (fun history => nativeDecodedState setup leaks history.state)) =
      (ProtocolState.step setup.program point
        (fun _ => decodeEventAction setup.program event action)).map some := by
  classical
  let menu := bounds.onePacketMenu (runtime setup) leaks
  obtain ⟨found, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program) menu
    horizon scheduler (current ▸ start.trace) control rfl
  rw [atSent] at residual
  have sameRank := isPrefix_unique residual.checkpoint.ordered ordered
  subst sameRank
  have beforeDecoded : decodedPoint setup sent = some point :=
    (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have acts := (decodedPoint_actor who ready beforeDecoded).trans owned
  obtain ⟨target, stepEq⟩ := ProtocolState.step_eq_pure_of_actor who who setup.program point
    (fun _ => decodeEventAction setup.program event action) acts
  rw [stepEq, PMF.pure_map]
  refine (map_congr_on_support _ (g := fun _ => some target) ?_).trans (PMF.map_const _ _)
  intro stopped supported
  obtain ⟨final, completedAction, state, compiled, succeeded⟩ := counted_accepted_stop_config
    inclusion completes certificate players ready ordered start current
    clear invariant atSent owned fresh stopped supported
  have completedDiscloses := disclose_of_outputSucceeded (outputEq := outputEq) codeEq
    compiled succeeded
  have sameAction : completedAction = action :=
    (cast_inj _).mp (completedDiscloses.trans disclosing.symm)
  rw [sameAction] at compiled
  obtain ⟨before, after, decodedBefore, decodedAfter, reached⟩ :=
    decodedPoint_step residual event ready action _ compiled
  rw [beforeDecoded] at decodedBefore
  cases Option.some.inj decodedBefore
  rw [stepEq, PMF.mem_support_pure_iff] at reached
  subst reached
  rw [state]
  exact decodedAfter


include inclusion in
/-- A transmitting canonical disclosure at an actual clear first callback has
exactly its source step law from the resulting response history. Freshness and
acceptance follow from counted native opportunity and the canonical packet. -/
theorem counted_firstActivation_disclosure_sourceLaw
    {delay : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup leaks).Control,
    (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control) →
    ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
    OpportunityAt (runtime setup) leaks control.execution delay)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : ∀ control : (application setup leaks).Control,
    (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control) →
    ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
    (application setup leaks).terminal (some control) →
    control.execution.application.config.cut.Terminal)
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (clear : ExclusionEvidence 0 ∅ (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks}
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (action : (graph setup).Action event)
    (disclosing : (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) = true)
    (material : (application setup leaks).Submission)
    (submits : ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event action).transmission = some material)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (current : start.state = some ⟨remaining, none,
      execution.respond (application setup leaks) who
      ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
        (execution.observe (application setup leaks) who) event action)⟩) :
    ((((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (fun history => LateStopped setup leaks bounds horizon scheduler rank history ∨
          ¬ Clear history.state) start).map
        (fun history => nativeDecodedState setup leaks history.state)) =
      (ProtocolState.step setup.program point
        (fun _ => decodeEventAction setup.program event action)).map some := by
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have rawTrace := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
    horizon scheduler trace
  have fits := firstActivation_inclusionFits_of_counted_opportunity setup leaks bounds
    horizon scheduler
    delay bound opportunity timely trace rfl clear event turn never
  have fresh : FreshCall setup leaks who event bound
      (respondEntry setup leaks execution who ((runtime setup).canonicalServiceDecision leaks who
        (execution.recall who) (execution.observe (application setup leaks) who) event action))
      (sentEnvelope setup leaks execution who material) := by
    rw [respondEntry_of_transmission execution who _ material submits]
    exact canonical_freshCall rawTrace bound who event turn fits action material submits
  have bindSuccess : ∀ owner payload' outputEq' codeEq',
      nodeView (graph setup) event = .bind owner payload' outputEq' codeEq' →
        ∃ value', (cast (congrArg EventGraph.EventField.Action outputEq') action :
          PublicationResult (L.Val payload')) = .success value' := by
    intro owner payload' outputEq' codeEq' other
    rw [node] at other
    cases other
  have invariant := acceptanceInvariant_respond bounds horizon scheduler trace event turn action
    material submits bindSuccess (current ▸ start.trace)
  have responseClear : ∀ response : (application setup leaks).Action,
      ExclusionEvidence 0 ∅
        (⟨(execution.respond (application setup leaks) who response).application,
        ∅⟩ : RecoveryState (graph setup)) := by
    intro response
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => exact clear
    | some submission => exact clear.submit who submission
  exact counted_disclosed_stop_sourceLaw inclusion completes certificate
    players ready ordered (outputEq := outputEq) codeEq action disclosing start current
    (responseClear _) invariant
    ((runtime setup).reactive_respond_application leaks execution who _).1 owned fresh decoded

end Vegas
