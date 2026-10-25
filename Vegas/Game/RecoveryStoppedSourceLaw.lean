/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketStoppedSourceLaw
import Vegas.Game.RecoveryCountedService
import Vegas.Game.RecoveryStoppedCommitment
import Vegas.Game.RecoveryStoppedAcceptance
import Vegas.Game.RecoveryCommitmentFreshCall

/-! # Source-step laws at actual recovery event completion -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat}
  {recoveryScheduler : ((runtime setup).recoveryApplication leaks).Scheduler}
  {bound : (graph setup).EventId → Nat}
  (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks initial horizon recoveryScheduler
    bound)

local notation "scheduler" => RecoveryProjection.nativeScheduler (runtime setup) leaks
  recoveryScheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun state => ExclusionEvidence 0 ∅ (RecoveryState.mk state ∅))

include initialized nativeLaw inclusion in
/-- A protected fixed-value binding has exactly the source step law at its
actual completion boundary, stopped also at first public exclusion. The law
uses actual recovery service and arbitrary continuation policies. -/
theorem recovery_committed_stop_sourceLaw
    (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon recoveryScheduler)
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
  exact counted_committed_stop_sourceLaw (setup := setup) (leaks := leaks) (bounds := bounds)
    (outputEq := outputEq) (inclusion := Recovery.ProtectedInclusion.clear_counted_native bounds
    initialized nativeLaw inclusion) (completes := Recovery.CompletesPlay.clear_counted_native
    bounds initialized nativeLaw completes) certificate players ready ordered codeEq call action
    successful start current clear invariant atSent fixed owned fresh decoded


include initialized nativeLaw inclusion in
/-- A count-permitted fixed-value commitment at its actual clear first callback
has exactly the source step law from the resulting response history. Freshness,
the acceptance invariant and pending public clarity are derived from the packet
and the actual recovery opportunity and inclusion bounds. -/
theorem recovery_firstActivation_commitment_sourceLaw
    {delay : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon recoveryScheduler
      delay)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon recoveryScheduler)
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
  exact counted_firstActivation_commitment_sourceLaw (setup := setup) (leaks := leaks) (bounds :=
    bounds) (outputEq := outputEq) (opportunity := Recovery.Opportunity.clear_counted_native
    bounds initialized nativeLaw opportunity) (inclusion :=
    Recovery.ProtectedInclusion.clear_counted_native bounds initialized nativeLaw inclusion)
    (timely := timely) (completes := Recovery.CompletesPlay.clear_counted_native bounds
    initialized nativeLaw completes) certificate players trace clear event turn never node
    response member material sends packet after ordered decoded start current

include initialized nativeLaw inclusion in
/-- A protected recorded opening has exactly its successful disclosure source
step law at the actual completion boundary. Only actual recovery inclusion and
completion are assumed, with arbitrary continuation policies. -/
theorem recovery_disclosed_stop_sourceLaw
    (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon recoveryScheduler)
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
  exact counted_disclosed_stop_sourceLaw (setup := setup) (leaks := leaks) (bounds := bounds)
    (outputEq := outputEq) (inclusion := Recovery.ProtectedInclusion.clear_counted_native bounds
    initialized nativeLaw inclusion) (completes := Recovery.CompletesPlay.clear_counted_native
    bounds initialized nativeLaw completes) certificate players ready ordered codeEq action
    disclosing start current clear invariant atSent owned fresh decoded


include initialized nativeLaw inclusion in
/-- A transmitting canonical disclosure at an actual clear first callback has
exactly its source step law from the resulting response history. Freshness and
acceptance follow from actual recovery opportunity and the canonical packet. -/
theorem recovery_firstActivation_disclosure_sourceLaw
    {delay : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon recoveryScheduler
      delay)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon recoveryScheduler)
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
  exact counted_firstActivation_disclosure_sourceLaw (setup := setup) (leaks := leaks) (bounds :=
    bounds) (outputEq := outputEq) (opportunity := Recovery.Opportunity.clear_counted_native
    bounds initialized nativeLaw opportunity) (inclusion :=
    Recovery.ProtectedInclusion.clear_counted_native bounds initialized nativeLaw inclusion)
    (timely := timely) (completes := Recovery.CompletesPlay.clear_counted_native bounds
    initialized nativeLaw completes) certificate players trace clear event turn never node action
    disclosing material submits ordered decoded start current

end Vegas
