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
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat}
  {recoveryScheduler : (runtime.recoveryApplication leaks).Scheduler}
  {bound : (graph setup).EventId → Nat}
  (inclusion : Recovery.ProtectedInclusion runtime leaks initial horizon recoveryScheduler
    bound)

local notation "scheduler" => RecoveryProjection.nativeScheduler runtime leaks
  recoveryScheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks) (fun state => ExclusionEvidence 0 ∅ (RecoveryState.mk
    state ∅))

include initialized nativeLaw inclusion in
/-- A protected fixed-value binding has exactly the source step law at its
actual completion boundary, stopped also at first public exclusion. The law
uses actual recovery service and arbitrary continuation policies. -/
theorem recovery_committed_stop_sourceLaw
    (completes : Recovery.CompletesPlay runtime leaks initial horizon recoveryScheduler)
    (certificate : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu runtime leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {who : Player} {entry : (application setup runtime leaks).PlayerEntry}
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
    (start : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control)
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (invariant : AcceptanceInvariant setup runtime leaks bounds horizon scheduler who entry
      message event
      sent (some control))
    (atSent : control.execution.application.config = sent)
    (fixed : control.execution.application.candidates.lookup candidate =
      .openable ⟨payload, value⟩)
    (owned : (graph setup).actor? event = some who)
    (fresh : FreshCall setup leaks who event bound entry message)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank sent = some point) :
    ((((bounds.onePacketMenu runtime leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (fun history => LateStopped setup runtime leaks bounds horizon scheduler rank history ∨
          ¬ Clear history.state) start).map
        (fun history => nativeDecodedState setup runtime leaks history.state)) =
      (ProtocolState.step setup.program point
        (fun _ => decodeEventAction setup.program event action)).map some := by
  exact counted_committed_stop_sourceLaw (runtime := runtime) (setup := setup) (leaks := leaks)
    (bounds := bounds)
    (outputEq := outputEq) (inclusion := Recovery.ProtectedInclusion.clear_counted_native (runtime
      := runtime) bounds
    initialized nativeLaw inclusion) (completes := Recovery.CompletesPlay.clear_counted_native
      (runtime := runtime)
    bounds initialized nativeLaw completes) certificate players ready ordered codeEq call action
    successful start current clear invariant atSent fixed owned fresh decoded


include initialized nativeLaw inclusion in
/-- A count-permitted fixed-value commitment at its actual clear first callback
has exactly the source step law from the resulting response history. Freshness,
the acceptance invariant and pending public clarity are derived from the packet
and the actual recovery opportunity and inclusion bounds. -/
theorem recovery_firstActivation_commitment_sourceLaw
    {delay : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity runtime leaks initial horizon recoveryScheduler
      delay)
    (timely : runtime.AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay runtime leaks initial horizon recoveryScheduler)
    (certificate : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu runtime leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {remaining : Nat} {who : Player} {execution : (application setup runtime leaks).Execution}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (clear : ExclusionEvidence 0 ∅ (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup runtime leaks who event entry)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (response : (application setup runtime leaks).Action)
    (member : response ∈ bounds.onePacketActions runtime leaks who
      (execution.recall who) (execution.observe (application setup runtime leaks) who))
    (material : (application setup runtime leaks).Submission)
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    {value : L.Val payload}
    (after : material.call.candidateAfter who
      (execution.observe (application setup runtime leaks) who).application.candidates
      (.prepared serial) = .openable ⟨payload, value⟩)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (start : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (current : start.state = some ⟨remaining, none,
      execution.respond (application setup runtime leaks) who response⟩) :
    ((((bounds.onePacketMenu runtime leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (fun history => LateStopped setup runtime leaks bounds horizon scheduler rank history ∨
          ¬ Clear history.state) start).map
        (fun history => nativeDecodedState setup runtime leaks history.state)) =
      (ProtocolState.step setup.program point
        (fun _ => sourceOfValue setup event outputEq value)).map some := by
  exact counted_firstActivation_commitment_sourceLaw (runtime := runtime) (setup := setup) (leaks
    := leaks) (bounds :=
    bounds) (outputEq := outputEq) (opportunity := Recovery.Opportunity.clear_counted_native
      (runtime := runtime)
    bounds initialized nativeLaw opportunity) (inclusion :=
    Recovery.ProtectedInclusion.clear_counted_native (runtime := runtime) bounds initialized
      nativeLaw inclusion)
    (timely := timely) (completes := Recovery.CompletesPlay.clear_counted_native (runtime :=
      runtime) bounds
    initialized nativeLaw completes) certificate players trace clear event turn never node
    response member material sends packet after ordered decoded start current

include initialized nativeLaw inclusion in
/-- A protected recorded opening has exactly its successful disclosure source
step law at the actual completion boundary. Only actual recovery inclusion and
completion are assumed, with arbitrary continuation policies. -/
theorem recovery_disclosed_stop_sourceLaw
    (completes : Recovery.CompletesPlay runtime leaks initial horizon recoveryScheduler)
    (certificate : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu runtime leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {who : Player} {entry : (application setup runtime leaks).PlayerEntry}
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
    (start : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control)
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (invariant : AcceptanceInvariant setup runtime leaks bounds horizon scheduler who entry
      message event
      sent (some control))
    (atSent : control.execution.application.config = sent)
    (owned : (graph setup).actor? event = some who)
    (fresh : FreshCall setup leaks who event bound entry message)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank sent = some point) :
    ((((bounds.onePacketMenu runtime leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (fun history => LateStopped setup runtime leaks bounds horizon scheduler rank history ∨
          ¬ Clear history.state) start).map
        (fun history => nativeDecodedState setup runtime leaks history.state)) =
      (ProtocolState.step setup.program point
        (fun _ => decodeEventAction setup.program event action)).map some := by
  exact counted_disclosed_stop_sourceLaw (runtime := runtime) (setup := setup) (leaks := leaks)
    (bounds := bounds)
    (outputEq := outputEq) (inclusion := Recovery.ProtectedInclusion.clear_counted_native (runtime
      := runtime) bounds
    initialized nativeLaw inclusion) (completes := Recovery.CompletesPlay.clear_counted_native
      (runtime := runtime)
    bounds initialized nativeLaw completes) certificate players ready ordered codeEq action
    disclosing start current clear invariant atSent owned fresh decoded


include initialized nativeLaw inclusion in
/-- A transmitting canonical disclosure at an actual clear first callback has
exactly its source step law from the resulting response history. Freshness and
acceptance follow from actual recovery opportunity and the canonical packet. -/
theorem recovery_firstActivation_disclosure_sourceLaw
    {delay : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity runtime leaks initial horizon recoveryScheduler
      delay)
    (timely : runtime.AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay runtime leaks initial horizon recoveryScheduler)
    (certificate : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu runtime leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {remaining : Nat} {who : Player} {execution : (application setup runtime leaks).Execution}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (clear : ExclusionEvidence 0 ∅ (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup runtime leaks who event entry)
    {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks}
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (action : (graph setup).Action event)
    (disclosing : (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) = true)
    (material : (application setup runtime leaks).Submission)
    (submits : (runtime.canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup runtime leaks) who) event action).transmission = some
        material)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (start : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (current : start.state = some ⟨remaining, none,
      execution.respond (application setup runtime leaks) who
      (runtime.canonicalServiceDecision leaks who (execution.recall who)
        (execution.observe (application setup runtime leaks) who) event action)⟩) :
    ((((bounds.onePacketMenu runtime leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (fun history => LateStopped setup runtime leaks bounds horizon scheduler rank history ∨
          ¬ Clear history.state) start).map
        (fun history => nativeDecodedState setup runtime leaks history.state)) =
      (ProtocolState.step setup.program point
        (fun _ => decodeEventAction setup.program event action)).map some := by
  exact counted_firstActivation_disclosure_sourceLaw (runtime := runtime) (setup := setup) (leaks
    := leaks) (bounds :=
    bounds) (outputEq := outputEq) (opportunity := Recovery.Opportunity.clear_counted_native
      (runtime := runtime)
    bounds initialized nativeLaw opportunity) (inclusion :=
    Recovery.ProtectedInclusion.clear_counted_native (runtime := runtime) bounds initialized
      nativeLaw inclusion)
    (timely := timely) (completes := Recovery.CompletesPlay.clear_counted_native (runtime :=
      runtime) bounds
    initialized nativeLaw completes) certificate players trace clear event turn never node action
    disclosing material submits ordered decoded start current

end Vegas
