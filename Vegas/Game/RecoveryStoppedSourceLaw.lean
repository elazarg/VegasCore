/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryStoppedCommitment

/-! # Source-step laws at actual recovery binding completion -/

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
  (app := application setup leaks) (fun state => PublicExclusionRecord (RecoveryState.mk state ∅))

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
    (clear : PublicExclusionRecord
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
  obtain ⟨final, state, compiled, _succeeded⟩ := recovery_committed_stop_config
    initialized nativeLaw inclusion completes certificate players ready ordered
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

end Vegas
