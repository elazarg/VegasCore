/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateSuccess
import Vegas.Game.RevealServiceRosterContinuation

/-! # Terminal source prefixes under arbitrary native continuations -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem terminalPrefix_transition {initial : PMF (application setup leaks).State}
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    (control : (application setup leaks).Control)
    (ordered : control.execution.application.config.cut.IsPrefix (graph setup).order.eventCount)
    (joint : Player → Option (application setup leaks).Action)
    {after : (application setup leaks).ProtocolState}
    (reached : after ∈ ((application setup leaks).transition initial horizon scheduler
      (some control) joint).support) :
    ∃ next : (application setup leaks).Control, after = some next ∧
      next.execution.application.config = control.execution.application.config := by
  let app := application setup leaks
  rcases control with ⟨remaining, actor, execution⟩
  cases actor with
  | some who =>
      change after ∈ (PMF.pure _).support at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨_, rfl, ((runtime setup).reactive_respond_application leaks execution who _).1⟩
  | none =>
      cases remaining with
      | zero =>
          change after ∈ (PMF.pure _).support at reached
          cases (PMF.mem_support_pure_iff _ _).mp reached
          exact ⟨_, rfl, rfl⟩
      | succ remaining =>
          obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          obtain ⟨next, stepped, rfl⟩ := PMF.support_map .. ▸ moved
          refine ⟨_, rfl, ?_⟩
          rcases environmentStep_configStep setup leaks execution next command stepped with
            same | ⟨event, ready, action, _member⟩
          · exact same
          · exact (ready.1 ((ordered.2 event).mpr event.isLt)).elim

/-- Once every source event has completed, any finite native continuation has
the exact source continuation readout law. No service hypothesis is required. -/
theorem terminalPrefix_readout_law [Fintype Player] (bounds : MessageBounds (graph setup))
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ who,
      (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    (control : (application setup leaks).Control) (state : start.state = some control)
    (ordered : control.execution.application.config.cut.IsPrefix (graph setup).order.eventCount)
    (profile : BehavioralProfile setup.program) :
    ((InformationModel.runBehavioralTerminalFrom
      (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler)
      certificate players start).map
        (fun final => sourceReadout setup leaks final.state)) =
      sourceContinuation setup profile (graph setup).order.eventCount
        control.execution.application.config := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
  let closed := fun endpoint : (application setup leaks).ProtocolState =>
    ∃ current : (application setup leaks).Control, endpoint = some current ∧
      current.execution.application.config = control.execution.application.config
  have preserved := model.runBehavioralTerminalFrom_support_closed certificate players closed
    (fun before joint _legal after holds member => by
      obtain ⟨current, rfl, same⟩ := holds
      obtain ⟨next, nextState, nextConfig⟩ := terminalPrefix_transition
        (initial := initialLaw setup) (horizon := horizon) (scheduler := scheduler) current
        (same.symm ▸ ordered) joint member
      exact ⟨next, nextState, nextConfig.trans same⟩)
    start ⟨control, state, rfl⟩
  have readout : ((model.runBehavioralTerminalFrom certificate players start).map
        (fun final => sourceReadout setup leaks final.state)) =
      PMF.pure (sourceReadout setup leaks (some control)) := by
    refine (map_congr_on_support _ (g := fun _ => sourceReadout setup leaks (some control))
      (fun final supported => ?_)).trans (PMF.map_const _ _)
    obtain ⟨current, currentState, same⟩ := preserved final supported
    rw [currentState, sourceReadout_eq_decode, sourceReadout_eq_decode, same]
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual profile menu horizon scheduler start.trace
    control state
  have rankEq : rank = (graph setup).order.eventCount :=
    isPrefix_unique residual.checkpoint.ordered ordered
  subst rank
  have decoded := residual.decode
  have stopped := decodeSourcePrefix?_terminal setup.program _ _ _ _ _ _ _ decoded
  simp only [sourceServicePrefix?] at decoded
  have terminalReadout := sourceServicePrefix?_terminal_readout setup
    control.execution.application.config
  rw [readout]
  unfold sourceContinuation
  rw [Setup.continuationLaw_terminal setup profile _ (by rw [decoded]; exact stopped)]
  change PMF.pure (sourceReadout setup leaks (some control)) =
    PMF.pure (setup.protocolReadout (sourceServicePrefix? setup
      (eventCount setup.program) control.execution.application.config))
  rw [terminalReadout]
  exact congrArg PMF.pure (sourceReadout_eq_decode setup leaks control)

end Vegas
