/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateSuccess
import Vegas.Game.SourceTerminalReadout
import Vegas.Game.RevealServicePayoffs

/-! # Terminal source prefixes under arbitrary native continuations -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Once every source event has completed, any finite native continuation has
the exact source continuation readout law. No service hypothesis is required. -/
theorem terminalPrefix_readout_law [Fintype Player] (bounds : MessageBounds (graph setup))
    {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler}
    (certificate : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ who,
      (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
        scheduler).BehavioralPolicy who)
    (start : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    (control : (application setup runtime leaks).Control) (state : start.state = some control)
    (ordered : control.execution.application.config.cut.IsPrefix (graph setup).order.eventCount)
    (profile : BehavioralProfile setup.program) :
    ((InformationModel.runBehavioralTerminalFrom
      (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler)
      certificate players start).map
        (fun final => sourceReadout setup runtime leaks final.state)) =
      sourceContinuation setup profile (graph setup).order.eventCount
        control.execution.application.config := by
  let menu := bounds.onePacketMenu runtime leaks
  let model := onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
  let closed := fun endpoint : (application setup runtime leaks).ProtocolState =>
    ∃ current : (application setup runtime leaks).Control, endpoint = some current ∧
      current.execution.application.config = control.execution.application.config
  have preserved := model.runBehavioralTerminalFrom_support_closed certificate players closed
    (fun before joint _legal after holds member => by
      obtain ⟨current, rfl, same⟩ := holds
      have terminal : current.execution.application.config.cut.Terminal := by
        apply Finset.eq_univ_of_forall
        intro event
        exact (((same.symm ▸ ordered).2 event).mpr event.isLt)
      obtain ⟨next, nextState, nextConfig⟩ := sourceTerminal_transition (runtime := runtime) current
        (initial := initialLaw setup) (horizon := horizon) (scheduler := scheduler)
        terminal joint member
      exact ⟨next, nextState, nextConfig.trans same⟩)
    start ⟨control, state, rfl⟩
  have readout : ((model.runBehavioralTerminalFrom certificate players start).map
        (fun final => sourceReadout setup runtime leaks final.state)) =
      PMF.pure (sourceReadout setup runtime leaks (some control)) := by
    refine (map_congr_on_support _ (g := fun _ => sourceReadout setup runtime leaks (some control))
      (fun final supported => ?_)).trans (PMF.map_const _ _)
    obtain ⟨current, currentState, same⟩ := preserved final supported
    rw [currentState, sourceReadout, serviceSourceReadout_eq_decode,
      serviceSourceReadout_eq_decode, same]
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (runtime := runtime) profile menu horizon
    scheduler start.trace
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
  change PMF.pure (sourceReadout setup runtime leaks (some control)) =
    PMF.pure (setup.protocolReadout (sourceServicePrefix? setup
      (eventCount setup.program) control.execution.application.config))
  rw [terminalReadout]
  exact congrArg PMF.pure (serviceSourceReadout_eq_decode setup leaks control)

end Vegas
