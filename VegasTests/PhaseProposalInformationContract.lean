/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalNativeSourceInformation

/-! # Complete native information determines every matched full source input -/

noncomputable section

namespace VegasTests

open Vegas Vegas.SourceProgram Vegas.EventGraph Vegas.EventGraphRuntime Interaction
  GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

example
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {runtime : EventGraphRuntime (serviceGraph setup mode)}
    {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode))}
    {bounds : MessageBounds (serviceGraph setup mode)}
    {plan : RuntimePhasePlan (serviceGraph setup mode)}
    {values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1)}
    {horizon : Nat} {scheduler : (phaseApplication runtime leaks).Scheduler}
    {leftControl rightControl : (phaseApplication runtime leaks).Control}
    {leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some leftControl)}
    {rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some rightControl)}
    {who : Player} {leftEvent rightEvent : (serviceGraph setup mode).EventId}
    {leftHistory rightHistory : setup.proposalRecoveryProtocol.History}
    (left : PhaseProposalNativeSourceMatch setup mode runtime leaks bounds plan values
      horizon scheduler leftControl leftTrace who leftEvent leftHistory)
    (right : PhaseProposalNativeSourceMatch setup mode runtime leaks bounds plan values
      horizon scheduler rightControl rightTrace who rightEvent rightHistory)
    (complete : leaks = MessageNetwork.completePendingObservation)
    (same : ((PhaseCount.onePacketMenu runtime leaks bounds).information
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon scheduler).infoOf who leftTrace =
      ((PhaseCount.onePacketMenu runtime leaks bounds).information
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon scheduler).infoOf who rightTrace) :
    setup.proposalRecoveryModel.infoOf who leftHistory.trace =
      setup.proposalRecoveryModel.infoOf who rightHistory.trace := by
  exact left.info_eq_of_information right complete same

end VegasTests
