/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCommitmentFreshCall
import Vegas.Game.RecoveryCountedService
import Vegas.Game.OnePacketCommitmentCompletion
import Vegas.Game.RecoveryFirstActivation

/-! # Fresh commitment calls under actual recovery opportunity -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol Interaction EventGraphRuntime
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}

/-- Every count-permitted commitment at an actual clear first activation is a
fresh protected call under the recovery opportunity and timeliness bounds. -/
theorem recovery_commitment_freshCall
    {initial : PMF (RecoveryState (graph setup))}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
    (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
    {horizon : Nat} {scheduler : ((runtime setup).recoveryApplication leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon scheduler delay)
    (timely : (runtime setup).AsyncTimely delay bound)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace
      (some ⟨remaining, some who, execution⟩))
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
    (packet : material.call.packet = .commitment event (who, .prepared serial)) :
    FreshCall setup leaks who event bound (respondEntry setup leaks execution who response)
      (sentEnvelope setup leaks execution who material) := by
  exact counted_commitment_freshCall (setup := setup) (leaks := leaks) (bounds := bounds)
    (outputEq := outputEq) (opportunity := Recovery.Opportunity.clear_counted_native bounds
    initialized nativeLaw opportunity) (timely := timely) trace clear event turn never node
    response member material sends packet

end Vegas
