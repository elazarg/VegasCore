/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketOwnerKeyed
import Vegas.Game.OnePacketOwnerInfoSite

/-! # Agreeing base laws at two late sites with one key

At two late-delivery sites of `who` with the same late-delivery key, at neither
of which `who` owes a failure, the owner swap between their views sends the
first site's information state to the second's (`Vegas.ownerSwap_info`), so in
a well-formed setup with independent hidden initial cells their base laws agree
on every payoff of the operational record (`Vegas.ownerSwap_baseLawAgrees_late`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **Agreeing base laws at two late sites with one key.** -/
theorem ownerSwap_baseLawAgrees_late
    [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependent)
    (covers : bounds.CoversInputValues)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (weight : List (Option (OperationalState setup leaks)) → ℝ) {who : Player}
    {site₁ site₂ : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who}
    {past₁ past₂ : List (application setup leaks).PlayerEntry}
    {view₁ view₂ : (application setup leaks).PlayerView}
    (firstSite : site₁.1 = some (past₁, view₁)) (secondSite : site₂.1 = some (past₂, view₂))
    (sameKey : lateKey setup leaks who site₁.1 = lateKey setup leaks who site₂.1)
    (firstDebtFree : ∀ history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who site₁.1, ∀ point,
      nativeDecodedState setup leaks history.1.state = some point →
        ¬ ProtocolState.OwesFailure who setup.program point)
    (secondDebtFree : ∀ history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who site₂.1, ∀ point,
      nativeDecodedState setup leaks history.1.state = some point →
        ¬ ProtocolState.OwesFailure who setup.program point)
    (firstLate : LateDelivery setup leaks who site₁.1)
    (secondLate : LateDelivery setup leaks who site₂.1)
    (payoff : List (Option (OperationalState setup leaks)) → ℝ) :
    BaseLawAgrees
      (fun history => othersSourceWeight setup leaks bounds horizon scheduler assessment who
        history.trace * weight (operationalRecord setup leaks bounds horizon scheduler
          history.trace))
      (fun history => RegularTrace setup leaks bounds horizon scheduler assessment who
        history.trace) site₁ site₂ payoff :=
  ownerSwap_baseLawAgrees wellFormed independent covers assessment weight
    firstSite secondSite sameKey firstDebtFree secondDebtFree
    (ownerSwap_info firstSite secondSite sameKey firstDebtFree secondDebtFree firstLate
      secondLate) payoff

end Vegas
