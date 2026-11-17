module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketPrescribedSupport
public import Vegas.Game.OnePacketPublicInitialSignal

@[expose] public section

/-! # Initial priors and repeated opportunities to submit -/

namespace Vegas

open SourceProgram Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (timeouts : EventTimeouts setup.informationGraph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
  (bounds : MessageBounds setup.informationGraph) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)

/-- At a legal one-packet decision, an owner who has already passed up a ready
event has no further opportunity to submit for it. -/
def SingleSubmissionOpportunity : Prop :=
  ∀ who (site : (onePacketInformation setup timeouts leaks bounds horizon scheduler).InformationSite
    who), ¬ LateDelivery setup timeouts leaks who site.1

/-- Publicly conditioned independence accommodates repeated opportunities.
With at most two players, a single opportunity permits arbitrary private priors. -/
inductive SequentialPriorCondition : Prop where
  | independent {Public : Type} (signal : State L setup.context → Public)
      (prior : setup.PrivateInputsIndependentGiven signal)
      (observable : setup.PublicInitialSignal signal)
  | singleOpportunity (players : Fintype.card Player ≤ 2)
      (once : SingleSubmissionOpportunity setup timeouts leaks bounds horizon scheduler)

end Vegas
