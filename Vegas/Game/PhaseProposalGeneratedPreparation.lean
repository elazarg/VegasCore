/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalRepairFiber

/-! # Generated unusable binding preparations in actual native own play -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open EventGraph Interaction GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
/-- A literal binding SEND with missing or mistyped private preparation.
The declaration's type is fixed by its actual event. Initial failed inputs,
automatic NONE cells and later guard rejection do not satisfy this predicate. -/
def GeneratedUnusableBindingAction (owner : Player) (action : (app).Action) : Prop :=
  ∃ (event : graph.EventId) (payload : L.Ty) (serial : Nat) (opening : Option (Raw L))
      (evidence : EvidenceRequest graph),
    graph.outputLayout event = .binding owner payload ∧
      action = ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩ ∧
      opening.bind (fun raw => raw.as? payload) = none

/-- A submitted unusable preparation occurred in the actual owner's own play. -/
def GeneratedUnusableBindingHistory
    {Player : Type} [DecidableEq Player] [Fintype Player]
    {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (bounds : MessageBounds graph) (initial : PMF (phaseApplication runtime leaks).State)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) (owner : Player)
    (history : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).History) : Prop :=
  ∃ record ∈ (ReactiveApplication.ResponseMenu.information
      (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler).ownPlay
        owner history.trace,
    GeneratedUnusableBindingAction runtime leaks owner record.2

end Vegas.EventGraphRuntime.PhaseProposal
