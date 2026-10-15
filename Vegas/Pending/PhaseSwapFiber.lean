/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSwapSymmetry

/-! # Exact guarded information-fiber counterparts in the phased protocol -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

/-- The existing history exchange restricts to the full actual information
fiber of a fixed observer. Only histories satisfying the primitive native
read guards occur in this domain; raw bad-binding repair remains separate. -/
def phaseSwapInformationFiberEquiv (bounds : MessageBounds graph)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (swap : HiddenSwap graph)
    (initialClosed : ∀ state ∈ initial.support, state.swap swap ∈ initial.support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (expiry : ∀ event, swap.values.ExpiryFixed event) (who : Player)
    (fields : ∀ field, graph.fieldVisibleTo who field → swap.values.value field = id)
    (actions : ∀ event, graph.actor? event = some who → swap.values.action event = id)
    (handles : ∀ slot, swap.raw (who, slot) = id)
    (input : (phaseApplication runtime leaks).Info) :
    {history : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial
        horizon scheduler).History // PhaseSwapGuardState swap history.state ∧
      ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon scheduler).infoOf
        who history.trace = input} ≃
    {history : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial
        horizon scheduler).History // PhaseSwapGuardState swap history.state ∧
      ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon scheduler).infoOf
        who history.trace = input} := by
  let symmetry := phaseOnePacketSwapSymmetry bounds initial horizon scheduler swap
    initialClosed bounded expiry
  have involutive := phaseOnePacketSwapSymmetry_involutive bounds initial horizon scheduler
    swap initialClosed bounded expiry
  let fiber := fun history : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      initial horizon scheduler).History => PhaseSwapGuardState swap history.state ∧
    ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon scheduler).infoOf
      who history.trace = input
  refine symmetry.exchange involutive fiber fiber (fun _ member => member.1)
    (fun _ member => member.1) ?_ ?_
  · intro history member
    exact ⟨involutive.guard_map history.state member.1,
      (phase_infoOf_mapTrace_of_fixed bounds initial horizon scheduler swap initialClosed
        bounded expiry who fields actions handles history member.1).trans member.2⟩
  · intro history member
    exact ⟨involutive.guard_map history.state member.1,
      (phase_infoOf_mapTrace_of_fixed bounds initial horizon scheduler swap initialClosed
        bounded expiry who fields actions handles history member.1).trans member.2⟩

end Vegas.EventGraphRuntime
