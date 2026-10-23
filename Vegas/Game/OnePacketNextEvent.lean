/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSureFailure

/-! # Protocol transitions as configuration steps

One protocol transition from an initialized state reaches an initialized state
whose event-graph configuration follows from the one before by one
configuration step (`Vegas.transition_some_configStep`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- One protocol transition from an initialized state reaches an initialized
state by one configuration step. -/
theorem transition_some_configStep (initial : PMF (application setup leaks).State)
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    (before : (application setup leaks).Control) (after : (application setup leaks).ProtocolState)
    (joint : Player → Option (application setup leaks).Action)
    (reached : after ∈ ((application setup leaks).transition initial horizon scheduler
      (some before) joint).support) :
    ∃ next, after = some next ∧ ConfigStep setup before.execution.application.config
      next.execution.application.config := by
  have stays : ∃ next, after = some next := by
    rcases before with ⟨remaining, current, execution⟩
    cases current with
    | some who => exact ⟨_, (PMF.mem_support_pure_iff _ _).mp reached⟩
    | none =>
        cases remaining with
        | zero => exact ⟨_, (PMF.mem_support_pure_iff _ _).mp reached⟩
        | succ remaining =>
            obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
            obtain ⟨next, _, same⟩ := PMF.support_map .. ▸ moved
            exact ⟨_, same.symm⟩
  obtain ⟨next, rfl⟩ := stays
  exact ⟨next, rfl, transition_configStep initial horizon scheduler before next joint reached⟩

end Vegas
