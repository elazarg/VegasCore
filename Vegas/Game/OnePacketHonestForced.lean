/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLawApproximation
import Vegas.Source.IntendedDeparture

/-! # The intended-or-owed region

Along every history of the one-packet game, under any profile and any
scheduler, the decoding of the configuration is a point of the intended game
or one at which some player owes a failed reveal
(`Vegas.decodedState_intended_or_owes`): every source step from the intended
game stays in it or leaves a debt, and debts persist
(`Vegas.intendedOrOwed_stepClosed`). An information state is reached when
as-if-honest play reaches it from initialization (`Vegas.HonestReached`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable (setup) in
/-- A point of the intended game, or one at which some player owes a failed
reveal. -/
def IntendedOrOwed (point : ProtocolState setup.program) : Prop :=
  ProtocolState.Intended setup.program point ∨
    ∃ who, ProtocolState.OwesFailure who setup.program point

theorem intendedOrOwed_stepClosed : StepClosed setup (IntendedOrOwed setup) := by
  intro state joint target holds reached
  rcases holds with intended | ⟨who, owed⟩
  · exact ProtocolState.intended_or_owesFailure_step setup.program state joint target intended
      reached
  · exact Or.inr ⟨who, ProtocolState.owesFailure_step who setup.program state joint target owed
      reached⟩

/-- **Intended or owed along every history.** For a well-formed setup, along
every history of a response menu of the default runtime from its initial law,
under any scheduler, the configuration decodes to a point of the intended game
or one at which some player owes a failed reveal. -/
theorem decodedState_intended_or_owes (wellFormed : setup.WellFormed)
    (profile : BehavioralProfile setup.program)
    (menu : (application setup leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) :
    ∀ {state} (_ : (menu.protocol (initialLaw setup) horizon scheduler).Trace state)
      (control : (application setup leaks).Control), state = some control →
      DecodedState setup leaks profile (IntendedOrOwed setup) (some control) := by
  intro state trace control current
  refine decodedState_history_of_stepClosed intendedOrOwed_stepClosed ?_ menu horizon scheduler
    trace control current
  intro initial member
  exact Or.inl (ProtocolState.intended_entry setup.program _
    (setup.initialConfig_intended wellFormed member)
    (wellFormed.guardsSatisfiable initial member))

section Domination

variable [Fintype Player] (bounds : MessageBounds (graph setup))

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem apply_eq_one_of_subsingleton {α : Type} [Subsingleton α] (law : PMF α) (a : α) :
    law a = 1 := by
  rw [← law.tsum_coe, tsum_eq_single a (fun other different =>
    (different (Subsingleton.elim other a)).elim)]

end Domination

end Vegas
