/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

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
  intro state trace
  induction trace with
  | start => intro _ initialized; cases initialized
  | @extend before after prior joint _ realized ih =>
      intro control current
      subst current
      cases before with
      | none =>
          change some control ∈ ((initialLaw setup).map fun state =>
            some ⟨horizon, none, ReactiveApplication.Execution.initial
              (application setup leaks) state⟩).support at realized
          obtain ⟨state, supported, same⟩ := PMF.support_map .. ▸ realized
          cases Option.some.inj same
          obtain ⟨initial, initialMem, rfl⟩ := PMF.support_map .. ▸ supported
          let residual := SourceResidual.initial setup profile initial
          refine ⟨0, ⟨residual⟩, fun point decoded => ?_⟩
          change sourceServicePrefix? setup 0 (EventGraphRuntime.State.initial
            (graph := graph setup) (setup.eventInputs initial)).config = some point at decoded
          rw [residual.decode, Option.some.injEq] at decoded
          subst decoded
          exact Or.inl (ProtocolState.intended_entry setup.program _
            (setup.initialConfig_intended wellFormed initialMem)
            (wellFormed.guardsSatisfiable initial initialMem))
      | some previous =>
          exact decodedHolds_transition intendedOrOwed_stepClosed (initialLaw setup) horizon
            scheduler (some previous) (some control) joint (ih previous rfl) realized

section Domination

variable [Fintype Player] (bounds : MessageBounds (graph setup))

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem apply_eq_one_of_subsingleton {α : Type} [Subsingleton α] (law : PMF α) (a : α) :
    law a = 1 := by
  rw [← law.tsum_coe, tsum_eq_single a (fun other different =>
    (different (Subsingleton.elim other a)).elim)]

end Domination

end Vegas
