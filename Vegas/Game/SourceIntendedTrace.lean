/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.IntendedPreservation
import Vegas.Source.CommitRecoveryProjection

/-! # Intended source histories and persistent departure debt -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Every initialized source history either has an intended history at the
same typed point or retains a player's debt from its first unintended action. -/
theorem sourceTrace_intended_or_owes (wellFormed : setup.WellFormed)
    (admission : CommitmentInterface setup.program) :
    ∀ {state : setup.ProtocolState}
      (_ : (setup.executionProtocol admission).Trace state),
      Nonempty (setup.intendedProtocol.Trace state) ∨
        ∃ who, setup.OwesFailureState who state
  | _, .start => Or.inl ⟨.start⟩
  | _, .extend (source := before) prior joint legal reached => by
      classical
      obtain previous | ⟨who, owed⟩ :=
        sourceTrace_intended_or_owes wellFormed admission prior
      · obtain ⟨original⟩ := previous
        by_cases offered : ∀ who,
            joint who ∈ setup.intendedMenu who (setup.protocolObserve who before)
        · have intendedLegal : setup.intendedProtocol.Legal before joint := by
            refine ⟨legal.1, fun who => ?_⟩
            have member : joint who ∈ setup.intendedModel.menu who
                (setup.intendedModel.infoOf who original) := by
              rw [setup.intended_info who original]
              exact offered who
            have permitted :=
              (setup.intendedModel.menu_adequate who original (joint who)).mp member
            revert permitted
            cases joint who <;> exact id
          refine Or.inl ⟨original.extend joint intendedLegal ?_⟩
          change _ ∈ (setup.protocolStep before joint).support at reached ⊢
          exact reached
        · obtain ⟨who, missing⟩ := not_forall.mp offered
          cases chosen : joint who with
          | none =>
              have inactive := legal.2 who
              rw [chosen] at inactive
              have permitted : LegalOption setup.intendedProtocol before who none := inactive
              have member :=
                (setup.intendedModel.menu_adequate who original none).mpr permitted
              rw [setup.intended_info who original] at member
              exact (missing (chosen ▸ member)).elim
          | some action =>
              refine Or.inr ⟨who, setup.owesFailureState_of_deviation admission who
                (setup.intendedState_trace wellFormed original) joint legal chosen ?_ _ reached⟩
              simpa only [chosen] using missing
      · exact Or.inr ⟨who, setup.owesFailureState_step who admission before joint legal _
          owed reached⟩

/-- An actual source endpoint with no departure debt is realized by an
initialized intended source history, including its complete effective own words. -/
theorem intendedTrace_of_not_owes (wellFormed : setup.WellFormed)
    (admission : CommitmentInterface setup.program) {state : setup.ProtocolState}
    (trace : (setup.executionProtocol admission).Trace state)
    (debtFree : ∀ who, ¬ setup.OwesFailureState who state) :
    Nonempty (setup.intendedProtocol.Trace state) := by
  obtain intended | ⟨who, owed⟩ :=
    setup.sourceTrace_intended_or_owes wellFormed admission trace
  · exact intended
  · exact (debtFree who owed).elim

/-- Projecting an actual clear recovery history does not hide source debt:
either its exact typed point has an intended history, or some player owes a failure. -/
theorem clearRecoveryTrace_intended_or_owes (wellFormed : setup.WellFormed)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state)
    (clear : setup.CommitRecoveryClear state) :
    Nonempty (setup.intendedProtocol.Trace (setup.commitRecoverySourceState state)) ∨
      ∃ who, setup.OwesFailureState who (setup.commitRecoverySourceState state) :=
  setup.sourceTrace_intended_or_owes wellFormed
    (CommitmentInterface.forfeiture setup.program) (setup.commitRecoveryClearTrace trace clear)

end Vegas.SourceProgram.Setup
