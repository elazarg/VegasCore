/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryLift
import Vegas.Game.IntendedPreservation

/-! # Intended source histories inside the actual source recovery protocol -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem intendedState_elim {state : setup.ProtocolState}
    (intended : setup.IntendedState state) :
    state.elim True (ProtocolState.Intended setup.program) := by
  cases state <;> exact intended

/-- Lift every legal intended history, including zero-probability histories of
a later selected equilibrium. No execution or information premise is assumed. -/
def commitRecoveryLiftTrace (wellFormed : setup.WellFormed) :
    ∀ {point : setup.intendedProtocol.State} (_trace : setup.intendedProtocol.Trace point),
      {history : setup.commitRecoveryProtocol.History //
        setup.commitRecoverySourceState history.state = point ∧
          setup.CommitRecoveryClear history.state}
  | _, .start => ⟨setup.commitRecoveryProtocol.initHistory, rfl, trivial⟩
  | point, @Trace.extend _ _ source _ prior joint legal supported =>
      let earlier := commitRecoveryLiftTrace wellFormed prior
      let sourceLegal : setup.intendedProtocol.Legal
          (setup.commitRecoverySourceState earlier.1.state) joint := by
        rw [earlier.2.1]
        exact legal
      let intended : (setup.commitRecoverySourceState earlier.1.state).elim True
          (ProtocolState.Intended setup.program) := by
        rw [earlier.2.1]
        exact setup.intendedState_elim (setup.intendedState_trace wellFormed prior)
      let recoveryLegal := setup.commitRecovery_lift_legal earlier.1.state earlier.2.2
        joint sourceLegal
      let target := setup.commitRecoveryLiftSuccessor earlier.1.state earlier.2.2 point
      have realized : target ∈ (setup.commitRecoveryProtocol.step earlier.1.state
          ⟨(fun who => CommitRecoveryMove.lift (joint who)), recoveryLegal⟩).support := by
        rw [setup.commitRecovery_lift_step earlier.1.state earlier.2.2 intended joint sourceLegal,
          PMF.support_map]
        refine ⟨point, ?_, rfl⟩
        change point ∈ (setup.protocolStep (setup.commitRecoverySourceState earlier.1.state)
          joint).support
        rw [earlier.2.1]
        exact supported
      ⟨⟨target, earlier.1.trace.extend
          (fun who => CommitRecoveryMove.lift (joint who)) recoveryLegal realized⟩,
        setup.commitRecoveryLiftSuccessor_source earlier.1.state earlier.2.2 point,
        setup.commitRecoveryLiftSuccessor_clear earlier.1.state earlier.2.2 point⟩

theorem commitRecoveryLiftTrace_length (wellFormed : setup.WellFormed) :
    ∀ {point : setup.intendedProtocol.State} (trace : setup.intendedProtocol.Trace point),
      (setup.commitRecoveryLiftTrace wellFormed trace).1.trace.length = trace.length
  | _, .start => rfl
  | _, .extend prior _ _ _ => by
      simp only [commitRecoveryLiftTrace, Trace.length,
        commitRecoveryLiftTrace_length wellFormed prior]

def commitRecoveryLiftHistory (wellFormed : setup.WellFormed)
    (history : setup.intendedProtocol.History) : setup.commitRecoveryProtocol.History :=
  (setup.commitRecoveryLiftTrace wellFormed history.trace).1

theorem commitRecoveryLiftHistory_source (wellFormed : setup.WellFormed)
    (history : setup.intendedProtocol.History) :
    setup.commitRecoverySourceState (setup.commitRecoveryLiftHistory wellFormed history).state =
      history.state := (setup.commitRecoveryLiftTrace wellFormed history.trace).2.1

theorem commitRecoveryLiftHistory_clear (wellFormed : setup.WellFormed)
    (history : setup.intendedProtocol.History) :
    setup.CommitRecoveryClear (setup.commitRecoveryLiftHistory wellFormed history).state :=
  (setup.commitRecoveryLiftTrace wellFormed history.trace).2.2

theorem commitRecoveryLiftHistory_length (wellFormed : setup.WellFormed)
    (history : setup.intendedProtocol.History) :
    (setup.commitRecoveryLiftHistory wellFormed history).trace.length = history.trace.length :=
  setup.commitRecoveryLiftTrace_length wellFormed history.trace

theorem commitRecoveryLiftHistory_private (wellFormed : setup.WellFormed) (who : Player)
    (history : setup.intendedProtocol.History) :
    setup.commitRecoveryPrivate who (setup.commitRecoveryLiftHistory wellFormed history).state =
      setup.intendedModel.infoOf who history.trace := by
  have observed (state : setup.commitRecoveryProtocol.State) :
      setup.commitRecoveryPrivate who state =
        setup.protocolObserve who (setup.commitRecoverySourceState state) := by
    cases state <;> rfl
  rw [observed, setup.commitRecoveryLiftHistory_source wellFormed history,
    setup.intended_info]

end Vegas.SourceProgram.Setup
