/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySourceEnvironment
import Vegas.Game.RecoverySourceTerminal
import Vegas.Source.CommitRecoveryAttemptDebt
import Vegas.Source.CommitRecoveryFailureCoverage
import Interaction.ReactivePolicyInvariant
import Interaction.ReactiveRawRoundTrace

/-! # Saved unusable declarations force the actual native exclusion payoff

The selected checkpoint is propagated by the existing native transition
producers. Their already constructed source path retains saved debt through
arbitrary later actions and resets. No clean source-kernel law is required.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace RecoverySourceWitness

variable {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
  {plan : RuntimePhasePlan (serviceGraph setup mode)} {state : PhaseRuntimeState
    (serviceGraph setup mode)}

/-- Debt belongs to the saved semantic source entry. A private preparation
that was never accepted is not tested by this predicate. -/
def CheckpointDebt (witness : RecoverySourceWitness setup mode plan state) (who : Player) : Prop :=
  who ∈ state.entry.excluded ∨ ProtocolState.OwesFailure who setup.program
    (witness.checkpoint.residual.lift
      (ProtocolState.entry witness.checkpoint.residual.tail witness.checkpoint.source))

/-- An unresolved unusable binding is read through the actual checkpoint
references. Earlier publication failures and guard debt require no repair. -/
theorem checkpointDebt_of_failed_binding
    (witness : RecoverySourceWitness setup mode plan state) (who : Player)
    {name : VarId} {payload : L.Ty}
    (cell : HasVar witness.checkpoint.residual.context name (.commitment who payload))
    (unresolved : name ∈ witness.checkpoint.residual.names)
    (failed : (witness.checkpoint.refs.get cell).get? state.entry.native.config.store =
      some .failure) : witness.CheckpointDebt who := by
  have stored : witness.checkpoint.source.state.get cell = .failure :=
    Option.some.inj ((witness.checkpoint.agrees cell).symm.trans failed)
  have localFailure : witness.checkpoint.source.FailedBinding who
      witness.checkpoint.residual.names :=
    ⟨witness.checkpoint.unique, name, payload, cell, unresolved, stored⟩
  exact Or.inr (Or.inr (witness.checkpoint.origin.failedBinding_lift who _
    (ProtocolState.failedBinding_entry _ _ localFailure)))

private theorem debt_of_source_reaches
    (who : Player) (witness : RecoverySourceWitness setup mode plan state)
    (owed : witness.CheckpointDebt who)
    {nextState : PhaseRuntimeState (serviceGraph setup mode)}
    (next : RecoverySourceWitness setup mode plan nextState) (fuel : Nat)
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, witness.checkpoint.trace⟩ ⟨_, next.checkpoint.trace⟩) :
    next.CheckpointDebt who := by
  let debt : setup.commitRecoveryProtocol.State → Prop := fun source =>
    ∃ current, source = some current ∧ (who ∈ current.excluded ∨
      (ProtocolState.OwesFailure who setup.program current.saved ∧
        ProtocolState.OwesFailure who setup.program current.point))
  have closed (before after : setup.commitRecoveryProtocol.State)
      (joint : Player → Option (CommitRecoveryMove Player L))
      (legal : setup.commitRecoveryProtocol.Legal before joint)
      (supported : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support) :
      debt before → debt after := by
    rintro ⟨current, rfl, owed⟩
    obtain ⟨last, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact ⟨last, rfl, current.step_preserves_excluded_or_owesFailure who owed joint last
      reached⟩
  have initial : debt (some (CommitRecoveryState.atPoint
      (witness.checkpoint.residual.lift
        (ProtocolState.entry witness.checkpoint.residual.tail witness.checkpoint.source))
      state.entry.excluded state.generation)) := by
    refine ⟨_, rfl, ?_⟩
    rcases owed with excluded | owes
    · exact Or.inl excluded
    · exact Or.inr ⟨owes, owes⟩
  have retain {last : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace last)
      (earlier : TracePrefix witness.checkpoint.trace trace) : debt last := by
    induction earlier with
    | refl => exact initial
    | @extend before after prior earlier joint legal supported ih =>
        exact closed before after joint legal supported ih
  have retained := retain next.checkpoint.trace path.tracePrefix
  obtain ⟨current, same, remaining⟩ := retained
  cases Option.some.inj same
  rcases remaining with excluded | owes
  · exact Or.inl excluded
  · exact Or.inr owes.2

end RecoverySourceWitness

/-- Some actual chosen saved checkpoint carries permanent own debt. The
native current store and physical traffic remain otherwise unrestricted. -/
def PhaseCheckpointDebt (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (plan : RuntimePhasePlan (serviceGraph setup mode)) (who : Player)
    (state : PhaseRuntimeState (serviceGraph setup mode)) : Prop :=
  ∃ witness : RecoverySourceWitness setup mode plan state, witness.CheckpointDebt who

theorem phaseCheckpointDebt_invariant
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample) (who : Player) :
    (phaseApplication runtime leaks).Invariant (PhaseCheckpointDebt setup mode plan who) where
  submit state owner material valid := by
    obtain ⟨witness, owed⟩ := valid
    exact ⟨witness.submit runtime leaks owner material, owed⟩
  handle state message next valid accepted := by
    obtain ⟨witness, owed⟩ := valid
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · rename_i allowed
      obtain ⟨result, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      obtain ⟨nextWitness, _delta, fuel, path⟩ := witness.after_handle runtime leaks maximal
        message result allowed handled
      exact ⟨nextWitness, RecoverySourceWitness.debt_of_source_reaches who witness owed
        nextWitness fuel path⟩
    · cases accepted
  environment state command next valid supported := by
    obtain ⟨witness, owed⟩ := valid
    change next ∈ (state.environment runtime command).support at supported
    unfold PhaseRuntimeState.environment at supported
    split at supported
    · rename_i authorized
      obtain ⟨result, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      obtain ⟨nextWitness, _delta, fuel, path⟩ := witness.after_environment_source runtime leaks
        maximal
        command result authorized reached
      exact ⟨nextWitness, RecoverySourceWitness.debt_of_source_reaches who witness owed
        nextWitness fuel path⟩
    · rw [PMF.mem_support_pure_iff] at supported
      subst next
      exact ⟨witness, owed⟩

/-- Saved debt is retained by each actual raw protocol transition after
initialization, without a restriction on the current player's response. -/
theorem phaseCheckpointDebt_transition
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (before after : (phaseApplication runtime leaks).Control)
    (joint : Player → Option (phaseApplication runtime leaks).Action)
    (who : Player) (owed : PhaseCheckpointDebt setup mode plan who before.execution.application)
    (reached : some after ∈ ((phaseApplication runtime leaks).transition initial horizon
      scheduler (some before) joint).support) :
    PhaseCheckpointDebt setup mode plan who after.execution.application := by
  let invariant := phaseCheckpointDebt_invariant setup mode runtime leaks plan maximal who
  let step : (phaseApplication runtime leaks).StepRelation
      (fun before after => PhaseCheckpointDebt setup mode plan who before →
        PhaseCheckpointDebt setup mode plan who after) := {
    refl := fun _ valid => valid
    submit := fun state owner material valid => invariant.submit state owner material valid
    handle := fun state message next accepted valid =>
      invariant.handle state message next valid accepted
    environment := fun state command next moved valid =>
      invariant.environment state command next valid moved }
  exact step.transition initial horizon scheduler before after joint reached owed

/-- At actual phase exhaustion the SAME selected checkpoint becomes a genuine
source terminal. Its permanent debt therefore yields native exclusion. -/
theorem phaseCheckpointDebt_excluded_of_finished
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (finished : control.execution.application.phases = []) (who : Player)
    (owed : PhaseCheckpointDebt setup mode plan who control.execution.application) :
    who ∈ control.execution.application.current.excluded := by
  obtain ⟨witness, owed⟩ := owed
  have sourceExcluded : who ∈ control.execution.application.entry.excluded := by
    rcases owed with excluded | debt
    · exact excluded
    · exact setup.commitRecovery_terminal_excluded_of_owesFailure witness.checkpoint.trace
        _ rfl who debt (witness.checkpoint.terminal finished)
  rw [← phaseTerminalExclusion_history runtime leaks plan inputs horizon scheduler trace finished]
  exact sourceExcluded

/-- Saved own debt fixes the terminal payoff on every actual completed suffix;
this is equality, rather than an application of the weak lower bound. -/
theorem phaseCheckpointDebt_terminal_payoff
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (players : Player → (phaseApplication runtime leaks).Policy)
    (count : Nat) (before after : (phaseApplication runtime leaks).Execution)
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some ⟨count, none, before⟩))
    (who : Player) (owed : PhaseCheckpointDebt setup mode plan who before.application)
    (reached : after ∈ ((phaseApplication runtime leaks).runRounds scheduler players count
      before).support)
    (finished : after.application.phases = [])
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ) :
    phaseExclusionBase setup mode runtime leaks utility excludedPayoff
      (some ⟨0, none, after⟩) who = excludedPayoff who := by
  have invariant := phaseCheckpointDebt_invariant setup mode runtime leaks plan maximal who
  have retained := (invariant.policyInvariant (phaseApplication runtime leaks) players).runRounds
    scheduler count before
      after owed reached
  obtain ⟨finalTrace⟩ := (phaseApplication runtime leaks).raw_trace_runRounds
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler players 0 count before after
      (by simpa only [Nat.zero_add] using trace) reached
  exact phaseExclusionBase_of_excluded setup mode runtime leaks utility excludedPayoff
    ⟨0, none, after⟩ who (phaseCheckpointDebt_excluded_of_finished setup mode runtime leaks
      plan inputs horizon scheduler ⟨0, none, after⟩ finalTrace finished who retained)

end Vegas
