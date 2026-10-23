/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalTransition
import Vegas.Pending.PhaseBindingSampleReplay

/-! # Selected normalized source witnesses for actual environment commands -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Environment processing retains its exact native result and the same
normalizer-selected source trace, including automatic phase advances. -/
theorem RecoverySourceWitness.after_environment_source
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode)}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (witness : RecoverySourceWitness setup mode plan state)
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (command : EnvironmentCommand ((toEventGraph setup.program).withMode mode))
    (result : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (authorized : state.commandAllowed command = true)
    (supported : result ∈ (environmentStep runtime state.current.native command).support) :
    let raw : PhaseRuntimeState ((toEventGraph setup.program).withMode mode) :=
      { state with current := state.current.environmentResult command result }
    ∃ next : RecoverySourceWitness setup mode plan raw.normalize,
      (witness.checkpoint.transfer (other := raw) rfl rfl rfl).ProposalDelta plan
        next.checkpoint ∧
      ∃ fuel : Nat, setup.commitRecoveryProtocol.ReachesWithin fuel
        ⟨_, witness.checkpoint.trace⟩ ⟨_, next.checkpoint.trace⟩ := by
  dsimp only
  let raw : PhaseRuntimeState ((toEventGraph setup.program).withMode mode) :=
    { state with current := state.current.environmentResult command result }
  let rawWitness := witness.raw_environment runtime command result authorized supported
  obtain ⟨nextCheckpoint, nextAligned, nextChronology, fuel, sourcePath, nextOrigins,
    proposalDelta⟩ :=
    rawWitness.checkpoint.normalized_archived raw plan rawWitness.suffix rawWitness.chronology
      rawWitness.exclusions rawWitness.failures rawWitness.aligned rawWitness.origins
        rawWitness.archives rawWitness.native.choose_spec rawWitness.binding rawWitness.receipts
          rawWitness.stored rawWitness.remembered rawWitness.order maximal
  have reached : raw.normalize ∈ (state.environment runtime command).support := by
    rw [PhaseRuntimeState.environment, ite_eq_left authorized]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, supported, rfl⟩
  have graphOrder := (toEventGraph setup.program).withMode_revealRelaxedOrdered
    (toEventGraph_barrierOrdered setup.program) mode
  obtain ⟨inputs, native⟩ := witness.native
  refine ⟨{
    checkpoint := nextCheckpoint
    aligned := nextAligned
    chronology := nextChronology
    origins := nextOrigins
    native := ⟨inputs, (phaseApplication_invariant runtime leaks inputs).environment _ _ _
      native reached⟩
    binding := (phaseApplication_bindingInvariant runtime leaks).environment _ _ _
      witness.binding reached
    receipts := (phaseApplication_receiptRecord runtime leaks graphOrder).environment _ _ _
      witness.receipts reached
    stored := (phaseApplication_storedCheckpoint runtime leaks).environment _ _ _
      witness.stored reached
    remembered := (phaseApplication_historyCheckpoint runtime leaks).environment _ _ _
      witness.remembered reached
    order := (phaseApplication_publicFailureOrder graphOrder runtime leaks).environment _ _ _
      witness.order reached
    suffix := (phaseApplication_planSuffix runtime leaks plan).environment _ _ _
      witness.suffix reached
    archives := ((PhaseRuntimeState.archivesBefore_invariant runtime leaks).environment _ _ _
      ⟨witness.order.frontier.adjacent, witness.archives⟩ reached).2
    exclusions := (phaseApplication_archivedExclusions runtime leaks).environment _ _ _
      witness.exclusions reached
    failures := (phaseApplication_publicFailureCheckpoint runtime leaks).environment _ _ _
      witness.failures reached
  }, proposalDelta, fuel, sourcePath⟩

end Vegas
