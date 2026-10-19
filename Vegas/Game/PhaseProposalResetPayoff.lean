/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalFreshPayoff
import Vegas.Game.ProposalRecoveryContinuation
import Vegas.Game.ProposalRecoveryPayoff

/-! # Actual terminal payoff laws after a shared enriched source reset -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => PMF.map (PhaseRuntimeState.initial plan)
  (PMF.map encodeInputs setup.initialLaw)
local notation "horizon" => ReservedEpoch.executionHorizon runtime

omit [Fintype Player] in
theorem RecoverySourceCheckpoint.history_eq_of_same_attempt_path [Finite Player]
    {before after : PhaseRuntimeState (serviceGraph setup mode)}
    (first : RecoverySourceCheckpoint setup mode before)
    (last : RecoverySourceCheckpoint setup mode after)
    (entry : before.entry = after.entry) (attempt : before.attempt = after.attempt)
    {fuel : Nat} (path : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, first.trace⟩ ⟨_, last.trace⟩) :
    (⟨_, first.trace⟩ : setup.commitRecoveryProtocol.History) = ⟨_, last.trace⟩ := by
  classical
  let := Fintype.ofFinite Player
  have decreasing : ∀ {count : Nat} {start ending : setup.commitRecoveryProtocol.History},
      setup.commitRecoveryProtocol.ReachesWithin count start ending →
      ∀ current, start.state = some current →
        ∃ next, ending.state = some next ∧ next.potential ≤ current.potential ∧
          (next.potential = current.potential → ending = start) := by
    intro count start ending reached
    induction reached with
    | refl count history =>
        intro current stateEq
        exact ⟨current, stateEq, le_rfl, fun _ => rfl⟩
    | @step count start ending joint legal reached realized later ih =>
        intro current stateEq
        have raw : reached ∈ ((current.step joint).map some).support := by
          rcases start with ⟨source, trace⟩
          dsimp only at stateEq
          subst source
          exact realized
        obtain ⟨middle, supported, middleEq⟩ := (PMF.mem_support_map_iff _ _ _).mp raw
        obtain ⟨next, nextState, lower, _same⟩ := ih middle middleEq.symm
        have running : ¬ ProtocolState.terminal setup.program current.point := by
          simpa only [Setup.commitRecoveryProtocol, stateEq, Option.elim_some] using legal.1
        have strict := current.step_potential_lt joint middle running supported
        refine ⟨next, nextState, lower.trans strict.le, ?_⟩
        intro equal
        exact ((lower.trans_lt strict).ne equal).elim
  obtain ⟨current, currentEq, _lower, equal⟩ := decreasing path _ rfl
  have currentIsLast : current = CommitRecoveryState.atPoint
      (last.residual.lift (ProtocolState.entry last.residual.tail last.source))
        after.entry.excluded after.generation := Option.some.inj currentEq.symm
  subst current
  have firstPosition := first.saved_position
  have lastPosition := last.saved_position
  have phase := congrArg CommitAttemptId.phase attempt
  have firstBound := ProtocolState.remaining_le_instructionCount setup.program
    (first.residual.lift (ProtocolState.entry first.residual.tail first.source))
  have lastBound := ProtocolState.remaining_le_instructionCount setup.program
    (last.residual.lift (ProtocolState.entry last.residual.tail last.source))
  have remaining : ProtocolState.remaining setup.program
      (first.residual.lift (ProtocolState.entry first.residual.tail first.source)) =
      ProtocolState.remaining setup.program
        (last.residual.lift (ProtocolState.entry last.residual.tail last.source)) := by omega
  have potentials : (CommitRecoveryState.atPoint
      (last.residual.lift (ProtocolState.entry last.residual.tail last.source))
        after.entry.excluded after.generation).potential =
      (CommitRecoveryState.atPoint
        (first.residual.lift (ProtocolState.entry first.residual.tail first.source))
          before.entry.excluded before.generation).potential := by
    simp only [CommitRecoveryState.potential, CommitRecoveryState.atPoint, remaining, entry]
  exact (equal potentials).symm

/-- Each physical suffix uses the fresh terminal coupling at its OWN literal
endpoint and full witness. Equality of the source reset image transports the
common prescribed source continuation; no native continuation law is assumed. -/
theorem phaseProposal_fresh_payoff_law_eq_of_erased_source
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : horizon ≤ bounds.candidateCount)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (anchor : Bool → (app).Control) (idle : ∀ side, (anchor side).actor = none)
    (traces : ∀ side, ((menu).protocol initial horizon
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some (anchor side)))
    (entryExcluded : ∀ side, (anchor side).execution.application.entry.excluded =
      (anchor side).execution.application.current.excluded)
    (fresh : ∀ side who, ∀ record ∈ (anchor side).execution.recall who,
      record.beforeView.application.2.attempt ≠ (anchor side).execution.application.attempt)
    (witness : ∀ side, RecoverySourceWitness setup mode plan (anchor side).execution.application)
    (archived : ∀ side, (witness side).checkpoint.ArchivedProposals
      (anchor side).execution.network.inputs)
    (proper : ∀ side who, who ∉ (anchor side).execution.application.current.excluded →
      (witness side).checkpoint.source.BindingsHoldValues who)
    (same : setup.proposalRecoveryErasedHistory
        ⟨_, setup.proposalRecoveryLiftTrace
          (nativeArchiveLabels setup
            (PhaseProposal.sourceArchive (anchor false).execution.network.inputs))
              (witness false).checkpoint.trace⟩ =
      setup.proposalRecoveryErasedHistory
        ⟨_, setup.proposalRecoveryLiftTrace
          (nativeArchiveLabels setup
            (PhaseProposal.sourceArchive (anchor true).execution.network.inputs))
              (witness true).checkpoint.trace⟩) :
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let model := (menu).information initial horizon scheduler
    let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
    let profile := fun side who => (menu).restrictPolicy initial horizon scheduler who
      (ReactiveApplication.anchoredPolicy (anchor side).execution
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who)
    ∀ who, (model.runBehavioralTerminalFrom certificate (profile false)
        ⟨some (anchor false), traces false⟩).map
          (fun final => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
            final.state who) =
      (model.runBehavioralTerminalFrom certificate (profile true)
        ⟨some (anchor true), traces true⟩).map
          (fun final => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
            final.state who) := by
  classical
  intro scheduler model certificate profile who
  let q0 := setup.proposalRecoveryNormalizedTrembledProfile
    0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
  let sourceCertificate := setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
  let start : Bool → setup.proposalRecoveryProtocol.History := fun side =>
    ⟨_, setup.proposalRecoveryLiftTrace
      (nativeArchiveLabels setup
        (PhaseProposal.sourceArchive (anchor side).execution.network.inputs))
          (witness side).checkpoint.trace⟩
  let sourceLaw := fun side => setup.proposalRecoveryModel.runBehavioralTerminalFrom
    sourceCertificate q0 (start side)
  have projected (side : Bool) :
      (model.runBehavioralTerminalFrom certificate (profile side)
        ⟨some (anchor side), traces side⟩).map
          (fun final => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
            final.state who) =
      (sourceLaw side).map (setup.proposalRecoveryPayoff utility excludedPayoff who) := by
    exact phaseProposal_fresh_behavioral_payoff_law setup mode runtime leaks bounds plan complete
      covered maximal values fullValues tape activationGap processingGap gaps margin capacity
        utility excludedPayoff (anchor side) (idle side) (traces side) (entryExcluded side)
          (fresh side) (witness side) (archived side) (proper side) who
  rw [projected false, projected true]
  have normalized : ∀ owner first second,
      setup.proposalRecoveryQuery owner first = setup.proposalRecoveryQuery owner second →
        (q0 owner first).map Subtype.val = (q0 owner second).map Subtype.val :=
    setup.proposalRecoveryPrescribedProfile_normalized _
  have sourceEq := setup.proposalRecovery_terminal_erased_eq q0 normalized sourceCertificate
    (start false) (start true) same
  have payoffEq := congrArg
    (PMF.map (setup.proposalRecoveryImagePayoff utility excludedPayoff who)) sourceEq
  simpa only [PMF.map_comp, Function.comp_def, ← setup.proposalRecoveryPayoff_eq_image]
    using payoffEq

end Vegas
