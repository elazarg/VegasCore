/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalFreshTerminalCoupling
import Vegas.Game.ProposalRecoveryPayoff

/-! # Fresh payoff readouts under the original residual scheduler posterior -/

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

/-- Projection of the actual full terminal joint at one supplied checkpoint.
The native suffix retains its original physical state and remembered actions. -/
theorem phaseProposal_fresh_behavioral_payoff_law
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
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (anchor : (app).Control) (idle : anchor.actor = none)
    (trace : ((menu).protocol initial horizon
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some anchor))
    (entryExcluded : anchor.execution.application.entry.excluded =
      anchor.execution.application.current.excluded)
    (fresh : ∀ who, ∀ record ∈ anchor.execution.recall who,
      record.beforeView.application.2.attempt ≠ anchor.execution.application.attempt)
    (witness : RecoverySourceWitness setup mode plan anchor.execution.application)
    (archived : witness.checkpoint.ArchivedProposals anchor.execution.network.inputs)
    (proper : ∀ who, who ∉ anchor.execution.application.current.excluded →
      witness.checkpoint.source.BindingsHoldValues who) :
    let fixed := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let players := ReactiveApplication.anchoredPolicy anchor.execution
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values)
    let q0 := setup.proposalRecoveryNormalizedTrembledProfile
      0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
    let model := (menu).information initial horizon fixed
    let certificate := ((menu).bounded initial horizon fixed).wellFoundedHistories
    let profile := fun owner => (menu).restrictPolicy initial horizon fixed owner (players owner)
    ∀ who, (model.runBehavioralTerminalFrom certificate profile ⟨some anchor, trace⟩).map
        (fun final => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
          final.state who) =
      (setup.proposalRecoveryModel.runBehavioralTerminalFrom
        setup.proposalRecoveryProtocol_bounded.wellFoundedHistories q0
        ⟨_, setup.proposalRecoveryLiftTrace
          (nativeArchiveLabels setup (PhaseProposal.sourceArchive anchor.execution.network.inputs))
            witness.checkpoint.trace⟩).map
              (setup.proposalRecoveryPayoff utility excludedPayoff who) := by
  intro fixed players q0 model certificate profile who
  let start : setup.proposalRecoveryProtocol.History :=
    ⟨_, setup.proposalRecoveryLiftTrace
      (nativeArchiveLabels setup (PhaseProposal.sourceArchive anchor.execution.network.inputs))
        witness.checkpoint.trace⟩
  let sourceLaw := setup.proposalRecoveryModel.runBehavioralTerminalFrom
    setup.proposalRecoveryProtocol_bounded.wellFoundedHistories q0 start
  obtain ⟨joint, nativeLaw, sourceLawEq, supported⟩ :=
    RecoverySourceWitness.ordinary_fresh_terminal_coupling setup mode runtime leaks bounds plan
      complete covered maximal values fullValues tape activationGap processingGap gaps margin
        capacity utility excludedPayoff anchor idle trace entryExcluded fresh witness archived
          proper
  change joint.map Prod.snd = sourceLaw at sourceLawEq
  have payoff : (model.runBehavioralTerminalFrom certificate profile ⟨some anchor, trace⟩).map
      (fun final => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
        final.state who) = sourceLaw.map
          (setup.proposalRecoveryPayoff utility excludedPayoff who) := by
    rw [← nativeLaw, ← sourceLawEq]
    calc
      _ = joint.map ((fun final => phaseExclusionBase setup mode runtime leaks utility
          excludedPayoff final.state who) ∘ Prod.fst) := PMF.map_comp _ _ _
      _ = joint.map ((setup.proposalRecoveryPayoff utility excludedPayoff who) ∘ Prod.snd) := by
        apply map_congr_on_support
        intro pair member
        obtain ⟨ending, _next, current, _finished, _retained, _sourceRetained, _exact,
          _sourceTerminal, _endingE, _sourceE, _theta, _readout, same⟩ := supported pair member
        change phaseExclusionBase setup mode runtime leaks utility excludedPayoff pair.1.state
          who = setup.proposalRecoveryPayoff utility excludedPayoff who pair.2
        rw [current]
        exact congrFun same who
      _ = _ := (PMF.map_comp _ _ _).symm
  exact payoff

/-- The same selected full-history payoff readout for the physical finish runner. -/
theorem phaseProposal_fresh_finish_payoff_law
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
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (anchor : (app).Control) (idle : anchor.actor = none)
    (trace : ((menu).protocol initial horizon
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some anchor))
    (entryExcluded : anchor.execution.application.entry.excluded =
      anchor.execution.application.current.excluded)
    (fresh : ∀ who, ∀ record ∈ anchor.execution.recall who,
      record.beforeView.application.2.attempt ≠ anchor.execution.application.attempt)
    (witness : RecoverySourceWitness setup mode plan anchor.execution.application)
    (archived : witness.checkpoint.ArchivedProposals anchor.execution.network.inputs)
    (proper : ∀ who, who ∉ anchor.execution.application.current.excluded →
      witness.checkpoint.source.BindingsHoldValues who) :
    let fixed := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let players := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
    let q0 := setup.proposalRecoveryNormalizedTrembledProfile
      0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
    ∀ who, ((app).finish initial horizon fixed players (some anchor)).map
        (fun state => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
          state who) =
      (setup.proposalRecoveryModel.runBehavioralTerminalFrom
        setup.proposalRecoveryProtocol_bounded.wellFoundedHistories q0
        ⟨_, setup.proposalRecoveryLiftTrace
          (nativeArchiveLabels setup (PhaseProposal.sourceArchive anchor.execution.network.inputs))
            witness.checkpoint.trace⟩).map
              (setup.proposalRecoveryPayoff utility excludedPayoff who) := by
  intro fixed players q0 who
  let model := (menu).information initial horizon fixed
  let certificate := ((menu).bounded initial horizon fixed).wellFoundedHistories
  let anchored := ReactiveApplication.anchoredPolicy anchor.execution players
  let profile := fun owner => (menu).restrictPolicy initial horizon fixed owner (anchored owner)
  have payoff := phaseProposal_fresh_behavioral_payoff_law setup mode runtime leaks bounds plan
    complete covered maximal values fullValues tape activationGap processingGap gaps margin
      capacity utility excludedPayoff anchor idle trace entryExcluded fresh witness archived
        proper who
  have enough : (app).rank horizon (some anchor) ≤ 2 * horizon + 1 := by
    have bounded := (app).trace_bound initial horizon fixed
      ((menu).toRawTrace initial horizon fixed trace)
    omega
  have decoded : (menu).decodeProfile initial horizon fixed profile = anchored := by
    funext owner
    apply (menu).decode_restrictPolicy_of_covered initial horizon fixed owner
    intro past view action selected
    exact (menu).anchoredPolicy_covered initial horizon fixed anchor trace
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values)
      owner (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values owner)
      past view action selected
  have physical : (model.runBehavioralTerminalFrom certificate profile
      ⟨some anchor, trace⟩).map History.state =
      (app).finish initial horizon fixed anchored (some anchor) := by
    rw [model.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
      ((menu).bounded initial horizon fixed)]
    rw [(menu).run_eq_finish initial horizon fixed profile _ ⟨some anchor, trace⟩ enough, decoded]
  have sameFinish : (app).finish initial horizon fixed anchored (some anchor) =
      (app).finish initial horizon fixed players (some anchor) := by
    simp only [ReactiveApplication.finish, idle, ReactiveApplication.resume, PMF.pure_bind,
      anchored, ReactiveApplication.runRounds_anchoredPolicy]
  rw [sameFinish] at physical
  calc
    _ = ((model.runBehavioralTerminalFrom certificate profile ⟨some anchor, trace⟩).map
        History.state).map (fun state => phaseExclusionBase setup mode runtime leaks utility
          excludedPayoff state who) := congrArg (PMF.map _) physical.symm
    _ = _ := (PMF.map_comp _ _ _).trans payoff

end Vegas
