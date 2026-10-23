/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ReservedEpochBindingReset
import Vegas.Game.RecoveryOriginalRetryWitness
import Vegas.Game.PhaseProposalSavedBindingValues
import Vegas.Game.PhaseProposalResetPayoff

/-! # Actual selected reset endpoints and their complete payoff laws -/

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
local notation "initial" =>
  PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)
local notation "horizon" => ReservedEpoch.executionHorizon runtime

/-- This consumes the original first-exit pair, including its selected retry
points, words and history extensions. Both full witnesses are packaged at those
literal endpoints; properness is inherited from the restored saved cells. -/
theorem phaseProposal_original_reset_payoff_law_eq
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
    (anchor : (app).Control)
    (anchorTrace : ((menu).protocol initial horizon
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some anchor))
    (witness : RecoverySourceWitness setup mode plan anchor.execution.application)
    (archived : witness.checkpoint.ArchivedProposals anchor.execution.network.inputs)
    (oldProper : ∀ who, who ∉ anchor.execution.application.current.excluded →
      witness.checkpoint.source.BindingsHoldValues who)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : anchor.execution.application.phases = phase :: remaining)
    (kind : phase.kind = .commitment)
    (before ending : Bool → (app).Control)
    (priors : ∀ side, ((menu).protocol initial horizon
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some (before side)))
    (traces : ∀ side, ((menu).protocol initial horizon
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some (ending side)))
    (kept : ∀ side, TracePrefix anchorTrace (priors side))
    (same : ∀ side, (before side).execution.application.attempt =
      anchor.execution.application.attempt)
    (idle : ∀ side, (ending side).actor = none)
    (changed : ∀ side, (ending side).execution.application.attempt ≠
      (before side).execution.application.attempt)
    (raw : Bool → RecoveryState (serviceGraph setup mode))
    (effects : ∀ side, PhaseClosingEffect runtime leaks (before side).execution
      (ending side).execution (raw side))
    (normalized : ∀ side, (ending side).execution.application =
      ({ (before side).execution.application with current := raw side } :
        PhaseRuntimeState (serviceGraph setup mode)).normalize)
    (finished : ∀ side, phase.Finished (phase.drain (raw side)))
    (missed : ∀ side, (((phase.drain (raw side)).excluded \
      (before side).execution.application.entry.excluded) ∩ phase.owners).Nonempty)
    (survives : ∀ side, (phase.owners \ (phase.drain (raw side)).excluded).Nonempty)
    (inherited : ∀ side, anchor.execution.application.current.excluded ⊆
      (ending side).execution.application.current.excluded)
    (archive : PhaseProposal.sourceArchive (ending false).execution.network.inputs =
      PhaseProposal.sourceArchive (ending true).execution.network.inputs)
    (paired : PairedBindingResetSources witness.checkpoint
      (ending false).execution.application (ending true).execution.application
        (phase.drain (raw false)) (phase.drain (raw true))) :
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let model := (menu).information initial horizon scheduler
    let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
    let profile := fun side who => (menu).restrictPolicy initial horizon scheduler who
      (ReactiveApplication.anchoredPolicy (ending side).execution
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who)
    ∀ who, (model.runBehavioralTerminalFrom certificate (profile false)
        ⟨some (ending false), traces false⟩).map
          (fun final => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
            final.state who) =
      (model.runBehavioralTerminalFrom certificate (profile true)
        ⟨some (ending true), traces true⟩).map
          (fun final => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
            final.state who) := by
  classical
  intro scheduler model certificate profile who
  obtain ⟨left, right, leftPath, rightPath, leftPoint, rightPoint, leftWord, rightWord,
    leftOwn, rightOwn, _erased, enriched⟩ := paired
  let selected (side : Bool) : RecoverySourceCheckpoint setup mode
      (ending side).execution.application :=
    match side with
    | false => left
    | true => right
  have paths : ∀ side, ∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, witness.checkpoint.trace⟩ ⟨_, (selected side).trace⟩ := by
    intro side; cases side
    · exact leftPath
    · exact rightPath
  have words : ∀ side, setup.recoveryJointRecall (selected side).trace =
      (witness.checkpoint.commitInstructionWord (phase.drain (raw side)).native).reverse ++
        setup.recoveryJointRecall witness.checkpoint.trace := by
    intro side; cases side
    · exact leftWord
    · exact rightWord
  have own : ∀ side owner, owner ∉ (phase.drain (raw side)).excluded →
      (selected side).source.history owner = witness.checkpoint.source.history owner ++
        (decodeHistory setup.program ((phase.drain (raw side)).native.config.history.map
          ((toEventGraph setup.program).fromModeCompletion mode)) owner).drop
            (decodeHistory setup.program
              (anchor.execution.application.entry.native.config.history.map
              ((toEventGraph setup.program).fromModeCompletion mode)) owner).length := by
    intro side; cases side
    · exact leftOwn
    · exact rightOwn
  have packages : ∀ side, ∃ next : RecoverySourceWitness setup mode plan
      (ending side).execution.application, next.checkpoint = selected side ∧
        next.checkpoint.ArchivedProposals (ending side).execution.network.inputs := by
    intro side
    obtain ⟨beforeW, beforeArchive, beforeHistory, saved, checkpointEq⟩ :=
      RecoverySourceWitness.prefix_at_same_attempt setup mode runtime leaks bounds plan maximal
        scheduler anchor (before side) anchorTrace (priors side) (kept side) (same side) witness
          archived
    have phases := (phaseProposal_same_attempt_archive_metadata setup mode runtime leaks bounds
      plan horizon scheduler anchor (before side) anchorTrace (priors side) (kept side)
        (same side).symm).1
    have beforeInstalled : (before side).execution.application.phases = phase :: remaining :=
      phases.trans installed
    have low : phase.low = (before side).execution.application.attempt.phase := by
      simp only [PhaseRuntimeState.attempt, beforeInstalled, List.head?_cons, Option.map_some,
        Option.getD_some]
    have committing := beforeW.checkpoint.compiled.atCommit_of_bindingPhase setup.program mode
      beforeW.checkpoint.residual.tail beforeW.checkpoint.refs beforeW.checkpoint.source.revelations
        beforeW.checkpoint.registry beforeW.checkpoint.embedding beforeW.checkpoint.before
          (before side).execution.application.attempt.phase phase kind low beforeW.checkpoint.source
    obtain ⟨fuel, path⟩ := paths side
    apply beforeW.original_retry_archived_source setup mode runtime leaks bounds plan maximal
      horizon scheduler (before side) (ending side) (priors side) beforeArchive (raw side)
        (effects side) (changed side) (normalized side) phase remaining beforeInstalled kind
          committing (finished side) (missed side) (survives side) (selected side) fuel
    · rwa [beforeHistory]
    · have sameWord : beforeW.checkpoint.commitInstructionWord (phase.drain (raw side)).native =
          witness.checkpoint.commitInstructionWord (phase.drain (raw side)).native :=
        (congrArg (fun checkpoint : RecoverySourceCheckpoint setup mode
            (before side).execution.application =>
          checkpoint.commitInstructionWord (phase.drain (raw side)).native) checkpointEq).trans
            (witness.checkpoint.transfer_binding_readback saved
              (congrArg CommitAttemptId.generation (same side))
              (congrArg CommitAttemptId.phase (same side)) (phase.drain (raw side))).2
      have recallEq := congrArg (fun history : setup.commitRecoveryProtocol.History =>
        setup.recoveryJointRecall history.trace) beforeHistory
      rw [sameWord, recallEq]
      exact words side
    · rw [checkpointEq]
      simpa only [RecoverySourceCheckpoint.transfer, saved] using own side
  choose next exactCheckpoint nextArchived using packages
  have proper : ∀ side owner, owner ∉ (ending side).execution.application.current.excluded →
      (next side).checkpoint.source.BindingsHoldValues owner := by
    intro side owner active
    rw [exactCheckpoint side]
    have original : witness.checkpoint.source.BindingsHoldValues owner :=
      oldProper owner (fun excluded => active (inherited side excluded))
    apply witness.checkpoint.bindingsHoldValues_of_restored_point (selected side) owner original
      (ProtocolState.history setup.program
        (witness.checkpoint.commitResultPoint (phase.drain (raw side))))
    cases side
    · exact leftPoint
    · exact rightPoint
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _member, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have fresh : ∀ side owner, ∀ record ∈ (ending side).execution.recall owner,
      record.beforeView.application.2.attempt ≠ (ending side).execution.application.attempt := by
    intro side
    rcases effects side with ⟨id, message, native, _found, moved, _handled, _rawEq⟩ |
        ⟨command, native, moved, _supported, _rawEq⟩
    · exact phase_ownRecall_fresh_after_environment runtime leaks initial initialized horizon
        scheduler (before side) ((menu).toRawTrace initial horizon scheduler (priors side))
          (ending side).execution (.include id) moved (Ne.symm (changed side))
    · exact phase_ownRecall_fresh_after_environment runtime leaks initial initialized horizon
        scheduler (before side) ((menu).toRawTrace initial horizon scheduler (priors side))
          (ending side).execution (.application command) moved (Ne.symm (changed side))
  have entryExcluded : ∀ side, (ending side).execution.application.entry.excluded =
      (ending side).execution.application.current.excluded := by
    intro side
    rw [normalized side]
    apply PhaseRuntimeState.normalize_entry_excluded_of_changed
    rw [← normalized side]
    exact changed side
  apply phaseProposal_fresh_payoff_law_eq_of_erased_source setup mode runtime leaks bounds plan
    complete covered maximal values fullValues tape activationGap processingGap gaps margin capacity
      utility excludedPayoff ending idle traces entryExcluded fresh next nextArchived proper
  rw [exactCheckpoint false, exactCheckpoint true, archive]
  exact enriched _

end Vegas
