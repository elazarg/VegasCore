/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalCurrentBindingGain
import Vegas.Pending.PhaseAttemptReceiptSnapshot
import Vegas.Game.PhaseProposalOrdinaryBindingCheckpoint
import Vegas.Game.ReservedEpochStoppedFootprint
import Vegas.Game.ProposalRecoveryFutureFlags
import Vegas.Source.ProposalRecoveryPreparationRepairMoves
import Interaction.ReactiveLocalContinuation
import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound

/-! # Qualified binding payoffs at the original native information

The current response is a literal counted-menu atom. The first exit from its
original attempt retains the completed physical image before normalization.
The terminal continuation starts at that same stopped history, retaining both
the original initializer and the scheduler's accumulated observations.
-/

noncomputable section

namespace Vegas.PhaseProposalQualifiedBinding

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  {tapeLength : Nat} (prior : PMF (ReservedEpoch.Tape Player tapeLength))

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" =>
  PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)
local notation "horizon" => ReservedEpoch.executionHorizon runtime
local notation "scheduler" => ReactiveApplication.SchedulerImplementation.scheduler
  (ReservedEpoch.implementation runtime leaks (ReservedEpoch.packetCapacity runtime) prior)
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- Zero future flags use the original ordinary value table. -/
def unflaggedStrategy
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1)) :
    ∀ who, (N).BehavioralPolicy who :=
  fun who => (menu).restrictPolicy initial horizon scheduler who
    (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who)

variable (values : ∀ who (key : setup.ProposalRecoveryComponent who),
  PMF (setup.CommitRecoveryValueChoice who key.1))

local notation "clean" => unflaggedStrategy setup mode runtime leaks bounds plan prior values

open Classical in
/-- One actual response, with the chosen atom committed at this history's
actual information. Subsequent play is defined separately. -/
def currentStep (who : Player) (history : (E).History)
    (choice : (N).Choice who ((N).infoOf who history.trace)) : PMF (E).History :=
  (N).runBehavioralFrom
    (Profile.update (sig := (N).behavioralSignature) clean who
      ((clean who).commit ((N).infoOf who history.trace) choice)) 1 history

/-- The literal atom has exactly its native physical response image. -/
theorem currentStep_state (who : Player) (history : (E).History)
    (choice : (N).Choice who ((N).infoOf who history.trace))
    (remaining : Nat) (execution : (app).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (response : (app).Action) (selected : choice.1 = some response) :
    (currentStep setup mode runtime leaks bounds plan prior values who history choice).map
      History.state = PMF.pure (some ⟨remaining, none, execution.respond app who response⟩) := by
  exact (menu).run_commit_response initial horizon scheduler clean history who remaining
    execution current choice response selected

/-- The first exit compares namespaces to the original current history. -/
def attemptExit (start stop : (E).History) : Prop :=
  match start.state, stop.state with
  | some before, some after =>
      after.execution.application.attempt ≠ before.execution.application.attempt
  | _, _ => False

/-- Retain the first attempt exit and finish from that same full history. -/
def stoppedFinish (who : Player) (history : (E).History)
    (choice : (N).Choice who ((N).infoOf who history.trace)) :
    PMF ((E).History × (E).History) :=
  (currentStep setup mode runtime leaks bounds plan prior values who history choice).bind
    fun after =>
      ((N).runBehavioralUntil ((menu).bounded initial horizon scheduler).wellFoundedHistories clean
        (attemptExit setup mode runtime leaks bounds plan prior history) after).bind fun stop =>
          ((N).runBehavioralTerminalFrom
            ((menu).bounded initial horizon scheduler).wellFoundedHistories clean stop).map
              fun terminal => (stop, terminal)

/-- Erasing the recorded exit gives exactly the original postresponse terminal
law. In particular stopping does not redraw a tape or an initial input. -/
theorem stoppedFinish_terminal (who : Player) (history : (E).History)
    (choice : (N).Choice who ((N).infoOf who history.trace)) :
    (stoppedFinish setup mode runtime leaks bounds plan prior values who history choice).map
        Prod.snd =
      (currentStep setup mode runtime leaks bounds plan prior values who history choice).bind
        ((N).runBehavioralTerminalFrom
          ((menu).bounded initial horizon scheduler).wellFoundedHistories clean) := by
  unfold stoppedFinish
  rw [PMF.map_bind]
  apply bind_congr_on_support
  intro after _
  rw [PMF.map_bind]
  calc
    _ = ((N).runBehavioralUntil
        ((menu).bounded initial horizon scheduler).wellFoundedHistories clean
        (attemptExit setup mode runtime leaks bounds plan prior history) after).bind
          ((N).runBehavioralTerminalFrom
            ((menu).bounded initial horizon scheduler).wellFoundedHistories clean) := by
      apply bind_congr_on_support
      intro stop _
      calc
        _ = ((N).runBehavioralTerminalFrom
            ((menu).bounded initial horizon scheduler).wellFoundedHistories clean stop).map id :=
          PMF.map_comp _ _ _
        _ = _ := PMF.map_id _
    _ = _ := ((N).runBehavioralTerminalFrom_eq_bind_runBehavioralUntil
      ((menu).bounded initial horizon scheduler).wellFoundedHistories clean
      (attemptExit setup mode runtime leaks bounds plan prior history) after).symm

/-- The stopped experiment's terminal physical marginal is the actual native
finish after the literal current response, under the original scheduler. -/
theorem stoppedFinish_state (who : Player) (history : (E).History)
    (choice : (N).Choice who ((N).infoOf who history.trace))
    (remaining : Nat) (execution : (app).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (response : (app).Action) (selected : choice.1 = some response) :
    (stoppedFinish setup mode runtime leaks bounds plan prior values who history choice).map
        (fun result => result.2.state) =
      (app).finish initial horizon scheduler
        ((menu).decodeProfile initial horizon scheduler clean)
        (some ⟨remaining, none, execution.respond app who response⟩) := by
  calc
    _ = ((stoppedFinish setup mode runtime leaks bounds plan prior values who history choice).map
        Prod.snd).map History.state := (PMF.map_comp _ _ _).symm
    _ = _ := by
      rw [stoppedFinish_terminal]
      exact phaseProposal_response_kernel_finish setup mode runtime leaks bounds plan prior clean
        (fun _ => currentStep setup mode runtime leaks bounds plan prior values who history choice)
        remaining who execution response
        (currentStep_state setup mode runtime leaks bounds plan prior values who history choice
          remaining execution current response selected)

/-- Disintegrating the same terminal marginal uses the scheduler posterior
at the original callback, including all its earlier environment observations. -/
theorem stoppedFinish_seed_marginal (who : Player) (history : (E).History)
    (choice : (N).Choice who ((N).infoOf who history.trace))
    (remaining : Nat) (execution : (app).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (response : (app).Action) (selected : choice.1 = some response) :
    (stoppedFinish setup mode runtime leaks bounds plan prior values who history choice).map
        (fun result => result.2.state) =
      (((app).schedulerMixture prior
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime))).posterior
          execution.environmentRecall).bind fun tape =>
        (app).finish initial horizon
          (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
          ((menu).decodeProfile initial horizon scheduler clean)
          (some ⟨remaining, none, execution.respond app who response⟩) := by
  rw [stoppedFinish_state setup mode runtime leaks bounds plan prior values who history choice
    remaining execution current response selected]
  simpa only [PMF.pure_bind] using
    (phaseProposal_current_finish_seed_marginal setup mode runtime leaks plan prior
      ((menu).decodeProfile initial horizon scheduler clean) remaining who execution
      (PMF.pure response))

omit values in
/-- Admission is read from the original drained closing image, before any
retry or exhausted checkpoint restoration. Only entry-active owners are tested;
guard acceptance at publication is not part of this gate. -/
def originalAdmissionGate (start stop : (E).History) : Prop :=
  ∃ (origin before ending : (app).Control)
      (phase : RuntimePhase (serviceGraph setup mode))
      (priorTrace : (E).Trace (some before))
      (joint : Player → Option (app).Action)
      (legal : (E).Legal (some before) joint)
      (realized : some ending ∈ ((app).transition initial horizon scheduler
        (some before) joint).support)
      (raw : RecoveryState (serviceGraph setup mode)),
    start.state = some origin ∧
    stop = ⟨some ending, priorTrace.extend joint legal realized⟩ ∧
    TracePrefix start.trace priorTrace ∧
    phase ∈ origin.execution.application.phases.head? ∧
    phase ∈ before.execution.application.phases.head? ∧
    phase.kind = .commitment ∧
    before.execution.application.attempt = origin.execution.application.attempt ∧
    ending.execution.application.attempt ≠ origin.execution.application.attempt ∧
    PhaseClosingEffect runtime leaks before.execution ending.execution raw ∧
    ending.execution.application =
      ({ before.execution.application with current := raw } :
        PhaseRuntimeState (serviceGraph setup mode)).normalize ∧
    phase.Finished (phase.drain raw) ∧
    ∀ event ∈ phase.events, ∀ owner,
      (serviceGraph setup mode).actor? event = some owner →
      owner ∉ origin.execution.application.entry.excluded →
      (phase.drain raw).native.accepted (.inr event) ≠ none

omit values in
/-- All entry-active admissions force a genuinely clean original closing
image. An admitted unusable value is still an admission in this statement. -/
theorem closing_all_admitted_no_new_failure
    (before ending : (app).Control) (priorTrace : (E).Trace (some before))
    (phase : RuntimePhase (serviceGraph setup mode))
    (installed : phase ∈ before.execution.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (raw : RecoveryState (serviceGraph setup mode))
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt)
    (finished : phase.Finished (phase.drain raw))
    (admitted : ∀ event ∈ phase.events, ∀ owner,
      (serviceGraph setup mode).actor? event = some owner →
      owner ∉ before.execution.application.entry.excluded →
      (phase.drain raw).native.accepted (.inr event) ≠ none) :
    ¬ (((phase.drain raw).excluded \ before.execution.application.entry.excluded) ∩
      phase.owners).Nonempty := by
  classical
  obtain ⟨_native, _binding, receipts, _stored, _remembered, _coverage⟩ :=
    phaseClosingEffect_checkpoint_facts setup mode runtime leaks bounds plan horizon scheduler
      before ending priorTrace raw effect changed
  have record := (receipts.exclusion.installed phase (by
    simpa only using installed)).phase_drain phase
  rintro ⟨owner, member⟩
  have excluded := Finset.mem_sdiff.mp (Finset.mem_inter.mp member).1
  rcases (record.excluded owner).mp excluded.1 with inherited |
      ⟨event, lower, acting, failed⟩
  · exact excluded.2 inherited
  · have read := ReservedEpoch.original_binding_publicFailure_iff runtime leaks
      (serviceGraph_revealRelaxedOrdered setup mode) plan (setup.initialLaw.map encodeInputs)
      horizon scheduler before ((menu).toRawTrace initial horizon scheduler priorTrace)
      ending.execution raw changed effect phase installed commitment finished event
    have notEarlier : ¬ event.val < phase.low := Nat.not_lt.mpr lower
    have upper : event.val < phase.high := by
      by_contra beyond
      have impossible := read.mp failed
      simp only [notEarlier, beyond, ↓reduceIte] at impossible
    have absent : raw.native.accepted (.inr event) = none := by
      simpa only [notEarlier, upper, ↓reduceIte] using read.mp failed
    have present := admitted event ((phase.mem_events event).mpr ⟨lower, upper⟩)
      owner acting excluded.2
    rw [(phase.drain_tables raw).1] at present
    exact present absent

omit values in
/-- An actual all-admitted close constructs its initialized source extension
and exact decoded word from the original drained image. No source checkpoint,
matching cursor or independently selected source history is an input. -/
theorem exists_closing_source_word
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (before ending : (app).Control) (priorTrace : (E).Trace (some before))
    (phase : RuntimePhase (serviceGraph setup mode))
    (installed : phase ∈ before.execution.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (raw : RecoveryState (serviceGraph setup mode))
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt)
    (finished : phase.Finished (phase.drain raw))
    (admitted : ∀ event ∈ phase.events, ∀ owner,
      (serviceGraph setup mode).actor? event = some owner →
      owner ∉ before.execution.application.entry.excluded →
      (phase.drain raw).native.accepted (.inr event) ≠ none) :
    ∃ (remaining : List (RuntimePhase (serviceGraph setup mode)))
      (witness : RecoverySourceWitness setup mode plan before.execution.application)
      (next : RecoverySourceCheckpoint setup mode
        (⟨remaining, before.execution.application.generation, phase.drain raw, phase.drain raw,
          before.execution.application.retired⟩ : PhaseRuntimeState (serviceGraph setup mode))),
      before.execution.application.phases = phase :: remaining ∧
      witness.checkpoint.ArchivedProposals before.execution.network.inputs ∧
      ∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
        ⟨_, witness.checkpoint.trace⟩ ⟨_, next.trace⟩ ∧
        setup.recoveryJointRecall next.trace =
          (witness.checkpoint.commitInstructionWord (phase.drain raw).native).reverse ++
            setup.recoveryJointRecall witness.checkpoint.trace := by
  classical
  have initialEq : initial = setup.initialLaw.map
      (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) := PMF.map_comp _ _ _
  have counted : ((menu).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some before) := by
    rw [← initialEq]
    exact priorTrace
  obtain ⟨witness, archived⟩ := recoverySourceCheckpoint_proposalArchive_history setup mode runtime
    leaks bounds plan maximal horizon scheduler counted
  obtain ⟨remaining, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp installed)
  have low : phase.low = before.execution.application.attempt.phase := by
    simp only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
      Option.getD_some]
  have committing := witness.checkpoint.compiled.atCommit_of_bindingPhase setup.program mode
    witness.checkpoint.residual.tail witness.checkpoint.refs witness.checkpoint.source.revelations
    witness.checkpoint.registry witness.checkpoint.embedding witness.checkpoint.before
    before.execution.application.attempt.phase phase commitment low witness.checkpoint.source
  have chain := (phasePlanGeometry_history runtime leaks plan maximal
    (setup.initialLaw.map encodeInputs) horizon scheduler
    ((menu).toRawTrace initial horizon scheduler priorTrace)).2.2
  obtain ⟨native, binding, receipts, stored, remembered, coverage⟩ :=
    phaseClosingEffect_checkpoint_facts setup mode runtime leaks bounds plan horizon scheduler
      before ending priorTrace raw effect changed
  obtain ⟨draw, invariant⟩ := native
  let frame : PhaseRuntimeState (serviceGraph setup mode) :=
    { before.execution.application with current := raw }
  let checkpoint : RecoverySourceCheckpoint setup mode frame :=
    witness.checkpoint.transfer rfl rfl rfl
  have noNewFailure := closing_all_admitted_no_new_failure setup mode runtime leaks bounds plan
    prior before ending priorTrace phase installed commitment raw effect changed finished admitted
  obtain ⟨⟨next, _point, ⟨fuel, reached, word⟩, _history, _intended⟩, _normalized⟩ :=
    checkpoint.after_commit_clean committing phase remaining phases chain binding receipts stored
      remembered invariant coverage finished noNewFailure
  exact ⟨remaining, witness, next, phases, archived, fuel, reached, word⟩

omit values in
/-- The qualification inspects literal foreign own play at the original
information history. The initializer is not conditioned separately. -/
def foreignGood (who : Player) (history : (E).History) : Prop :=
  ∀ owner, owner ≠ who →
    ¬ PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds
      initial horizon scheduler owner history

open Classical in
/-- The full original assessment belief followed by a literal current atom,
the original admission gate, and the same stopped history's causal finish.
Unqualified mass is retained as `none`, rather than renormalized away. -/
def qualifiedPayoff (assessment : (N).BehavioralAssessment)
    (who : Player) (site : (N).InformationSite who) (choice : (N).Choice who site.1)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) : PMF (Option ℝ) :=
  (assessment.belief who site).bind fun history =>
    (stoppedFinish setup mode runtime leaks bounds plan prior values who history.val
      (history.property.symm ▸ choice)).map fun result =>
        if foreignGood setup mode runtime leaks bounds plan prior who history.val ∧
            originalAdmissionGate setup mode runtime leaks bounds plan prior history.val result.1
        then some (phaseExclusionBase setup mode runtime leaks utility excludedPayoff
          result.2.state who)
        else none

open Classical in
/-- Actual full-posterior qualification, without a payoff or normalization. -/
def qualificationLaw (assessment : (N).BehavioralAssessment)
    (who : Player) (site : (N).InformationSite who) (choice : (N).Choice who site.1) : PMF Bool :=
  (assessment.belief who site).bind fun history =>
    (stoppedFinish setup mode runtime leaks bounds plan prior values who history.val
      (history.property.symm ▸ choice)).map fun result =>
        decide (foreignGood setup mode runtime leaks bounds plan prior who history.val ∧
          originalAdmissionGate setup mode runtime leaks bounds plan prior history.val result.1)

/-- The coefficient is the mass of actual qualification at the original
information, including foreign-past failures in the complement. -/
def qualificationMass (assessment : (N).BehavioralAssessment)
    (who : Player) (site : (N).InformationSite who) (choice : (N).Choice who site.1) : ℝ :=
  (qualificationLaw setup mode runtime leaks bounds plan prior values assessment who site choice
    true).toReal

/-- The retained `some` mass is exactly the physical qualification event. -/
theorem qualifiedPayoff_isSome (assessment : (N).BehavioralAssessment)
    (who : Player) (site : (N).InformationSite who) (choice : (N).Choice who site.1)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    (qualifiedPayoff setup mode runtime leaks bounds plan prior values assessment who site choice
      utility excludedPayoff).map Option.isSome =
      qualificationLaw setup mode runtime leaks bounds plan prior values assessment who site
        choice := by
  classical
  simp only [qualifiedPayoff, qualificationLaw, PMF.map_bind, PMF.map_comp]
  apply bind_congr_on_support
  intro history _
  congr 1
  funext result
  simp only [Function.comp_def]
  split_ifs <;> simp_all

/-- The source continuation uses the same ordinary table with all three future
flag rates set to zero. Its past belief is supplied by the actual assessment. -/
def sourceUnflaggedStrategy : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who :=
  setup.proposalRecoveryNormalizedTrembledProfile
    0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values

omit values in
/-- The source qualification retains generated preparations in canceled
attempts; only foreign generated preparation failures are filtered. -/
def sourceForeignGood (who : Player) (history : setup.proposalRecoveryProtocol.History) : Prop :=
  ∀ owner, owner ≠ who → ¬ setup.GeneratedPreparationHistory owner history

open Classical in
/-- Causally insert the selected source atom and then use the zero-flag
continuation. This never conditions a baseline future on the selected value. -/
def sourceCausalPayoff (assessment : setup.proposalRecoveryModel.BehavioralAssessment)
    (who : Player) (site : setup.proposalRecoveryModel.InformationSite who)
    (choice : setup.proposalRecoveryModel.Choice who site.1)
    (positive : ∃ history ∈
        {history : setup.proposalRecoveryModel.InformationHistory who site.1 |
          sourceForeignGood setup who history.val},
      history ∈ (assessment.belief who site).support)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) : PMF (Option ℝ) :=
  let profile := sourceUnflaggedStrategy setup values
  let sourceCertificate := setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
  ((assessment.belief who site).filter
      {history | sourceForeignGood setup who history.val} positive).bind fun history =>
    ((setup.proposalRecoveryModel.runBehavioralFrom
      (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) profile who
        ((profile who).commit site.1 choice)) 1 history.val).bind
      (setup.proposalRecoveryModel.runBehavioralTerminalFrom sourceCertificate profile)).map
        (fun terminal => some (setup.proposalRecoveryPayoff utility excludedPayoff who terminal))

end Vegas.PhaseProposalQualifiedBinding
