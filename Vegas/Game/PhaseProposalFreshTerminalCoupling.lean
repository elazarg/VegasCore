/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryPublicClosingWitness
import Vegas.Game.PhaseProposalBindingWitness
import Vegas.Game.PhaseProposalSampleHistoryJoin
import Vegas.Game.PhaseProposalSampleHistoryCoupling
import Vegas.Game.RecoverySameAttemptWitness
import Vegas.Game.PhaseProposalAttemptArchive
import Vegas.Compile.EventGraphParameterReadout
import Interaction.ReactiveAnchoredStopped
import GameTheory.Analysis.Protocol.InformationLocalization
import Vegas.EventGraph.PrivateInputs
import Vegas.Game.CommitRecoveryPayoff
import Vegas.Game.PhaseExclusionPayoff
import Vegas.Game.RecoverySourceReadout
import Vegas.Game.RecoverySourceTerminal
import Vegas.Pending.PhaseTerminalExclusion

/-! # Full ordinary terminal histories at a fresh native boundary -/

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
local notation "graph" => serviceGraph setup mode
local notation "initial" =>
  PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)
local notation "horizon" => ReservedEpoch.executionHorizon runtime

omit [Fintype Player] in
private theorem initial_law_eq :
    (PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)) =
      setup.initialLaw.map (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) := by
  rw [PMF.map_comp]
  rfl

private theorem witness_cast_history
    {state other : PhaseRuntimeState graph} (same : state = other)
    (witness : RecoverySourceWitness setup mode plan state) :
    (⟨_, (same ▸ witness).checkpoint.trace⟩ : setup.commitRecoveryProtocol.History) =
      ⟨_, witness.checkpoint.trace⟩ := by
  cases same
  rfl

private theorem witness_cast_archive
    {state other : PhaseRuntimeState graph} (same : state = other)
    (witness : RecoverySourceWitness setup mode plan state)
    (messages : List (Message Player (CommitAttemptPacket graph))) :
    (same ▸ witness).checkpoint.ArchivedProposals messages ↔
      witness.checkpoint.ArchivedProposals messages := by
  cases same
  rfl

private theorem witness_cast_bindings
    {state other : PhaseRuntimeState graph} (same : state = other)
    (witness : RecoverySourceWitness setup mode plan state) (who : Player) :
    (same ▸ witness).checkpoint.source.BindingsHoldValues who ↔
      witness.checkpoint.source.BindingsHoldValues who := by
  cases same
  rfl

private theorem requestless_prefix_inputs
    (scheduler : (app).Scheduler) (anchor ending : (app).Control)
    (anchorTrace : ((menu).protocol initial horizon scheduler).Trace (some anchor))
    (endingTrace : ((menu).protocol initial horizon scheduler).Trace (some ending))
    (kept : TracePrefix anchorTrace endingTrace)
    (requestless : ∀ (before : (app).Control)
      (prior : ((menu).protocol initial horizon scheduler).Trace (some before)),
      TracePrefix anchorTrace prior → TracePrefix prior endingTrace →
      prior.length < endingTrace.length →
      ∀ owner coordinate, ¬ before.execution.application.SeedRequest owner coordinate) :
    ending.execution.network.inputs = anchor.execution.network.inputs := by
  have inputs : ∀ {state} (trace : ((menu).protocol initial horizon scheduler).Trace state),
      TracePrefix anchorTrace trace →
      (∀ (before : (app).Control)
        (prior : ((menu).protocol initial horizon scheduler).Trace (some before)),
        TracePrefix anchorTrace prior → TracePrefix prior trace → prior.length < trace.length →
        ∀ owner coordinate, ¬ before.execution.application.SeedRequest owner coordinate) →
      ∃ current : (app).Control, state = some current ∧
        current.execution.network.inputs = anchor.execution.network.inputs := by
    intro state trace retained
    induction retained with
    | refl => exact fun _ => ⟨anchor, rfl, rfl⟩
    | @extend source target prior earlier actions legal supported ih =>
        intro scope
        have earlierScope : ∀ (before : (app).Control)
            (prefixTrace : ((menu).protocol initial horizon scheduler).Trace (some before)),
            TracePrefix anchorTrace prefixTrace → TracePrefix prefixTrace prior →
            prefixTrace.length < prior.length →
            ∀ owner coordinate, ¬ before.execution.application.SeedRequest owner coordinate := by
          intro before prefixTrace after beforeLast shorter
          exact scope before prefixTrace after
            (beforeLast.trans (.extend .refl actions legal supported))
            (by simp only [Trace.length]; omega)
        obtain ⟨before, stateEq, previousInputs⟩ := ih earlierScope
        subst source
        have absent := scope before prior earlier (.extend .refl actions legal supported)
          (by simp only [Trace.length]; omega)
        change target ∈ ((app).transition initial horizon scheduler (some before) actions).support
          at supported
        rcases before with ⟨remaining, actor, execution⟩
        cases actor with
        | some owner =>
            have singleton := PhaseCount.onePacketActions_eq_singleton_of_no_request runtime leaks
              bounds plan (setup.initialLaw.map encodeInputs) horizon scheduler remaining owner
                execution prior (absent owner)
            have offered := legal.2 owner
            cases selected : actions owner with
            | none =>
                simp [selected, ReactiveApplication.ResponseMenu.protocol,
                  ReactiveApplication.actor] at offered
            | some action =>
                rw [selected] at offered
                have admissible : action ∈ PhaseCount.onePacketActions runtime leaks bounds owner
                    (execution.recall owner) (execution.observe (app) owner) := offered.2
                rw [singleton] at admissible
                have silent := Finset.mem_singleton.mp admissible
                subst action
                cases (PMF.mem_support_pure_iff _ _).mp supported
                refine ⟨_, rfl, ?_⟩
                simpa only [selected, Option.getD_some, ReactiveApplication.Execution.respond]
                  using previousInputs
        | none =>
            cases remaining with
            | zero =>
                cases (PMF.mem_support_pure_iff _ _).mp supported
                exact ⟨_, rfl, previousInputs⟩
            | succ remaining =>
                obtain ⟨command, _selected, moved⟩ :=
                  Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
                obtain ⟨next, reached, rfl⟩ := PMF.support_map .. ▸ moved
                exact ⟨_, rfl, ((app).environmentStep_inputs execution next command reached).trans
                  previousInputs⟩
  obtain ⟨current, equal, same⟩ := inputs endingTrace kept requestless
  cases Option.some.inj equal
  exact same

private theorem completed_prefix_inputs
    (scheduler : (app).Scheduler) (anchor ending : (app).Control)
    (anchorTrace : ((menu).protocol initial horizon scheduler).Trace (some anchor))
    (endingTrace : ((menu).protocol initial horizon scheduler).Trace (some ending))
    (kept : TracePrefix anchorTrace endingTrace)
    (finished : anchor.execution.application.phases = []) :
    ending.execution.network.inputs = anchor.execution.network.inputs := by
  have emptyInvariant : (app).Invariant (fun state => state.phases = []) := by
    constructor
    · intro state owner material empty
      exact empty
    · intro state message next empty accepted
      change state.handle runtime message = some next at accepted
      simp only [PhaseRuntimeState.handle, PhaseRuntimeState.allows, empty,
        List.head?_nil, Bool.and_false, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte, reduceCtorEq] at accepted
    · intro state command next empty selected
      change next ∈ (state.environment runtime command).support at selected
      unfold PhaseRuntimeState.environment at selected
      split at selected
      · obtain ⟨native, _supported, rfl⟩ := PMF.support_map .. ▸ selected
        change (PhaseRuntimeState.settle state.phases state.generation state.entry
          (state.current.environmentResult command native) state.retired).phases = []
        rw [empty]
        rfl
      · cases (PMF.mem_support_pure_iff _ _).mp selected
        exact empty
  apply requestless_prefix_inputs setup mode runtime leaks bounds plan scheduler anchor ending
    anchorTrace endingTrace kept
  intro before prior retained _beforeLast _shorter owner coordinate request
  have empty := emptyInvariant.tracePrefix (menu) initial horizon scheduler anchor before
    anchorTrace prior retained finished
  obtain ⟨phase, installed, _inside⟩ := request.2.1
  rw [empty, List.head?_nil] at installed
  cases installed

/-- Ordinary play from a genuine fresh boundary couples both complete native
and enriched source terminal histories, retaining the selected full witness,
the original source prefix, typed terminal store and permanent exclusions. -/
theorem RecoverySourceWitness.ordinary_fresh_terminal_coupling
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
    (anchor : (app).Control) (idle : anchor.actor = none)
    (anchorTrace : ((menu).protocol initial horizon
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
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let model := (menu).information initial horizon scheduler
    let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
    let profile := fun who => (menu).restrictPolicy initial horizon scheduler who
      (ReactiveApplication.anchoredPolicy anchor.execution
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who)
    let sourceProfile := setup.proposalRecoveryNormalizedTrembledProfile
      0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
    let sourceCertificate := setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
    let start : setup.proposalRecoveryProtocol.History :=
      ⟨_, setup.proposalRecoveryLiftTrace
        (nativeArchiveLabels setup (PhaseProposal.sourceArchive anchor.execution.network.inputs))
          witness.checkpoint.trace⟩
    ∃ joint : PMF (((menu).protocol initial horizon scheduler).History ×
        setup.proposalRecoveryProtocol.History),
      joint.map Prod.fst = model.runBehavioralTerminalFrom certificate profile
        ⟨some anchor, anchorTrace⟩ ∧
      joint.map Prod.snd = setup.proposalRecoveryModel.runBehavioralTerminalFrom
        sourceCertificate sourceProfile start ∧
      ∀ pair ∈ joint.support,
        ∃ (ending : (app).Control)
          (next : RecoverySourceWitness setup mode plan ending.execution.application),
          pair.1.state = some ending ∧ ending.execution.application.phases = [] ∧
          TracePrefix anchorTrace pair.1.trace ∧ TracePrefix start.trace pair.2.trace ∧
          pair.2 = ⟨_, setup.proposalRecoveryLiftTrace
            (nativeArchiveLabels setup
              (PhaseProposal.sourceArchive ending.execution.network.inputs))
                next.checkpoint.trace⟩ ∧
          setup.proposalRecoveryProtocol.terminal pair.2.state ∧
          ending.execution.application.current.excluded =
            ending.execution.application.entry.excluded ∧
          pair.2.state.map CommitRecoveryState.excluded =
            some ending.execution.application.current.excluded ∧
          (∃ original ∈ setup.initialLaw.support,
            ending.execution.application.current.native.config.inputs = encodeInputs original ∧
            (setup.protocolReadout (setup.commitRecoverySourceState pair.2.state)).map
              (initialState setup.program) = some original) ∧
          phaseSourceReadout setup mode runtime leaks (some ending) =
            setup.protocolReadout (setup.commitRecoverySourceState pair.2.state) ∧
          (fun who => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
            (some ending) who) = fun who => setup.commitRecoveryPayoff utility excludedPayoff who
              ⟨pair.2.state, setup.proposalRecoveryEraseTrace pair.2.trace⟩ := by
  classical
  intro scheduler model certificate profile sourceProfile sourceCertificate start
  have contract : PhaseService.AsyncContract runtime leaks initial horizon scheduler
      (fun _ => activationGap + 1) (fun _ => processingGap + 1) := {
    opportunity := ReservedEpoch.family_opportunity runtime leaks
      (ReservedEpoch.packetCapacity runtime) (ReservedEpoch.completionCycles runtime) tape
        activationGap processingGap gaps plan (serviceGraph_revealRelaxedOrdered setup mode)
          maximal (setup.initialLaw.map encodeInputs)
    inclusion := ReservedEpoch.family_protectedInclusion runtime leaks
      (ReservedEpoch.completionCycles runtime) tape activationGap processingGap gaps plan
        (setup.initialLaw.map encodeInputs)
    completes := ReservedEpoch.family_completesPlay runtime leaks tape plan
      (serviceGraph_revealRelaxedOrdered setup mode) maximal (setup.initialLaw.map encodeInputs) }
  have initializedOrdered : ∀ state ∈ (initial).support, state.Ordered := by
    intro state supported
    obtain ⟨input, _selected, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan input
  generalize workEq : instructionCount witness.checkpoint.residual.tail = work
  induction work using Nat.strong_induction_on generalizing anchor anchorTrace witness with
  | h work ih =>
    cases phases : anchor.execution.application.phases with
    | nil =>
        let native := model.runBehavioralTerminalFrom certificate profile
          ⟨some anchor, anchorTrace⟩
        let joint := native.map fun final => (final, start)
        have sourceEnded : setup.proposalRecoveryProtocol.terminal start.state :=
          witness.checkpoint.terminal phases
        have sourcePure : setup.proposalRecoveryModel.runBehavioralTerminalFrom
            sourceCertificate sourceProfile start = PMF.pure start := by
          exact setup.proposalRecoveryProtocol.randomizedBackwardLaw_of_terminal sourceEnded
        refine ⟨joint, ?_, ?_, ?_⟩
        · simp only [joint, PMF.map_comp, Function.comp_def]
          exact PMF.map_id _
        · rw [sourcePure]
          rw [show joint = native.map (fun final => (final, start)) from rfl, PMF.map_comp]
          exact PMF.map_const _ _
        · intro pair supported
          obtain ⟨final, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          subst pair
          have reached := ((menu).protocol initial horizon
            scheduler).randomizedBackwardLaw_support_reaches
            ⟨some anchor, anchorTrace⟩ final member
          obtain ⟨fuel, nativePath⟩ := reached
          have kept := nativePath.tracePrefix
          have follower := RecoverySourceWitness.prefix_archived_source setup mode runtime leaks
            bounds plan maximal horizon scheduler
          rw [← initial_law_eq setup mode plan] at follower
          obtain ⟨ending, stateEq, next, nextArchived, sourceFuel, sourcePath⟩ :=
            follower anchor anchorTrace witness archived final.trace kept
          have raw := (menu).toRawTrace initial horizon scheduler (stateEq ▸ final.trace)
          have terminal := model.runBehavioralTerminalFrom_support_terminal certificate profile
            ⟨some anchor, anchorTrace⟩ final member
          have actualTerminal : (app).terminal (some ending) := by
            change (app).terminal final.state at terminal
            rwa [stateEq] at terminal
          have nextPhases := (ReservedEpoch.terminal_history_complete runtime leaks tape plan
            (serviceGraph_revealRelaxedOrdered setup mode) maximal (setup.initialLaw.map
              encodeInputs)
              ending raw actualTerminal).1
          have semanticEq := sourcePath.eq_of_terminal (witness.checkpoint.terminal phases)
          have historyEq : start = (⟨_, setup.proposalRecoveryLiftTrace
              (nativeArchiveLabels setup
                (PhaseProposal.sourceArchive ending.execution.network.inputs))
                  next.checkpoint.trace⟩ : setup.proposalRecoveryProtocol.History) := by
            have sameInputs := completed_prefix_inputs setup mode runtime leaks bounds plan
              scheduler anchor ending anchorTrace (stateEq ▸ final.trace) (by
                have represented := StateSymmetry.history_cast stateEq final.trace
                exact (congrArg (fun history :
                  ((menu).protocol initial horizon scheduler).History =>
                    TracePrefix anchorTrace history.trace) represented).mpr kept) phases
            have lifted := congrArg (fun history : setup.commitRecoveryProtocol.History =>
              (⟨history.state, setup.proposalRecoveryLiftTrace
                (nativeArchiveLabels setup
                  (PhaseProposal.sourceArchive ending.execution.network.inputs))
                    history.trace⟩ : setup.proposalRecoveryProtocol.History)) semanticEq
            simpa only [start, sameInputs] using lifted.symm
          obtain ⟨semantic, point, terminal, readout, payoffs⟩ :=
            next.checkpoint.terminal_history runtime leaks plan (setup.initialLaw.map encodeInputs)
              horizon scheduler ending raw nextPhases utility excludedPayoff
          have flags := phaseTerminalExclusion_history runtime leaks plan
            (setup.initialLaw.map encodeInputs) horizon scheduler raw nextPhases
          have semanticState : semantic.state = start.state :=
            point.trans (congrArg History.state historyEq).symm
          refine ⟨ending, next, stateEq, nextPhases, kept, .refl, historyEq, sourceEnded,
            flags.symm, ?_, ?_, ?_, ?_⟩
          · rw [historyEq]
            change some ending.execution.application.entry.excluded =
              some ending.execution.application.current.excluded
            exact congrArg some flags
          · have originalInvariant : (app).Invariant (fun state =>
                ∃ draw ∈ setup.initialLaw.support, state.Invariant (encodeInputs draw)) := by
              constructor
              · intro state owner material valid
                obtain ⟨draw, supported, nativeInvariant⟩ := valid
                exact ⟨draw, supported,
                  (phaseApplication_invariant runtime leaks (encodeInputs draw)).submit
                    state owner material nativeInvariant⟩
              · intro state message updated valid accepted
                obtain ⟨draw, supported, nativeInvariant⟩ := valid
                exact ⟨draw, supported,
                  (phaseApplication_invariant runtime leaks (encodeInputs draw)).handle
                    state message updated nativeInvariant accepted⟩
              · intro state command updated valid selected
                obtain ⟨draw, supported, nativeInvariant⟩ := valid
                exact ⟨draw, supported,
                  (phaseApplication_invariant runtime leaks (encodeInputs draw)).environment
                    state command updated nativeInvariant selected⟩
            have original : ∃ draw ∈ setup.initialLaw.support,
                ending.execution.application.Invariant (encodeInputs draw) := by
              apply originalInvariant.history initial horizon scheduler ?_ raw
              intro state supported
              obtain ⟨input, selected, rfl⟩ := PMF.support_map .. ▸ supported
              obtain ⟨draw, drawSupport, rfl⟩ := PMF.support_map .. ▸ selected
              exact ⟨draw, drawSupport,
                (PhaseRuntimeState.initial_invariant plan (encodeInputs draw)).1⟩
            obtain ⟨draw, drawSupport, nativeInvariant⟩ := original
            obtain ⟨terminalState, terminalRead⟩ := ProtocolState.exists_readout_of_terminal
              setup.program (next.checkpoint.residual.lift
                (ProtocolState.entry next.checkpoint.residual.tail next.checkpoint.source))
                  (next.checkpoint.terminal nextPhases)
            have decoded : decodeState? (terminalRefs setup.program)
                ending.execution.application.current.native.config.store = some terminalState :=
              (next.checkpoint.terminal_readback nextPhases next.stored).trans terminalRead
            have terminalAgree : (terminalRefs setup.program).Agrees terminalState
                ending.execution.application.current.native.config.store :=
              decodeState?_agrees (terminalRefs setup.program) _ terminalState decoded
            have terminalInputs :
                (ContextRefs.initial setup.context (outputLayout setup.program)).Agrees
                  (initialState setup.program terminalState)
                    ending.execution.application.current.native.config.store :=
              terminalRefsWith_initial_agrees setup.program
              (ContextRefs.initial setup.context (outputLayout setup.program))
                (outputEmbedding setup.program).ref _ terminalState
                  terminalAgree
            have originalInputs :
                (ContextRefs.initial setup.context (outputLayout setup.program)).Agrees draw
                  ending.execution.application.current.native.config.store :=
              ContextRefs.initial_agrees (outputLayout setup.program) draw
              ending.execution.application.current.native.config.store (fun input => by
                rw [EventGraph.Config.store_input, nativeInvariant.active.reachable.inputs_eq])
            have sameOriginal : initialState setup.program terminalState = draw := by
              funext name cell ref
              have sameValue := Option.some.inj
                ((terminalInputs ref).symm.trans (originalInputs ref))
              cases cell <;> exact sameValue
            refine ⟨draw, drawSupport, nativeInvariant.active.reachable.inputs_eq, ?_⟩
            have read : setup.protocolReadout (setup.commitRecoverySourceState start.state) =
                some terminalState := by
              rw [← semanticState, point]
              exact terminalRead
            rw [read, Option.map_some, sameOriginal]
          · simpa only [semanticState] using readout
          · simpa only [Setup.commitRecoveryPayoff, semanticState] using payoffs
    | cons phase remaining =>
        have installed : anchor.execution.application.phases.head? = some phase := by
          simp only [phases, List.head?_cons]
        let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
          match history.state with
          | none => False
          | some control => control.execution.application.attempt ≠
            anchor.execution.application.attempt
        let stoppedLaw := model.runBehavioralUntil certificate profile stopped
          ⟨some anchor, anchorTrace⟩
        have sameStopKernel (other :
            ((menu).protocol initial horizon scheduler).History → Prop)
            (same : ∀ history, stopped history = other history) :
            stoppedLaw = model.runBehavioralUntil
              ((menu).bounded initial horizon scheduler).wellFoundedHistories profile other
                ⟨some anchor, anchorTrace⟩ := by
          apply congrArg (fun stop => model.runBehavioralUntil certificate profile stop
            ⟨some anchor, anchorTrace⟩)
          exact funext same
        let stepLaw := setup.proposalRecoveryModel.runBehavioralFrom sourceProfile
          (phase.high - phase.low) start
        have closing : ∀ final ∈ stoppedLaw.support,
            ∃ (ending before : (app).Control)
              (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
              (actions : Player → Option (app).Action)
              (legal : ((menu).protocol initial horizon scheduler).Legal (some before) actions)
              (realized : some ending ∈ ((app).transition initial horizon scheduler
                (some before) actions).support)
              (raw : RecoveryState graph) (rest : List (RuntimePhase graph))
              (beforeWitness : RecoverySourceWitness setup mode plan before.execution.application)
              (rawWitness : RecoverySourceWitness setup mode plan
                ({before.execution.application with current := raw} : PhaseRuntimeState graph)),
              final.state = some ending ∧ ending.actor = none ∧
              ending.execution.application.attempt ≠ anchor.execution.application.attempt ∧
              TracePrefix anchorTrace prior ∧
              TracePrefix (prior.extend actions legal realized) final.trace ∧
              ∃ sameAttempt : before.execution.application.attempt =
                  anchor.execution.application.attempt,
              before.execution.application.phases = phase :: rest ∧
              phase.Finished (phase.drain raw) ∧
              (phase.drain raw).FailureCoverage ∧
              (phase.drain raw).excluded = ending.execution.application.current.excluded ∧
              ending.execution.application =
                ({before.execution.application with current := raw} : PhaseRuntimeState
                  graph).normalize ∧
              PhaseClosingEffect runtime leaks before.execution ending.execution raw ∧
              beforeWitness.checkpoint.ArchivedProposals before.execution.network.inputs ∧
              (⟨_, beforeWitness.checkpoint.trace⟩ : setup.commitRecoveryProtocol.History) =
                ⟨_, witness.checkpoint.trace⟩ ∧
              rawWitness.checkpoint = beforeWitness.checkpoint.transfer
                (other := {before.execution.application with current := raw}) rfl rfl rfl ∧
              ∃ saved : before.execution.application.entry = anchor.execution.application.entry,
                beforeWitness.checkpoint = witness.checkpoint.transfer saved
                  (congrArg CommitAttemptId.generation sameAttempt)
                  (congrArg CommitAttemptId.phase sameAttempt) := by
          intro final supported
          obtain ⟨ending, stateEq, changed, nextIdle, snapshot, finished, _binding, coverage,
            imageE, _accepted, before, prior, actions, legal, realized, raw, fromAnchor, toFinal,
            sameAttempt, beforeInstalled, snapshotEq, normalized, effect⟩ :=
            phase_attempt_stopped_receipt_snapshot runtime leaks (menu) plan
              (setup.initialLaw.map encodeInputs) horizon scheduler
                (fun _ => activationGap + 1) (fun _ => processingGap + 1) contract profile
                  anchor anchorTrace phase (Option.mem_def.mpr installed) final (by
                    refine (congrArg (fun law : PMF
                      (((menu).protocol initial horizon scheduler).History) =>
                        final ∈ law.support) (sameStopKernel _ ?_)).mp supported
                    intro history
                    rcases history with ⟨state, trace⟩
                    cases state <;> rfl)
          subst snapshot
          obtain ⟨rest, beforePhases⟩ :=
            List.head?_eq_some_iff.mp (Option.mem_def.mp beforeInstalled)
          obtain ⟨beforeWitness, beforeArchived, sameSemanticHistory,
            ⟨sameEntry, beforeCheckpoint⟩⟩ :=
            RecoverySourceWitness.prefix_at_same_attempt setup mode runtime leaks bounds
              plan maximal
              scheduler
              anchor before anchorTrace prior fromAnchor sameAttempt witness archived
          have changedBefore : ending.execution.application.attempt ≠
              before.execution.application.attempt := fun equal => changed (equal.trans sameAttempt)
          obtain ⟨rawWitness, rawCheckpoint, _rawHistory⟩ :=
            RecoverySourceWitness.raw_closing_checkpoint setup mode runtime leaks plan before ending
              beforeWitness raw
              effect changedBefore
          exact ⟨ending, before, prior, actions, legal, realized, raw, rest, beforeWitness,
            rawWitness, stateEq, nextIdle, changed, fromAnchor, toFinal, sameAttempt, beforePhases,
            finished, coverage, imageE, normalized, effect, beforeArchived, sameSemanticHistory,
            rawCheckpoint, sameEntry, beforeCheckpoint⟩
        let continuation : (((menu).protocol initial horizon scheduler).History ×
            setup.proposalRecoveryProtocol.History) → Prop := fun pair =>
              ∃ (ending : (app).Control)
                (next : RecoverySourceWitness setup mode plan ending.execution.application),
                pair.1.state = some ending ∧ ending.actor = none ∧
                TracePrefix anchorTrace pair.1.trace ∧
                ending.execution.application.entry.excluded =
                  ending.execution.application.current.excluded ∧
                (∀ who, ∀ record ∈ ending.execution.recall who,
                  record.beforeView.application.2.attempt ≠ ending.execution.application.attempt) ∧
                next.checkpoint.ArchivedProposals ending.execution.network.inputs ∧
                (∀ who, who ∉ ending.execution.application.current.excluded →
                  next.checkpoint.source.BindingsHoldValues who) ∧
                instructionCount next.checkpoint.residual.tail < work ∧
                TracePrefix start.trace
                  (setup.proposalRecoveryLiftTrace
                    (nativeArchiveLabels setup
                      (PhaseProposal.sourceArchive ending.execution.network.inputs))
                        next.checkpoint.trace) ∧
                setup.proposalRecoveryModel.runBehavioralTerminalFrom
                    sourceCertificate sourceProfile pair.2 =
                  setup.proposalRecoveryModel.runBehavioralTerminalFrom sourceCertificate
                    sourceProfile ⟨_, setup.proposalRecoveryLiftTrace
                      (nativeArchiveLabels setup
                        (PhaseProposal.sourceArchive ending.execution.network.inputs))
                          next.checkpoint.trace⟩
        have completedContinuation
            (pair : ((menu).protocol initial horizon scheduler).History ×
              setup.proposalRecoveryProtocol.History)
            (stoppedSupport : pair.1 ∈ stoppedLaw.support)
            (sourceMember : pair.2 ∈ stepLaw.support)
            (ending before : (app).Control)
            (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
            (beforeWitness : RecoverySourceWitness setup mode plan before.execution.application)
            (raw : RecoveryState graph)
            (rawWitness : RecoverySourceWitness setup mode plan
              ({before.execution.application with current := raw} : PhaseRuntimeState graph))
            (rest : List (RuntimePhase graph))
            (completed : RecoverySourceWitness setup mode plan
              (⟨rest, before.execution.application.generation, phase.drain raw, phase.drain raw,
                before.execution.application.retired⟩ : PhaseRuntimeState graph))
            (finalState : pair.1.state = some ending) (nextIdle : ending.actor = none)
            (changed : ending.execution.application.attempt ≠ anchor.execution.application.attempt)
            (sameAttempt : before.execution.application.attempt =
              anchor.execution.application.attempt)
            (beforePhases : before.execution.application.phases = phase :: rest)
            (finished : phase.Finished (phase.drain raw))
            (imageE : (phase.drain raw).excluded = ending.execution.application.current.excluded)
            (normalized : ending.execution.application =
              ({before.execution.application with current := raw} : PhaseRuntimeState
                graph).normalize)
            (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
            (beforeArchived : beforeWitness.checkpoint.ArchivedProposals
              before.execution.network.inputs)
            (rawCheckpoint : rawWitness.checkpoint = beforeWitness.checkpoint.transfer
              (other := {before.execution.application with current := raw}) rfl rfl rfl)
            (phaseDelta : rawWitness.checkpoint.ProposalDelta plan completed.checkpoint)
            (completedProper : ∀ who, who ∉ (phase.drain raw).excluded →
              completed.checkpoint.source.BindingsHoldValues who)
            (exactHistory : pair.2 = ⟨_, setup.proposalRecoveryLiftTrace
              (nativeArchiveLabels setup (PhaseProposal.sourceArchive
                ending.execution.network.inputs))
                completed.checkpoint.trace⟩)
            (noRetry : ¬ (phase.kind = .commitment ∧
              (((phase.drain raw).excluded \ before.execution.application.entry.excluded) ∩
                phase.owners).Nonempty)) : continuation pair := by
          have settled : ending.execution.application = PhaseRuntimeState.settle rest
              before.execution.application.generation (phase.drain raw) (phase.drain raw)
                before.execution.application.retired := by
            rw [normalized]
            change PhaseRuntimeState.settle before.execution.application.phases
              before.execution.application.generation before.execution.application.entry
                raw before.execution.application.retired = _
            rw [beforePhases, PhaseRuntimeState.settle_clean phase rest
              before.execution.application.generation before.execution.application.entry
                raw before.execution.application.retired finished noRetry]
          obtain ⟨next, nextPath, sourceKernel, _nextDelta, nextArchive⟩ :=
            RecoverySourceWitness.completed_normalized_archived_source setup mode runtime leaks
              bounds plan maximal horizon scheduler before ending prior beforeWitness beforeArchived
                raw effect rawWitness rawCheckpoint phase rest beforePhases finished normalized
                  settled completed phaseDelta sourceCertificate sourceProfile
          let finalWitness : RecoverySourceWitness setup mode plan
              ending.execution.application := settled.symm ▸ next
          have finalHistory := witness_cast_history setup mode plan settled.symm next
          have finalLifted := congrArg (fun history : setup.commitRecoveryProtocol.History =>
            (⟨history.state, setup.proposalRecoveryLiftTrace
              (nativeArchiveLabels setup
                (PhaseProposal.sourceArchive ending.execution.network.inputs))
                  history.trace⟩ : setup.proposalRecoveryProtocol.History)) finalHistory
          have nextEntry : ending.execution.application.entry.excluded =
              ending.execution.application.current.excluded := by
            rw [settled]
            exact PhaseRuntimeState.settle_entry_excluded_of_same rest
              before.execution.application.generation (phase.drain raw) (phase.drain raw)
                before.execution.application.retired rfl
          obtain ⟨normalFuel, normalPath⟩ := nextPath
          have preserved := (completed.checkpoint.fresh_normalization_source_law mode
            rest before.execution.application.generation (phase.drain raw)
              before.execution.application.retired completed.order.frontier next.checkpoint
                normalPath sourceProfile
                  (nativeArchiveLabels setup
                    (PhaseProposal.sourceArchive ending.execution.network.inputs))).2
          have nextProper : ∀ who,
              who ∉ ending.execution.application.current.excluded →
                finalWitness.checkpoint.source.BindingsHoldValues who := by
            intro who active
            have surviving : who ∉ (phase.drain raw).excluded := imageE.symm ▸ active
            have live : next.checkpoint.source.BindingsHoldValues who :=
              preserved who surviving (completedProper who surviving)
            apply (witness_cast_bindings setup mode plan settled.symm next who).mpr
            intro name payload cell
            exact live cell
          have nativePrefix := model.runBehavioralUntil_support_prefix certificate
            profile stopped ⟨some anchor, anchorTrace⟩ pair.1 stoppedSupport
          have nextFresh : ∀ who, ∀ record ∈ ending.execution.recall who,
              record.beforeView.application.2.attempt ≠
                ending.execution.application.attempt := by
            have different : before.execution.application.attempt ≠
                ending.execution.application.attempt :=
              fun equal => changed (equal.symm.trans sameAttempt)
            rcases effect with ⟨id, message, result, found, moved, handled, rawEq⟩ |
                ⟨command, result, moved, sampled, rawEq⟩
            · exact phase_ownRecall_fresh_after_environment runtime leaks initial
                initializedOrdered horizon scheduler before
                  ((menu).toRawTrace initial horizon scheduler prior) ending.execution
                    (.include id) moved different
            · exact phase_ownRecall_fresh_after_environment runtime leaks initial
                initializedOrdered horizon scheduler before
                  ((menu).toRawTrace initial horizon scheduler prior) ending.execution
                    (.application command) moved different
          have sourcePrefix : TracePrefix start.trace
              (setup.proposalRecoveryLiftTrace
                (nativeArchiveLabels setup
                  (PhaseProposal.sourceArchive ending.execution.network.inputs))
                    finalWitness.checkpoint.trace) := by
            have onward := setup.proposalRecoveryLiftTrace_prefix
              (nativeArchiveLabels setup
                (PhaseProposal.sourceArchive ending.execution.network.inputs))
                  normalPath.tracePrefix
            have initialKept := (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin
              sourceProfile (phase.high - phase.low) start pair.2 sourceMember).tracePrefix
            rw [exactHistory] at initialKept
            change TracePrefix start.trace
              (⟨_, setup.proposalRecoveryLiftTrace
                (nativeArchiveLabels setup
                  (PhaseProposal.sourceArchive ending.execution.network.inputs))
                    finalWitness.checkpoint.trace⟩ : setup.proposalRecoveryProtocol.History).trace
            rw [finalLifted]
            exact initialKept.trans onward
          have smaller : instructionCount finalWitness.checkpoint.residual.tail < work := by
            let endingTrace : ((menu).protocol initial horizon scheduler).Trace
                (some ending) := finalState ▸ pair.1.trace
            have retained : TracePrefix anchorTrace endingTrace := by
              exact (congrArg (fun history :
                ((menu).protocol initial horizon scheduler).History =>
                  TracePrefix anchorTrace history.trace)
                    (StateSymmetry.history_cast finalState pair.1.trace)).mpr nativePrefix
            have ordered := (phaseApplication_seedOrder runtime leaks).history initial
              horizon scheduler initializedOrdered
                ((menu).toRawTrace initial horizon scheduler anchorTrace)
            have progress := phase_attempt_progress_of_prefix runtime leaks (menu)
              initial initializedOrdered horizon scheduler anchor ending anchorTrace
                endingTrace retained ordered
            have finalGeneration :=
              (phaseProposal_fresh_settle_completion_origin rest
                before.execution.application.generation (phase.drain raw)
                  before.execution.application.retired).1
            have sameGeneration : ending.execution.application.attempt.generation =
                anchor.execution.application.attempt.generation := by
              change ending.execution.application.generation =
                anchor.execution.application.generation
              exact (congrArg PhaseRuntimeState.generation settled).trans
                (finalGeneration.trans (congrArg CommitAttemptId.generation sameAttempt))
            have strict : anchor.execution.application.attempt.phase <
                ending.execution.application.attempt.phase := by
              have different : ending.execution.application.attempt.phase ≠
                  anchor.execution.application.attempt.phase := by
                intro equal
                apply changed
                have extensional (first last : CommitAttemptId)
                    (phases : first.phase = last.phase)
                    (generations : first.generation = last.generation) : first = last := by
                  cases first
                  cases last
                  cases phases
                  cases generations
                  rfl
                exact extensional _ _ equal sameGeneration
              omega
            have firstCount := witness.checkpoint.compiled.countEq
            have lastCount := finalWitness.checkpoint.compiled.countEq
            change anchor.execution.application.attempt.phase +
              eventCount witness.checkpoint.residual.tail =
                eventCount setup.program at firstCount
            change ending.execution.application.attempt.phase +
              eventCount finalWitness.checkpoint.residual.tail =
                eventCount setup.program at lastCount
            simp only [eventCount_eq_instructionCount] at firstCount lastCount
            change instructionCount witness.checkpoint.residual.tail = work
              at workEq
            omega
          have nextArchived : finalWitness.checkpoint.ArchivedProposals
              ending.execution.network.inputs :=
            (witness_cast_archive setup mode plan settled.symm next
              ending.execution.network.inputs).mpr nextArchive
          refine ⟨ending, finalWitness, finalState, nextIdle, nativePrefix, nextEntry,
            nextFresh, nextArchived, nextProper, smaller, sourcePrefix, ?_⟩
          rw [exactHistory]
          rw [finalLifted]
          exact sourceKernel
        have phaseLaw : ∃ phaseJoint : PMF
            (((menu).protocol initial horizon scheduler).History ×
              setup.proposalRecoveryProtocol.History),
            phaseJoint.map Prod.fst = stoppedLaw ∧
            phaseJoint.map Prod.snd = stepLaw ∧
            ∀ pair ∈ phaseJoint.support, continuation pair := by
          cases kind : phase.kind with
          | commitment =>
              obtain ⟨Δ, P, block, suffix, cursor, size, sourceEq, image, sourceImage,
                sourceLaw, selected⟩ :=
                witness.ordinary_installed_binding_history setup mode runtime leaks bounds plan
                  complete covered maximal values fullValues tape activationGap processingGap
                    gaps margin capacity anchor idle anchorTrace phase installed kind entryExcluded
                      fresh archived proper
              let phaseJoint := stoppedLaw.map fun final => (final, sourceImage final)
              refine ⟨phaseJoint, ?_, ?_, ?_⟩
              · simp only [phaseJoint, PMF.map_comp, Function.comp_def]
                exact PMF.map_id _
              · simp only [phaseJoint, PMF.map_comp, Function.comp_def]
                convert sourceLaw using 1
                · apply congrArg (PMF.map sourceImage)
                  apply sameStopKernel
                  intro history
                  rcases history with ⟨state, trace⟩
                  cases state <;> rfl
                · simp only [stepLaw, size, sourceEq, sourceProfile, start]
              · intro pair supported
                obtain ⟨final, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
                subst pair
                obtain ⟨ending, before, prior, actions, legal, realized, raw, rest, selectedCP,
                  finalState, fromAnchor, toFinal, effect, sameAttempt, beforePhases, finished,
                  imageEq, settled, unchangedE,
                  archiveEq, ⟨selectedFuel, selectedPath⟩, selectedWord, semanticEq,
                  historyEq, selectedProper⟩ := selected final
                    (by
                      refine (congrArg (fun law : PMF
                        (((menu).protocol initial horizon scheduler).History) =>
                          final ∈ law.support) (sameStopKernel _ ?_)).mp member
                      intro history
                      rcases history with ⟨state, trace⟩
                      cases state <;> rfl)
                have priorToFinal : TracePrefix prior final.trace :=
                  (TracePrefix.extend (.refl : TracePrefix prior prior) actions legal
                    realized).trans
                    toFinal
                have priorShorter : prior.length < final.trace.length := by
                  have longer := toFinal.length_le
                  change prior.length + 1 ≤ final.trace.length at longer
                  omega
                obtain ⟨beforeWitness, beforeArchived, sameSemanticHistory,
                  ⟨sameEntry, beforeCheckpoint⟩⟩ :=
                  RecoverySourceWitness.prefix_at_same_attempt setup mode runtime leaks bounds
                    plan maximal scheduler
                    anchor before anchorTrace prior fromAnchor sameAttempt witness archived
                have closeMeta : ending.execution.application.attempt ≠
                    before.execution.application.attempt ∧ ending.actor = none := by
                  obtain ⟨last, lastState, changed, nextIdle, _rest⟩ :=
                    phase_attempt_stopped_receipt_snapshot runtime leaks (menu) plan
                      (setup.initialLaw.map encodeInputs) horizon scheduler
                        (fun _ => activationGap + 1) (fun _ => processingGap + 1) contract
                          profile anchor anchorTrace phase (Option.mem_def.mpr installed) final
                            (by
                              refine (congrArg (fun law : PMF
                                (((menu).protocol initial horizon scheduler).History) =>
                                  final ∈ law.support) (sameStopKernel _ ?_)).mp member
                              intro history
                              rcases history with ⟨state, trace⟩
                              cases state <;> rfl)
                  have equal := Option.some.inj (lastState.symm.trans finalState)
                  cases equal
                  exact ⟨fun same => changed (same.trans sameAttempt), nextIdle⟩
                have changed := closeMeta.1
                obtain ⟨rawWitness, rawCheckpoint, rawHistory⟩ :=
                  RecoverySourceWitness.raw_closing_checkpoint setup mode runtime leaks
                  plan before ending beforeWitness raw effect changed
                have clean : ¬ (((phase.drain raw).excluded \
                    before.execution.application.entry.excluded) ∩ phase.owners).Nonempty := by
                  have imageE : (phase.drain raw).excluded =
                      before.execution.application.entry.excluded := by
                    rw [← imageEq, unchangedE, sameEntry, entryExcluded]
                  rw [imageE]
                  simp only [Finset.sdiff_self, Finset.empty_inter, Finset.not_nonempty_empty,
                    not_false_eq_true]
                obtain ⟨completed, completedPoint, ⟨fuel, completedPath, completedWord⟩,
                  delta, normalized⟩ := rawWitness.completed_binding_history maximal phase rest
                    beforePhases kind finished clean
                have sourceMemberCursor : sourceImage final ∈
                    (setup.proposalRecoveryModel.runBehavioralFrom sourceProfile block.length
                      ⟨some cursor.current, cursor.trace⟩).support := by
                  rw [← sourceLaw]
                  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final,
                    (by
                      refine (congrArg (fun law : PMF
                        (((menu).protocol initial horizon scheduler).History) =>
                          final ∈ law.support) (sameStopKernel _ ?_)).mp member
                      intro history
                      rcases history with ⟨state, trace⟩
                      cases state <;> rfl), rfl⟩
                have sourceMember : sourceImage final ∈ stepLaw.support := by
                  change sourceImage final ∈ (setup.proposalRecoveryModel.runBehavioralFrom
                    sourceProfile (phase.high - phase.low) start).support
                  rw [← size]
                  have cursorStart : (⟨some cursor.current, cursor.trace⟩ :
                      setup.proposalRecoveryProtocol.History) = start := sourceEq
                  rw [← cursorStart]
                  exact sourceMemberCursor
                have rawStart : (⟨_, rawWitness.checkpoint.trace⟩ :
                    setup.commitRecoveryProtocol.History) = ⟨_, witness.checkpoint.trace⟩ :=
                  rawHistory.trans sameSemanticHistory
                have rawWord : rawWitness.checkpoint.commitInstructionWord (phase.drain
                  raw).native =
                    witness.checkpoint.commitInstructionWord (phase.drain raw).native := by
                  rw [rawCheckpoint, beforeCheckpoint]
                  simp only [RecoverySourceCheckpoint.transfer,
                    RecoverySourceCheckpoint.commitInstructionWord]
                  rw [congrArg RecoveryState.excluded sameEntry]
                have word : setup.recoveryJointRecall selectedCP.trace =
                    setup.recoveryJointRecall completed.checkpoint.trace := by
                  have decoded := congrArg (fun history : setup.commitRecoveryProtocol.History =>
                    setup.recoveryJointRecall history.trace) semanticEq
                  have original := congrArg (fun history : setup.commitRecoveryProtocol.History =>
                    setup.recoveryJointRecall history.trace) rawStart
                  rw [completedWord, rawWord, original]
                  exact decoded.symm.trans selectedWord
                have path := completedPath
                rw [rawStart] at path
                let first := CommitRecoveryState.atPoint
                  (witness.checkpoint.residual.lift
                    (ProtocolState.entry witness.checkpoint.residual.tail
                      witness.checkpoint.source))
                      anchor.execution.application.entry.excluded
                        anchor.execution.application.generation
                have cursorState : cursor.current = first :=
                  Option.some.inj (congrArg History.state sourceEq)
                have positive : 0 < block.length := by
                  rw [size]
                  have nonempty := phase.nonempty
                  omega
                have committing : ProtocolState.atCommit setup.program first.point = true := by
                  rw [← cursorState, cursor.point, cursor.origin.atCommit_lift]
                  cases block with
                  | nil => exact (Nat.not_lt_zero _ positive).elim
                  | commit => rfl
                have window : block.length + ProtocolState.commitEnd setup.program first.point ≤
                    ProtocolState.remaining setup.program first.point := by
                  rw [← cursorState, cursor.point, cursor.origin.commitEnd_lift,
                    cursor.origin.remaining_lift]
                  exact block.length_le_commit_window suffix cursor.source
                have reached := setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin
                  sourceProfile block.length ⟨some cursor.current, cursor.trace⟩
                    (sourceImage final) sourceMemberCursor
                have length := reached.trace_length_le_add
                have initialLength := congrArg (fun history :
                  setup.proposalRecoveryProtocol.History =>
                  history.trace.length) sourceEq
                simp only [setup.proposalRecoveryLiftTrace_length] at initialLength
                have finalLength := congrArg (fun history : setup.commitRecoveryProtocol.History =>
                  history.trace.length) semanticEq
                simp only [setup.proposalRecoveryEraseTrace_length] at finalLength
                change (sourceImage final).trace.length = selectedCP.trace.length at finalLength
                change cursor.trace.length = witness.checkpoint.trace.length at initialLength
                change (sourceImage final).trace.length ≤ cursor.trace.length + block.length
                  at length
                have within : selectedCP.trace.length + ProtocolState.commitEnd setup.program
                    first.point ≤ witness.checkpoint.trace.length +
                      ProtocolState.remaining setup.program first.point := by
                  omega
                have semantic : (⟨_, selectedCP.trace⟩ : setup.commitRecoveryProtocol.History) =
                    ⟨_, completed.checkpoint.trace⟩ :=
                  setup.commitRecovery_history_eq_of_commit_window first witness.checkpoint.trace
                    committing selectedCP.trace completed.checkpoint.trace selectedPath path word
                      within
                have exactHistory : sourceImage final = ⟨_, setup.proposalRecoveryLiftTrace
                    (nativeArchiveLabels setup
                      (PhaseProposal.sourceArchive ending.execution.network.inputs))
                        completed.checkpoint.trace⟩ :=
                  historyEq.trans (congrArg (fun history : setup.commitRecoveryProtocol.History =>
                    (⟨history.state, setup.proposalRecoveryLiftTrace
                      (nativeArchiveLabels setup
                        (PhaseProposal.sourceArchive ending.execution.network.inputs))
                          history.trace⟩ :
                          setup.proposalRecoveryProtocol.History)) semantic)
                have completedProper : ∀ who, who ∉ (phase.drain raw).excluded →
                    completed.checkpoint.source.BindingsHoldValues who := by
                  intro who active
                  have live := (selectedCP.origin.bindingsHoldValues_lift who _).mpr
                    ((ProtocolState.bindingsHoldValues_entry who selectedCP.residual.tail
                      selectedCP.source).mpr (selectedProper who active))
                  have points := congrArg CommitRecoveryState.point
                    (Option.some.inj (congrArg History.state semantic))
                  change selectedCP.residual.lift
                      (ProtocolState.entry selectedCP.residual.tail selectedCP.source) =
                    completed.checkpoint.residual.lift
                      (ProtocolState.entry completed.checkpoint.residual.tail
                        completed.checkpoint.source) at points
                  rw [points] at live
                  intro name payload cell
                  exact (ProtocolState.bindingsHoldValues_entry who
                    completed.checkpoint.residual.tail
                    completed.checkpoint.source).mp
                      ((completed.checkpoint.origin.bindingsHoldValues_lift who _).mp live) cell
                have imageExcluded : (phase.drain raw).excluded =
                    ending.execution.application.current.excluded := by
                  rw [settled]
                  exact (phaseProposal_fresh_settle_completion_origin rest
                    before.execution.application.generation (phase.drain raw)
                      before.execution.application.retired).2.2.1.symm
                exact completedContinuation (final, sourceImage final) member sourceMember ending
                  before
                  prior beforeWitness raw rawWitness rest completed finalState closeMeta.2
                    (fun same => changed (same.trans sameAttempt.symm)) sameAttempt beforePhases
                      finished imageExcluded (settled.trans normalized.symm) effect beforeArchived
                        rawCheckpoint delta completedProper exactHistory
                          (fun failure => clean failure.2)
          | reveal =>
              have anchorShape : (⟨anchor.remaining, none, anchor.execution⟩ : (app).Control) =
                  anchor := by
                rcases anchor with ⟨remaining, actor, execution⟩
                cases idle
                rfl
              let installedTrace : ((menu).protocol initial horizon scheduler).Trace
                  (some ⟨anchor.remaining, none, anchor.execution⟩) :=
                (congrArg some anchorShape.symm) ▸ anchorTrace
              have installedHistory := StateSymmetry.history_cast
                (congrArg some anchorShape.symm) anchorTrace
              have rawTrace := (menu).toRawTrace initial horizon scheduler anchorTrace
              have geometry := (phaseApplication_quiescent runtime leaks
                  (serviceGraph_revealRelaxedOrdered setup mode)).history initial horizon scheduler
                (fun state supported => by
                  obtain ⟨input, _member, rfl⟩ := PMF.support_map .. ▸ supported
                  exact phaseApplication_initial_quiescent plan
                    (serviceGraph_revealRelaxedOrdered setup mode) maximal input) rawTrace
              have living := (phaseApplication_live runtime leaks).history initial horizon scheduler
                (fun state supported => by
                  obtain ⟨input, _member, rfl⟩ := PMF.support_map .. ▸ supported
                  exact ⟨PhaseRuntimeState.initial_frontier plan input,
                    PhaseRuntimeState.initial_live plan input⟩) rawTrace
              have observerExists : ∃ who, who ∉ anchor.execution.application.current.excluded := by
                rcases anchor.execution.application.request_or_sample geometry.1 living.2
                    geometry.2.2 (by rw [phases]; exact List.cons_ne_nil _ _) with
                    ⟨who, event, requested⟩ | ⟨actual, event, actualInstalled, sampleKind, _rest⟩
                · exact ⟨who, requested.2.2.2.2⟩
                · have equal : actual = phase := Option.some.inj
                    (actualInstalled.symm.trans installed)
                  subst actual
                  cases kind.symm.trans sampleKind
              obtain ⟨observer, observerActive⟩ := observerExists
              have localPhase : ∀ final ∈ stoppedLaw.support,
                  ∃ selected : setup.proposalRecoveryProtocol.History,
                    stepLaw = PMF.pure selected ∧ continuation (final, selected) := by
                intro final stoppedSupport
                obtain ⟨ending, before, prior, actions, legal, realized, raw, rest,
                  beforeWitness, rawWitness, finalState, nextIdle, changed, fromAnchor,
                  toFinal, sameAttempt, beforePhases, finished, coverage, imageE, normalized,
                  effect, beforeArchived, sameHistory, rawCheckpoint,
                  ⟨sameEntry, beforeCheckpoint⟩⟩ := closing final stoppedSupport
                let labels := nativeArchiveLabels setup
                  (PhaseProposal.sourceArchive ending.execution.network.inputs)
                have rows := phaseProposalUnflagged_fresh_publication_rows setup mode runtime leaks
                  bounds plan covered maximal values tape activationGap processingGap gaps margin
                    anchor.remaining anchor.execution installedTrace
                      witness.checkpoint witness.stored proper fresh before ending prior actions
                        legal realized (by
                          exact (congrArg (fun history :
                            ((menu).protocol initial horizon scheduler).History =>
                              TracePrefix history.trace prior) installedHistory).mpr fromAnchor)
                          sameAttempt
                          changed phase (Option.mem_def.mpr installed) kind raw effect coverage
                            imageE
                            final (by
                              rw [installedHistory]
                              refine (congrArg (fun law : PMF
                                (((menu).protocol initial horizon scheduler).History) =>
                                  final ∈ law.support) (sameStopKernel _ ?_)).mp stoppedSupport
                              intro history
                              rcases history with ⟨state, trace⟩
                              cases state <;> rfl) finalState
                              toFinal
                have truth : ∀ event ∈ phase.events, ∀ owner, (graph).actor? event = some owner →
                    owner ∉ before.execution.application.entry.excluded →
                    owner ∉ (phase.drain raw).native.failureOwnersBefore event.val →
                    ∀ (payload : L.Ty) (publication : (graph).outputLayout event = .publication
                      payload)
                      (action : ((graph).outputLayout event).Action),
                    (⟨event, action⟩ : (graph).Completion) ∈ (phase.drain
                      raw).native.config.history →
                      cast (congrArg EventField.Action publication) action = true := by
                  intro event inside owner acting active scan payload publication action recorded
                  have anchorActive : owner ∉ anchor.execution.application.current.excluded := by
                    rw [← entryExcluded, ← congrArg RecoveryState.excluded sameEntry]
                    exact active
                  exact (PhaseProposal.publicationDiscloses_cast publication action).trans
                    (rows event inside owner acting anchorActive scan action recorded)
                obtain ⟨completed, ⟨fuel, path⟩, publicPath, law, delta⟩ :=
                  rawWitness.ordinary_completed_reveal_history maximal phase rest beforePhases
                    kind finished truth values labels
                have closingInputs : ending.execution.network.inputs =
                    before.execution.network.inputs := by
                  rcases effect with ⟨id, message, result, found, moved, handled, rawEq⟩ |
                      ⟨command, result, moved, sampled, rawEq⟩
                  · exact (app).environmentStep_inputs before.execution ending.execution
                      (.include id) moved
                  · exact (app).environmentStep_inputs before.execution ending.execution
                      (.application command) moved
                have metadata := phaseProposal_same_attempt_archive_metadata setup mode runtime
                  leaks bounds plan horizon scheduler anchor before anchorTrace prior fromAnchor
                    sameAttempt.symm
                have oldBuckets : (PhaseProposal.sourceArchive
                  ending.execution.network.inputs).filter
                      (fun proposal => proposal.address.phase <
                        anchor.execution.application.attempt.phase) =
                    (PhaseProposal.sourceArchive anchor.execution.network.inputs).filter
                      (fun proposal => proposal.address.phase <
                        anchor.execution.application.attempt.phase) := by
                  rw [closingInputs]
                  exact metadata.2.2
                have oldLabels := setup.proposalRecoveryLiftTrace_eq_of_withheld_labels labels
                  (nativeArchiveLabels setup
                    (PhaseProposal.sourceArchive anchor.execution.network.inputs))
                      witness.checkpoint.trace (by
                        intro before after priorTrace joint legal supported retained owner move
                          selected revealing
                        cases before with
                        | none =>
                            have offered := legal.2 owner
                            rw [selected] at offered
                            exact False.elim offered.1
                        | some state =>
                            have offered := legal.2 owner
                            rw [selected] at offered
                            obtain ⟨author, name, action⟩ := revealing
                            have notCommit := ProtocolState.not_atCommit_of_recoveryAvailable_reveal
                              owner setup.program state.point move offered.2
                                ⟨author, name, false, action⟩
                            have earlier := setup.proposalRecovery_noncommit_prefix_rank_lt observer
                              state _ priorTrace witness.checkpoint.trace joint legal supported
                                retained
                                notCommit (by
                                  change observer ∉ anchor.execution.application.entry.excluded
                                  rwa [entryExcluded])
                            exact nativeArchiveLabels_eq_of_earlier setup _ _
                              anchor.execution.application.attempt.phase oldBuckets _ owner state
                                rfl
                                (earlier.2.trans_eq witness.checkpoint.saved_position))
                have rawStart : (⟨_, setup.proposalRecoveryLiftTrace labels
                    rawWitness.checkpoint.trace⟩ : setup.proposalRecoveryProtocol.History) = start
                      := by
                  have semantic : (⟨_, rawWitness.checkpoint.trace⟩ :
                      setup.commitRecoveryProtocol.History) = ⟨_, witness.checkpoint.trace⟩ := by
                    rw [rawCheckpoint]
                    exact (beforeWitness.checkpoint.transfer_history rfl rfl rfl).trans sameHistory
                  have lifted := congrArg (fun history : setup.commitRecoveryProtocol.History =>
                    (⟨history.state, setup.proposalRecoveryLiftTrace labels history.trace⟩ :
                      setup.proposalRecoveryProtocol.History)) semantic
                  rw [oldLabels] at lifted
                  exact lifted
                have phaseLaw : stepLaw = PMF.pure
                    (⟨_, setup.proposalRecoveryLiftTrace labels completed.checkpoint.trace⟩ :
                      setup.proposalRecoveryProtocol.History) := by
                  rw [rawStart] at law
                  exact law
                have completedProper : ∀ who, who ∉ (phase.drain raw).excluded →
                    completed.checkpoint.source.BindingsHoldValues who := by
                  intro who active
                  have globalLive := ProtocolState.noncommit_path_bindingsHoldValues setup.program
                    (fun first last moved => ⟨moved.1.2.1, moved.1.2.2⟩) _ _ publicPath who
                      (by
                        intro survives
                        have live : rawWitness.checkpoint.source.BindingsHoldValues who := by
                          rw [rawCheckpoint, beforeCheckpoint]
                          exact proper who (by
                            rw [← entryExcluded, ← congrArg RecoveryState.excluded sameEntry]
                            exact survives)
                        exact (rawWitness.checkpoint.origin.bindingsHoldValues_lift who _).mpr
                          ((ProtocolState.bindingsHoldValues_entry who
                            rawWitness.checkpoint.residual.tail rawWitness.checkpoint.source).mpr
                              live))
                      active
                  intro name payload cell
                  exact (ProtocolState.bindingsHoldValues_entry who
                    completed.checkpoint.residual.tail
                    completed.checkpoint.source).mp
                      ((completed.checkpoint.origin.bindingsHoldValues_lift who _).mp globalLive)
                        cell
                let selected : setup.proposalRecoveryProtocol.History :=
                  ⟨_, setup.proposalRecoveryLiftTrace labels completed.checkpoint.trace⟩
                have sourceMember : selected ∈ stepLaw.support := by
                  rw [phaseLaw]
                  exact (PMF.mem_support_pure_iff _ _).mpr rfl
                refine ⟨selected, phaseLaw, ?_⟩
                exact completedContinuation (final, selected) stoppedSupport sourceMember ending
                  before
                  prior beforeWitness raw rawWitness rest completed finalState nextIdle changed
                    sameAttempt beforePhases finished imageE normalized effect beforeArchived
                      rawCheckpoint delta completedProper rfl (by
                        rintro ⟨impossible, _⟩
                        cases kind.symm.trans impossible)
              let sourceImage := fun final => if positive : final ∈ stoppedLaw.support then
                (localPhase final positive).choose else start
              have selectedLaw : ∀ final ∈ stoppedLaw.support,
                  stepLaw = PMF.pure (sourceImage final) := by
                intro final positive
                simpa only [sourceImage, dite_eq_left positive] using
                  (localPhase final positive).choose_spec.1
              let joint := stoppedLaw.map fun final => (final, sourceImage final)
              refine ⟨joint, ?_, ?_, ?_⟩
              · simp only [joint, PMF.map_comp, Function.comp_def]
                exact PMF.map_id _
              · simp only [joint, PMF.map_comp, Function.comp_def]
                let representative := stoppedLaw.support_nonempty.choose
                have positive := stoppedLaw.support_nonempty.choose_spec
                rw [selectedLaw representative positive]
                apply pmf_eq_pure_of_support_subset_singleton
                intro selected member
                obtain ⟨final, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
                have belongs : sourceImage final ∈ stepLaw.support := by
                  rw [selectedLaw final supported]
                  exact (PMF.mem_support_pure_iff _ _).mpr rfl
                rw [selectedLaw representative positive] at belongs
                exact (PMF.mem_support_pure_iff _ _).mp belongs
              · intro pair member
                obtain ⟨final, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
                simpa only [sourceImage, dite_eq_left supported] using
                  (localPhase final supported).choose_spec.2
          | sample =>
              let anchorWitness := witness
              let initialTrace := witness.checkpoint.trace
              rcases witness with ⟨checkpoint, aligned, chronology, origins, nativeInvariant,
                binding, receipts, stored, remembered, order, suffixW, archives, exclusions,
                failures⟩
              rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding,
                beforeRefs, compiled, terminalAlignment, agrees, guards, preservedFailures, unique,
                ranks, actors, commits, owners, endpoints, automatic, histories, memories, steps,
                menus, readouts, _trace, views, historyAlignment, origin⟩
              have low : phase.low = anchor.execution.application.attempt.phase := by
                simp only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
                  Option.getD_some]
              have count := compiled.countEq
              change anchor.execution.application.attempt.phase + eventCount program =
                eventCount setup.program at count
              have positive : 0 < eventCount program := by
                have bounded := phase.bounded
                change phase.high ≤ eventCount setup.program at bounded
                have nonempty := phase.nonempty
                omega
              let zero : Fin (eventCount program) := ⟨0, positive⟩
              have ranked : (embedding.event zero).val = phase.low := by
                rw [compiled.rankEq]
                dsimp only [zero]
                omega
              have headSample : RuntimePhaseKind.sample.Matches (outputLayout program zero) := by
                have typed := phase.fields (embedding.event zero) (by omega)
                  (by have nonempty := phase.nonempty; omega)
                rw [kind] at typed
                change RuntimePhaseKind.sample.Matches
                  (outputLayout setup.program (embedding.event zero)) at typed
                rw [embedding.layout_eq] at typed
                exact typed
              cases program with
              | ret payoffs => simp only [eventCount] at positive; omega
              | commit name owner fresh guard tail =>
                  obtain ⟨payload, impossible⟩ := headSample
                  cases impossible
              | reveal published owner name fresh selected unresolved tail =>
                  obtain ⟨payload, impossible⟩ := headSample
                  cases impossible
              | @sample _ _ name payload fresh law tail =>
                  let event := embedding.event zero
                  have output : (graph).outputLayout event = .publicData payload := by
                    change outputLayout setup.program (embedding.event zero) = _
                    simpa only [zero, outputLayout, Fin.mk_zero, Fin.cases_zero] using
                      embedding.layout_eq zero
                  have code : cast (congrArg (EventCode (graphLayout setup.program)) output)
                      ((graph).nodes event) = .sample payload (compilePublicDist refs law) := by
                    simpa only [event, zero, EventGraph.withMode_nodes, compileRankedNodes,
                      outputLayout,
                      Fin.mk_zero, Fin.cases_zero, Setup.eventGraph] using compiled.nodeEq zero
                  have actorless : (graph).actor? event = none :=
                    (EventCode.actor_cast output _).symm.trans (congrArg EventCode.actor code)
                  let rawTrace := (menu).toRawTrace initial horizon scheduler anchorTrace
                  have geometry := (phaseApplication_quiescent runtime leaks
                      (serviceGraph_revealRelaxedOrdered setup mode)).history initial horizon
                    scheduler (fun state supported => by
                      obtain ⟨input, _member, rfl⟩ := PMF.support_map .. ▸ supported
                      exact phaseApplication_initial_quiescent plan
                        (serviceGraph_revealRelaxedOrdered setup mode) maximal input) rawTrace
                  have living := (phaseApplication_live runtime leaks).history initial horizon
                    scheduler (fun state supported => by
                      obtain ⟨input, _member, rfl⟩ := PMF.support_map .. ▸ supported
                      exact ⟨PhaseRuntimeState.initial_frontier plan input,
                        PhaseRuntimeState.initial_live plan input⟩) rawTrace
                  obtain ⟨selected, selectedRank, selectedReady, _selectedActor⟩ :=
                    anchor.execution.application.sample_ready_of_live geometry.1 living.2
                      geometry.2.2 phase installed kind
                  have selectedEq : selected = event := Fin.ext (selectedRank.trans ranked.symm)
                  subst selected
                  let current := CommitRecoveryState.atPoint
                    (lift (.inl source)) anchor.execution.application.entry.excluded
                      anchor.execution.application.generation
                  let sourceTrace := setup.proposalRecoveryLiftTrace
                    (nativeArchiveLabels setup
                      (PhaseProposal.sourceArchive anchor.execution.network.inputs)) initialTrace
                  have currentAgree : refs.Agrees source.state
                      anchor.execution.application.current.native.config.store :=
                    anchorWitness.checkpoint.current_agrees anchorWitness.stored
                  obtain ⟨joint, nativeLaw, sourceLaw, support⟩ :=
                    phaseProposal_ordinary_sample_stopped_coupling setup mode runtime leaks bounds
                      plan (setup.initialLaw.map encodeInputs)
                        (serviceGraph_revealRelaxedOrdered setup mode) maximal tape anchor
                          anchorTrace
                          anchorWitness.order.frontier phase remaining phases kind fresh law tail
                            lift
                            origin source current sourceTrace rfl refs currentAgree event ranked
                              selectedReady output code values profile
                  have one : phase.high - phase.low = 1 := by
                    have singleton := phase.sample_singleton kind
                    omega
                  have nativePhase : joint.map Prod.fst = stoppedLaw := by
                    refine nativeLaw.trans (sameStopKernel _ ?_).symm
                    intro history
                    rcases history with ⟨state, trace⟩
                    cases state <;> rfl
                  have sourcePhase : joint.map Prod.snd = stepLaw := by
                    simpa only [stepLaw, one, sourceProfile, start, current, sourceTrace,
                      initialTrace, anchorWitness, ProtocolState.entry] using sourceLaw
                  refine ⟨joint, nativePhase, sourcePhase, ?_⟩
                  intro pair member
                  obtain ⟨value, valueSupport, sourcePoint, sampleSourcePrefix, observedStopped⟩
                    :=
                    support pair member
                  have stoppedSupport : pair.1 ∈ stoppedLaw.support := by
                    rw [← nativePhase]
                    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨pair, member, rfl⟩
                  have sourceMemberStep : pair.2 ∈ stepLaw.support := by
                    rw [← sourcePhase]
                    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨pair, member, rfl⟩
                  obtain ⟨ending, before, prior, actions, legal, realized, raw, rest,
                    beforeWitness, rawWitness, finalState, nextIdle, changed, fromAnchor,
                    toFinal, sameAttempt, beforePhases, finished, coverage, imageE, normalized,
                    effect, beforeArchived, sameHistory, rawCheckpoint,
                    ⟨sameEntry, beforeCheckpoint⟩⟩ :=
                    closing pair.1 stoppedSupport
                  obtain ⟨completed, ⟨fuel, completedPath⟩, publicPath, addresses, ownWord,
                    intended, replay, sameE, phaseDelta, observed⟩ :=
                    rawWitness.completed_sample_history maximal phase rest beforePhases kind
                      finished
                  have target : pair.2.state = some (CommitRecoveryState.atPoint
                      (completed.checkpoint.residual.lift
                        (ProtocolState.entry completed.checkpoint.residual.tail
                          completed.checkpoint.source))
                      (phase.drain raw).excluded before.execution.application.generation) := by
                    rw [rawCheckpoint, beforeCheckpoint] at observed
                    dsimp only [RecoverySourceCheckpoint.transfer, anchorWitness] at observed
                    obtain ⟨chosenEvent, chosenOutput, sampled, _sampledSupport, chosenRank,
                      recorded, nextPoint⟩ := observed
                    have beforeLow : before.execution.application.attempt.phase = phase.low := by
                      simp only [PhaseRuntimeState.attempt, beforePhases, List.head?_cons,
                        Option.map_some, Option.getD_some]
                    have sameEvent : chosenEvent = event := Fin.ext
                      (chosenRank.trans (beforeLow.trans ranked.symm))
                    subst chosenEvent
                    let field : FieldRef (graphLayout setup.program) (.publicData payload) :=
                      ⟨.inr event, output⟩
                    change field.get? (phase.drain raw).native.config.store = some sampled
                      at recorded
                    have drainEq := phase.sample_drain_eq kind event ranked actorless raw
                    have inside : event ∈ phase.events := (phase.mem_events event).mpr
                      ⟨ranked.ge, by have nonempty := phase.nonempty; omega⟩
                    have completedRaw : event ∈ raw.native.config.cut.completed := by
                      rw [← drainEq]
                      exact finished inside
                    have keptStore := before.execution.application.sample_normalization_keepsStore
                      phase rest beforePhases kind event ranked actorless raw completedRaw
                    have finalRead : field.get?
                      ending.execution.application.current.native.config.store =
                        some sampled := by
                      rw [normalized]
                      exact field.get?_preserved _ _ keptStore sampled (by
                        simpa only [drainEq] using recorded)
                    have stoppedRead : field.get?
                        ending.execution.application.current.native.config.store = some value :=
                          by
                      simpa only [finalState, Option.bind_some] using observedStopped
                    have sameValue : sampled = value :=
                      Option.some.inj (finalRead.symm.trans stoppedRead)
                    have sameGeneration : before.execution.application.generation =
                        anchor.execution.application.generation :=
                      congrArg CommitAttemptId.generation sameAttempt
                    rw [sameValue] at nextPoint
                    rw [nextPoint, sameE, sameEntry, sameGeneration]
                    exact sourcePoint
                  have exactHistory : pair.2 = ⟨_, setup.proposalRecoveryLiftTrace
                      (nativeArchiveLabels setup
                        (PhaseProposal.sourceArchive ending.execution.network.inputs))
                          completed.checkpoint.trace⟩ := by
                    have sourceMember : pair.2 ∈
                        (setup.proposalRecoveryModel.runBehavioralFrom sourceProfile 1
                          start).support :=
                      by
                        simpa only [stepLaw, one] using sourceMemberStep
                    have rawStart : (⟨_, setup.proposalRecoveryLiftTrace
                        (nativeArchiveLabels setup
                          (PhaseProposal.sourceArchive ending.execution.network.inputs))
                            rawWitness.checkpoint.trace⟩ :
                        setup.proposalRecoveryProtocol.History) = start := by
                      let endingTrace : ((menu).protocol initial horizon scheduler).Trace
                          (some ending) := finalState ▸ pair.1.trace
                      have kept := model.runBehavioralUntil_support_prefix certificate profile
                        stopped ⟨some anchor, anchorTrace⟩ pair.1 stoppedSupport
                      have endingHistoryEq := StateSymmetry.history_cast finalState pair.1.trace
                      have retained : TracePrefix anchorTrace endingTrace := by
                        exact (congrArg (fun history :
                          ((menu).protocol initial horizon scheduler).History =>
                            TracePrefix anchorTrace history.trace) endingHistoryEq).mpr kept
                      have initialized : ∀ state ∈ (initial).support, state.Ordered := by
                        intro state selected
                        obtain ⟨input, _selected, rfl⟩ := PMF.support_map .. ▸ selected
                        exact PhaseRuntimeState.initial_ordered plan input
                      have ordered := (phaseApplication_seedOrder runtime leaks).history
                        initial horizon scheduler initialized
                          ((menu).toRawTrace initial horizon scheduler anchorTrace)
                      have sameInputs := requestless_prefix_inputs setup mode runtime leaks
                        bounds plan scheduler anchor ending anchorTrace endingTrace retained
                          (by
                            intro middle prefixTrace after beforeLast shorter owner coordinate
                              request
                            have toFinal : TracePrefix prefixTrace pair.1.trace := by
                              exact (congrArg (fun history :
                                ((menu).protocol initial horizon scheduler).History =>
                                  TracePrefix prefixTrace history.trace)
                                    endingHistoryEq).mp beforeLast
                            have shorterFinal : prefixTrace.length < pair.1.trace.length := by
                              change prefixTrace.length < (⟨some ending, endingTrace⟩ :
                                ((menu).protocol initial horizon scheduler).History).trace.length
                                at shorter
                              rwa [endingHistoryEq] at shorter
                            have going := model.runBehavioralUntil_support_first certificate
                              profile stopped ⟨some anchor, anchorTrace⟩ pair.1 stoppedSupport
                                ⟨some middle, prefixTrace⟩ after toFinal shorterFinal
                            have same : middle.execution.application.attempt =
                                anchor.execution.application.attempt :=
                              Classical.not_not.mp going
                            have metadata := phase_attempt_metadata_of_prefix runtime leaks
                              (menu) initial initialized horizon scheduler anchor middle
                                anchorTrace prefixTrace after ordered same.symm
                            have installedNow : phase ∈
                              middle.execution.application.phases.head? :=
                              (congrArg (fun phases => phase ∈ phases.head?)
                                (congrArg Prod.fst metadata)).mp
                                  (Option.mem_def.mpr installed)
                            obtain ⟨actualPhase, actualInstalled, inside⟩ := request.2.1
                            have phaseEq : actualPhase = phase := Option.some.inj
                              ((Option.mem_def.mp actualInstalled).symm.trans
                                (Option.mem_def.mp installedNow))
                            subst actualPhase
                            obtain ⟨lower, upper⟩ := (phase.mem_events coordinate.event).mp inside
                            have coordinateEq : coordinate.event = event := Fin.ext (by
                              have eventRank := ranked
                              have width := one
                              omega)
                            have acting := request.2.2.2.1
                            rw [coordinateEq, actorless] at acting
                            cases acting)
                      have rawHistory : (⟨_, rawWitness.checkpoint.trace⟩ :
                          setup.commitRecoveryProtocol.History) =
                          ⟨_, anchorWitness.checkpoint.trace⟩ := by
                        rw [rawCheckpoint]
                        exact (beforeWitness.checkpoint.transfer_history rfl rfl rfl).trans
                          sameHistory
                      have lifted := congrArg (fun history :
                        setup.commitRecoveryProtocol.History =>
                        (⟨history.state, setup.proposalRecoveryLiftTrace
                          (nativeArchiveLabels setup
                            (PhaseProposal.sourceArchive ending.execution.network.inputs))
                              history.trace⟩ : setup.proposalRecoveryProtocol.History)) rawHistory
                      simpa only [start, sourceTrace, anchorWitness, initialTrace, sameInputs]
                        using lifted
                    apply rawWitness.checkpoint.sample_history_eq_of_target
                      rawWitness.order.frontier phase rest beforePhases kind completed.checkpoint
                        completedPath values
                          (nativeArchiveLabels setup
                            (PhaseProposal.sourceArchive ending.execution.network.inputs))
                          pair.2
                    · rw [rawStart]
                      exact sourceMember
                    · exact target
                  have noRetry : ¬ (phase.kind = .commitment ∧
                      (((phase.drain raw).excluded \
                        before.execution.application.entry.excluded) ∩
                        phase.owners).Nonempty) := by
                    rintro ⟨impossible, _⟩
                    cases kind.symm.trans impossible
                  have imageExcluded : (phase.drain raw).excluded =
                      anchor.execution.application.current.excluded :=
                    sameE.trans ((congrArg RecoveryState.excluded sameEntry).trans entryExcluded)
                  have completedProper : ∀ who, who ∉ (phase.drain raw).excluded →
                      completed.checkpoint.source.BindingsHoldValues who := by
                    intro who active
                    have oldLive : source.BindingsHoldValues who :=
                      proper who (imageExcluded ▸ active)
                    have sampledLive : (sampleSuccessor name source value).BindingsHoldValues
                      who :=
                      by
                        intro selected ty cell
                        cases cell with
                        | there cell => exact oldLive cell
                    have globalLive : ProtocolState.BindingsHoldValues who setup.program
                        (lift (.inr (ProtocolState.entry tail (sampleSuccessor name source
                          value)))) :=
                      (origin.bindingsHoldValues_lift who _).mpr
                        ((ProtocolState.bindingsHoldValues_entry who tail _).mpr sampledLive)
                    have completedPoint := congrArg CommitRecoveryState.point
                      (Option.some.inj (target.symm.trans sourcePoint))
                    change completed.checkpoint.residual.lift
                        (ProtocolState.entry completed.checkpoint.residual.tail
                          completed.checkpoint.source) =
                      lift (.inr (ProtocolState.entry tail (sampleSuccessor name source value)))
                      at completedPoint
                    rw [← completedPoint] at globalLive
                    intro name payload cell
                    exact (ProtocolState.bindingsHoldValues_entry who
                      completed.checkpoint.residual.tail completed.checkpoint.source).mp
                        ((completed.checkpoint.origin.bindingsHoldValues_lift who _).mp
                          globalLive) cell
                  have sourceMember : pair.2 ∈ stepLaw.support := sourceMemberStep
                  exact completedContinuation pair stoppedSupport sourceMember ending before
                    prior beforeWitness
                    raw rawWitness rest completed finalState nextIdle changed sameAttempt
                      beforePhases finished
                      imageE normalized effect beforeArchived rawCheckpoint phaseDelta
                        completedProper exactHistory
                        noRetry
        obtain ⟨phaseJoint, nativePhaseLaw, sourcePhaseLaw, phaseSupport⟩ := phaseLaw
        have children : ∀ pair ∈ phaseJoint.support,
            ∃ child : PMF (((menu).protocol initial horizon scheduler).History ×
                setup.proposalRecoveryProtocol.History),
              child.map Prod.fst = model.runBehavioralTerminalFrom certificate profile pair.1 ∧
              child.map Prod.snd = setup.proposalRecoveryModel.runBehavioralTerminalFrom
                sourceCertificate sourceProfile pair.2 ∧
              ∀ final ∈ child.support,
                ∃ (ending : (app).Control)
                  (next : RecoverySourceWitness setup mode plan ending.execution.application),
                  final.1.state = some ending ∧ ending.execution.application.phases = [] ∧
                  TracePrefix anchorTrace final.1.trace ∧ TracePrefix start.trace final.2.trace ∧
                  final.2 = ⟨_, setup.proposalRecoveryLiftTrace
                    (nativeArchiveLabels setup
                      (PhaseProposal.sourceArchive ending.execution.network.inputs))
                        next.checkpoint.trace⟩ ∧
                  setup.proposalRecoveryProtocol.terminal final.2.state ∧
                  ending.execution.application.current.excluded =
                    ending.execution.application.entry.excluded ∧
                  final.2.state.map CommitRecoveryState.excluded =
                    some ending.execution.application.current.excluded ∧
                  (∃ original ∈ setup.initialLaw.support,
                    ending.execution.application.current.native.config.inputs =
                      encodeInputs original ∧
                    (setup.protocolReadout (setup.commitRecoverySourceState final.2.state)).map
                      (initialState setup.program) = some original) ∧
                  phaseSourceReadout setup mode runtime leaks (some ending) =
                    setup.protocolReadout (setup.commitRecoverySourceState final.2.state) ∧
                  (fun who => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
                    (some ending) who) = fun who => setup.commitRecoveryPayoff utility
                      excludedPayoff
                      who ⟨final.2.state, setup.proposalRecoveryEraseTrace final.2.trace⟩ := by
          intro pair supported
          obtain ⟨ending, next, stateEq, nextIdle, nativePrefix, nextEntry, nextFresh, nextArchived,
            nextProper, smaller, sourcePrefix, sourceKernel⟩ := phaseSupport pair supported
          let nextTrace : ((menu).protocol initial horizon scheduler).Trace (some ending) :=
            stateEq ▸ pair.1.trace
          have nextHistoryEq := StateSymmetry.history_cast stateEq pair.1.trace
          have anchorPrefix : TracePrefix anchorTrace nextTrace := by
            exact (congrArg (fun history :
              ((menu).protocol initial horizon scheduler).History =>
                TracePrefix anchorTrace history.trace) nextHistoryEq).mpr nativePrefix
          obtain ⟨child, nativeChild, sourceChild, childSupport⟩ :=
            ih (instructionCount next.checkpoint.residual.tail) smaller ending nextIdle nextTrace
              nextEntry nextFresh next nextArchived nextProper rfl
          have reanchored : model.runBehavioralTerminalFrom certificate
              (fun who => (menu).restrictPolicy initial horizon scheduler who
                (ReactiveApplication.anchoredPolicy ending.execution
                  (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who))
                ⟨some ending, nextTrace⟩ =
              model.runBehavioralTerminalFrom certificate profile pair.1 := by
            have pairEq : (⟨some ending, nextTrace⟩ :
                ((menu).protocol initial horizon scheduler).History) = pair.1 := by
              dsimp only [nextTrace]
              cases pair with
              | mk native source =>
                  cases native
                  cases stateEq
                  rfl
            rw [← pairEq]
            apply model.runBehavioralTerminalFrom_congr certificate
            intro later reached running who
            obtain ⟨fuel, path⟩ := reached
            have anchorPrefix : TracePrefix anchorTrace nextTrace := by
              dsimp only [nextTrace]
              cases pair with
              | mk native source =>
                  cases native
                  cases stateEq
                  exact nativePrefix
            have earlier := (app).reaches_recall_prefix initial horizon scheduler
              ((menu).reaches_raw initial horizon scheduler anchorPrefix.reachesWithin)
                anchor ending rfl rfl who
            rcases later with ⟨state, laterTrace⟩
            have observed := (menu).info initial horizon scheduler who laterTrace
            change model.infoOf who laterTrace = (app).observe who state at observed
            cases state with
            | none => rw [observed]; rfl
            | some current =>
                by_cases active : current.actor = some who
                · have laterRecall := (app).reaches_recall_prefix initial horizon scheduler
                    ((menu).reaches_raw initial horizon scheduler path)
                      ending current rfl rfl who
                  simp only [ReactiveApplication.observe, ite_eq_left active] at observed
                  rw [observed]
                  apply (menu).restrictPolicy_eq_of_law_eq initial horizon scheduler who
                  rw [ReactiveApplication.anchoredPolicy_of_extends ending.execution _ who _ _
                    laterRecall, ReactiveApplication.anchoredPolicy_of_extends anchor.execution _
                      who _ _ (earlier.trans laterRecall)]
                · simp only [ReactiveApplication.observe, ite_eq_right active] at observed
                  rw [observed]
                  rfl
          refine ⟨child, nativeChild.trans reanchored, sourceChild.trans sourceKernel.symm, ?_⟩
          intro final member
          obtain ⟨last, lastWitness, lastState, lastPhases, lastPrefix, fullSourcePrefix,
            fullHistory, terminal, excluded, sourceE, original, readout, payoffs⟩ :=
              childSupport final member
          refine ⟨last, lastWitness, lastState, lastPhases, ?_, ?_, fullHistory, terminal,
            excluded, sourceE, original, readout, payoffs⟩
          · exact anchorPrefix.trans lastPrefix
          · exact sourcePrefix.trans fullSourcePrefix
        choose child nativeChild sourceChild childSupport using children
        let joint := phaseJoint.bindOnSupport child
        refine ⟨joint, ?_, ?_, ?_⟩
        · rw [model.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil
            certificate profile stopped ⟨some anchor, anchorTrace⟩]
          change (phaseJoint.bindOnSupport child).map Prod.fst = _
          rw [map_bindOnSupport]
          calc
            _ = phaseJoint.bind (fun pair =>
                model.runBehavioralTerminalFrom certificate profile pair.1) :=
              bindOnSupport_eq_bind_of_eq_on_support _ nativeChild
            _ = (phaseJoint.map Prod.fst).bind
                (model.runBehavioralTerminalFrom certificate profile) := by rw [PMF.bind_map]; rfl
            _ = _ := by rw [nativePhaseLaw]
        · rw [setup.proposalRecoveryModel.runBehavioralTerminalFrom_eq_bind_runBehavioralFrom
            sourceCertificate sourceProfile (phase.high - phase.low) start]
          change (phaseJoint.bindOnSupport child).map Prod.snd = _
          rw [map_bindOnSupport]
          calc
            _ = phaseJoint.bind (fun pair =>
                setup.proposalRecoveryModel.runBehavioralTerminalFrom
                  sourceCertificate sourceProfile pair.2) :=
              bindOnSupport_eq_bind_of_eq_on_support _ sourceChild
            _ = (phaseJoint.map Prod.snd).bind
                (setup.proposalRecoveryModel.runBehavioralTerminalFrom
                  sourceCertificate sourceProfile) := by rw [PMF.bind_map]; rfl
            _ = _ := by rw [sourcePhaseLaw]
        · intro final member
          obtain ⟨pair, supported, conditional⟩ :=
            (PMF.mem_support_bindOnSupport_iff _ _).mp member
          exact childSupport pair supported final conditional

end Vegas
