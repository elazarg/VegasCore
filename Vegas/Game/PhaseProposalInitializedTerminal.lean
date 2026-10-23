/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalFreshTerminalCoupling
import Interaction.ReactiveSchedulerTerminalMixture
import Interaction.ReactiveTerminalEvaluation

/-! # Original initialized draws and tapes in the ordinary terminal joint law -/

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

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
private theorem encoded_inputs_injective {Γ : SourceCtx Player L} :
    Function.Injective (encodeInputs (Player := Player) (L := L) (Γ := Γ)) := by
  intro first second equal
  funext name cell selected
  have values := congrArg (fun inputs =>
    cast (congrArg EventGraph.EventField.Value (inputLayout_inputId selected))
      (inputs (inputId selected))) equal
  rw [encodeInputs_get, encodeInputs_get] at values
  cases cell <;> exact values

omit [Fintype Player] in
private def initialized_source_history (theta : State L setup.context)
    (supported : theta ∈ setup.initialLaw.support) : setup.proposalRecoveryProtocol.History :=
  ⟨_, setup.proposalRecoveryLiftTrace
    (nativeArchiveLabels setup (PhaseProposal.sourceArchive
      ([] : List (Message Player (CommitAttemptPacket (serviceGraph setup mode))))))
      (RecoverySourceCheckpoint.initialized setup mode plan theta supported).trace⟩

omit [Fintype Player] in
private theorem checkpoint_cast_history
    {first second : PhaseRuntimeState (serviceGraph setup mode)} (same : first = second)
    (checkpoint : RecoverySourceCheckpoint setup mode first) :
    (⟨_, (cast (congrArg (RecoverySourceCheckpoint setup mode) same) checkpoint).trace⟩ :
      setup.commitRecoveryProtocol.History) = ⟨_, checkpoint.trace⟩ := by
  cases same
  rfl

private theorem initialized_source_terminal
    (profile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who) :
    setup.proposalRecoveryModel.runBehavioralTerminalFrom
        setup.proposalRecoveryProtocol_bounded.wellFoundedHistories profile
          setup.proposalRecoveryProtocol.initHistory =
      setup.initialLaw.bindOnSupport (fun theta supported =>
        setup.proposalRecoveryModel.runBehavioralTerminalFrom
          setup.proposalRecoveryProtocol_bounded.wellFoundedHistories profile
            (initialized_source_history setup mode plan theta supported)) := by
  classical
  have running : ¬ setup.proposalRecoveryProtocol.terminal
      setup.proposalRecoveryProtocol.initHistory.state := fun impossible => impossible
  rw [setup.proposalRecoveryModel.runBehavioralTerminalFrom_of_not_terminal _ _ running,
    setup.proposalRecoveryModel.behavioralJoint_eq_pure_of_no_active profile _ running
      (fun _ impossible => impossible), PMF.pure_bind]
  let draw := fun theta : State L setup.context => some (CommitRecoveryState.atPoint
    (ProtocolState.entry setup.program (setup.initialConfig theta)) ∅ 0)
  have legal : setup.proposalRecoveryProtocol.Legal
      setup.proposalRecoveryProtocol.initHistory.state (fun _ => none) :=
    ⟨(fun impossible => impossible), fun _ impossible => impossible⟩
  change ((setup.initialLaw.map draw).bindOnSupport (fun _ realized =>
    setup.proposalRecoveryModel.runBehavioralTerminalFrom
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories profile
        (setup.proposalRecoveryProtocol.initHistory.extend legal realized))) = _
  have mapEq : setup.initialLaw.bindOnSupport (fun theta _ => PMF.pure (draw theta)) =
      setup.initialLaw.map draw := by
    rw [PMF.bindOnSupport_eq_bind]
    exact PMF.bind_pure_comp _ _
  have bindCast {A B : Type} (first second : PMF A) (same : first = second)
      (kernel : ∀ target ∈ second.support, PMF B) :
      first.bindOnSupport (fun target supported => kernel target (same ▸ supported)) =
        second.bindOnSupport kernel := by
    cases same
    rfl
  rw [← bindCast _ _ mapEq (fun _ realized =>
    setup.proposalRecoveryModel.runBehavioralTerminalFrom
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories profile
        (setup.proposalRecoveryProtocol.initHistory.extend legal realized))]
  rw [PMF.bindOnSupport_bindOnSupport]
  apply bindOnSupport_congr
  intro theta supported
  rw [PMF.pure_bindOnSupport]
  apply congrArg (setup.proposalRecoveryModel.runBehavioralTerminalFrom
    setup.proposalRecoveryProtocol_bounded.wellFoundedHistories profile)
  have raw := checkpoint_cast_history setup mode
    (phaseInitial_eq_raw plan (encodeInputs theta)).symm
      (RecoverySourceCheckpoint.initial setup mode plan theta supported)
  have lifted := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    (⟨_, setup.proposalRecoveryLiftTrace
      (nativeArchiveLabels setup (PhaseProposal.sourceArchive
      ([] : List (Message Player (CommitAttemptPacket (serviceGraph setup mode))))))
        history.trace⟩ :
        setup.proposalRecoveryProtocol.History)) raw
  change _ = initialized_source_history setup mode plan theta supported
  exact lifted.symm

private def initialized_control (theta : State L setup.context) : (app).Control :=
  ⟨horizon, none, ReactiveApplication.Execution.initial app
    (PhaseRuntimeState.initial plan (encodeInputs theta))⟩

private def initialized_trace (scheduler : (app).Scheduler)
    (theta : State L setup.context) (supported : theta ∈ setup.initialLaw.support) :
    ((menu).protocol initial horizon scheduler).Trace
      (some (initialized_control setup mode runtime leaks plan theta)) := by
  refine .extend .start (fun _ => none) ⟨(fun impossible => impossible), ?_⟩ ?_
  · intro who
    exact fun impossible => by cases impossible
  · change some (initialized_control setup mode runtime leaks plan theta) ∈
      ((initial).map (fun state => some
        (⟨horizon, none, ReactiveApplication.Execution.initial app state⟩ : (app).Control))).support
    apply (PMF.mem_support_map_iff _ _ _).mpr
    refine ⟨PhaseRuntimeState.initial plan (encodeInputs theta), ?_, rfl⟩
    apply (PMF.mem_support_map_iff _ _ _).mpr
    refine ⟨encodeInputs theta, ?_, rfl⟩
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨theta, supported, rfl⟩

/-- The original setup draw and the whole exogenous reserved tape retain their
literal product law. The actual implementation has the native marginal, and
the complete initialized ordinary source history has the other marginal. -/
theorem phaseProposalUnflagged_initialized_terminal_coupling
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (initialValues : ∀ theta ∈ setup.initialLaw.support,
      ∀ {name : VarId} {owner : Player} {payload : L.Ty}
        (cell : HasVar setup.context name (.commitment owner payload)),
        ∃ value, theta.get cell = .success value)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    {length : Nat} (prior : PMF (ReservedEpoch.Tape Player length))
    (activationGap processingGap : Nat)
    (gaps : ∀ tape ∈ prior.support,
      tape.BoundedGaps (ReservedEpoch.completionCycles runtime) activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : horizon ≤ bounds.candidateCount)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    let scheduler := (ReservedEpoch.implementation runtime leaks
      (ReservedEpoch.packetCapacity runtime) prior).scheduler
    let players := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
    let sourceProfile := setup.proposalRecoveryNormalizedTrembledProfile
      0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
    ∃ joint : PMF ((State L setup.context × ReservedEpoch.Tape Player length) ×
        ((app).ProtocolState × setup.proposalRecoveryProtocol.History)),
      joint.map Prod.fst = setup.initialLaw.bind (fun theta => prior.map (Prod.mk theta)) ∧
      joint.map (fun result => result.2.1) =
        (app).finish initial horizon scheduler players none ∧
      joint.map (fun result => result.2.2) =
        setup.proposalRecoveryModel.runBehavioralTerminalFrom
          setup.proposalRecoveryProtocol_bounded.wellFoundedHistories sourceProfile
            setup.proposalRecoveryProtocol.initHistory ∧
      ∀ result ∈ joint.support,
        result.1.1 ∈ setup.initialLaw.support ∧ result.1.2 ∈ prior.support ∧
        ∃ (ending : (app).Control)
          (next : RecoverySourceWitness setup mode plan ending.execution.application),
          result.2.1 = some ending ∧ ending.execution.application.phases = [] ∧
          result.2.2 = ⟨_, setup.proposalRecoveryLiftTrace
            (nativeArchiveLabels setup
              (PhaseProposal.sourceArchive ending.execution.network.inputs))
                next.checkpoint.trace⟩ ∧
          setup.proposalRecoveryProtocol.terminal result.2.2.state ∧
          ending.execution.application.current.native.config.inputs = encodeInputs result.1.1 ∧
          (setup.protocolReadout (setup.commitRecoverySourceState result.2.2.state)).map
            (initialState setup.program) = some result.1.1 ∧
          result.2.2.state.map CommitRecoveryState.excluded =
            some ending.execution.application.current.excluded ∧
          phaseSourceReadout setup mode runtime leaks (some ending) =
            setup.protocolReadout (setup.commitRecoverySourceState result.2.2.state) ∧
          (fun who => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
            (some ending) who) = fun who => setup.commitRecoveryPayoff utility excludedPayoff who
              ⟨result.2.2.state, setup.proposalRecoveryEraseTrace result.2.2.trace⟩ := by
  classical
  intro scheduler players sourceProfile
  have atInput (theta : State L setup.context) (supported : theta ∈ setup.initialLaw.support)
      (tape : ReservedEpoch.Tape Player length) (selected : tape ∈ prior.support) :
      ∃ joint : PMF ((app).ProtocolState × setup.proposalRecoveryProtocol.History),
        joint.map Prod.fst = (app).finish initial horizon
          (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
            players (some (initialized_control setup mode runtime leaks plan theta)) ∧
        joint.map Prod.snd = setup.proposalRecoveryModel.runBehavioralTerminalFrom
          setup.proposalRecoveryProtocol_bounded.wellFoundedHistories sourceProfile
            (initialized_source_history setup mode plan theta supported) ∧
        ∀ pair ∈ joint.support,
          ∃ (ending : (app).Control)
            (next : RecoverySourceWitness setup mode plan ending.execution.application),
            pair.1 = some ending ∧ ending.execution.application.phases = [] ∧
            pair.2 = ⟨_, setup.proposalRecoveryLiftTrace
              (nativeArchiveLabels setup
                (PhaseProposal.sourceArchive ending.execution.network.inputs))
                  next.checkpoint.trace⟩ ∧
            setup.proposalRecoveryProtocol.terminal pair.2.state ∧
            ending.execution.application.current.native.config.inputs = encodeInputs theta ∧
            (setup.protocolReadout (setup.commitRecoverySourceState pair.2.state)).map
              (initialState setup.program) = some theta ∧
            pair.2.state.map CommitRecoveryState.excluded =
              some ending.execution.application.current.excluded ∧
            phaseSourceReadout setup mode runtime leaks (some ending) =
              setup.protocolReadout (setup.commitRecoverySourceState pair.2.state) ∧
            (fun who => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
              (some ending) who) = fun who => setup.commitRecoveryPayoff utility excludedPayoff who
                ⟨pair.2.state, setup.proposalRecoveryEraseTrace pair.2.trace⟩ := by
    let anchor := initialized_control setup mode runtime leaks plan theta
    let witness := RecoverySourceWitness.initialized setup mode plan theta supported
    let fixed := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let trace := initialized_trace setup mode runtime leaks bounds plan fixed theta supported
    have proper : ∀ who, who ∉ anchor.execution.application.current.excluded →
        witness.checkpoint.source.BindingsHoldValues who := by
      intro who _active
      have point := RecoverySourceCheckpoint.initialized_point setup mode plan theta supported
      have whole : ProtocolState.BindingsHoldValues who setup.program
          (witness.checkpoint.residual.lift (ProtocolState.entry
            witness.checkpoint.residual.tail witness.checkpoint.source)) := by
        change ProtocolState.BindingsHoldValues who setup.program
          ((RecoverySourceCheckpoint.initialized setup mode plan theta supported).residual.lift
            (ProtocolState.entry
              (RecoverySourceCheckpoint.initialized setup mode plan theta supported).residual.tail
                (RecoverySourceCheckpoint.initialized setup mode plan theta supported).source))
        rw [point]
        apply (ProtocolState.bindingsHoldValues_entry who setup.program _).mpr
        exact initialValues theta supported
      have localValues : ProtocolState.BindingsHoldValues who witness.checkpoint.residual.tail
          (ProtocolState.entry witness.checkpoint.residual.tail witness.checkpoint.source) :=
        (witness.checkpoint.origin.bindingsHoldValues_lift who _).mp whole
      intro name payload cell
      exact ((ProtocolState.bindingsHoldValues_entry who
        witness.checkpoint.residual.tail witness.checkpoint.source).mp localValues) cell
    obtain ⟨joint, native, source, linked⟩ := RecoverySourceWitness.ordinary_fresh_terminal_coupling
      setup mode runtime leaks bounds plan complete covered maximal values fullValues tape
        activationGap processingGap (gaps tape selected) margin capacity utility excludedPayoff
          anchor rfl trace (by
            change (PhaseRuntimeState.initial plan (encodeInputs theta)).entry.excluded =
              (PhaseRuntimeState.initial plan (encodeInputs theta)).current.excluded
            rw [phaseInitial_eq_raw])
            (fun _ _ impossible => by cases impossible) witness
              (RecoverySourceWitness.initialized_archivedProposals
                setup mode plan theta supported) proper
    refine ⟨joint.map (fun pair => (pair.1.state, pair.2)), ?_, ?_, ?_⟩
    · have projected := congrArg (PMF.map History.state) native
      have samePlayers : ReactiveApplication.anchoredPolicy anchor.execution players = players := by
        funext who past view
        apply ReactiveApplication.anchoredPolicy_of_extends
        exact List.nil_prefix
      rw [samePlayers] at projected
      rw [(menu).terminal_run_restrict_eq_finish initial horizon fixed
        ((menu).bounded initial horizon fixed).wellFoundedHistories players
          (fun who control _trace _acting =>
            phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values who
              (control.execution.recall who) (control.execution.observe app who))
            ⟨some anchor, trace⟩] at projected
      simpa only [PMF.map_comp, Function.comp_def] using projected
    · simpa only [PMF.map_comp, Function.comp_def, initialized_source_history, anchor,
        initialized_control, ReactiveApplication.Execution.initial, MessageNetwork.empty, witness,
        RecoverySourceWitness.initialized] using source
    · intro pair member
      obtain ⟨original, originalMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      obtain ⟨ending, next, endingEq, ended, kept, _sourceKept, image, terminal,
        _sameExcluded, excluded, ⟨draw, _drawSupport, inputEq, initialEq⟩, readout, payoff⟩ :=
          linked original originalMember
      have nativeInvariant :=
        (phaseApplication_invariant runtime leaks (encodeInputs theta)).reaches
        initial horizon fixed ((menu).reaches_raw initial horizon fixed kept.reachesWithin)
          anchor ending rfl endingEq (PhaseRuntimeState.initial_invariant plan
            (encodeInputs theta)).1
      have literalInputs := nativeInvariant.active.reachable.inputs_eq
      have sameDraw : draw = theta := encoded_inputs_injective
        (inputEq.symm.trans literalInputs)
      refine ⟨ending, next, endingEq, ended, image, terminal, literalInputs, ?_, excluded,
        readout, payoff⟩
      simpa only [sameDraw] using initialEq
  choose conditional native source linked using atInput
  let joint := prior.bindOnSupport fun tape selected =>
    setup.initialLaw.bindOnSupport fun theta supported =>
      (conditional theta supported tape selected).map fun pair => ((theta, tape), pair)
  refine ⟨joint, ?_, ?_, ?_, ?_⟩
  · dsimp only [joint]
    simp only [map_bindOnSupport, PMF.map_comp, Function.comp_def]
    rw [bindOnSupport_eq_bind_of_eq_on_support prior (g := fun tape =>
      setup.initialLaw.map (fun theta => (theta, tape))) (by
        intro tape selected
        rw [bindOnSupport_eq_bind_of_eq_on_support setup.initialLaw (by
          intro theta supported
          exact PMF.map_const _ _)]
        exact PMF.bind_pure_comp _ _)]
    calc
      _ = prior.bind (fun tape => setup.initialLaw.bind
          (fun theta => PMF.pure (theta, tape))) := by
        apply congrArg (PMF.bind prior)
        funext tape
        exact (PMF.bind_pure_comp _ _).symm
      _ = setup.initialLaw.bind (fun theta => prior.bind
          (fun tape => PMF.pure (theta, tape))) := PMF.bind_comm _ _ _
      _ = _ := by
        apply congrArg (PMF.bind setup.initialLaw)
        funext theta
        exact PMF.bind_pure_comp _ _
  · dsimp only [joint]
    simp only [map_bindOnSupport, PMF.map_comp, Function.comp_def]
    rw [bindOnSupport_eq_bind_of_eq_on_support prior (g := fun tape =>
      (app).finish initial horizon
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
          players none) (by
        intro tape selected
        rw [bindOnSupport_eq_bind_of_eq_on_support setup.initialLaw
          (g := fun theta => (app).finish initial horizon
            (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
              players (some (initialized_control setup mode runtime leaks plan theta)))
          (fun theta supported => native theta supported tape selected)]
        simp only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind,
          initialized_control, PMF.bind_map, Function.comp_def])]
    simpa only [PMF.map_comp, Function.comp_def, scheduler, ReservedEpoch.implementation] using
      (app).schedulerMixture_finish_marginal prior
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime))
          initial horizon players none
  · dsimp only [joint]
    apply map_bindOnSupport_const
    intro tape selected
    simp only [map_bindOnSupport, PMF.map_comp, Function.comp_def]
    rw [bindOnSupport_congr setup.initialLaw (fun theta supported =>
      source theta supported tape selected)]
    exact (initialized_source_terminal setup mode plan sourceProfile).symm
  · intro result member
    obtain ⟨tape, selected, thetaJoint⟩ := (PMF.mem_support_bindOnSupport_iff _ _).mp member
    obtain ⟨theta, supported, pairJoint⟩ :=
      (PMF.mem_support_bindOnSupport_iff _ _).mp thetaJoint
    obtain ⟨pair, pairMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp pairJoint
    exact ⟨supported, selected, linked theta supported tape selected pair pairMember⟩

/-- The actual initialized implementation preserves the original input,
exclusions, complete typed terminal readout and the whole payoff vector jointly. -/
theorem phaseProposalUnflagged_initialized_joint_readout
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (initialValues : ∀ theta ∈ setup.initialLaw.support,
      ∀ {name : VarId} {owner : Player} {payload : L.Ty}
        (cell : HasVar setup.context name (.commitment owner payload)),
        ∃ value, theta.get cell = .success value)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    {length : Nat} (prior : PMF (ReservedEpoch.Tape Player length))
    (activationGap processingGap : Nat)
    (gaps : ∀ tape ∈ prior.support,
      tape.BoundedGaps (ReservedEpoch.completionCycles runtime) activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : horizon ≤ bounds.candidateCount)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    ((app).finish initial horizon
      (ReservedEpoch.implementation runtime leaks
        (ReservedEpoch.packetCapacity runtime) prior).scheduler
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) none).map
          (fun state =>
            ((phaseSourceReadout setup mode runtime leaks state).map (initialState setup.program),
              state.map (fun current => current.execution.application.current.excluded),
              phaseSourceReadout setup mode runtime leaks state,
              fun who => phaseExclusionBase setup mode runtime leaks utility excludedPayoff state
                who)) =
      (setup.proposalRecoveryModel.runBehavioralTerminalFrom
        setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
          (setup.proposalRecoveryNormalizedTrembledProfile
            0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
              setup.proposalRecoveryProtocol.initHistory).map (fun history =>
                ((setup.protocolReadout (setup.commitRecoverySourceState history.state)).map
                    (initialState setup.program),
                  history.state.map CommitRecoveryState.excluded,
                  setup.protocolReadout (setup.commitRecoverySourceState history.state),
                  fun who => setup.commitRecoveryPayoff utility excludedPayoff who
                    ⟨history.state, setup.proposalRecoveryEraseTrace history.trace⟩)) := by
  obtain ⟨joint, _draws, native, source, linked⟩ :=
    phaseProposalUnflagged_initialized_terminal_coupling setup mode runtime leaks bounds plan
      complete covered maximal initialValues values fullValues prior activationGap processingGap
        gaps margin capacity utility excludedPayoff
  rw [← native, ← source, PMF.map_comp, PMF.map_comp]
  apply map_congr_on_support
  intro result member
  obtain ⟨_thetaSupport, _tapeSupport, ending, _next, state, _phases, _history, _terminal,
    _nativeInputs, _sourceInputs, excluded, readout, payoff⟩ := linked result member
  dsimp only [Function.comp_def]
  rw [state]
  simp only [Option.map_some, excluded, readout, payoff]

end Vegas
