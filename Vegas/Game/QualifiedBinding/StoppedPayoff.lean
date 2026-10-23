/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.QualifiedBinding.AnnotationMass

/-! # Fixed-tape qualified source payoff attachment -/

noncomputable section

namespace Vegas.PhaseProposalQualifiedBinding

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (values : ∀ who (key : setup.ProposalRecoveryComponent who),
    PMF (setup.CommitRecoveryValueChoice who key.1))

open scoped ENNReal

attribute [local implicit_reducible] InformationModel.InformationSite

section QualifiedPayoffAttachment

variable (implementation : ReservedConcurrentImplementation setup)

local notation "nativeApplication" => implementation.application
local notation "nativeMenu" => PhaseCount.onePacketMenu implementation.runtime
  implementation.leaks implementation.bounds
local notation "nativeInitial" => implementation.initial
local notation "nativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu implementation.runtime implementation.leaks implementation.bounds)
  implementation.initial implementation.horizon implementation.scheduler
local notation "nativeModel" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu implementation.runtime implementation.leaks implementation.bounds)
  implementation.initial implementation.horizon implementation.scheduler

private def fixedTapeCompatible
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (state : (nativeApplication).ProtocolState) : Prop :=
  state.elim True fun control => (nativeApplication).commandConsistentFrom
    (fun tape past view => ReservedEpoch.command implementation.runtime implementation.leaks
      (ReservedEpoch.packetCapacity implementation.runtime) tape past.length view)
    tape [] control.execution.environmentRecall

private theorem fixed_tape_step
    (serviceScheduler : (nativeApplication).Scheduler)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (before after : (nativeApplication).ProtocolState)
    (joint : Player → Option (nativeApplication).Action)
    (realized : after ∈ ((nativeApplication).transition nativeInitial implementation.horizon
      serviceScheduler before joint).support)
    (compatible : fixedTapeCompatible setup implementation tape after) :
    fixedTapeCompatible setup implementation tape before ∧
      after ∈ ((nativeApplication).transition nativeInitial implementation.horizon
        (ReservedEpoch.family implementation.runtime implementation.leaks
          (ReservedEpoch.packetCapacity implementation.runtime) tape) before joint).support := by
  cases before with
  | none => exact ⟨True.intro, realized⟩
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some owner =>
          rw [ReactiveApplication.transition, PMF.mem_support_pure_iff] at realized
          subst after
          refine ⟨?_, ?_⟩
          · simpa only [fixedTapeCompatible, Option.elim_some,
              (nativeApplication).respond_environmentRecall] using compatible
          · exact (PMF.mem_support_pure_iff _ _).mpr rfl
      | none =>
          cases remaining with
          | zero =>
              rw [ReactiveApplication.transition, PMF.mem_support_pure_iff] at realized
              subst after
              exact ⟨compatible, (PMF.mem_support_pure_iff _ _).mpr rfl⟩
          | succ remaining =>
              obtain ⟨command, _selected, moved⟩ :=
                (PMF.mem_support_bind_iff ..).mp realized
              obtain ⟨next, supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp moved
              have recalled := (nativeApplication).environmentStep_environmentRecall execution next
                command supported
              change (nativeApplication).commandConsistentFrom _ tape [] next.environmentRecall
                at compatible
              rw [recalled, (nativeApplication).commandConsistent_snoc] at compatible
              refine ⟨compatible.1, ?_⟩
              apply (PMF.mem_support_bind_iff ..).mpr
              refine ⟨command, ?_, ?_⟩
              · rw [ReservedEpoch.family, compatible.2]
                exact (PMF.mem_support_pure_iff _ _).mpr rfl
              · exact (PMF.mem_support_map_iff ..).mpr ⟨next, supported, rfl⟩

private def fixedTapeTrace
    (serviceScheduler : (nativeApplication).Scheduler)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength) :
    ∀ {state : (nativeApplication).ProtocolState},
      ((nativeMenu).protocol nativeInitial implementation.horizon serviceScheduler).Trace state →
      fixedTapeCompatible setup implementation tape state →
      ((nativeMenu).protocol nativeInitial implementation.horizon
        (ReservedEpoch.family implementation.runtime implementation.leaks
          (ReservedEpoch.packetCapacity implementation.runtime) tape)).Trace state
  | _, .start, _ => .start
  | _, .extend prior joint legal realized, compatible =>
      let fixed := fixed_tape_step setup implementation serviceScheduler tape _ _ joint realized
        compatible
      .extend (fixedTapeTrace serviceScheduler tape prior fixed.1) joint legal fixed.2

private theorem fixed_tape_compatible_of_prefix
    (serviceScheduler : (nativeApplication).Scheduler)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    {first : (nativeApplication).ProtocolState}
    {prior : ((nativeMenu).protocol nativeInitial implementation.horizon serviceScheduler).Trace
      first} :
    ∀ {last : (nativeApplication).ProtocolState}
      {trace : ((nativeMenu).protocol nativeInitial implementation.horizon serviceScheduler).Trace
        last},
      TracePrefix prior trace → fixedTapeCompatible setup implementation tape last →
        fixedTapeCompatible setup implementation tape first
  | _, _, .refl, compatible => compatible
  | _, _, .extend kept joint legal realized, compatible =>
      fixed_tape_compatible_of_prefix serviceScheduler tape kept
        (fixed_tape_step setup implementation serviceScheduler tape _ _ joint realized
          compatible).1

private theorem fixed_tape_trace_prefix
    (serviceScheduler : (nativeApplication).Scheduler)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    {first : (nativeApplication).ProtocolState}
    {prior : ((nativeMenu).protocol nativeInitial implementation.horizon serviceScheduler).Trace
      first} :
    ∀ {last : (nativeApplication).ProtocolState}
      {trace : ((nativeMenu).protocol nativeInitial implementation.horizon serviceScheduler).Trace
        last}
      (retained : TracePrefix prior trace)
      (compatible : fixedTapeCompatible setup implementation tape last),
      TracePrefix
        (fixedTapeTrace setup implementation serviceScheduler tape prior
          (fixed_tape_compatible_of_prefix setup implementation serviceScheduler tape retained
            compatible))
        (fixedTapeTrace setup implementation serviceScheduler tape trace compatible)
  | _, _, .refl, _ => .refl
  | _, _, .extend kept joint legal realized, compatible =>
      .extend (fixed_tape_trace_prefix serviceScheduler tape kept
        (fixed_tape_step setup implementation serviceScheduler tape _ _ joint realized
          compatible).1) _ _ _

private theorem prefix_tape_compatible
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (supported : tape ∈ (prefixTapeLaw setup implementation ⟨some control, trace⟩).support) :
    tape ∈ implementation.prior.support ∧
      fixedTapeCompatible setup implementation tape (some control) := by
  obtain ⟨original, ⟨fixed⟩⟩ :=
    (nativeApplication).schedulerMixture_trace_of_posterior_support implementation.prior
      (ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime)) nativeInitial implementation.horizon
      control ((nativeMenu).toRawTrace nativeInitial implementation.horizon
        implementation.scheduler trace) tape supported
  refine ⟨original, ?_⟩
  exact ((nativeApplication).deterministic_transcript_invariant
    (fun tape past view => ReservedEpoch.command implementation.runtime implementation.leaks
      (ReservedEpoch.packetCapacity implementation.runtime) tape past.length view) tape).history
    nativeInitial implementation.horizon (fun _ _ => True.intro) fixed

private theorem fixed_tape_trace_length
    (serviceScheduler : (nativeApplication).Scheduler)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength) :
    ∀ {state : (nativeApplication).ProtocolState}
      (trace : ((nativeMenu).protocol nativeInitial implementation.horizon serviceScheduler).Trace
        state) (compatible : fixedTapeCompatible setup implementation tape state),
      (fixedTapeTrace setup implementation serviceScheduler tape trace compatible).length =
        trace.length
  | _, .start, _ => rfl
  | _, .extend prior joint _legal realized, compatible =>
      congrArg (· + 1) (fixed_tape_trace_length serviceScheduler tape prior
        (fixed_tape_step setup implementation serviceScheduler tape _ _ joint realized
          compatible).1)

/-- A supported tape changes the service proof of an original prefix while
retaining its literal chronological emitted assignments. -/
private theorem fixed_tape_emission_frontier
    (serviceScheduler : (nativeApplication).Scheduler)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength) :
    ∀ {state : (nativeApplication).ProtocolState}
      (trace : ((nativeMenu).protocol nativeInitial implementation.horizon serviceScheduler).Trace
        state) (compatible : fixedTapeCompatible setup implementation tape state)
      (anchor : (nativeApplication).Execution)
      (phase : RuntimePhase (serviceGraph setup .concurrent)) (anchorLength : Nat)
      (config : (serviceGraph setup .concurrent).Config),
      phaseProposalEmissionFrontier setup .concurrent implementation.runtime implementation.leaks
        anchor phase anchorLength config nativeInitial implementation.horizon
          (ReservedEpoch.family implementation.runtime implementation.leaks
            (ReservedEpoch.packetCapacity implementation.runtime) tape)
          ((nativeMenu).toRawTrace nativeInitial implementation.horizon _
            (fixedTapeTrace setup implementation serviceScheduler tape trace compatible)) =
        phaseProposalEmissionFrontier setup .concurrent implementation.runtime implementation.leaks
          anchor phase anchorLength config nativeInitial implementation.horizon serviceScheduler
            ((nativeMenu).toRawTrace nativeInitial implementation.horizon serviceScheduler trace)
  | _, .start, _, _, _, _, _ => rfl
  | _, .extend prior joint legal realized, compatible, anchor, phase, anchorLength, config => by
      simp only [fixedTapeTrace, ReactiveApplication.ResponseMenu.toRawTrace,
        phaseProposalEmissionFrontier, ReactiveApplication.ResponseMenu.toRawTrace_length,
        fixed_tape_emission_frontier serviceScheduler tape prior
          (fixed_tape_step setup implementation serviceScheduler tape _ _ joint realized
            compatible).1 anchor phase anchorLength config]
      have length := ((nativeMenu).toRawTrace_length nativeInitial implementation.horizon
        (ReservedEpoch.family implementation.runtime implementation.leaks
          (ReservedEpoch.packetCapacity implementation.runtime) tape)
        (fixedTapeTrace setup implementation serviceScheduler tape prior
          (fixed_tape_step setup implementation serviceScheduler tape _ _ joint realized
            compatible).1)).trans
        (fixed_tape_trace_length setup implementation serviceScheduler tape prior _)
      exact congrArg (fun depth => if anchorLength ≤ depth then _ else _) length

private theorem source_terminal_payoff_of_erased_history
    (first second : setup.proposalRecoveryProtocol.History)
    (same : setup.proposalRecoveryErasedHistory first =
      setup.proposalRecoveryErasedHistory second)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) :
    (setup.proposalRecoveryModel.runBehavioralTerminalFrom
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
      (sourceUnflaggedStrategy setup values) first).map
        (setup.proposalRecoveryPayoff utility excludedPayoff who) =
      (setup.proposalRecoveryModel.runBehavioralTerminalFrom
        setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
        (sourceUnflaggedStrategy setup values) second).map
          (setup.proposalRecoveryPayoff utility excludedPayoff who) := by
  have normalized : ∀ owner left right,
      setup.proposalRecoveryQuery owner left = setup.proposalRecoveryQuery owner right →
        ((sourceUnflaggedStrategy setup values) owner left).map Subtype.val =
          ((sourceUnflaggedStrategy setup values) owner right).map Subtype.val :=
    by
      dsimp only [sourceUnflaggedStrategy, Setup.proposalRecoveryNormalizedTrembledProfile]
      exact setup.proposalRecoveryPrescribedProfile_normalized _
  have terminal := setup.proposalRecovery_terminal_erased_eq
    (sourceUnflaggedStrategy setup values) normalized
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories first second same
  simpa only [PMF.map_comp, Function.comp_def, ← setup.proposalRecoveryPayoff_eq_image]
    using congrArg
      (PMF.map (setup.proposalRecoveryImagePayoff utility excludedPayoff who)) terminal

omit [Fintype Player] in
/-- A full semantic commitment word attaches to the actual archive lift.
The source suffix is replayed from the retained erased entry before commitment
determinacy is used, so hidden historical proposal causes remain literal. -/
private theorem binding_close_erased_history_of_semantic_word
    (first : setup.proposalRecoveryProtocol.History)
    (current : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (same : setup.proposalRecoveryErasedHistory first =
      setup.proposalRecoveryErasedHistory ⟨some current, prior⟩)
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (left : setup.proposalRecoveryProtocol.History)
    (right : setup.commitRecoveryProtocol.History)
    (leftPrefix : TracePrefix first.trace left.trace)
    (rightPrefix : TracePrefix (setup.proposalRecoveryEraseTrace prior) right.trace)
    (word : List (Player → Option (CommitRecoveryMove Player L)))
    (leftWord : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace left.trace) =
      word ++ setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace first.trace))
    (rightWord : setup.recoveryJointRecall right.trace =
      word ++ setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace prior))
    (within : word.length + ProtocolState.commitEnd setup.program current.point ≤
      ProtocolState.remaining setup.program current.point)
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    (ordinary : setup.proposalRecoveryLiftTrace labels
      (setup.proposalRecoveryEraseTrace prior) = prior) :
    setup.proposalRecoveryErasedHistory left =
      setup.proposalRecoveryErasedHistory
        ⟨right.state, setup.proposalRecoveryLiftTrace labels right.trace⟩ := by
  obtain ⟨replayed, emitted, retained, erased, originalWord, replayedWord,
      _originalLength, replayedLength⟩ :=
    setup.proposalRecovery_supported_suffix_of_erased_history_eq first
      ⟨some current, prior⟩ same left.trace leftPrefix
  have originalSemantic := congrArg
    (List.map SourceProgram.Setup.proposalRecoveryJoint) originalWord
  simp only [List.map_append, setup.proposalRecoveryJointRecall_semantic] at originalSemantic
  have emittedSemantic : emitted.map SourceProgram.Setup.proposalRecoveryJoint = word :=
    List.append_cancel_right (originalSemantic.symm.trans leftWord)
  have replayedSemantic := congrArg
    (List.map SourceProgram.Setup.proposalRecoveryJoint) replayedWord
  simp only [List.map_append, setup.proposalRecoveryJointRecall_semantic,
    emittedSemantic] at replayedSemantic
  have sameWord : setup.recoveryJointRecall
      (setup.proposalRecoveryEraseTrace replayed.trace) =
        setup.recoveryJointRecall right.trace := replayedSemantic.trans rightWord.symm
  have wordLength : emitted.length = word.length := by
    simpa only [List.length_map] using congrArg List.length emittedSemantic
  have replayedWithin : replayed.trace.length +
      ProtocolState.commitEnd setup.program current.point ≤
        prior.length + ProtocolState.remaining setup.program current.point := by
    change replayed.trace.length = prior.length + emitted.length at replayedLength
    omega
  have semantic := setup.commitRecovery_history_eq_of_commit_window current
    (setup.proposalRecoveryEraseTrace prior) committing
    (setup.proposalRecoveryEraseTrace replayed.trace) right.trace
    (proposalRecovery_reaches_semantic setup retained.reachesWithin)
    rightPrefix.reachesWithin sameWord (by
      simpa only [setup.proposalRecoveryEraseTrace_length] using replayedWithin)
  have lift := proposalRecovery_liftTrace_commit_window setup labels current prior ordinary
    committing replayed.trace retained replayedWithin
  have enriched := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    (⟨history.state, setup.proposalRecoveryLiftTrace labels history.trace⟩ :
      setup.proposalRecoveryProtocol.History)) semantic
  have equal : replayed =
      (⟨right.state, setup.proposalRecoveryLiftTrace labels right.trace⟩ :
        setup.proposalRecoveryProtocol.History) := by
    simpa only [lift] using enriched
  exact erased.trans (congrArg setup.proposalRecoveryErasedHistory equal)

omit [Fintype Player] in
private theorem checkpoint_binding_values_of_erased_history
    {state : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (checkpoint : RecoverySourceCheckpoint setup .concurrent state)
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (same : setup.proposalRecoveryErasedHistory ⟨some current, trace⟩ =
      setup.proposalRecoveryErasedHistory
        ⟨_, setup.proposalRecoveryLiftTrace labels checkpoint.trace⟩)
    (who : Player)
    (proper : ProtocolState.BindingsHoldValues who setup.program current.point) :
    checkpoint.source.BindingsHoldValues who := by
  have states := Option.some.inj (congrArg (fun image : setup.ProposalRecoveryHistoryImage =>
    image.1.1) same)
  have points := congrArg CommitRecoveryState.point states
  apply (ProtocolState.bindingsHoldValues_entry who checkpoint.residual.tail _).mp
  apply (checkpoint.origin.bindingsHoldValues_lift who _).mp
  apply (ProtocolState.bindingsHoldValues_withHistory who setup.program _ (fun _ => [])).mp
  change ProtocolState.BindingsHoldValues who setup.program
    (CommitRecoveryState.eraseHistory
      (CommitRecoveryState.atPoint (checkpoint.residual.lift
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
          state.entry.excluded state.generation)).point
  rw [← points]
  exact (ProtocolState.bindingsHoldValues_withHistory who setup.program current.point
    (fun _ => [])).mpr proper

open Classical in
/-- Every legal proper alias reads the original admission bit. Both the
focal owned word and the foreign words keep their original tape coordinates. -/
private theorem bindingAdmissionBit_eq_available_binding
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control)) (active : control.actor = some who)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload)
    (value : L.Val payload) (serial : Nat)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (available : (⟨some material⟩ : (nativeApplication).Action) ∈
      (nativeMenu).actions who (control.execution.recall who)
        (control.execution.observe nativeApplication who))
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    (prepared : PhaseProposal.bindingPreparation material = some ⟨payload, value⟩)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (installed : phase ∈ control.execution.application.phases.head?)
    (commitment : phase.kind = .commitment) :
    bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape =
      decide (∀ named ∈ phase.events, ∀ owner,
        (serviceGraph setup .concurrent).actor? named = some owner →
        owner ∉ control.execution.application.entry.excluded →
        ReservedEpoch.ownedAcceptanceWord implementation.runtime implementation.leaks tape
          (control.execution.respond nativeApplication who ⟨some material⟩) owner named) := by
  classical
  let offered := (∃ candidate : WitnessedSubmission (serviceGraph setup .concurrent),
    (⟨some candidate⟩ : (nativeApplication).Action) ∈
      (nativeMenu).actions who (control.execution.recall who)
        (control.execution.observe nativeApplication who) ∧
    ∃ (domain : L.Ty) (value : L.Val domain) (serial : Nat),
      (serviceGraph setup .concurrent).outputLayout event = .binding who domain ∧
      candidate.call.packet = .commitment event (who, .prepared serial) ∧
      PhaseProposal.bindingPreparation candidate = some ⟨domain, value⟩)
  have existsOffered : offered :=
    ⟨material, available, payload, value, serial, binding, packet, prepared⟩
  let representative := Classical.choose existsOffered
  have representativeAvailable : (⟨some representative⟩ : (nativeApplication).Action) ∈
      (nativeMenu).actions who (control.execution.recall who)
        (control.execution.observe nativeApplication who) :=
    (Classical.choose_spec existsOffered).1
  have trace' : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace
        (some ⟨control.remaining, some who, control.execution⟩) := by
    rw [← active]
    have initialEq : ((setup.initialLaw.map encodeInputs).map
        (PhaseRuntimeState.initial implementation.plan)) = nativeInitial := PMF.map_comp _ _ _
    exact cast (congrArg (fun law => ((nativeMenu).protocol law implementation.horizon
      implementation.scheduler).Trace (some control)) initialEq.symm) trace
  have words (owner : Player) (named : (serviceGraph setup .concurrent).EventId) :
      ReservedEpoch.ownedAcceptanceWord implementation.runtime implementation.leaks tape
        (control.execution.respond nativeApplication who ⟨some representative⟩) owner named ↔
      ReservedEpoch.ownedAcceptanceWord implementation.runtime implementation.leaks tape
        (control.execution.respond nativeApplication who ⟨some material⟩) owner named := by
    by_cases same : owner = who
    · subst owner
      exact ReservedEpoch.ownedAcceptanceWord_available_bindings_eq implementation.runtime
        implementation.leaks tape implementation.bounds implementation.plan
          (serviceGraph_revealRelaxedOrdered setup .concurrent)
            (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
              control.remaining who control.execution trace' representative material
                representativeAvailable available phase installed commitment named
    · exact (ReservedEpoch.ownedAcceptanceWord_respond_foreign implementation.runtime
        implementation.leaks tape control.execution who owner same ⟨some representative⟩
          named).trans
        (ReservedEpoch.ownedAcceptanceWord_respond_foreign implementation.runtime
          implementation.leaks tape control.execution who owner same ⟨some material⟩
            named).symm
  unfold bindingAdmissionBit
  dsimp only [History.state]
  rw [dite_eq_left existsOffered]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨actual, actualInstalled, _actualKind, accepted⟩
    have equal : actual = phase := Option.some.inj
      ((Option.mem_def.mp actualInstalled).symm.trans (Option.mem_def.mp installed))
    subst actual
    intro named inside owner acting surviving
    exact (words owner named).mp (accepted named inside owner acting surviving)
  · intro accepted
    refine ⟨phase, installed, commitment, ?_⟩
    intro named inside owner acting surviving
    exact (words owner named).mpr (accepted named inside owner acting surviving)

open Classical in
/-- The qualification experiment disintegrates on the original prefix tape
posterior. The current atom is inserted before either stopped continuation. -/
theorem stoppedFinish_qualified_physical
    (operational : implementation.Operational)
    (who : Player) (history : (nativeProtocol).History)
    (choice : (nativeModel).Choice who ((nativeModel).infoOf who history.trace))
    (remaining : Nat) (execution : (nativeApplication).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (response : (nativeApplication).Action) (selected : choice.1 = some response)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (installed : phase ∈ execution.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    (stoppedFinish setup .concurrent implementation.runtime implementation.leaks
      implementation.bounds implementation.plan implementation.prior values who history
      choice).map (fun result =>
        if foreignGood setup .concurrent implementation.runtime implementation.leaks
            implementation.bounds implementation.plan implementation.prior who history ∧
            originalAdmissionGate setup .concurrent implementation.runtime implementation.leaks
              implementation.bounds implementation.plan implementation.prior history result.1
        then some (phaseExclusionBase setup .concurrent implementation.runtime
          implementation.leaks utility excludedPayoff result.2.state who)
        else none) =
      (prefixTapeLaw setup implementation history).bind fun tape =>
        ((nativeApplication).runUntil
          (ReservedEpoch.family implementation.runtime implementation.leaks
            (ReservedEpoch.packetCapacity implementation.runtime) tape)
          (phaseProposalUnflaggedPolicy setup .concurrent implementation.runtime
            implementation.leaks implementation.bounds implementation.plan values)
          (fun next => next.application.attempt ≠ execution.application.attempt)
          remaining (execution.respond nativeApplication who response)).bind fun ending =>
            ((nativeApplication).finish nativeInitial implementation.horizon
              (ReservedEpoch.family implementation.runtime implementation.leaks
                (ReservedEpoch.packetCapacity implementation.runtime) tape)
              (phaseProposalUnflaggedPolicy setup .concurrent implementation.runtime
                implementation.leaks implementation.bounds implementation.plan values)
              (some ⟨implementation.horizon - ending.environmentRecall.length, none, ending⟩)).map
                (fun terminal =>
                  if foreignGood setup .concurrent implementation.runtime implementation.leaks
                      implementation.bounds implementation.plan implementation.prior who history ∧
                      ending.application.attempt ≠ execution.application.attempt ∧
                      ending.application.current.excluded = execution.application.entry.excluded
                  then some (phaseExclusionBase setup .concurrent implementation.runtime
                    implementation.leaks utility excludedPayoff terminal who)
                  else none) := by
  have joint := stoppedFinish_gate_seed_joint setup .concurrent implementation.runtime
    implementation.leaks implementation.bounds implementation.plan implementation.prior values
      implementation.activationGap implementation.processingGap operational.boundedGaps
        operational.maximalPhases who history choice remaining execution current response selected
          phase installed commitment
  let read := fun result : (Bool × (nativeApplication).ProtocolState) ×
      ReservedEpoch.Tape Player implementation.tapeLength =>
    if foreignGood setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan implementation.prior who history ∧
        result.1.1 = true
    then some (phaseExclusionBase setup .concurrent implementation.runtime
      implementation.leaks utility excludedPayoff result.1.2 who)
    else none
  have projected := congrArg (PMF.map read) joint
  simpa only [read, ← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind, PMF.pure_bind,
    PMF.bind_const, decide_eq_true_eq, prefixTapeLaw, current, and_assoc,
    ReservedConcurrentImplementation.initial, ReservedConcurrentImplementation.horizon]
      using projected

/-- The fixed tape's actual active callback is already beyond processing;
inserting its current response leaves that same environment cursor. -/
private theorem response_after_processing
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (who : Player) (control : (nativeApplication).Control)
    (trace : ((nativeMenu).protocol nativeInitial implementation.horizon
      (ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) tape)).Trace (some control))
    (active : control.actor = some who) (response : (nativeApplication).Action) :
    ReservedEpoch.packetCapacity implementation.runtime ≤
      (control.execution.respond nativeApplication who response).environmentRecall.length %
        ReservedEpoch.cycleWidth
          («graph» := serviceGraph setup .concurrent)
          (ReservedEpoch.packetCapacity implementation.runtime) := by
  have actual := ReservedEpoch.active_after_processing implementation.runtime
    implementation.leaks (ReservedEpoch.packetCapacity implementation.runtime) tape nativeInitial
      implementation.horizon control ((nativeMenu).toRawTrace nativeInitial
        implementation.horizon _ trace) who active
  simpa only [(nativeApplication).respond_environmentRecall] using actual

/-- The original all-admission word characterizes the clean first exit on
each actual stopped support point, including its false branch. -/
private theorem closing_gate_iff_acceptance_word
    (serviceScheduler : (nativeApplication).Scheduler)
    (before ending : (nativeApplication).Control)
    (trace : ((nativeMenu).protocol nativeInitial implementation.horizon
      serviceScheduler).Trace (some before))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (installed : phase ∈ before.execution.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (raw : RecoveryState (serviceGraph setup .concurrent))
    (effect : PhaseClosingEffect implementation.runtime implementation.leaks
      before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt)
    (finished : phase.Finished (phase.drain raw))
    (coverage : (phase.drain raw).FailureCoverage)
    (excluded : (phase.drain raw).excluded = ending.execution.application.current.excluded)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (anchor : (nativeApplication).Execution)
    (word : ∀ event ∈ phase.events, ∀ owner payload,
      (serviceGraph setup .concurrent).outputLayout event = .binding owner payload →
      (raw.native.accepted (.inr event) ≠ none ↔
        ReservedEpoch.ownedAcceptanceWord implementation.runtime implementation.leaks tape
          anchor owner event)) :
    ending.execution.application.current.excluded = before.execution.application.entry.excluded ↔
      ∀ event ∈ phase.events, ∀ owner,
        (serviceGraph setup .concurrent).actor? event = some owner →
        owner ∉ before.execution.application.entry.excluded →
        ReservedEpoch.ownedAcceptanceWord implementation.runtime implementation.leaks tape
          anchor owner event := by
  have trace' : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon serviceScheduler).Trace (some before) := by
    rw [PMF.map_comp]
    exact trace
  constructor
  · intro clean event inside owner acting active
    obtain ⟨author, payload, binding⟩ := commitment ▸ phase.fields event
      ((phase.mem_events event).mp inside).1 ((phase.mem_events event).mp inside).2
    have sameOwner : author = owner := Option.some.inj
      (((serviceGraph setup .concurrent).actor?_of_outputLayout_binding binding).symm.trans acting)
    subst author
    apply (word event inside owner payload binding).mp
    intro absent
    have read := ReservedEpoch.original_binding_publicFailure_iff implementation.runtime
      implementation.leaks (serviceGraph_revealRelaxedOrdered setup .concurrent)
        implementation.plan (setup.initialLaw.map encodeInputs) implementation.horizon
          serviceScheduler before ((nativeMenu).toRawTrace _ implementation.horizon
            serviceScheduler trace') ending.execution raw changed effect phase installed commitment
              finished event
    have failure : (phase.drain raw).native.PublicFailure event := read.mpr (by
      simp only [not_lt_of_ge ((phase.mem_events event).mp inside).1,
        ((phase.mem_events event).mp inside).2, ↓reduceIte]
      exact absent)
    exact active (clean ▸ excluded ▸ coverage.covered event owner acting failure)
  · intro admitted
    have clean := closing_all_admitted_excluded_eq setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan serviceScheduler before ending
        trace phase installed commitment raw effect changed finished
          (by
            intro event inside owner acting active
            obtain ⟨author, payload, binding⟩ := commitment ▸ phase.fields event
              ((phase.mem_events event).mp inside).1 ((phase.mem_events event).mp inside).2
            have sameOwner : author = owner := Option.some.inj
              (((serviceGraph setup .concurrent).actor?_of_outputLayout_binding binding).symm.trans
                acting)
            subst author
            rw [(phase.drain_tables raw).1]
            exact (word event inside owner payload binding).mpr
              (admitted event inside owner acting active))
    exact excluded.symm.trans clean

/-- The full witness at an actual clean close uses the supplied raw operation.
The ordinary closing theorem supplies its readout; the raw witness supplies
the proposal delta required by the archived normalizer. -/
private theorem ordinary_clean_closing_witness
    (operational : implementation.Operational)
    (serviceScheduler : (nativeApplication).Scheduler)
    (before ending : (nativeApplication).Control)
    (trace : ((nativeMenu).protocol nativeInitial implementation.horizon
      serviceScheduler).Trace (some before))
    (witness : RecoverySourceWitness setup .concurrent implementation.plan
      before.execution.application)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (rest : List (RuntimePhase (serviceGraph setup .concurrent)))
    (installed : before.execution.application.phases = phase :: rest)
    (commitment : phase.kind = .commitment)
    (raw : RecoveryState (serviceGraph setup .concurrent))
    (effect : PhaseClosingEffect implementation.runtime implementation.leaks
      before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt)
    (normalized : ending.execution.application =
      ({ before.execution.application with current := raw } :
        PhaseRuntimeState (serviceGraph setup .concurrent)).normalize)
    (finished : phase.Finished (phase.drain raw))
    (excluded : (phase.drain raw).excluded = before.execution.application.entry.excluded) :
    ∃ (rawWitness : RecoverySourceWitness setup .concurrent implementation.plan
        ({ before.execution.application with current := raw } :
          PhaseRuntimeState (serviceGraph setup .concurrent)))
      (completed : RecoverySourceWitness setup .concurrent implementation.plan
        (⟨rest, before.execution.application.generation, phase.drain raw, phase.drain raw,
          before.execution.application.retired⟩ :
            PhaseRuntimeState (serviceGraph setup .concurrent))),
      rawWitness.checkpoint = witness.checkpoint.transfer
        (other := { before.execution.application with current := raw }) rfl rfl rfl ∧
      (⟨_, rawWitness.checkpoint.trace⟩ : setup.commitRecoveryProtocol.History) =
        ⟨_, witness.checkpoint.trace⟩ ∧
      (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
        ⟨_, witness.checkpoint.trace⟩ ⟨_, completed.checkpoint.trace⟩ ∧
        setup.recoveryJointRecall completed.checkpoint.trace =
          (witness.checkpoint.commitInstructionWord (phase.drain raw).native).reverse ++
            setup.recoveryJointRecall witness.checkpoint.trace) ∧
      rawWitness.checkpoint.ProposalDelta implementation.plan completed.checkpoint ∧
      ending.execution.application = PhaseRuntimeState.settle rest
        before.execution.application.generation (phase.drain raw) (phase.drain raw)
          before.execution.application.retired ∧
      (match commitPhase witness.checkpoint.residual.tail with
      | ⟨_, _, suffix, block, reconstruct, _⟩ =>
        let embedding := cast (congrArg (fun program => OutputEmbedding
          (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
            witness.checkpoint.embedding
        phaseProposalBindingWord setup.program block suffix embedding
          before.execution.application.entry.excluded (phase.drain raw).native.config.store
            witness.checkpoint.source =
              witness.checkpoint.commitInstructionWord (phase.drain raw).native) := by
  have committing := witness.checkpoint.compiled.atCommit_of_bindingPhase setup.program
    .concurrent witness.checkpoint.residual.tail witness.checkpoint.refs
      witness.checkpoint.source.revelations witness.checkpoint.registry
        witness.checkpoint.embedding witness.checkpoint.before
          before.execution.application.attempt.phase phase commitment (by
            simp only [PhaseRuntimeState.attempt, installed, List.head?_cons,
              Option.map_some, Option.getD_some]) witness.checkpoint.source
  obtain ⟨_checkpoint, _point, _path, _settled, readout⟩ :=
    witness.checkpoint.ordinary_closing_binding_checkpoint setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
        operational.maximalPhases implementation.horizon serviceScheduler before ending
          (by erw [PMF.map_comp]; exact trace) committing phase rest installed commitment raw
            effect changed normalized finished excluded
  obtain ⟨rawWitness, rawCheckpoint, rawHistory⟩ :=
    RecoverySourceWitness.raw_closing_checkpoint setup .concurrent implementation.runtime
      implementation.leaks implementation.plan before ending witness raw effect changed
  obtain ⟨completed, _point, ⟨fuel, path, instructions⟩, delta, settled⟩ :=
    rawWitness.completed_binding_history operational.maximalPhases phase rest installed
      commitment finished (by rw [excluded]; simp)
  have read := witness.checkpoint.transfer_binding_readback
    (other := { before.execution.application with current := raw }) rfl rfl rfl
      (phase.drain raw)
  have word : rawWitness.checkpoint.commitInstructionWord (phase.drain raw).native =
      witness.checkpoint.commitInstructionWord (phase.drain raw).native := by
    rw [rawCheckpoint, read.2]
  have recalled := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    setup.recoveryJointRecall history.trace) rawHistory
  rw [word, recalled] at instructions
  exact ⟨rawWitness, completed, rawCheckpoint, rawHistory,
    ⟨fuel, rawHistory ▸ path, instructions⟩, delta, normalized.trans settled, readout⟩

/-- Normalization and finish use the same actual closing operation and tape.
The completed witness may come from any supported full-word attachment. -/
private theorem completed_binding_finish_payoff
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (tapeSupported : tape ∈ implementation.prior.support)
    (before ending : (nativeApplication).Control)
    (prior : ((nativeMenu).protocol nativeInitial implementation.horizon
      (ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) tape)).Trace (some before))
    (trace : ((nativeMenu).protocol nativeInitial implementation.horizon
      (ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) tape)).Trace (some ending))
    (idle : ending.actor = none)
    (beforeWitness : RecoverySourceWitness setup .concurrent implementation.plan
      before.execution.application)
    (beforeArchived : beforeWitness.checkpoint.ArchivedProposals
      before.execution.network.inputs)
    (raw : RecoveryState (serviceGraph setup .concurrent))
    (effect : PhaseClosingEffect implementation.runtime implementation.leaks
      before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt)
    (rawWitness : RecoverySourceWitness setup .concurrent implementation.plan
      ({ before.execution.application with current := raw } :
        PhaseRuntimeState (serviceGraph setup .concurrent)))
    (rawCheckpoint : rawWitness.checkpoint = beforeWitness.checkpoint.transfer
      (other := { before.execution.application with current := raw }) rfl rfl rfl)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (rest : List (RuntimePhase (serviceGraph setup .concurrent)))
    (installed : before.execution.application.phases = phase :: rest)
    (finished : phase.Finished (phase.drain raw))
    (excluded : (phase.drain raw).excluded = ending.execution.application.current.excluded)
    (normalized : ending.execution.application =
      ({ before.execution.application with current := raw } :
        PhaseRuntimeState (serviceGraph setup .concurrent)).normalize)
    (settled : ending.execution.application = PhaseRuntimeState.settle rest
      before.execution.application.generation (phase.drain raw) (phase.drain raw)
        before.execution.application.retired)
    (completed : RecoverySourceWitness setup .concurrent implementation.plan
      (⟨rest, before.execution.application.generation, phase.drain raw, phase.drain raw,
        before.execution.application.retired⟩ :
          PhaseRuntimeState (serviceGraph setup .concurrent)))
    (delta : rawWitness.checkpoint.ProposalDelta implementation.plan completed.checkpoint)
    (proper : ∀ owner, owner ∉ (phase.drain raw).excluded →
      completed.checkpoint.source.BindingsHoldValues owner)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) :
    ((nativeApplication).finish nativeInitial implementation.horizon
      (ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) tape)
      (phaseProposalUnflaggedPolicy setup .concurrent implementation.runtime
        implementation.leaks implementation.bounds implementation.plan values)
      (some ending)).map (fun state => phaseExclusionBase setup .concurrent
        implementation.runtime implementation.leaks utility excludedPayoff state who) =
      (setup.proposalRecoveryModel.runBehavioralTerminalFrom
        setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
        (sourceUnflaggedStrategy setup values)
        ⟨_, setup.proposalRecoveryLiftTrace
          (nativeArchiveLabels setup (PhaseProposal.sourceArchive ending.execution.network.inputs))
          completed.checkpoint.trace⟩).map
            (setup.proposalRecoveryPayoff utility excludedPayoff who) := by
  let fixed := ReservedEpoch.family implementation.runtime implementation.leaks
    (ReservedEpoch.packetCapacity implementation.runtime) tape
  have prior' : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon fixed).Trace (some before) := by
    rw [PMF.map_comp]
    exact prior
  have trace' : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon fixed).Trace (some ending) := by
    rw [PMF.map_comp]
    exact trace
  obtain ⟨next, nextPath, sourceKernel, _nextDelta, nextArchived⟩ :=
    RecoverySourceWitness.completed_normalized_archived_source setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
        operational.maximalPhases implementation.horizon fixed before ending prior'
          beforeWitness beforeArchived raw effect rawWitness rawCheckpoint phase rest installed
            finished normalized settled completed delta
              setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
                (sourceUnflaggedStrategy setup values)
  let finalWitness : RecoverySourceWitness setup .concurrent implementation.plan
      ending.execution.application := settled.symm ▸ next
  have castFacts {state other : PhaseRuntimeState (serviceGraph setup .concurrent)}
      (equal : state = other) (witness : RecoverySourceWitness setup .concurrent
        implementation.plan state) :
      ((equal ▸ witness).checkpoint.ArchivedProposals ending.execution.network.inputs ↔
        witness.checkpoint.ArchivedProposals ending.execution.network.inputs) ∧
      (∀ owner, (equal ▸ witness).checkpoint.source.BindingsHoldValues owner ↔
        witness.checkpoint.source.BindingsHoldValues owner) ∧
      ((⟨_, (equal ▸ witness).checkpoint.trace⟩ : setup.commitRecoveryProtocol.History) =
        ⟨_, witness.checkpoint.trace⟩) := by
    cases equal
    exact ⟨Iff.rfl, fun _ => Iff.rfl, rfl⟩
  have transported := castFacts settled.symm next
  have archived : finalWitness.checkpoint.ArchivedProposals ending.execution.network.inputs :=
    transported.1.mpr nextArchived
  have preserved := (completed.checkpoint.fresh_normalization_source_law .concurrent rest
    before.execution.application.generation (phase.drain raw)
      before.execution.application.retired completed.order.frontier next.checkpoint
        (Classical.choose_spec nextPath) (sourceUnflaggedStrategy setup values)
          (nativeArchiveLabels setup
            (PhaseProposal.sourceArchive ending.execution.network.inputs))).2
  have finalProper : ∀ owner, owner ∉ ending.execution.application.current.excluded →
      finalWitness.checkpoint.source.BindingsHoldValues owner := by
    intro owner active
    apply (transported.2.1 owner).mpr
    exact preserved owner (excluded.symm ▸ active) (proper owner (excluded.symm ▸ active))
  have fresh : ∀ owner, ∀ record ∈ ending.execution.recall owner,
      record.beforeView.application.2.attempt ≠ ending.execution.application.attempt := by
    have initialized : ∀ state ∈
        ((setup.initialLaw.map encodeInputs).map
          (PhaseRuntimeState.initial implementation.plan)).support, state.Ordered := by
      intro state member
      obtain ⟨inputs, _supported, rfl⟩ := PMF.support_map .. ▸ member
      exact PhaseRuntimeState.initial_ordered implementation.plan inputs
    rcases effect with ⟨id, message, result, _found, moved, _handled, _rawEq⟩ |
      ⟨command, result, moved, _supported, _rawEq⟩ <;>
      exact phase_ownRecall_fresh_after_environment implementation.runtime implementation.leaks
        _ initialized implementation.horizon fixed before
          ((nativeMenu).toRawTrace _ implementation.horizon fixed prior')
            ending.execution _ moved (Ne.symm changed)
  have finalLaw := phaseProposal_fresh_finish_payoff_law setup .concurrent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan
      operational.completePending operational.outputValues operational.maximalPhases values
        fullValues tape implementation.activationGap implementation.processingGap
          (operational.boundedGaps tape tapeSupported) operational.timely
            operational.candidateReserve utility excludedPayoff ending idle trace'
              (by
                rw [normalized]
                apply PhaseRuntimeState.normalize_entry_excluded_of_changed
                rw [← normalized]
                exact changed) fresh finalWitness archived finalProper who
  have lifted := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    (⟨history.state, setup.proposalRecoveryLiftTrace
      (nativeArchiveLabels setup (PhaseProposal.sourceArchive ending.execution.network.inputs))
        history.trace⟩ : setup.proposalRecoveryProtocol.History)) transported.2.2
  have liftedLaw := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
    (setup.proposalRecoveryModel.runBehavioralTerminalFrom
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
      (sourceUnflaggedStrategy setup values) history).map
        (setup.proposalRecoveryPayoff utility excludedPayoff who)) lifted
  have kernelLaw := congrArg (PMF.map
    (setup.proposalRecoveryPayoff utility excludedPayoff who)) sourceKernel
  have combined := finalLaw.trans (liftedLaw.trans kernelLaw.symm)
  simpa only [ReservedConcurrentImplementation.initial, ReservedConcurrentImplementation.horizon,
    PMF.map_comp, Function.comp_def] using combined

/-- Inserting a legal proper preparation conditions the original graph joint
on its full issued cylinder and the selected value. Its actual response trace
computes exactly the frontier of that conditional law. -/
private theorem inserted_binding_frontier_posterior
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨some control, trace⟩)
    (entry : NativeBindingEntry setup implementation operational control trace who event)
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal (some control) joint)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (selected : joint who = some ⟨some material⟩)
    (serial : Nat) (packet : material.call.packet = .commitment event (who, .prepared serial))
    (value : L.Val payload)
    (prepared : PhaseProposal.bindingPreparation material = some ⟨payload, value⟩)
    (realized : some ⟨control.remaining, none,
        control.execution.respond nativeApplication who ⟨some material⟩⟩ ∈
      ((nativeProtocol).step (some control) ⟨joint, legal⟩).support) :
    let profile := phaseProposalBindingPotentialProfile setup .concurrent implementation.runtime
      implementation.leaks implementation.plan entry.entry.execution entry.phase values
    let original := (serviceGraph setup .concurrent).canonicalContinuation profile
      entry.entry.execution.application.current.native.config
    let observed := fun key => issuedBindingObservation setup implementation control entry.phase
      key &&
      decide ((⟨.inr event, clean.binding⟩ : FieldRef (serviceGraph setup .concurrent).layout
        (.binding who payload)).get? key.2.1 = some (.success value))
    let frontier := phaseProposalEmissionFrontier setup .concurrent implementation.runtime
      implementation.leaks entry.entry.execution entry.phase entry.entryTrace.length
        entry.entry.execution.application.current.native.config nativeInitial implementation.horizon
          implementation.scheduler ((nativeMenu).toRawTrace nativeInitial implementation.horizon
            implementation.scheduler (trace.extend joint legal realized))
    true ∈ (original.map observed).support ∧
      (serviceGraph setup .concurrent).canonicalContinuation profile frontier =
        fiberPosterior original observed true := by
  classical
  intro profile original observed afterFrontier
  let frontier := phaseProposalEmissionFrontier setup .concurrent implementation.runtime
    implementation.leaks entry.entry.execution entry.phase entry.entryTrace.length
      entry.entry.execution.application.current.native.config nativeInitial implementation.horizon
        implementation.scheduler ((nativeMenu).toRawTrace nativeInitial implementation.horizon
          implementation.scheduler trace)
  obtain ⟨ready, present, posterior, _graphMass⟩ := binding_value_frontier_posterior setup values
    implementation operational fullValues control trace who active event payload clean foreign
      entry value
  have code : cast (congrArg (EventCode (serviceGraph setup .concurrent).layout)
      clean.binding) ((serviceGraph setup .concurrent).nodes event) = .bind who payload := by
    cases nodeView (serviceGraph setup .concurrent) event with
    | bind owner domain shape code =>
        obtain ⟨rfl, rfl⟩ := EventField.binding.inj (shape.symm.trans clean.binding)
        exact code
    | resolve owner domain source checks shape code => cases shape.symm.trans clean.binding
    | sample domain law shape code => cases shape.symm.trans clean.binding
  have result : (((⟨some material⟩ : (nativeApplication).Action).transmission.bind
      PhaseProposal.bindingPreparation).bind (fun raw => raw.as? payload)).elim
        PublicationResult.failure PublicationResult.success = .success value := by
    simp only [prepared, Option.bind_some, Raw.as?_mk, Option.elim_some]
  have afterEq : afterFrontier = phaseProposalBindingFrontierDrain setup .concurrent
      implementation.runtime implementation.leaks entry.entry.execution entry.phase
        (frontier.complete event ready
          (cast (congrArg EventField.Action clean.binding.symm) (.success value))
          (cast (congrArg EventField.Value clean.binding.symm) (.success value))) := by
    dsimp only [afterFrontier]
    rw [ReactiveApplication.ResponseMenu.toRawTrace, phaseProposalEmissionFrontier,
      ite_eq_left (by
        simpa only [ReactiveApplication.ResponseMenu.toRawTrace_length] using
          entry.retained.length_le)]
    have advance := phaseProposalBindingFrontierAdvance_binding setup .concurrent
      implementation.runtime implementation.leaks entry.entry.execution entry.phase frontier
        control.remaining who control.execution joint ⟨some material⟩ selected material rfl
          event (who, .prepared serial) packet payload clean.binding code entry.sameAttempt.symm
            entry.inside ready
    simpa only [← active, phaseProposalPreparedBindingAction, result] using advance
  exact ⟨present, by rw [afterEq]; exact posterior⟩

private def fixedStoppedLaw
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (remaining : Nat) (execution : (nativeApplication).Execution)
    (trace : ((nativeMenu).protocol nativeInitial implementation.horizon
      (ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) tape)).Trace
          (some ⟨remaining, none, execution⟩)) :
    PMF (((nativeMenu).protocol nativeInitial implementation.horizon
      (ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) tape)).History) :=
  let fixed := ReservedEpoch.family implementation.runtime implementation.leaks
    (ReservedEpoch.packetCapacity implementation.runtime) tape
  let players := ReactiveApplication.anchoredPolicy execution
    (phaseProposalUnflaggedPolicy setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values)
  let profile := fun owner => (nativeMenu).restrictPolicy nativeInitial implementation.horizon
    fixed owner (players owner)
  ((nativeMenu).information nativeInitial implementation.horizon fixed).runBehavioralUntil
    ((nativeMenu).bounded nativeInitial implementation.horizon fixed).wellFoundedHistories profile
    (fun history => match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ execution.application.attempt)
    ⟨some ⟨remaining, none, execution⟩, trace⟩

/-- Counted stopping retains the entire actual control and therefore commutes
with any continuation kernel on that control. -/
private theorem fixed_stopped_bind_state {A : Type}
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (remaining : Nat) (execution : (nativeApplication).Execution)
    (trace : ((nativeMenu).protocol nativeInitial implementation.horizon
      (ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) tape)).Trace
          (some ⟨remaining, none, execution⟩))
    (reward : (nativeApplication).ProtocolState → PMF A) :
    (fixedStoppedLaw setup values implementation tape remaining execution trace).bind
        (fun final => reward final.state) =
      ((nativeApplication).runUntil
        (ReservedEpoch.family implementation.runtime implementation.leaks
          (ReservedEpoch.packetCapacity implementation.runtime) tape)
        (phaseProposalUnflaggedPolicy setup .concurrent implementation.runtime
          implementation.leaks implementation.bounds implementation.plan values)
        (fun next => next.application.attempt ≠ execution.application.attempt)
        remaining execution).bind fun ending =>
          reward (some ⟨implementation.horizon - ending.environmentRecall.length, none, ending⟩)
            := by
  let fixed := ReservedEpoch.family implementation.runtime implementation.leaks
    (ReservedEpoch.packetCapacity implementation.runtime) tape
  let players := phaseProposalUnflaggedPolicy setup .concurrent implementation.runtime
    implementation.leaks implementation.bounds implementation.plan values
  let anchored := ReactiveApplication.anchoredPolicy execution players
  let profile := fun owner => (nativeMenu).restrictPolicy nativeInitial implementation.horizon
    fixed owner (anchored owner)
  have decoded : (nativeMenu).decodeProfile nativeInitial implementation.horizon fixed profile =
      anchored := by
    funext owner
    apply (nativeMenu).decode_restrictPolicy_of_covered nativeInitial implementation.horizon fixed
      owner
    exact (nativeMenu).anchoredPolicy_covered nativeInitial implementation.horizon fixed
      ⟨remaining, none, execution⟩ trace players owner
        (phaseProposalUnflaggedPolicy_covered setup .concurrent implementation.runtime
          implementation.leaks implementation.bounds implementation.plan values owner)
  have state := attemptUntil_state setup .concurrent implementation.runtime implementation.leaks
    implementation.bounds nativeInitial fixed profile execution.application.attempt remaining
      execution trace
  rw [decoded, ReactiveApplication.runUntil_anchoredPolicy_of_extends fixed execution players
    (fun next => next.application.attempt ≠ execution.application.attempt) remaining execution
      (fun _ => List.prefix_refl _)] at state
  have integrated := congrArg
    (fun law : PMF (nativeApplication).ProtocolState => law.bind reward) state
  dsimp only [fixedStoppedLaw, fixed, players, anchored, profile,
    ReservedConcurrentImplementation.horizon, ReservedConcurrentImplementation.application]
      at integrated ⊢
  simp only [PMF.bind_map, Function.comp_def] at integrated
  convert integrated using 3 ; first
  | rfl
  | funext history; cases history.state <;> rfl

/-- The fixed original tape gives the same gate on every actual stopped
support point, including a false all-admission word. -/
private theorem fixed_stopped_admission_bit
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (who : Player) (control : (nativeApplication).Control)
    (originalTrace : (nativeProtocol).Trace (some control))
    (active : control.actor = some who)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (tapeSupported : tape ∈ implementation.prior.support)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload)
    (value : L.Val payload) (serial : Nat)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (available : (⟨some material⟩ : (nativeApplication).Action) ∈
      (nativeMenu).actions who (control.execution.recall who)
        (control.execution.observe nativeApplication who))
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    (prepared : PhaseProposal.bindingPreparation material = some ⟨payload, value⟩)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (installed : phase ∈ control.execution.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (postTrace : ((nativeMenu).protocol nativeInitial implementation.horizon
      (ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) tape)).Trace
          (some ⟨control.remaining, none,
            control.execution.respond nativeApplication who ⟨some material⟩⟩))
    (afterProcessing : ReservedEpoch.packetCapacity implementation.runtime ≤
      (control.execution.respond nativeApplication who ⟨some material⟩).environmentRecall.length %
        ReservedEpoch.cycleWidth («graph» := serviceGraph setup .concurrent)
          (ReservedEpoch.packetCapacity implementation.runtime)) :
    ∀ final ∈ (fixedStoppedLaw setup values implementation tape control.remaining
        (control.execution.respond nativeApplication who ⟨some material⟩) postTrace).support,
      ∃ ending : (nativeApplication).Control,
        final.state = some ending ∧ ending.actor = none ∧
        ending.execution.application.attempt ≠ control.execution.application.attempt ∧
        (ending.execution.application.current.excluded =
          control.execution.application.entry.excluded ↔
          bindingAdmissionBit setup implementation who event ⟨some control, originalTrace⟩ tape =
            true) := by
  classical
  intro final supported
  let fixed := ReservedEpoch.family implementation.runtime implementation.leaks
    (ReservedEpoch.packetCapacity implementation.runtime) tape
  let after := control.execution.respond nativeApplication who ⟨some material⟩
  let initializer := (setup.initialLaw.map encodeInputs).map
    (PhaseRuntimeState.initial implementation.plan)
  have initialEq : initializer = nativeInitial := PMF.map_comp _ _ _
  dsimp only [initializer] at initialEq
  have afterInstalled : phase ∈ after.application.phases.head? := installed
  have stopped := phaseProposalUnflagged_stopped_acceptance_word setup .concurrent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan
    operational.completePending operational.outputValues operational.maximalPhases
    (serviceGraph_revealRelaxedOrdered setup .concurrent) values fullValues tape
    implementation.activationGap implementation.processingGap
    (operational.boundedGaps tape tapeSupported) operational.timely operational.candidateReserve
    control.remaining after
  erw [initialEq] at stopped
  obtain ⟨ending, before, prior, joint, legal, realized, raw, stateEq, idle, changed,
      fromStart, _toFinal, sameAttempt, beforeInstalled, effect, finished, _normalized,
      coverage, excluded, _tables, _candidates, _archive, _retired, _retiredAfter, word,
      _survives, _footprint⟩ :=
    stopped postTrace phase afterInstalled commitment afterProcessing final (by
      dsimp only [fixedStoppedLaw, after, fixed, ReservedConcurrentImplementation.horizon,
        ReservedConcurrentImplementation.application] at supported ⊢
      convert supported using 3 ; first
      | rfl
      | funext history; cases history.state <;> rfl)
  have initialized : ∀ state ∈ (nativeInitial).support, state.Ordered := by
    intro state member
    obtain ⟨draw, _support, rfl⟩ := (PMF.mem_support_map_iff ..).mp member
    exact PhaseRuntimeState.initial_ordered implementation.plan (encodeInputs draw)
  have ordered := (phaseApplication_seedOrder implementation.runtime implementation.leaks).history
    nativeInitial implementation.horizon fixed initialized
      ((nativeMenu).toRawTrace nativeInitial implementation.horizon fixed postTrace)
  have saved := ((phase_attempt_progress_of_prefix implementation.runtime implementation.leaks
    nativeMenu nativeInitial initialized implementation.horizon fixed
    ⟨control.remaining, none, after⟩
    before postTrace prior fromStart ordered).2.2
      sameAttempt.symm).symm
  have sameSaved : before.execution.application.entry.excluded =
      control.execution.application.entry.excluded :=
    congrArg (fun entry => entry.excluded) saved
  have gate := closing_gate_iff_acceptance_word setup implementation fixed before ending
    prior phase beforeInstalled commitment raw effect
    (fun equal => changed (equal.trans sameAttempt)) finished coverage excluded tape after word
  rw [sameSaved] at gate
  have bit := bindingAdmissionBit_eq_available_binding setup implementation who control
    originalTrace
    active tape event payload binding value serial material available packet prepared phase
      installed
      commitment
  refine ⟨ending, stateEq, idle, changed, ?_⟩
  rw [gate, bit, decide_eq_true_eq]

/-- A matched complete source word determines the actual clean endpoint's
entire payoff kernel after the real closing operation and normalization. -/
private theorem binding_finish_payoff_of_full_word
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (tapeSupported : tape ∈ implementation.prior.support)
    (before ending : (nativeApplication).Control)
    (prior : ((nativeMenu).protocol nativeInitial implementation.horizon
      (ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) tape)).Trace (some before))
    (trace : ((nativeMenu).protocol nativeInitial implementation.horizon
      (ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) tape)).Trace (some ending))
    (idle : ending.actor = none)
    (witness : RecoverySourceWitness setup .concurrent implementation.plan
      before.execution.application)
    (archived : witness.checkpoint.ArchivedProposals before.execution.network.inputs)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (rest : List (RuntimePhase (serviceGraph setup .concurrent)))
    (installed : before.execution.application.phases = phase :: rest)
    (commitment : phase.kind = .commitment)
    (raw : RecoveryState (serviceGraph setup .concurrent))
    (effect : PhaseClosingEffect implementation.runtime implementation.leaks
      before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt)
    (normalized : ending.execution.application =
      ({ before.execution.application with current := raw } :
        PhaseRuntimeState (serviceGraph setup .concurrent)).normalize)
    (finished : phase.Finished (phase.drain raw))
    (clean : (phase.drain raw).excluded = before.execution.application.entry.excluded)
    (excluded : (phase.drain raw).excluded = ending.execution.application.current.excluded)
    (entry : setup.proposalRecoveryProtocol.History)
    (source : CommitRecoveryState setup.program)
    (sourceTrace : setup.proposalRecoveryProtocol.Trace (some source))
    (sourcePrefix : TracePrefix entry.trace sourceTrace)
    (sameEntry : setup.proposalRecoveryErasedHistory entry =
      setup.proposalRecoveryErasedHistory
        ⟨_, setup.proposalRecoveryLiftTrace
          (nativeArchiveLabels setup (PhaseProposal.sourceArchive ending.execution.network.inputs))
          witness.checkpoint.trace⟩)
    (sameWord : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace sourceTrace) =
      (witness.checkpoint.commitInstructionWord (phase.drain raw).native).reverse ++
        setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace entry.trace))
    (proper : ∀ owner, owner ∉ (phase.drain raw).excluded →
      ProtocolState.BindingsHoldValues owner setup.program source.point)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) :
    ((nativeApplication).finish nativeInitial implementation.horizon
      (ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) tape)
      (phaseProposalUnflaggedPolicy setup .concurrent implementation.runtime
        implementation.leaks implementation.bounds implementation.plan values)
      (some ending)).map (fun state => phaseExclusionBase setup .concurrent
        implementation.runtime implementation.leaks utility excludedPayoff state who) =
      (setup.proposalRecoveryModel.runBehavioralTerminalFrom
        setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
        (sourceUnflaggedStrategy setup values) ⟨some source, sourceTrace⟩).map
          (setup.proposalRecoveryPayoff utility excludedPayoff who) := by
  let fixed := ReservedEpoch.family implementation.runtime implementation.leaks
    (ReservedEpoch.packetCapacity implementation.runtime) tape
  let labels := nativeArchiveLabels setup
    (PhaseProposal.sourceArchive ending.execution.network.inputs)
  obtain ⟨rawWitness, completed, rawCheckpoint, _rawHistory, ⟨fuel, path, instructions⟩,
      delta, settled, _readout⟩ :=
    ordinary_clean_closing_witness setup implementation operational fixed before ending prior
      witness phase rest installed commitment raw effect changed normalized finished clean
  let current := CommitRecoveryState.atPoint
    (witness.checkpoint.residual.lift
      (ProtocolState.entry witness.checkpoint.residual.tail witness.checkpoint.source))
    before.execution.application.entry.excluded before.execution.application.generation
  let entryTrace := setup.proposalRecoveryLiftTrace labels witness.checkpoint.trace
  have atCommit : ProtocolState.atCommit setup.program current.point = true := by
    apply (witness.checkpoint.atCommit _).trans
    exact witness.checkpoint.compiled.atCommit_of_bindingPhase setup.program .concurrent
      witness.checkpoint.residual.tail witness.checkpoint.refs
        witness.checkpoint.source.revelations witness.checkpoint.registry
          witness.checkpoint.embedding witness.checkpoint.before
            before.execution.application.attempt.phase phase commitment (by
              simp only [PhaseRuntimeState.attempt, installed, List.head?_cons,
                Option.map_some, Option.getD_some]) witness.checkpoint.source
  have erased := binding_close_erased_history_of_semantic_word setup entry current entryTrace
    sameEntry atCommit ⟨some source, sourceTrace⟩ ⟨_, completed.checkpoint.trace⟩ sourcePrefix
    (by simpa only [entryTrace, setup.proposalRecoveryEraseTrace_lift] using path.tracePrefix)
    (witness.checkpoint.commitInstructionWord (phase.drain raw).native).reverse sameWord
    (by simpa only [entryTrace, setup.proposalRecoveryEraseTrace_lift] using instructions)
    (by
      simpa only [List.length_reverse, current, CommitRecoveryState.atPoint] using
        witness.checkpoint.commit_instruction_word_window (phase.drain raw).native)
    labels (by simp only [entryTrace, setup.proposalRecoveryEraseTrace_lift])
  have completedProper : ∀ owner, owner ∉ (phase.drain raw).excluded →
      completed.checkpoint.source.BindingsHoldValues owner := by
    intro owner active
    exact checkpoint_binding_values_of_erased_history setup completed.checkpoint labels source
      sourceTrace erased owner (proper owner active)
  have physical := completed_binding_finish_payoff setup values implementation operational
    fullValues tape tapeSupported before ending prior trace idle witness archived raw effect
      changed rawWitness rawCheckpoint phase rest installed finished excluded normalized settled
        completed delta completedProper utility excludedPayoff who
  have sourceLaw := source_terminal_payoff_of_erased_history setup values
    ⟨_, setup.proposalRecoveryLiftTrace labels completed.checkpoint.trace⟩
      ⟨some source, sourceTrace⟩ erased.symm utility excludedPayoff who
  exact physical.trans sourceLaw

/-- A common complete semantic word transports the entire stopped finish
kernel. The native side uses its real raw closing witness and actual archive;
the source side may retain any compatible hidden publication memories. -/
private theorem retained_binding_word_finish
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (control : (nativeApplication).Control) (originalTrace : (nativeProtocol).Trace (some control))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId)
    (entry : NativeBindingEntry setup implementation operational control originalTrace who
      event)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (tapeSupported : tape ∈ implementation.prior.support)
    (originTrace : ((nativeMenu).protocol nativeInitial implementation.horizon
      (ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) tape)).Trace (some entry.entry))
    (remaining : Nat) (execution : (nativeApplication).Execution)
    (trace : ((nativeMenu).protocol nativeInitial implementation.horizon
      (ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) tape)).Trace
          (some ⟨remaining, none, execution⟩))
    (retained : TracePrefix originTrace trace)
    (attempt : execution.application.attempt = entry.entry.execution.application.attempt)
    (installed : execution.application.phases.head? = some entry.phase)
    (excluded : execution.application.current.excluded =
      entry.entry.execution.application.current.excluded)
    (archive : PhaseProposal.sourceArchive execution.network.inputs =
      PhaseProposal.sourceArchive entry.entry.execution.network.inputs)
    (afterProcessing : ReservedEpoch.packetCapacity implementation.runtime ≤
      execution.environmentRecall.length % ReservedEpoch.cycleWidth
        («graph» := serviceGraph setup .concurrent) (ReservedEpoch.packetCapacity
          implementation.runtime))
    (admitted : ∀ owner, owner ∉ execution.application.current.excluded →
      ∀ named ∈ entry.phase.events, ∀ payload,
        (serviceGraph setup .concurrent).outputLayout named = .binding owner payload →
        ReservedEpoch.ownedAcceptanceWord implementation.runtime implementation.leaks tape
          execution owner named)
    (sourceEntry : setup.proposalRecoveryProtocol.History)
    (sameEntry : setup.proposalRecoveryErasedHistory sourceEntry =
      setup.proposalRecoveryErasedHistory ⟨some entry.cursor.current, entry.cursor.trace⟩)
    (sourceLaw : PMF setup.proposalRecoveryProtocol.History)
    (sourceSupport : ∀ completed ∈ sourceLaw.support,
      ∃ (current : CommitRecoveryState setup.program)
        (sourceTrace : setup.proposalRecoveryProtocol.Trace (some current)),
        completed = ⟨some current, sourceTrace⟩ ∧ TracePrefix sourceEntry.trace sourceTrace ∧
        setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace sourceTrace) =
          (setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace sourceTrace)).take
            entry.block.length ++
              setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace sourceEntry.trace) ∧
        ∀ owner, owner ∉ execution.application.current.excluded →
          ProtocolState.BindingsHoldValues owner setup.program current.point)
    (wordLaw : sourceLaw.map (fun completed =>
        ((setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace completed.trace)).take
          entry.block.length).reverse) =
      (((serviceGraph setup .concurrent).canonicalContinuation
        (phaseProposalBindingPotentialProfile setup .concurrent implementation.runtime
          implementation.leaks implementation.plan entry.entry.execution entry.phase values)
        (phaseProposalEmissionFrontier setup .concurrent implementation.runtime implementation.leaks
          entry.entry.execution entry.phase originTrace.length
            entry.entry.execution.application.current.native.config nativeInitial
              implementation.horizon
              (ReservedEpoch.family implementation.runtime implementation.leaks
                (ReservedEpoch.packetCapacity implementation.runtime) tape)
              ((nativeMenu).toRawTrace nativeInitial implementation.horizon _ trace))).map
        (fun key => phaseProposalBindingWord setup.program entry.block entry.suffix
          entry.cursor.embedding execution.application.current.excluded key.2.1
            entry.cursor.source)))
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    (fixedStoppedLaw setup values implementation tape remaining execution trace).bind
        (fun final => ((nativeApplication).finish nativeInitial implementation.horizon
          (ReservedEpoch.family implementation.runtime implementation.leaks
            (ReservedEpoch.packetCapacity implementation.runtime) tape)
          (phaseProposalUnflaggedPolicy setup .concurrent implementation.runtime
            implementation.leaks implementation.bounds implementation.plan values) final.state).map
          (fun terminal => some (phaseExclusionBase setup .concurrent implementation.runtime
            implementation.leaks utility excludedPayoff terminal who))) =
      sourceLaw.bind fun completed =>
        (setup.proposalRecoveryModel.runBehavioralTerminalFrom
          setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
          (sourceUnflaggedStrategy setup values) completed).map
            (fun terminal => some (setup.proposalRecoveryPayoff utility excludedPayoff who
              terminal)) := by
  classical
  let fixed := ReservedEpoch.family implementation.runtime implementation.leaks
    (ReservedEpoch.packetCapacity implementation.runtime) tape
  let initializer := (setup.initialLaw.map encodeInputs).map
    (PhaseRuntimeState.initial implementation.plan)
  have initialEq : initializer = nativeInitial := PMF.map_comp _ _ _
  dsimp only [initializer] at initialEq
  have locations : ∀ index : Fin (eventCount (entry.block.prepend entry.suffix)),
      index.val < entry.block.length → entry.cursor.embedding.event index ∈ entry.phase.events := by
    intro index inside
    apply entry.phase.mem_events _ |>.mpr
    have rank := entry.cursor.compiled.rankEq index
    rw [entry.offset] at rank
    have size := entry.size
    omega
  have stopped := phaseProposalUnflagged_stopped_binding_word_from_retained_entry
      (Γ := entry.witness.checkpoint.residual.context)
      (O := entry.witness.checkpoint.residual.names)
      (Δ := entry.targetContext) (P := entry.targetNames) setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
      operational.completePending operational.outputValues operational.maximalPhases values
        fullValues
      tape implementation.activationGap implementation.processingGap
      (operational.boundedGaps tape tapeSupported) operational.timely operational.candidateReserve
  erw [initialEq] at stopped
  obtain ⟨image, endpoints, words⟩ :=
    stopped ⟨remaining, none, execution⟩ rfl trace entry.phase installed
        entry.commitment
      entry.entry originTrace retained
      attempt.symm entry.entryInstalled entry.entryExcluded entry.fresh excluded afterProcessing
      admitted entry.block entry.suffix entry.cursor.embedding entry.cursor.source locations
  let physicalWord := fun final : ((nativeMenu).protocol nativeInitial implementation.horizon
    fixed).History =>
    phaseProposalBindingWord setup.program entry.block entry.suffix entry.cursor.embedding
      execution.application.current.excluded
      (image final).native.config.store
        entry.cursor.source
  let sourceWord := fun completed : setup.proposalRecoveryProtocol.History =>
    ((setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace completed.trace)).take
      entry.block.length).reverse
  have common : (fixedStoppedLaw setup values implementation tape remaining execution trace).map
      physicalWord = sourceLaw.map sourceWord := by
    apply Eq.trans ?_ wordLaw.symm
    dsimp only [fixedStoppedLaw, physicalWord, fixed, ReservedConcurrentImplementation.horizon,
      ReservedConcurrentImplementation.application] at words ⊢
    convert words using 3 ; first
    | rfl
    | funext history; cases history.state <;> rfl
  apply bind_eq_of_map_eq _ sourceLaw physicalWord sourceWord common
  intro final finalSupported completed completedSupported matched
  obtain ⟨ending, before, prior, joint, legal, realized, raw, stateEq, idle, changed,
      fromAnchor, _toFinal, effect, imageEq, finished, rawExcluded, snapshotExcluded,
      endingArchive, beforeAttempt, beforeInstalled, normalized, _valid, _coverage⟩ :=
    endpoints final (by
      dsimp only [fixedStoppedLaw, fixed, ReservedConcurrentImplementation.horizon,
        ReservedConcurrentImplementation.application] at finalSupported ⊢
      convert finalSupported using 3 ; first
      | rfl
      | funext history; cases history.state <;> rfl)
  obtain ⟨current, sourceTrace, completedEq, sourcePrefix, fullWord, proper⟩ :=
    sourceSupport completed completedSupported
  obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp beforeInstalled)
  have beforeOriginal : TracePrefix originTrace prior := retained.trans fromAnchor
  have sameAttempt := beforeAttempt.trans attempt
  have samePrefix := RecoverySourceWitness.prefix_at_same_attempt setup .concurrent
      implementation.runtime
      implementation.leaks implementation.bounds implementation.plan operational.maximalPhases
  erw [initialEq] at samePrefix
  obtain ⟨beforeWitness, beforeArchived, beforeHistory, saved, checkpointEq⟩ :=
    samePrefix fixed entry.entry before originTrace prior beforeOriginal sameAttempt
      entry.witness entry.archived
  have clean : (entry.phase.drain raw).excluded = before.execution.application.entry.excluded := by
    rw [← imageEq, rawExcluded, excluded, saved, entry.entryExcluded]
  obtain ⟨_rawWitness, _completedWitness, _rawCheckpoint, _rawHistory, _path, _delta, _settled,
      readout⟩ := ordinary_clean_closing_witness setup implementation operational fixed before
        ending
    prior beforeWitness entry.phase rest phases
    entry.commitment raw effect
    (fun equal => changed (equal.trans beforeAttempt)) normalized (imageEq ▸ finished) clean
  have transferRead := entry.witness.checkpoint.transfer_binding_readback saved
    (congrArg CommitAttemptId.generation sameAttempt) (congrArg CommitAttemptId.phase sameAttempt)
      (entry.phase.drain raw)
  let hasReadout (checkpoint : RecoverySourceCheckpoint setup .concurrent
      before.execution.application) : Prop :=
    match commitPhase checkpoint.residual.tail with
    | ⟨_, _, suffix, block, reconstruct, _⟩ =>
      let embedding := cast (congrArg (fun program => OutputEmbedding
        (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
          checkpoint.embedding
      phaseProposalBindingWord setup.program block suffix embedding
        before.execution.application.entry.excluded (entry.phase.drain raw).native.config.store
          checkpoint.source = checkpoint.commitInstructionWord (entry.phase.drain raw).native
  have originalReadout : hasReadout beforeWitness.checkpoint := readout
  have movedReadout := (congrArg hasReadout checkpointEq).mp originalReadout
  have decoded : phaseProposalBindingWord setup.program entry.block entry.suffix
    entry.cursor.embedding
      execution.application.current.excluded
      (image final).native.config.store
      entry.cursor.source = beforeWitness.checkpoint.commitInstructionWord
        (entry.phase.drain raw).native := by
    rw [imageEq, entry.source, checkpointEq, transferRead.2]
    have chosen := phaseProposalBindingWord_of_reconstruct setup
      entry.witness.checkpoint.residual.tail
      entry.witness.checkpoint.embedding entry.block entry.suffix entry.reconstruct
        entry.cursor.embedding
      entry.embedding entry.witness.checkpoint.source
        entry.entry.execution.application.entry.excluded
      (entry.phase.drain raw).native.config.store
      (entry.witness.checkpoint.commitInstructionWord (entry.phase.drain raw).native) entry.boundary
      (by
        have literalReadout := movedReadout
        have literalWord := transferRead.2
        dsimp only [hasReadout, RecoverySourceCheckpoint.transfer] at literalReadout
        dsimp only [RecoverySourceCheckpoint.transfer] at literalWord
        simpa only [saved] using literalReadout.trans literalWord)
    simpa only [excluded, ← entry.entryExcluded] using chosen
  have sameWord : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace sourceTrace) =
      (beforeWitness.checkpoint.commitInstructionWord (entry.phase.drain raw).native).reverse ++
        setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace sourceEntry.trace) := by
    have word := matched.symm.trans decoded
    rw [completedEq] at word
    have newest := congrArg List.reverse word
    simp only [sourceWord, List.reverse_reverse] at newest
    exact fullWord.trans (congrArg
      (fun word => word ++ setup.recoveryJointRecall
        (setup.proposalRecoveryEraseTrace sourceEntry.trace)) newest)
  have archiveEq := endingArchive.trans archive
  have start : setup.proposalRecoveryErasedHistory sourceEntry =
      setup.proposalRecoveryErasedHistory
        ⟨_, setup.proposalRecoveryLiftTrace
          (nativeArchiveLabels setup (PhaseProposal.sourceArchive ending.execution.network.inputs))
          beforeWitness.checkpoint.trace⟩ := by
    apply sameEntry.trans
    apply congrArg setup.proposalRecoveryErasedHistory
    rw [entry.cursorHistory, archiveEq]
    symm
    exact congrArg (fun history : setup.commitRecoveryProtocol.History =>
      (⟨history.state, setup.proposalRecoveryLiftTrace
        (nativeArchiveLabels setup (PhaseProposal.sourceArchive
          entry.entry.execution.network.inputs))
        history.trace⟩ : setup.proposalRecoveryProtocol.History)) beforeHistory
  have attached := binding_finish_payoff_of_full_word setup values implementation operational
    fullValues
    tape tapeSupported before ending prior (stateEq ▸ final.trace)
    idle beforeWitness beforeArchived
    entry.phase rest phases entry.commitment raw effect
    (fun equal => changed (equal.trans beforeAttempt)) normalized (imageEq ▸ finished) clean
    (imageEq ▸ snapshotExcluded) sourceEntry current sourceTrace sourcePrefix start sameWord
    (fun owner active => proper owner (by simpa only [← imageEq, rawExcluded] using active))
    utility excludedPayoff who
  have optionLaw := congrArg (PMF.map some) attached
  simpa only [stateEq, completedEq, PMF.map_comp, Function.comp_def, initialEq] using optionLaw

open Classical in
/-- On an admitted original tape, every compatible closed source entry has
the actual inserted preparation's complete stopped-and-finished payoff law. -/
private theorem fixed_binding_source_payoff
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨some control, trace⟩)
    (entry : NativeBindingEntry setup implementation operational control trace who event)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (tapeSupported : tape ∈ implementation.prior.support)
    (compatible : fixedTapeCompatible setup implementation tape (some control))
    (admitted : bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape =
      true)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (available : (⟨some material⟩ : (nativeApplication).Action) ∈
      (nativeMenu).actions who (control.execution.recall who)
        (control.execution.observe nativeApplication who))
    (serial : Nat) (packet : material.call.packet = .commitment event (who, .prepared serial))
    (value : L.Val payload)
    (prepared : PhaseProposal.bindingPreparation material = some ⟨payload, value⟩)
    (current : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some current))
    (erased : setup.proposalRecoveryErasedHistory ⟨some entry.cursor.current, entry.cursor.trace⟩ =
      setup.proposalRecoveryErasedHistory ⟨some current, targetTrace⟩)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    let fixed := ReservedEpoch.family implementation.runtime implementation.leaks
      (ReservedEpoch.packetCapacity implementation.runtime) tape
    let players := phaseProposalUnflaggedPolicy setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
    let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
    let count := (SourceProgram.commitPhase checkpoint.residual.tail).block.length
    let observed := bindingCompletedObservation setup implementation checkpoint control who event
      payload clean.binding value
    ((nativeApplication).runUntil fixed players
      (fun next => next.application.attempt ≠ control.execution.application.attempt)
        control.remaining
      (control.execution.respond nativeApplication who ⟨some material⟩)).bind
      (fun ending => ((nativeApplication).finish nativeInitial implementation.horizon fixed players
        (some ⟨implementation.horizon - ending.environmentRecall.length, none, ending⟩)).map
          (fun terminal => some (phaseExclusionBase setup .concurrent implementation.runtime
            implementation.leaks utility excludedPayoff terminal who))) =
      (fiberPosterior (setup.proposalRecoveryModel.runBehavioralFrom
        (sourceUnflaggedStrategy setup values) count ⟨some current, targetTrace⟩) observed
          true).bind
        (fun completed => (setup.proposalRecoveryModel.runBehavioralTerminalFrom
          setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
          (sourceUnflaggedStrategy setup values) completed).map
            (fun terminal => some (setup.proposalRecoveryPayoff utility excludedPayoff who
              terminal))) := by
  classical
  intro fixed players checkpoint count observed
  let joint := fun owner => if owner = who then some (⟨some material⟩ : (nativeApplication).Action)
    else none
  have legal : (nativeProtocol).Legal (some control) joint := by
    constructor
    · simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.terminal, active]
    · intro owner
      by_cases same : owner = who
      · subst owner
        simpa [joint, ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor,
          ReactiveApplication.ResponseMenu.available, active] using available
      · simp [joint, ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor,
          active, same, Ne.symm same]
  let after := control.execution.respond nativeApplication who ⟨some material⟩
  have afterExcluded : after.application.current.excluded =
      control.execution.application.current.excluded := rfl
  have realized : some ⟨control.remaining, none, after⟩ ∈
      ((nativeProtocol).step (some control) ⟨joint, legal⟩).support := by
    simp only [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.transition, active,
      joint, ↓reduceIte, Option.getD_some, PMF.mem_support_pure_iff]
    rfl
  let originalPost := trace.extend joint legal realized
  have afterCompatible : fixedTapeCompatible setup implementation tape
      (some ⟨control.remaining, none, after⟩) := by
    simpa only [fixedTapeCompatible, after, Option.elim_some,
      (nativeApplication).respond_environmentRecall] using compatible
  let fixedTrace := fixedTapeTrace setup implementation implementation.scheduler tape trace
    compatible
  let postTrace := fixedTapeTrace setup implementation implementation.scheduler tape originalPost
    afterCompatible
  let originTrace := fixedTapeTrace setup implementation implementation.scheduler tape
    entry.entryTrace
    (fixed_tape_compatible_of_prefix setup implementation implementation.scheduler tape
      entry.retained
      compatible)
  have originalRetained : TracePrefix entry.entryTrace originalPost :=
    .extend entry.retained joint legal realized
  have retained : TracePrefix originTrace postTrace :=
    fixed_tape_trace_prefix setup implementation implementation.scheduler tape originalRetained
      afterCompatible
  have process := response_after_processing setup implementation tape who control fixedTrace active
    ⟨some material⟩
  obtain ⟨saved, _represented⟩ := entry.selected
  have currentSaved : control.execution.application.current.excluded =
      control.execution.application.entry.excluded :=
    entry.excluded.trans (entry.entryExcluded.symm.trans (congrArg RecoveryState.excluded saved))
  have bit := bindingAdmissionBit_eq_available_binding setup implementation who control trace active
    tape event payload clean.binding value serial material available packet prepared entry.phase
      (Option.mem_def.mpr entry.installed) entry.commitment
  have allAdmitted : ∀ owner, owner ∉ after.application.current.excluded →
      ∀ named ∈ entry.phase.events, ∀ domain,
      (serviceGraph setup .concurrent).outputLayout named = .binding owner domain →
      ReservedEpoch.ownedAcceptanceWord implementation.runtime implementation.leaks tape after
        owner named := by
    have word := decide_eq_true_eq.mp (bit.symm ▸ admitted)
    intro owner survives named inside domain binding
    apply word named inside owner
      ((serviceGraph setup .concurrent).actor?_of_outputLayout_binding binding)
    exact currentSaved ▸ survives
  obtain ⟨graphPresent, graphPosterior⟩ := inserted_binding_frontier_posterior setup values
    implementation operational fullValues control trace who active event payload clean foreign entry
    joint legal material (by simp only [joint, ↓reduceIte]) serial packet value prepared realized
  obtain ⟨sourcePresent, sourceWord, sourceSupport⟩ := closed_entry_binding_word setup values
    implementation operational control trace who event payload clean.binding
    (currentSaved ▸ clean.request.2.2.2.2) entry value current targetTrace erased graphPresent
  have physicalFrontier := fixed_tape_emission_frontier setup implementation
    implementation.scheduler
    tape originalPost afterCompatible entry.entry.execution entry.phase entry.entryTrace.length
      entry.entry.execution.application.current.native.config
  have originLength := fixed_tape_trace_length setup implementation implementation.scheduler tape
    entry.entryTrace (fixed_tape_compatible_of_prefix setup implementation implementation.scheduler
      tape entry.retained compatible)
  have common : (fiberPosterior (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) entry.block.length ⟨some current, targetTrace⟩)
      observed true).map (fun completed =>
        ((setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace completed.trace)).take
          entry.block.length).reverse) =
      (((serviceGraph setup .concurrent).canonicalContinuation
        (phaseProposalBindingPotentialProfile setup .concurrent implementation.runtime
          implementation.leaks implementation.plan entry.entry.execution entry.phase values)
        (phaseProposalEmissionFrontier setup .concurrent implementation.runtime implementation.leaks
          entry.entry.execution entry.phase originTrace.length
            entry.entry.execution.application.current.native.config nativeInitial
              implementation.horizon
              fixed ((nativeMenu).toRawTrace nativeInitial implementation.horizon fixed
                postTrace))).map
        (fun key => phaseProposalBindingWord setup.program entry.block entry.suffix
          entry.cursor.embedding after.application.current.excluded key.2.1 entry.cursor.source))
            := by
    simpa only [originTrace, originLength, postTrace, physicalFrontier, graphPosterior,
      observed, checkpoint, originalPost, afterExcluded, fixed] using sourceWord
  have attached := retained_binding_word_finish setup values implementation operational fullValues
    control trace who event entry tape tapeSupported originTrace control.remaining after postTrace
    retained entry.sameAttempt.symm entry.installed entry.excluded
    ((PhaseProposal.commitment_response_archive implementation.runtime implementation.leaks
      control.execution who material event (who, .prepared serial) packet).trans entry.archiveEq)
    process allAdmitted ⟨some current, targetTrace⟩ erased.symm
    (fiberPosterior (setup.proposalRecoveryModel.runBehavioralFrom (sourceUnflaggedStrategy setup
      values)
      entry.block.length ⟨some current, targetTrace⟩) observed true)
    (by simpa only [afterExcluded, observed, checkpoint] using sourceSupport)
    common utility excludedPayoff
  have counted := fixed_stopped_bind_state setup values implementation tape control.remaining after
    postTrace (fun state => ((nativeApplication).finish nativeInitial implementation.horizon fixed
      players state).map (fun terminal => some (phaseExclusionBase setup .concurrent
        implementation.runtime implementation.leaks utility excludedPayoff terminal who)))
  have length := (selected_binding_observation setup implementation operational control trace
    who event payload clean.binding entry value).1
  rw [show count = entry.block.length from length]
  exact counted.symm.trans attached

open Classical in
private theorem source_binding_posterior_disintegration {A : Type}
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target : setup.proposalRecoveryProtocol.History) (supportedWord : SourceProgram.History
      Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who ⟨some control, trace⟩ tape target supportedWord ≠ 0)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (information : (nativeModel).infoOf who trace = some (past, view))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who past view event payload)
    (admitted : bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape =
      true)
    (value : L.Val payload) (pairLaw : ForeignPosteriorCutPair setup values implementation)
    (within : event.val - control.execution.application.attempt.phase ≤
      (SourceProgram.commitPhase
        (checkpointSelection setup implementation operational
          trace).val.checkpoint.residual.tail).block.length)
    (present : true ∈ ((setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values)
      (SourceProgram.commitPhase
        (checkpointSelection setup implementation operational
          trace).val.checkpoint.residual.tail).block.length
      target).map (bindingCompletedObservation setup implementation
        (checkpointSelection setup implementation operational trace).val.checkpoint control who
          event
          payload clean.binding value)).support)
    (reward : setup.proposalRecoveryProtocol.History → PMF A) :
    (fiberPosterior (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values)
      (SourceProgram.commitPhase
        (checkpointSelection setup implementation operational
          trace).val.checkpoint.residual.tail).block.length
      target) (bindingCompletedObservation setup implementation
        (checkpointSelection setup implementation operational trace).val.checkpoint control who
          event
          payload clean.binding value) true).bind reward =
      (((fiberPosterior (ordinaryForeignJoint setup values implementation operational who
          ⟨some control, trace⟩ target) Prod.snd true).map Prod.fst).bind fun word =>
        (sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
          event payload target word value).bind fun pair => reward pair.2) := by
  classical
  let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
  let block := SourceProgram.commitPhase checkpoint.residual.tail
  let k := event.val - control.execution.application.attempt.phase
  let ordinary := sourceUnflaggedStrategy setup values
  let pair := (setup.proposalRecoveryModel.runBehavioralFrom ordinary k target).bind fun cut =>
    (setup.proposalRecoveryModel.runBehavioralFrom ordinary (block.block.length - k) cut).map
      (Prod.mk cut)
  let observed := bindingCompletedObservation setup implementation checkpoint control who event
    payload clean.binding value
  let pairObserved := fun pair : setup.proposalRecoveryProtocol.History ×
      setup.proposalRecoveryProtocol.History =>
    match pair.2.state.bind (fun current => residualEntry? block.suffix
        (fun point => checkpoint.residual.lift
          (cast (congrArg ProtocolState block.reconstruct)
            (block.block.liftPoint block.suffix point))) current.point) with
    | none => false
    | some finished => decide (
        issuedLedger setup implementation block.block control.execution.application.attempt.phase
          control (control.execution.application.attempt.phase + block.block.length) who
            (finished.view who) ∧
        block.block.wordAction who k (finished.view who) = decodeEventAction setup.program event
          (cast (congrArg EventField.Action clean.binding.symm) (.success value)) ∧
        ∀ owner, owner ≠ who → issuedLedger setup implementation block.block
          control.execution.application.attempt.phase control
          (control.execution.application.attempt.phase + block.block.length) owner (finished.view
            owner))
  have observes : pairObserved = observed ∘ Prod.snd := by
    funext found
    dsimp only [pairObserved, observed, Function.comp_def]
    unfold bindingCompletedObservation
    unfold residualBindingObservation
    dsimp only
    split
    · rename_i leftEq
      split
      · rfl
      · rename_i secondFinal rightEq
        have impossible := leftEq.symm.trans rightEq
        cases impossible
    · rename_i firstFinal leftEq
      split
      · rename_i rightEq
        have impossible := leftEq.symm.trans rightEq
        cases impossible
      · rename_i secondFinal rightEq
        have finalEq : firstFinal = secondFinal := Option.some.inj (leftEq.symm.trans rightEq)
        cases finalEq
        apply decide_eq_decide.mpr
        constructor
        · rintro ⟨own, selected, foreign⟩
          refine ⟨?_, selected⟩
          intro owner
          by_cases same : owner = who
          · subst owner
            exact own
          · exact foreign owner same
        · rintro ⟨ledger, selected⟩
          exact ⟨ledger who, selected, fun owner _ => ledger owner⟩
  obtain ⟨_pairPresent, _foreignPresent, conditional, _ownPresent, _ownConditional⟩ :=
    pairLaw operational fullValues sourceProfile nativeProfile who control trace tape target
      supportedWord canonicalSupported positive past view information event payload clean admitted
        value
  have conditional' : fiberPosterior pair (observed ∘ Prod.snd) true =
      (fiberPosterior (ordinaryForeignJoint setup values implementation operational who
        ⟨some control, trace⟩ target) Prod.snd true).bind fun word =>
          sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩ event payload
            target word.1 value := by
    rw [← observes]
    exact conditional
  have split := source_split_pair_completed_posterior setup ordinary k (block.block.length - k)
    target observed (by simpa only [ordinary, checkpoint, block, k, Nat.add_sub_of_le within]
      using present)
  rw [Nat.add_sub_of_le within] at split
  have integrated := congrArg (fun law => law.bind reward) split
  calc
    _ = (fiberPosterior pair (observed ∘ Prod.snd) true).bind
        (fun found => reward found.2) := by
      simpa only [pair, PMF.bind_map, Function.comp_def] using integrated.symm
    _ = _ := by rw [conditional']; simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]

open Classical in
/-- On an admitted tape the original reach-weighted physical payoff is
exactly the full annotation sum. Every closed-entry cylinder is established
positive before its annotation is used to invoke the explicit pair law. -/
theorem annotated_admitted_tape
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control)) (active : control.actor = some who)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (reachPositive : (nativeModel).historyReachWeight nativeProfile ⟨some control, trace⟩ ≠ 0)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (tapePositive : prefixTapeLaw setup implementation ⟨some control, trace⟩ tape ≠ 0)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (foreign : foreignGood setup .concurrent implementation.runtime implementation.leaks
      implementation.bounds implementation.plan implementation.prior who ⟨some control, trace⟩)
    (admitted : bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape =
      true)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (available : (⟨some material⟩ : (nativeApplication).Action) ∈
      (nativeMenu).actions who (control.execution.recall who)
        (control.execution.observe nativeApplication who))
    (serial : Nat) (packet : material.call.packet = .commitment event (who, .prepared serial))
    (value : L.Val payload)
    (prepared : PhaseProposal.bindingPreparation material = some ⟨payload, value⟩)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) (outcome : Option ℝ)
    (pairLaw : ForeignPosteriorCutPair setup values implementation) :
    let fixed := ReservedEpoch.family implementation.runtime implementation.leaks
      (ReservedEpoch.packetCapacity implementation.runtime) tape
    let players := phaseProposalUnflaggedPolicy setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
    (nativeModel).historyReachWeight nativeProfile ⟨some control, trace⟩ *
      prefixTapeLaw setup implementation ⟨some control, trace⟩ tape *
      (((nativeApplication).runUntil fixed players
        (fun next => next.application.attempt ≠ control.execution.application.attempt)
          control.remaining
        (control.execution.respond nativeApplication who ⟨some material⟩)).bind fun ending =>
        ((nativeApplication).finish nativeInitial implementation.horizon fixed players
          (some ⟨implementation.horizon - ending.environmentRecall.length, none, ending⟩)).map
            (fun terminal => some (phaseExclusionBase setup .concurrent implementation.runtime
              implementation.leaks utility excludedPayoff terminal who))) outcome =
      ∑' cut : setup.proposalRecoveryProtocol.History,
        ∑' completed : setup.proposalRecoveryProtocol.History,
          ∑' target : setup.proposalRecoveryProtocol.History,
            ∑' word : SourceProgram.History Player L,
              annotatedPrefixWeight setup values implementation operational sourceProfile
                nativeProfile
                who ⟨some control, trace⟩ tape target word *
              sourceForcedBlockJoint setup values implementation who ⟨some control, trace⟩
                event payload target word value (cut, completed) *
              ((setup.proposalRecoveryModel.runBehavioralTerminalFrom
                setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
                (sourceUnflaggedStrategy setup values) completed).map
                (fun terminal => some (setup.proposalRecoveryPayoff utility excludedPayoff who
                  terminal)))
                  outcome := by
  classical
  intro fixed players
  let history : (nativeProtocol).History := ⟨some control, trace⟩
  let canonical := canonicalSource setup implementation operational history
  let closed := setup.proposalRecoveryClosedLaw sourceProfile who canonical
  let posterior := fun target => ((fiberPosterior
    (ordinaryForeignJoint setup values implementation operational who history target) Prod.snd
      true).map
      Prod.fst)
  let reward := fun completed : setup.proposalRecoveryProtocol.History =>
    (setup.proposalRecoveryModel.runBehavioralTerminalFrom
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
      (sourceUnflaggedStrategy setup values) completed).map
        (fun terminal => some (setup.proposalRecoveryPayoff utility excludedPayoff who terminal))
  let physical := ((nativeApplication).runUntil fixed players
    (fun next => next.application.attempt ≠ control.execution.application.attempt) control.remaining
    (control.execution.respond nativeApplication who ⟨some material⟩)).bind fun ending =>
      ((nativeApplication).finish nativeInitial implementation.horizon fixed players
        (some ⟨implementation.horizon - ending.environmentRecall.length, none, ending⟩)).map
          (fun terminal => some (phaseExclusionBase setup .concurrent implementation.runtime
            implementation.leaks utility excludedPayoff terminal who))
  obtain ⟨entry⟩ := qualified_binding_entry setup implementation operational control trace
    who
    event payload clean foreign
  obtain ⟨tapeSupported, compatible⟩ := prefix_tape_compatible setup implementation control trace
    tape
    ((PMF.mem_support_iff _ _).mpr tapePositive)
  obtain ⟨saved, _represented⟩ := entry.selected
  have currentSaved : control.execution.application.current.excluded =
      control.execution.application.entry.excluded :=
    entry.excluded.trans (entry.entryExcluded.symm.trans (congrArg RecoveryState.excluded saved))
  have alive : who ∉ control.execution.application.current.excluded := clean.request.2.2.2.2
  have guarded : (∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          history) ∧
      history.state.elim True (fun control => who ∉
        control.execution.application.current.excluded) :=
    ⟨foreign, alive⟩
  have mass : setup.proposalRecoveryClosedMass sourceProfile who canonical ≠ 0 := by
    apply (PMF.mem_support_iff _ _).mp
    exact (PMF.mem_support_map_iff ..).mpr
      ⟨canonical, (PMF.mem_support_iff _ _).mpr canonicalSupported, rfl⟩
  obtain ⟨_ready, graphPresent, _posterior, _graphMass⟩ :=
    binding_value_frontier_posterior setup values
    implementation operational fullValues control trace who active event payload clean foreign
      entry value
  have length := (selected_binding_observation setup implementation operational control trace
    who event payload clean.binding entry value).1
  have within : event.val - control.execution.application.attempt.phase ≤
      (SourceProgram.commitPhase
        (checkpointSelection setup implementation operational
          trace).val.checkpoint.residual.tail).block.length := by
    have bounds := (entry.phase.mem_events event).mp entry.inside
    have size := entry.size
    obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp entry.installed
    have low : control.execution.application.attempt.phase = entry.phase.low := by
      simp only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
        Option.getD_some]
    omega
  have allTargets : ∀ target ∈ closed.support,
      true ∈ ((ordinaryForeignJoint setup values implementation operational who history target).map
        Prod.snd).support ∧
      physical = (posterior target).bind (fun word =>
        (sourceForcedBlockJoint setup values implementation who history event payload target word
          value).bind
          fun pair => reward pair.2) := by
    intro target targetSupported
    have sameKey := (setup.proposalRecoveryClosedLaw_support sourceProfile who canonical target
      mass).mp
      targetSupported |>.1
    obtain ⟨current, targetTrace, targetEq, _good, erased⟩ := closed_key_entry_erased_history setup
      implementation operational who control trace event entry target foreign sameKey
    obtain ⟨sourcePresent, _words, _support⟩ := closed_entry_binding_word setup values
      implementation
      operational control trace who event payload clean.binding (currentSaved ▸ alive) entry value
      current targetTrace erased graphPresent
    have sourcePresent' : true ∈ ((setup.proposalRecoveryModel.runBehavioralFrom
        (sourceUnflaggedStrategy setup values)
        (SourceProgram.commitPhase
          (checkpointSelection setup implementation operational
            trace).val.checkpoint.residual.tail).block.length
        ⟨some current, targetTrace⟩).map (bindingCompletedObservation setup implementation
          (checkpointSelection setup implementation operational trace).val.checkpoint control who
            event
            payload clean.binding value)).support := by rwa [length]
    have foreignPresent := closed_entry_foreign_positive setup values implementation operational
      control
      trace who event payload clean.binding entry currentSaved value current targetTrace erased
        sourcePresent'
    have foreignPresent' : true ∈ ((ordinaryForeignJoint setup values implementation operational who
        history target).map Prod.snd).support := targetEq.symm ▸ foreignPresent
    obtain ⟨word, wordSupported⟩ := (posterior target).support_nonempty
    have annotation : annotatedPrefixWeight setup values implementation operational sourceProfile
        nativeProfile who history tape target word ≠ 0 := by
      unfold annotatedPrefixWeight
      dsimp only
      rw [ite_eq_left guarded, ite_eq_right ((PMF.mem_support_iff _ _).mp foreignPresent')]
      exact mul_ne_zero (mul_ne_zero reachPositive tapePositive)
        (mul_ne_zero ((PMF.mem_support_iff _ _).mp targetSupported)
          ((PMF.mem_support_iff _ _).mp wordSupported))
    have attached := fixed_binding_source_payoff setup values implementation operational fullValues
      control trace who active event payload clean foreign entry tape tapeSupported compatible
        admitted
      material available serial packet value prepared current targetTrace erased utility
        excludedPayoff
    have disintegrated := source_binding_posterior_disintegration setup values implementation
      operational fullValues sourceProfile nativeProfile who control trace tape target word
      canonicalSupported annotation (control.execution.recall who) (control.execution.observe
        nativeApplication who)
      (by
        change ((nativeMenu).signals nativeInitial implementation.horizon
          implementation.scheduler).infoOf who trace = _
        have observedInfo := (nativeMenu).info nativeInitial implementation.horizon
          implementation.scheduler who trace
        simpa only [ReactiveApplication.observe, active, ↓reduceIte] using observedInfo)
      event payload clean admitted value pairLaw within (targetEq.symm ▸ sourcePresent') reward
    exact ⟨foreignPresent', attached.trans (by simpa only [targetEq] using disintegrated)⟩
  have averaged : (closed.bind fun target => (posterior target).bind fun word =>
      (sourceForcedBlockJoint setup values implementation who history event payload target word
        value).bind
        fun pair => reward pair.2) = physical := by
    calc
      _ = closed.bind (fun _ => physical) := by
        apply bind_congr_on_support
        intro target supported
        exact (allTargets target supported).2.symm
      _ = _ := PMF.bind_const _ _
  have weighted := congrArg (fun law : PMF (Option ℝ) =>
    (nativeModel).historyReachWeight nativeProfile history * prefixTapeLaw setup implementation
      history tape *
      law outcome) averaged.symm
  rw [PMF.bind_apply, ← ENNReal.tsum_mul_left] at weighted
  calc
    _ = ∑' target, ∑' word, ∑' cut, ∑' completed,
        annotatedPrefixWeight setup values implementation operational sourceProfile nativeProfile
          who history tape target word *
        sourceForcedBlockJoint setup values implementation who history event payload target word
          value
          (cut, completed) * reward completed outcome := by
      rw [PMF.bind_apply, ← ENNReal.tsum_mul_left]
      rw [weighted]
      rw [PMF.bind_apply, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro target
      by_cases supported : target ∈ closed.support
      · rw [PMF.bind_apply, ← ENNReal.tsum_mul_left]
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro word
        rw [PMF.bind_apply, ENNReal.tsum_prod', ← ENNReal.tsum_mul_left]
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro cut
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left,
          ← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro completed
        unfold annotatedPrefixWeight
        dsimp only
        rw [ite_eq_left guarded,
          ite_eq_right ((PMF.mem_support_iff _ _).mp (allTargets target supported).1)]
        simp only [posterior, closed, canonical, mul_assoc]
      · have zero : closed target = 0 := not_not.mp (by
          simpa only [PMF.mem_support_iff] using supported)
        simp only [zero, mul_zero, zero_mul]
        apply (ENNReal.tsum_eq_zero.mpr ?_).symm
        intro word
        apply ENNReal.tsum_eq_zero.mpr
        intro cut
        apply ENNReal.tsum_eq_zero.mpr
        intro completed
        simp [annotatedPrefixWeight, closed, canonical, zero]
    _ = _ := by
      simpa only [history, reward] using tsum_interchange_blocks
        (fun target word cut completed =>
          annotatedPrefixWeight setup values implementation operational sourceProfile
            nativeProfile who history tape target word *
          sourceForcedBlockJoint setup values implementation who history event payload target
            word value (cut, completed) * reward completed outcome)

open Classical in
theorem fixed_tape_gate_law
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (supported : tape ∈ (prefixTapeLaw setup implementation ⟨some control, trace⟩).support)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload)
    (value : L.Val payload) (serial : Nat)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (available : (⟨some material⟩ : (nativeApplication).Action) ∈
      (nativeMenu).actions who (control.execution.recall who)
        (control.execution.observe nativeApplication who))
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    (prepared : PhaseProposal.bindingPreparation material = some ⟨payload, value⟩)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (installed : phase ∈ control.execution.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    let fixed := ReservedEpoch.family implementation.runtime implementation.leaks
      (ReservedEpoch.packetCapacity implementation.runtime) tape
    let players := phaseProposalUnflaggedPolicy setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
    let foreign := foreignGood setup .concurrent implementation.runtime implementation.leaks
      implementation.bounds implementation.plan implementation.prior who ⟨some control, trace⟩
    let after := control.execution.respond nativeApplication who ⟨some material⟩
    ((nativeApplication).runUntil fixed players
      (fun next => next.application.attempt ≠ control.execution.application.attempt)
      control.remaining after).bind (fun ending =>
        ((nativeApplication).finish nativeInitial implementation.horizon fixed players
          (some ⟨implementation.horizon - ending.environmentRecall.length, none, ending⟩)).map
          (fun terminal => if foreign ∧
              ending.application.attempt ≠ control.execution.application.attempt ∧
              ending.application.current.excluded = control.execution.application.entry.excluded
            then some (phaseExclusionBase setup .concurrent implementation.runtime
              implementation.leaks utility excludedPayoff terminal who) else none)) =
      if foreign ∧ bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape =
        true then
        ((nativeApplication).runUntil fixed players
          (fun next => next.application.attempt ≠ control.execution.application.attempt)
          control.remaining after).bind (fun ending =>
            ((nativeApplication).finish nativeInitial implementation.horizon fixed players
              (some ⟨implementation.horizon - ending.environmentRecall.length, none, ending⟩)).map
                (fun terminal => some (phaseExclusionBase setup .concurrent implementation.runtime
                  implementation.leaks utility excludedPayoff terminal who)))
      else PMF.pure none := by
  classical
  intro fixed players foreign after
  obtain ⟨tapeSupported, compatible⟩ := prefix_tape_compatible setup implementation control trace
    tape supported
  let actual := fixedTapeTrace setup implementation implementation.scheduler tape trace compatible
  have activeTrace : ((nativeMenu).protocol nativeInitial implementation.horizon fixed).Trace
      (some ⟨control.remaining, some who, control.execution⟩) := by
    simpa only [← active, fixed] using actual
  obtain ⟨postTrace⟩ := (nativeMenu).trace_respond nativeInitial implementation.horizon fixed
    control.remaining control.execution who ⟨some material⟩ activeTrace available
  have process := response_after_processing setup implementation tape who control actual active
    ⟨some material⟩
  have gate := fixed_stopped_admission_bit setup values implementation operational fullValues who
    control
    trace active tape tapeSupported event payload binding value serial material available packet
      prepared
    phase installed commitment postTrace process
  let reward := fun state : (nativeApplication).ProtocolState =>
    ((nativeApplication).finish nativeInitial implementation.horizon fixed players state).map
      (fun terminal => if foreign ∧ state.elim False (fun ending =>
          ending.execution.application.attempt ≠ control.execution.application.attempt ∧
          ending.execution.application.current.excluded =
            control.execution.application.entry.excluded)
        then some (phaseExclusionBase setup .concurrent implementation.runtime implementation.leaks
          utility excludedPayoff terminal who) else none)
  have counted := fixed_stopped_bind_state setup values implementation tape control.remaining after
    postTrace reward
  have ungated := fixed_stopped_bind_state setup values implementation tape control.remaining after
    postTrace (fun state => ((nativeApplication).finish nativeInitial implementation.horizon fixed
      players state).map (fun terminal => some (phaseExclusionBase setup .concurrent
        implementation.runtime implementation.leaks utility excludedPayoff terminal who)))
  have afterAttempt : after.application.attempt = control.execution.application.attempt := rfl
  rw [afterAttempt] at counted ungated
  simp only [reward, Option.elim_some] at counted
  dsimp only [fixed, players] at counted ⊢
  calc
    _ = (fixedStoppedLaw setup values implementation tape control.remaining after postTrace).bind
        (fun final => reward final.state) := by
      convert counted.symm using 1
      all_goals
        apply bind_congr_on_support
        intro ending _
        apply map_congr_on_support
        intro terminal _
        congr 1
    _ = _ := by
      by_cases admitted : foreign ∧ bindingAdmissionBit setup implementation who event
          ⟨some control, trace⟩ tape = true
      · rw [ite_eq_left admitted]
        erw [← ungated]
        apply bind_congr_on_support
        intro final member
        obtain ⟨ending, stateEq, _idle, changed, clean⟩ := gate final member
        have accepted : ending.execution.application.current.excluded =
            control.execution.application.entry.excluded := clean.mpr admitted.2
        simp only [reward, stateEq, Option.elim_some, admitted.1, accepted,
          true_and, and_true]
        simp only [ite_eq_left changed]
      · rw [ite_eq_right admitted]
        calc
          _ = (fixedStoppedLaw setup values implementation tape control.remaining after
              postTrace).bind
              (fun _ => PMF.pure none) := by
            apply bind_congr_on_support
            intro final member
            obtain ⟨ending, stateEq, _idle, changed, clean⟩ := gate final member
            have rejected : ¬ (foreign ∧
                ending.execution.application.attempt ≠ control.execution.application.attempt ∧
                ending.execution.application.current.excluded =
                  control.execution.application.entry.excluded) := by
              rintro ⟨good, _changed, accepted⟩
              exact admitted ⟨good, clean.mp accepted⟩
            simp only [reward, stateEq, Option.elim_some, rejected, ↓reduceIte]
            exact PMF.map_const _ _
          _ = _ := PMF.bind_const _ _

end QualifiedPayoffAttachment

end Vegas.PhaseProposalQualifiedBinding
