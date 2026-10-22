/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.QualifiedBinding.BindingReadback

/-! # Saved source images and factual commitment visits -/

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

variable (implementation : ReservedConcurrentImplementation setup)

local notation "nativeApplication" => implementation.application
local notation "nativeMenu" => PhaseCount.onePacketMenu implementation.runtime
  implementation.leaks implementation.bounds
local notation "nativeInitial" => implementation.initial
local notation "nativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  nativeMenu nativeInitial implementation.horizon implementation.scheduler

/-- Assign the reference application while retaining the exact raw callbacks
already sampled in the reconstructed prefix. -/
def sourceReplayExecution
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (recalls : Player → List (nativeApplication).PlayerEntry)
    (original : (nativeApplication).Execution) : (nativeApplication).Execution :=
  { original with
    application := sourceSnapshotAssignment setup implementation target reference lost
      original.application
    «recall» := recalls }


omit [Fintype Player] in
/-- Changing unsampled preparations does not change a field assignment whose
accepted handles already have fixed meanings. -/
private theorem sourceSnapshotPair_lost_congr
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (first second : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (valid : snapshot.BindingInvariant)
    (same : ∀ handle, snapshot.candidates.lookup handle ≠ .fresh →
      first handle = second handle) :
    sourceSnapshotPair setup implementation target reference first snapshot =
      sourceSnapshotPair setup implementation target reference second snapshot := by
  classical
  funext field
  by_cases visible : (serviceGraph setup .concurrent).fieldPublic field
  · simp only [sourceSnapshotPair, visible, ite_true]
  · cases field with
    | inl input => rfl
    | inr event =>
        simp only [sourceSnapshotPair, visible, ite_false]
        apply congrArg (fun read => (snapshot.config.store (.inr event)).bind read)
        funext before
        cases descriptor : nodeView (serviceGraph setup .concurrent) event with
        | bind owner payload shape code =>
            dsimp only
            cases result : cast (congrArg EventField.Value shape) before with
            | failure => rfl
            | success old =>
                cases accepted : snapshot.accepted (.inr event) with
                | none => rfl
                | some handle =>
                    simp only [Option.bind_some]
                    rw [same handle (valid.accepted_fixed (.inr event) handle accepted)]
        | resolve owner payload binding checks shape code => rfl
        | sample payload law shape code => rfl

omit [Fintype Player] in
/-- Lost draws at still fresh handles cannot affect an earlier assigned
snapshot, even though the handle assignment uses the final reference control. -/
private theorem sourceSnapshotState_lost_congr
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (first second : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (valid : snapshot.BindingInvariant)
    (same : ∀ handle, snapshot.candidates.lookup handle ≠ .fresh →
      first handle = second handle) :
    sourceSnapshotState setup implementation target reference first snapshot =
      sourceSnapshotState setup implementation target reference second snapshot := by
  classical
  have pairs : sourceSnapshotPairs setup implementation target reference first snapshot =
      sourceSnapshotPairs setup implementation target reference second snapshot := by
    simp only [sourceSnapshotPairs,
      sourceSnapshotPair_lost_congr setup implementation target reference first second
        snapshot valid same]
  have catalogue :
      (HiddenSwap.ofPairs (sourceSnapshotPairs setup implementation target reference first
        snapshot) (sourceHandlePairs setup implementation target reference first)).candidates
          snapshot.candidates =
      (HiddenSwap.ofPairs (sourceSnapshotPairs setup implementation target reference second
        snapshot) (sourceHandlePairs setup implementation target reference second)).candidates
          snapshot.candidates := by
    cases stored : snapshot.candidates with
    | mk table =>
        apply congrArg CommitmentCandidates.mk
        funext owner slot
        change swapCandidate (EventGraph.pairSwap
            (sourceHandlePairs setup implementation target reference first (owner, slot)))
              (table owner slot) =
          swapCandidate (EventGraph.pairSwap
            (sourceHandlePairs setup implementation target reference second (owner, slot)))
              (table owner slot)
        cases candidate : table owner slot with
        | fresh => rfl
        | unopenable => rfl
        | openable raw =>
            have fixed : snapshot.candidates.lookup (owner, slot) ≠ .fresh := by
              rw [stored]
              change table owner slot ≠ .fresh
              rw [candidate]
              intro impossible
              cases impossible
            have handles : sourceHandlePairs setup implementation target reference first
                (owner, slot) =
                sourceHandlePairs setup implementation target reference second (owner, slot) := by
              unfold sourceHandlePairs
              rw [same (owner, slot) fixed]
            rw [handles]
  unfold sourceSnapshotState State.swap
  rw [catalogue, pairs]
  rfl

/-- The sequential lost-draw law may extend its domain after a fresh
registration without altering any prior current, saved or retired image. -/
private theorem sourceSnapshotAssignment_lost_congr
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (first second : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (same : ∀ handle,
      control.execution.application.current.native.candidates.lookup handle ≠ .fresh →
      first handle = second handle) :
    sourceSnapshotAssignment setup implementation target reference first
        control.execution.application =
      sourceSnapshotAssignment setup implementation target reference second
        control.execution.application := by
  let inputs := setup.initialLaw.map encodeInputs
  have raw : ((nativeApplication).protocol
      (inputs.map (PhaseRuntimeState.initial implementation.plan)) implementation.horizon
        implementation.scheduler).Trace (some control) := by
    rw [show inputs.map (PhaseRuntimeState.initial implementation.plan) = nativeInitial by
      simp only [inputs, ReservedConcurrentImplementation.initial, PMF.map_comp,
        Function.comp_def]]
    exact (nativeMenu).toRawTrace nativeInitial implementation.horizon
      implementation.scheduler trace
  have record := phaseBindingRecord_history implementation.runtime implementation.leaks
    implementation.plan inputs implementation.horizon implementation.scheduler raw
  have archives := phaseRetiredBindings_history implementation.runtime implementation.leaks
    implementation.plan inputs implementation.horizon implementation.scheduler raw
  have restrict (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
      (kept : KeepsFixedCandidates snapshot control.execution.application.current.native) :
      ∀ handle, snapshot.candidates.lookup handle ≠ .fresh → first handle = second handle := by
    intro handle fixed
    apply same handle
    rw [kept handle fixed]
    exact fixed
  have current := sourceSnapshotState_lost_congr setup implementation target reference first
    second control.execution.application.current.native record.active same
  have saved := sourceSnapshotState_lost_congr setup implementation target reference first
    second control.execution.application.entry.native record.saved (restrict _ record.fixed)
  have retired :
      control.execution.application.retired.map (fun old => { old with
        state := sourceSnapshotState setup implementation target reference first old.state }) =
      control.execution.application.retired.map (fun old => { old with
        state := sourceSnapshotState setup implementation target reference second old.state }) := by
    apply List.map_congr_left
    intro old member
    have oldImage := sourceSnapshotState_lost_congr setup implementation target reference first
      second old.state (archives old member).1 (restrict _ (archives old member).2.2)
    cases old
    exact congrArg (RetiredCommitAttempt.mk _) oldImage
  unfold sourceSnapshotAssignment
  rw [current, saved, retired]

/-- Sampling a lost value at its first registration cannot alter an earlier
assigned application or any input subsequently read from that application. -/
theorem sourceSnapshotAssignment_extend_lost
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (handle : Handle (serviceGraph setup .concurrent)) (value : Option (Raw L))
    (before current : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before))
    (trace : (nativeProtocol).Trace (some current))
    (retained : TracePrefix prior trace)
    (fresh : current.execution.application.current.native.candidates.lookup handle = .fresh) :
    sourceSnapshotAssignment setup implementation target reference lost
        before.execution.application =
      sourceSnapshotAssignment setup implementation target reference
        (Function.update lost handle value) before.execution.application := by
  apply sourceSnapshotAssignment_lost_congr setup implementation target reference lost
    (Function.update lost handle value) before prior
  intro candidate fixed
  have different : candidate ≠ handle := by
    intro equal
    subst candidate
    let stable := phaseApplication_preservesFixedCandidates implementation.runtime
      implementation.leaks
    have preserved : (nativeApplication).Invariant (fun state =>
        state.current.native.candidates.lookup handle =
          before.execution.application.current.native.candidates.lookup handle) := by
      constructor
      · intro state owner material known
        exact (stable.submit state owner material handle (by rw [known]; exact fixed)).trans known
      · intro state message next known handled
        exact (stable.handle state message next handled handle
          (by rw [known]; exact fixed)).trans known
      · intro state command next known reached
        exact (stable.environment state command next reached handle
          (by rw [known]; exact fixed)).trans known
    have unchanged := preserved.tracePrefix (nativeMenu) nativeInitial implementation.horizon
      implementation.scheduler before current prior trace retained rfl
    exact fixed (unchanged.symm.trans fresh)
  exact (Function.update_of_ne different value lost).symm

/- The full focal information equality retains the focal observation of the
literal original base state, even when later hidden source choices differ. -/
omit [Fintype Player] in
private theorem sourceReplayBaseObservation
    (who : Player)
    (first second : CommitRecoveryState setup.program)
    (left : setup.proposalRecoveryProtocol.Trace (some first))
    (right : setup.proposalRecoveryProtocol.Trace (some second))
    (same : setup.proposalRecoveryModel.infoOf who left =
      setup.proposalRecoveryModel.infoOf who right) :
    sourceObserve who (ProtocolState.base setup.program first.point) =
      sourceObserve who (ProtocolState.base setup.program second.point) := by
  have signals := congrArg Prod.fst same
  change (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who left).1 =
    (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who right).1 at signals
  rw [InfoSignals.withOwnPlayRecall_infoOf,
    InfoSignals.withOwnPlayRecall_infoOf] at signals
  have semantic := congrArg (setup.proposalRecoveryEraseBaseInfo who) signals
  rw [setup.proposalRecoveryEraseBaseInfo_observed,
    setup.proposalRecoveryEraseBaseInfo_observed] at semantic
  have observed := congrArg (fun information => information.1.1) semantic
  have privateEq : setup.commitRecoveryPrivate who (some first) =
      setup.commitRecoveryPrivate who (some second) := by
    simpa only [setup.commitRecoverySignals_current] using observed
  have views : ProtocolState.observe who setup.program first.point =
      ProtocolState.observe who setup.program second.point := Option.some.inj privateEq
  exact ProtocolState.sourceObserve_base_eq_of_observe_eq who setup.program
    first.point second.point views

/- Equality of the source observation fixes every public initial graph input,
while leaving other players' private and binding values unrestricted. -/
omit [Fintype Player] in
omit [IExpr.ResultTypes L] in
private theorem sourceReplayPublicInputs {Γ : SourceCtx Player L}
    (who : Player) (first second : State L Γ)
    (same : sourceObserve who first = sourceObserve who second) :
    ∀ input, (inputLayout Γ input).IsPublic →
      encodeInputs first input = encodeInputs second input := by
  have locate : ∀ (Δ : SourceCtx Player L) (input : Fin Δ.length),
      ∃ (name : VarId) (cell : CellTy Player L),
        ∃ member : HasVar Δ name cell, inputId member = input := by
    intro Δ
    induction Δ with
    | nil => intro input; exact Fin.elim0 input
    | cons head tail ih =>
        rcases head with ⟨name, cell⟩
        intro input
        cases input using Fin.cases with
        | zero => exact ⟨name, cell, .here, rfl⟩
        | succ smaller =>
            obtain ⟨found, kind, member, position⟩ := ih smaller
            exact ⟨found, kind, .there member, congrArg Fin.succ position⟩
  intro input visible
  obtain ⟨name, cell, member, position⟩ := locate Γ input
  rw [← position] at visible ⊢
  rw [inputLayout_inputId member] at visible
  cases cell with
  | publicData payload =>
      have observed := congrArg
        (fun view => view.cells name (.publicData payload) member) same
      simp only [sourceObserve_publicData] at observed
      apply (Equiv.cast (congrArg EventField.Value
        (inputLayout_inputId member))).injective
      calc
        _ = cellValue (first.get member) := encodeInputs_get first member
        _ = cellValue (second.get member) := congrArg cellValue observed
        _ = _ := (encodeInputs_get second member).symm
  | publication payload =>
      have observed := congrArg
        (fun view => view.cells name (.publication payload) member) same
      simp only [sourceObserve_publication] at observed
      apply (Equiv.cast (congrArg EventField.Value
        (inputLayout_inputId member))).injective
      calc
        _ = cellValue (first.get member) := encodeInputs_get first member
        _ = cellValue (second.get member) := congrArg cellValue observed
        _ = _ := (encodeInputs_get second member).symm
  | privateInput owner payload =>
      have impossible : False := by
        simp only [cellField, EventField.IsPublic] at visible
      exact impossible.elim
  | commitment owner payload =>
      have impossible : False := by
        simp only [cellField, EventField.IsPublic] at visible
      exact impossible.elim

/- A supported forced source suffix keeps the original setup draw. Equal
focal information at the static cut therefore fixes each public input of the
whole target initializer, including publication results. -/
private theorem sourceReplayTargetPublicInputs
    (who : Player) (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (event : (serviceGraph setup .concurrent).EventId)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
      implementation.horizon implementation.scheduler reference
      (sourceCutTrace setup implementation referenceTrace) who event)
    (g : setup.proposalRecoveryProtocol.History)
    (sameInfo : setup.proposalRecoveryModel.infoOf who g.trace =
      setup.proposalRecoveryModel.infoOf who cut.trace)
    (choice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (supported : (⟨some targetCurrent, targetTrace⟩ :
      setup.proposalRecoveryProtocol.History) ∈
        (sourceForcedBlock setup values who g choice).support) :
    ∀ input, (serviceGraph setup .concurrent).fieldPublic (.inl input) →
      encodeInputs cut.theta input =
        encodeInputs (ProtocolState.base setup.program targetCurrent.point) input := by
  rcases g with ⟨state, gTrace⟩
  cases state with
  | none =>
      have impossible := source_information_metadata setup who
        ⟨some cut.current, cut.trace⟩ ⟨none, gTrace⟩ sameInfo.symm
      exact impossible.elim
  | some gCurrent =>
      have baseObservation := sourceReplayBaseObservation setup who cut.current gCurrent
        cut.trace gTrace sameInfo.symm
      rw [cut.base_eq_theta] at baseObservation
      have continuation : TracePrefix gTrace targetTrace := by
        have reached := supported
        unfold sourceForcedBlock at reached
        obtain ⟨middle, first, last⟩ := (PMF.mem_support_bind_iff ..).mp reached
        exact ((setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ 1
          ⟨some gCurrent, gTrace⟩ middle first).tracePrefix).trans
            ((setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ _
              middle ⟨some targetCurrent, targetTrace⟩ last).tracePrefix)
      have gBase := (source_initial_base_supported setup gCurrent gTrace).2
      obtain ⟨current, endpoint, targetBase, _saved⟩ :=
        setup.commitRecovery_base_of_prefix gCurrent
          (setup.proposalRecoveryEraseTrace gTrace) gBase
          (setup.proposalRecoveryEraseTrace targetTrace)
          (setup.proposalRecoveryEraseTrace_prefix continuation)
      have currentEq : current = targetCurrent := Option.some.inj endpoint.symm
      subst current
      rw [← targetBase] at baseObservation
      intro input visible
      exact sourceReplayPublicInputs who cut.theta
        (ProtocolState.base setup.program targetCurrent.point) baseObservation input
          (by change (inputLayout setup.context input).IsPublic at visible; exact visible)

/- The initial hidden input fields read the whole target source tuple. Public
input fields are fixed by their observed equality on the focal information
fiber; no independence of the original joint input law is used. -/
omit [Fintype Player] in
private theorem sourceReplayInitialInputs
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (oldInputs newInputs : (serviceGraph setup .concurrent).Inputs)
    (current : CommitRecoveryState setup.program)
    (present : target.state = some current)
    (newTuple : newInputs = encodeInputs (ProtocolState.base setup.program current.point))
    (publicInput : ∀ input, (serviceGraph setup .concurrent).fieldPublic (.inl input) →
      oldInputs input = newInputs input) :
    ∀ input,
      (sourceSnapshotState setup implementation target reference lost
        (EventGraphRuntime.State.initial oldInputs)).config.inputs input =
          newInputs input := by
  classical
  intro input
  change EventGraph.pairSwap
    (sourceSnapshotPair setup implementation target reference lost
      (EventGraphRuntime.State.initial oldInputs) (.inl input))
      (oldInputs input) = newInputs input
  by_cases visible : (serviceGraph setup .concurrent).fieldPublic (.inl input)
  · simp only [sourceSnapshotPair, visible, ↓reduceIte, EventGraph.pairSwap]
    exact publicInput input visible
  · simp only [sourceSnapshotPair, visible, ↓reduceIte,
      EventGraphRuntime.State.initial, EventGraph.Config.initial, present,
      Option.map_some, newTuple]
    exact Equiv.swap_apply_left _ _

/- An actual initialized native trace retains the successful opaque meaning
of every source commitment input. This uses the original whole input tuple,
not a marginal or an assumed candidate equivalence. -/
theorem sourceReplayReferenceInitialCatalogue
    (operational : implementation.Operational)
    (reference : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some reference))
    (theta : State L setup.context)
    (supported : theta ∈ setup.initialLaw.support)
    (inputsEq : reference.execution.application.current.native.config.inputs =
      encodeInputs theta) :
    ∀ input owner payload
      (_shape : (serviceGraph setup .concurrent).inputLayout input = .binding owner payload),
      reference.execution.application.current.native.candidates.lookup
          (owner, .initial input) =
        (EventGraphRuntime.State.initial (encodeInputs theta)).candidates.lookup
          (owner, .initial input) := by
  let inputs := setup.initialLaw.map encodeInputs
  have raw : ((nativeApplication).protocol
      (inputs.map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some reference) := by
    rw [show inputs.map (PhaseRuntimeState.initial implementation.plan) = nativeInitial by
      simp only [inputs, ReservedConcurrentImplementation.initial, PMF.map_comp,
        Function.comp_def]]
    exact (nativeMenu).toRawTrace nativeInitial implementation.horizon
      implementation.scheduler trace
  have valid := phaseBindingRecord_history implementation.runtime implementation.leaks
    implementation.plan inputs implementation.horizon implementation.scheduler raw
  intro input owner payload shape
  let field : FieldRef (serviceGraph setup .concurrent).layout
      (.binding owner payload) := ⟨.inl input, shape⟩
  have accepted : reference.execution.application.current.native.accepted (.inl input) =
      some (owner, .initial input) :=
    phaseInputBinding_history implementation.runtime implementation.leaks implementation.plan
      inputs implementation.horizon implementation.scheduler raw input owner payload shape
  have currentInputs : ∀ input,
      reference.execution.application.current.native.config.store (.inl input) =
        some (encodeInputs theta input) := by
    intro next
    rw [EventGraph.Config.store_input, inputsEq]
  obtain ⟨value, currentRead⟩ := input_binding_value setup .concurrent operational.wellFormed
    theta supported reference.execution.application.current.native.config.store currentInputs
      owner payload field input rfl
  obtain ⟨candidate, actualAccepted, _owned, actualCandidate⟩ :=
    valid.active.success_provenance field value currentRead
  have candidateEq : candidate = (owner, .initial input) := by
    exact Option.some.inj (actualAccepted.symm.trans accepted)
  subst candidate
  obtain ⟨initialValue, initialRead⟩ := input_binding_value setup .concurrent
    operational.wellFormed theta supported
      (EventGraphRuntime.State.initial (encodeInputs theta)).config.store
      (fun _ => rfl) owner payload field input rfl
  have sameValue : value = initialValue := by
    have sameStore : reference.execution.application.current.native.config.store
        (.inl input) =
          (EventGraphRuntime.State.initial (encodeInputs theta)).config.store
            (.inl input) := by
      rw [currentInputs input]
      rfl
    have sameRead := EventGraph.FieldRef.get?_congr field _ _ sameStore
    exact PublicationResult.success.inj
      (Option.some.inj (currentRead.symm.trans (sameRead.trans initialRead)))
  subst initialValue
  have castSome {α β : Type} (equal : α = β) (item : α) :
      cast (congrArg Option equal) (some item) = some (cast equal item) := by
    cases equal
    rfl
  have initialStore : (EventGraphRuntime.State.initial (encodeInputs theta)).config.store
      (.inl input) = some (encodeInputs theta input) := rfl
  dsimp only [field, FieldRef.get?] at initialRead
  rw [initialStore, castSome (congrArg EventField.Value shape)] at initialRead
  have decoded : cast (congrArg EventField.Value shape) (encodeInputs theta input) =
      .success value := Option.some.inj initialRead
  have initialCandidate := EventGraphRuntime.State.initial_candidate_binding_success
    (encodeInputs theta) input owner payload shape value decoded
  exact actualCandidate.trans initialCandidate.symm

/- Supported initial binding cells remain openable. Their raw meanings are
paired with the corresponding target initial values; all other initial slots
remain fresh, so the assigned initial catalogue is the target catalogue. -/
private theorem sourceReplayInitialCandidates
    (operational : implementation.Operational)
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (oldTheta newTheta : State L setup.context)
    (oldSupported : oldTheta ∈ setup.initialLaw.support)
    (newSupported : newTheta ∈ setup.initialLaw.support)
    (current : CommitRecoveryState setup.program)
    (present : target.state = some current)
    (newBase : ProtocolState.base setup.program current.point = newTheta)
    (oldCatalogue : ∀ input owner payload
      (_shape : (serviceGraph setup .concurrent).inputLayout input = .binding owner payload),
      reference.execution.application.current.native.candidates.lookup
          (owner, .initial input) =
        (EventGraphRuntime.State.initial (encodeInputs oldTheta)).candidates.lookup
          (owner, .initial input)) :
    ∀ owner slot,
      (sourceSnapshotState setup implementation target reference lost
        (EventGraphRuntime.State.initial (encodeInputs oldTheta))).candidates.lookup
          (owner, slot) =
        (EventGraphRuntime.State.initial (encodeInputs newTheta)).candidates.lookup
          (owner, slot) := by
  classical
  let graph := serviceGraph setup .concurrent
  have bindingValue (theta : State L setup.context)
      (supported : theta ∈ setup.initialLaw.support)
      (owner : Player) (payload : L.Ty) (input : graph.InputId)
      (shape : graph.inputLayout input = .binding owner payload) :
      ∃ value : L.Val payload,
        cast (congrArg EventField.Value shape) (encodeInputs theta input) =
          .success value := by
    let ref : FieldRef graph.layout (.binding owner payload) := ⟨.inl input, shape⟩
    obtain ⟨value, read⟩ := input_binding_value setup .concurrent operational.wellFormed
      theta supported (EventGraphRuntime.State.initial (encodeInputs theta)).config.store
        (fun _ => rfl) owner payload ref input rfl
    have stored : (EventGraphRuntime.State.initial (encodeInputs theta)).config.store
        (.inl input) = some (encodeInputs theta input) := rfl
    have castSome {α β : Type} (equal : α = β) (item : α) :
        cast (congrArg Option equal) (some item) = some (cast equal item) := by
      cases equal
      rfl
    dsimp only [ref, FieldRef.get?] at read
    rw [stored, castSome (congrArg EventField.Value shape)] at read
    exact ⟨value, Option.some.inj read⟩
  intro owner slot
  change swapCandidate
    (EventGraph.pairSwap (sourceHandlePairs setup implementation target reference lost
      (owner, slot)))
      ((EventGraphRuntime.State.initial (encodeInputs oldTheta)).candidates.lookup
        (owner, slot)) =
    (EventGraphRuntime.State.initial (encodeInputs newTheta)).candidates.lookup
      (owner, slot)
  cases slot with
  | prepared serial =>
      simp only [EventGraphRuntime.State.initial_candidate, swapCandidate_fresh]
  | «initial» input =>
      cases shape : graph.inputLayout input with
      | publicData payload =>
          have fresh (kind : EventField Player L) (value : kind.Value)
              (kindEq : kind = .publicData payload) :
              EventGraphRuntime.State.candidateOfValue owner kind value = .fresh := by
            cases kindEq
            rfl
          have oldFresh : (EventGraphRuntime.State.initial
              (encodeInputs oldTheta)).candidates.lookup (owner, .initial input) = .fresh := by
            rw [EventGraphRuntime.State.initial_candidate]
            exact fresh _ _ shape
          have newFresh : (EventGraphRuntime.State.initial
              (encodeInputs newTheta)).candidates.lookup (owner, .initial input) = .fresh := by
            rw [EventGraphRuntime.State.initial_candidate]
            exact fresh _ _ shape
          simp only [oldFresh, newFresh, swapCandidate_fresh]
      | publication payload =>
          have fresh (kind : EventField Player L) (value : kind.Value)
              (kindEq : kind = .publication payload) :
              EventGraphRuntime.State.candidateOfValue owner kind value = .fresh := by
            cases kindEq
            rfl
          have oldFresh : (EventGraphRuntime.State.initial
              (encodeInputs oldTheta)).candidates.lookup (owner, .initial input) = .fresh := by
            rw [EventGraphRuntime.State.initial_candidate]
            exact fresh _ _ shape
          have newFresh : (EventGraphRuntime.State.initial
              (encodeInputs newTheta)).candidates.lookup (owner, .initial input) = .fresh := by
            rw [EventGraphRuntime.State.initial_candidate]
            exact fresh _ _ shape
          simp only [oldFresh, newFresh, swapCandidate_fresh]
      | privateInput inputOwner payload =>
          have fresh (kind : EventField Player L) (value : kind.Value)
              (kindEq : kind = .privateInput inputOwner payload) :
              EventGraphRuntime.State.candidateOfValue owner kind value = .fresh := by
            cases kindEq
            rfl
          have oldFresh : (EventGraphRuntime.State.initial
              (encodeInputs oldTheta)).candidates.lookup (owner, .initial input) = .fresh := by
            rw [EventGraphRuntime.State.initial_candidate]
            exact fresh _ _ shape
          have newFresh : (EventGraphRuntime.State.initial
              (encodeInputs newTheta)).candidates.lookup (owner, .initial input) = .fresh := by
            rw [EventGraphRuntime.State.initial_candidate]
            exact fresh _ _ shape
          simp only [oldFresh, newFresh, swapCandidate_fresh]
      | binding bindingOwner payload =>
          by_cases same : bindingOwner = owner
          · subst bindingOwner
            obtain ⟨oldValue, oldSuccess⟩ :=
              bindingValue oldTheta oldSupported owner payload input shape
            obtain ⟨newValue, newSuccess⟩ :=
              bindingValue newTheta newSupported owner payload input shape
            let oldRaw : Raw L := ⟨payload, oldValue⟩
            let newRaw : Raw L := ⟨payload, newValue⟩
            have oldCandidate :
                (EventGraphRuntime.State.initial (encodeInputs oldTheta)).candidates.lookup
                  (owner, .initial input) = .openable oldRaw :=
              EventGraphRuntime.State.initial_candidate_binding_success
                (encodeInputs oldTheta) input owner payload shape oldValue oldSuccess
            have newCandidate :
                (EventGraphRuntime.State.initial (encodeInputs newTheta)).candidates.lookup
                  (owner, .initial input) = .openable newRaw :=
              EventGraphRuntime.State.initial_candidate_binding_success
                (encodeInputs newTheta) input owner payload shape newValue newSuccess
            have meaning : sourceHandleMeaning setup implementation target reference
                (owner, .initial input) = some newRaw := by
              simp only [sourceHandleMeaning, present, Option.bind_some, newBase,
                newCandidate]
            have pair : sourceHandlePairs setup implementation target reference lost
                (owner, .initial input) = some (oldRaw, newRaw) := by
              simp only [sourceHandlePairs, oldCatalogue input owner payload shape, oldCandidate,
                meaning, Option.orElse_some, Option.map_some]
            rw [oldCandidate, newCandidate, pair]
            simp only [EventGraph.pairSwap, swapCandidate_openable,
              Equiv.swap_apply_left]
          · have fresh (kind : EventField Player L) (value : kind.Value)
                (kindEq : kind = .binding bindingOwner payload) :
                EventGraphRuntime.State.candidateOfValue owner kind value = .fresh := by
              cases kindEq
              simp only [EventGraphRuntime.State.candidateOfValue, same, ↓reduceIte]
            have oldFresh : (EventGraphRuntime.State.initial
                (encodeInputs oldTheta)).candidates.lookup (owner, .initial input) = .fresh := by
              rw [EventGraphRuntime.State.initial_candidate]
              exact fresh _ _ shape
            have newFresh : (EventGraphRuntime.State.initial
                (encodeInputs newTheta)).candidates.lookup (owner, .initial input) = .fresh := by
              rw [EventGraphRuntime.State.initial_candidate]
              exact fresh _ _ shape
            simp only [oldFresh, newFresh, swapCandidate_fresh]

/- The actual well-formed initial source tuples give the whole native initial
image, including opaque initial candidates. -/
private theorem sourceReplayInitialNative
    (operational : implementation.Operational)
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (oldTheta newTheta : State L setup.context)
    (oldSupported : oldTheta ∈ setup.initialLaw.support)
    (newSupported : newTheta ∈ setup.initialLaw.support)
    (current : CommitRecoveryState setup.program)
    (present : target.state = some current)
    (newBase : ProtocolState.base setup.program current.point = newTheta)
    (publicInput : ∀ input, (serviceGraph setup .concurrent).fieldPublic (.inl input) →
      encodeInputs oldTheta input = encodeInputs newTheta input)
    (oldCatalogue : ∀ input owner payload
      (_shape : (serviceGraph setup .concurrent).inputLayout input = .binding owner payload),
      reference.execution.application.current.native.candidates.lookup
          (owner, .initial input) =
        (EventGraphRuntime.State.initial (encodeInputs oldTheta)).candidates.lookup
          (owner, .initial input)) :
    sourceSnapshotState setup implementation target reference lost
        (EventGraphRuntime.State.initial (encodeInputs oldTheta)) =
      EventGraphRuntime.State.initial (encodeInputs newTheta) := by
  let oldState : EventGraphRuntime.State (serviceGraph setup .concurrent) :=
    EventGraphRuntime.State.initial (encodeInputs oldTheta)
  let newState : EventGraphRuntime.State (serviceGraph setup .concurrent) :=
    EventGraphRuntime.State.initial (encodeInputs newTheta)
  have inputRows := sourceReplayInitialInputs setup implementation target reference lost
    (encodeInputs oldTheta) (encodeInputs newTheta) current present (by rw [newBase]) publicInput
  have candidateRows := sourceReplayInitialCandidates setup implementation operational target
    reference lost oldTheta newTheta oldSupported newSupported current present newBase oldCatalogue
  have config : (sourceSnapshotState setup implementation target reference lost oldState).config =
      newState.config := by
    apply EventGraph.Config.ext_fields
    · funext input
      exact inputRows input
    · rfl
    · rfl
    · rfl
  have candidates :
      (sourceSnapshotState setup implementation target reference lost oldState).candidates =
        newState.candidates := by
    change CommitmentCandidates.mk _ = CommitmentCandidates.mk _
    congr 1
    funext owner slot
    exact candidateRows owner slot
  change (sourceSnapshotState setup implementation target reference lost oldState) = newState
  calc
    sourceSnapshotState setup implementation target reference lost oldState =
        { oldState with
          config := (sourceSnapshotState setup implementation target reference lost
            oldState).config
          candidates := (sourceSnapshotState setup implementation target reference lost
            oldState).candidates } := rfl
    _ = { oldState with config := newState.config, candidates := newState.candidates } :=
      congrArg₂ (fun c d => { oldState with config := c, candidates := d }) config candidates
    _ = newState := rfl

/- The source initializer uses the entire target input tuple. The swap of the
raw initial native state is enough to carry every automatically settled phase,
including its entry and current snapshots, through the checked normalization
commutation. -/
omit [Fintype Player] in
private theorem sourceReplayAssignedInitial
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (originalInputs targetInputs : (serviceGraph setup .concurrent).Inputs)
    (nativeImage : sourceSnapshotState setup implementation target reference lost
      (EventGraphRuntime.State.initial originalInputs) =
        EventGraphRuntime.State.initial targetInputs) :
    sourceSnapshotAssignment setup implementation target reference lost
        (PhaseRuntimeState.initial implementation.plan originalInputs) =
      PhaseRuntimeState.initial implementation.plan targetInputs := by
  let original : PhaseRuntimeState (serviceGraph setup .concurrent) :=
    ⟨implementation.plan.phases, 0,
      ⟨EventGraphRuntime.State.initial originalInputs, ∅⟩,
      ⟨EventGraphRuntime.State.initial originalInputs, ∅⟩, []⟩
  let mapped : PhaseRuntimeState (serviceGraph setup .concurrent) :=
    ⟨implementation.plan.phases, 0,
      ⟨EventGraphRuntime.State.initial targetInputs, ∅⟩,
      ⟨EventGraphRuntime.State.initial targetInputs, ∅⟩, []⟩
  have seed : sourceSnapshotAssignment setup implementation target reference lost original =
      mapped := by
    simp only [original, mapped, sourceSnapshotAssignment, nativeImage, List.map_nil]
  calc
    sourceSnapshotAssignment setup implementation target reference lost
        (PhaseRuntimeState.initial implementation.plan originalInputs) =
      sourceSnapshotAssignment setup implementation target reference lost original.normalize :=
        rfl
    _ = (sourceSnapshotAssignment setup implementation target reference lost original).normalize :=
      (sourceSnapshotAssignment_normalize setup implementation target reference lost original).symm
    _ = mapped.normalize := congrArg PhaseRuntimeState.normalize seed
    _ = PhaseRuntimeState.initial implementation.plan targetInputs := rfl

/- The factual initialized native tuple is assigned to the supported whole
target tuple, including every initial commitment catalogue entry. -/
theorem sourceReplayInitialFromCut
    (operational : implementation.Operational)
    (who : Player) (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (event : (serviceGraph setup .concurrent).EventId)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
      implementation.horizon implementation.scheduler reference
      (sourceCutTrace setup implementation referenceTrace) who event)
    (g : setup.proposalRecoveryProtocol.History)
    (sameInfo : setup.proposalRecoveryModel.infoOf who g.trace =
      setup.proposalRecoveryModel.infoOf who cut.trace)
    (choice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (supported : (⟨some targetCurrent, targetTrace⟩ :
      setup.proposalRecoveryProtocol.History) ∈
        (sourceForcedBlock setup values who g choice).support)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L)) :
    sourceSnapshotAssignment setup implementation ⟨some targetCurrent, targetTrace⟩
        reference lost
        (PhaseRuntimeState.initial implementation.plan (encodeInputs cut.theta)) =
      PhaseRuntimeState.initial implementation.plan
        (encodeInputs (ProtocolState.base setup.program targetCurrent.point)) := by
  have catalogue := sourceReplayReferenceInitialCatalogue setup implementation
    operational reference referenceTrace cut.theta cut.thetaSupported cut.originalInputs
  have publicInput := sourceReplayTargetPublicInputs setup values implementation who
    reference referenceTrace event cut g sameInfo choice targetCurrent targetTrace supported
  have native := sourceReplayInitialNative setup implementation operational
    ⟨some targetCurrent, targetTrace⟩ reference lost cut.theta
    (ProtocolState.base setup.program targetCurrent.point) cut.thetaSupported
    (source_initial_base_supported setup targetCurrent targetTrace).1 targetCurrent rfl rfl
    publicInput catalogue
  exact sourceReplayAssignedInitial setup implementation
    ⟨some targetCurrent, targetTrace⟩ reference lost _ _ native

/- On an old reference, the assigned stored value depends only on its real
stored value and its accepted handle. This is the transport used at a genuine
close and inside automatic normalization, with the same fixed target and map. -/
omit [Fintype Player] in
private theorem sourceReplayAssignedStoreCongr
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before after : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (field : (serviceGraph setup .concurrent).Field)
    (stored : before.config.store field = after.config.store field)
    (accepted : ∀ (owner : Player) (payload : L.Ty)
      (shape : (serviceGraph setup .concurrent).layout field = .binding owner payload)
      (value : L.Val payload),
      before.config.store field =
        some (cast (congrArg EventField.Value shape.symm) (.success value)) →
      before.accepted field = after.accepted field) :
    (sourceSnapshotState setup implementation target reference lost before).config.store field =
      (sourceSnapshotState setup implementation target reference lost
        after).config.store field := by
  have paired : sourceSnapshotPair setup implementation target reference lost before field =
      sourceSnapshotPair setup implementation target reference lost after field := by
    cases field with
    | inl input =>
        unfold sourceSnapshotPair
        simp only [stored]
    | inr event =>
        unfold sourceSnapshotPair
        by_cases visible : (serviceGraph setup .concurrent).fieldPublic (.inr event)
        · simp only [visible, ↓reduceIte]
        · simp only [visible, ↓reduceIte]
          cases found : before.config.store (.inr event) with
          | none => simp only [← stored, found, Option.bind_none]
          | some value =>
              simp only [← stored, found, Option.bind_some]
              cases descriptor : nodeView (serviceGraph setup .concurrent) event with
              | bind owner payload shape code =>
                  cases result : cast (congrArg EventField.Value shape) value with
                  | failure => simp only [result]
                  | success raw =>
                      have valueEq : value =
                          cast (congrArg EventField.Value shape.symm) (.success raw) := by
                        have equal := congrArg
                          (cast (congrArg EventField.Value shape.symm)) result
                        simpa only [cast_cast, cast_eq] using equal
                      have same := accepted owner payload shape raw (by rw [← valueEq]; exact found)
                      simp only [result, same]
              | resolve owner payload input guards shape code => rfl
              | sample payload law shape code => rfl
  unfold sourceSnapshotState
  simp only [EventGraphRuntime.State.swap_config, EventGraph.Config.swap_store]
  change (before.config.store field).map
      (EventGraph.pairSwap
        (sourceSnapshotPair setup implementation target reference lost before field)) =
    (after.config.store field).map
      (EventGraph.pairSwap
        (sourceSnapshotPair setup implementation target reference lost after field))
  rw [stored, paired]

/- Agreement already established at a typed source entry survives an actual
physical extension whenever that entry's own stored cells and accepted
handles survive. Newly issued fields are handled by the row induction. -/
omit [Fintype Player] in
theorem sourceReplayEntryAgreesOfPreserved
    {Γ : SourceCtx Player L}
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (entry : SourceProgram.Config Player L Γ)
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before after : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (agrees : refs.Agrees entry.state
      (sourceSnapshotState setup implementation target reference lost before).config.store)
    (stored : ∀ {name cell} (source : HasVar Γ name cell),
      before.config.store (refs.get source).field =
        after.config.store (refs.get source).field)
    (accepted : ∀ {name cell} (source : HasVar Γ name cell)
      (owner : Player) (payload : L.Ty)
      (shape : (serviceGraph setup .concurrent).layout (refs.get source).field =
        .binding owner payload) (value : L.Val payload),
      before.config.store (refs.get source).field =
        some (cast (congrArg EventField.Value shape.symm) (.success value)) →
      before.accepted (refs.get source).field =
        after.accepted (refs.get source).field) :
    refs.Agrees entry.state
      (sourceSnapshotState setup implementation target reference lost after).config.store := by
  intro name cell source
  have same := sourceReplayAssignedStoreCongr setup implementation target reference lost
    before after (refs.get source).field (stored source) (accepted source)
  exact (EventGraph.FieldRef.get?_congr (refs.get source) _ _ same).symm.trans
    (agrees source)

/- Automatic clean settlement retains every previously stored value at the
saved endpoint. The entry and current snapshots are the same actual drain;
their equal exclusions rule out every retry or restore branch. -/
omit [Fintype Player] in
theorem sourceReplaySettleSavedStore
    (phases : List (RuntimePhase (serviceGraph setup .concurrent)))
    (generation : Nat)
    (current : RecoveryState (serviceGraph setup .concurrent))
    (retired : List (RetiredCommitAttempt (serviceGraph setup .concurrent))) :
    KeepsStore current.native
      (PhaseRuntimeState.settle phases generation current current retired).entry.native := by
  induction phases generalizing generation current retired with
  | nil => exact fun _ _ stored => stored
  | cons phase remaining ih =>
      have noFailure : ¬ (phase.kind = .commitment ∧
          (((phase.drain current).excluded \ current.excluded) ∩
            phase.owners).Nonempty) := by
        rw [phase.drain_excluded current]
        simp only [Finset.sdiff_self, Finset.empty_inter,
          Finset.not_nonempty_empty, and_false, not_false_eq_true]
      by_cases finished : phase.Finished (phase.drain current)
      · rw [PhaseRuntimeState.settle_clean phase remaining generation current current
          retired finished noFailure]
        have later := ih generation (phase.drain current) retired
        exact fun field value stored => later field value
          (phase.drain_keepsStore current field value stored)
      · simp only [PhaseRuntimeState.settle, ite_eq_right finished]
        exact fun _ _ stored => stored

/- Automatic clean settlement retains the accepted table of the saved
snapshot. A drain only fills missing results; it does not change accepted
handles, including handles issued before this phase. -/
omit [Fintype Player] in
private theorem sourceReplaySettleSavedAccepted
    (phases : List (RuntimePhase (serviceGraph setup .concurrent)))
    (generation : Nat)
    (current : RecoveryState (serviceGraph setup .concurrent))
    (retired : List (RetiredCommitAttempt (serviceGraph setup .concurrent))) :
    (PhaseRuntimeState.settle phases generation current current retired).entry.native.accepted =
      current.native.accepted := by
  induction phases generalizing generation current retired with
  | nil => rfl
  | cons phase remaining ih =>
      have noFailure : ¬ (phase.kind = .commitment ∧
          (((phase.drain current).excluded \ current.excluded) ∩
            phase.owners).Nonempty) := by
        rw [phase.drain_excluded current]
        simp only [Finset.sdiff_self, Finset.empty_inter,
          Finset.not_nonempty_empty, and_false, not_false_eq_true]
      by_cases finished : phase.Finished (phase.drain current)
      · rw [PhaseRuntimeState.settle_clean phase remaining generation current current
          retired finished noFailure]
        exact (ih generation (phase.drain current) retired).trans
          (phase.drain_tables current).1
      · simp only [PhaseRuntimeState.settle, ite_eq_right finished]

/- The selected target entry agreement passes through automatic clean
settlement. Swapping preserves occupancy, so each assigned reference already
has a raw stored value which settlement and its accepted handle preserve. -/
omit [Fintype Player] in
theorem sourceReplaySettleAssignedSavedAgreement
    {Γ : SourceCtx Player L}
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (targetEntry : SourceProgram.Config Player L Γ)
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (phases : List (RuntimePhase (serviceGraph setup .concurrent)))
    (generation : Nat)
    (current : RecoveryState (serviceGraph setup .concurrent))
    (retired : List (RetiredCommitAttempt (serviceGraph setup .concurrent)))
    (targetAgrees : refs.Agrees targetEntry.state
      (sourceSnapshotState setup implementation target reference lost
        current.native).config.store) :
    refs.Agrees targetEntry.state
      (sourceSnapshotState setup implementation target reference lost
        ((PhaseRuntimeState.settle phases generation current current
          retired).entry.native)).config.store := by
  have castOptionNone {first second : EventField Player L} (equal : first = second) :
      cast (congrArg (fun kind : EventField Player L => Option kind.Value) equal)
        (none : Option first.Value) = (none : Option second.Value) := by
    cases equal
    rfl
  apply sourceReplayEntryAgreesOfPreserved setup implementation refs targetEntry target
    reference lost current.native
    (PhaseRuntimeState.settle phases generation current current retired).entry.native
    targetAgrees
  · intro name cell source
    have occupied := targetAgrees source
    have kept := sourceReplaySettleSavedStore setup phases generation current retired
    let field := (refs.get source).field
    cases stored : current.native.config.store field with
    | none =>
        have swappedEmpty :
            (sourceSnapshotState setup implementation target reference lost
              current.native).config.store field = none := by
          simp only [sourceSnapshotState, State.swap_config, Config.swap_store,
            ValueSwap.store, stored, Option.map_none]
        have emptyRead : (refs.get source).get?
            (sourceSnapshotState setup implementation target reference lost
              current.native).config.store = none := by
          unfold FieldRef.get?
          rw [swappedEmpty]
          exact castOptionNone (refs.get source).layout_eq
        rw [emptyRead] at occupied
        cases occupied
    | some value =>
        exact (kept field value stored).symm
  · intro name cell source _owner _payload _shape _value _stored
    exact (congrFun (sourceReplaySettleSavedAccepted setup phases generation current retired)
      (refs.get source).field).symm

/- Retrying restores the prior entry's semantic store and accepted handles
literally. Its physical catalogue and clock may advance without changing any
assigned value read by that source entry. -/
omit [Fintype Player] in
theorem sourceReplayRestoredEntryAgreement
    {Γ : SourceCtx Player L}
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (source : SourceProgram.Config Player L Γ)
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (entry current : RecoveryState (serviceGraph setup .concurrent))
    (agrees : refs.Agrees source.state
      (sourceSnapshotState setup implementation target reference lost
        entry.native).config.store) :
    refs.Agrees source.state
      (sourceSnapshotState setup implementation target reference lost
        (PhaseRuntimeState.restore entry current).native).config.store := by
  apply sourceReplayEntryAgreesOfPreserved setup implementation refs source target reference
    lost entry.native (PhaseRuntimeState.restore entry current).native agrees
  · intro _name _cell _selected
    rfl
  · intro _name _cell _selected _owner _payload _shape _value _stored
    rfl

/- A dirty close archives the exact drained native snapshot before any
automatic exhaustion settlement. The selected after-witness therefore reads
that same snapshot at the original retired-list index. -/
omit [Fintype Player] in
private theorem sourceReplayDirtyRecordRetained
    (state : PhaseRuntimeState (serviceGraph setup .concurrent))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (remaining : List (RuntimePhase (serviceGraph setup .concurrent)))
    (installed : state.phases = phase :: remaining)
    (raw : RecoveryState (serviceGraph setup .concurrent))
    (finished : phase.Finished (phase.drain raw))
    (kind : phase.kind = .commitment)
    (missed : (((phase.drain raw).excluded \ state.entry.excluded) ∩
      phase.owners).Nonempty) :
    state.retired ++ [⟨⟨phase.low, state.generation⟩, (phase.drain raw).native⟩] <+:
      ({ state with current := raw } : PhaseRuntimeState
        (serviceGraph setup .concurrent)).normalize.retired := by
  change state.retired ++ [⟨⟨phase.low, state.generation⟩,
      (phase.drain raw).native⟩] <+:
        (PhaseRuntimeState.settle state.phases state.generation state.entry raw
          state.retired).retired
  rw [installed]
  by_cases survivors : (phase.owners \ (phase.drain raw).excluded).Nonempty
  · rw [PhaseRuntimeState.settle_retry phase remaining state.generation state.entry raw
      state.retired finished kind missed survivors]
  · rw [PhaseRuntimeState.settle_exhausted phase remaining state.generation state.entry raw
      state.retired finished kind missed survivors]
    exact PhaseRuntimeState.settle_archive _ _ _ _ _

/- A genuine syntactic suffix embeds points injectively; each consumed
constructor adds only one `Sum.inr`. This recovers the full source entry from
equality of selected checkpoint states. -/
omit [Fintype Player] in
theorem sourceReplaySuffixInjective
    {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState setup.program}
    (origin : ProtocolSuffix setup.program program lift) : Function.Injective lift := by
  induction origin with
  | «initial» => exact fun _ _ same => same
  | sampleTail _ _ _ _ ih =>
      intro first second same
      exact Sum.inr.inj (ih same)
  | commitTail _ _ _ _ ih =>
      intro first second same
      exact Sum.inr.inj (ih same)
  | revealTail _ _ _ _ _ ih =>
      intro first second same
      exact Sum.inr.inj (ih same)

/- Two selected checkpoints at the same whole source starting history decode
one physical image with the same residual syntax, embedding, source entry and
excluded set. The payload is the complete typed instruction word. -/
omit [Fintype Player] in
private theorem sourceReplayCommitInstructionWordEq
    {first second : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (left : RecoverySourceCheckpoint setup .concurrent first)
    (right : RecoverySourceCheckpoint setup .concurrent second)
    (native : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (phase : first.attempt.phase = second.attempt.phase)
    (same : (⟨_, left.trace⟩ : setup.commitRecoveryProtocol.History) =
      ⟨_, right.trace⟩) :
    left.commitInstructionWord native = right.commitInstructionWord native := by
  have residual := left.residual_eq_of_phase_eq right phase
  have embeddings := left.embedding_eq_of_phase_eq right phase
  have starting := Option.some.inj (congrArg History.state same)
  have point := congrArg CommitRecoveryState.point starting
  have masks := congrArg CommitRecoveryState.excluded starting
  change first.entry.excluded = second.entry.excluded at masks
  rcases left with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, alignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, history, memory, steps, menus, readout, leftTrace, views,
    historyAlignment, origin⟩
  rcases right with ⟨otherResidual, otherSource, otherRefs, otherRegistry, otherEmbedding,
    otherBefore, otherCompiled, otherAlignment, otherAgrees, otherGuards, otherFailures,
    otherUnique, otherRanks, otherActors, otherCommits, otherOwners, otherEndpoints,
    otherAutomatic, otherHistory, otherMemory, otherSteps, otherMenus, otherReadout,
    rightTrace, otherViews, otherHistoryAlignment, otherOrigin⟩
  change (⟨Γ, O, program, lift⟩ : ResidualProgram setup.program) = otherResidual at residual
  subst otherResidual
  have sameEmbedding : embedding = otherEmbedding := by simpa using embeddings
  have sameSource : source = otherSource := by
    apply ProtocolState.entry_injective program
    apply sourceReplaySuffixInjective setup origin
    exact point
  subst otherEmbedding
  subst otherSource
  dsimp only [RecoverySourceCheckpoint.commitInstructionWord]
  rw [masks]

/- The already selected after-witness reads the actual retired snapshot, not
an alternative closure witness. Its archived origin carries the decoder word
of the original drain and a literal path into the selected history. -/
private theorem sourceReplayDirtySelectedOrigin
    (state settled : PhaseRuntimeState (serviceGraph setup .concurrent))
    (prior : RecoverySourceWitness setup .concurrent implementation.plan state)
    (selected : RecoverySourceWitness setup .concurrent implementation.plan settled)
    (fuel : Nat)
    (retained : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, prior.checkpoint.trace⟩ ⟨_, selected.checkpoint.trace⟩)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (remaining : List (RuntimePhase (serviceGraph setup .concurrent)))
    (installed : state.phases = phase :: remaining)
    (raw : RecoveryState (serviceGraph setup .concurrent))
    (normalized : settled = ({ state with current := raw } : PhaseRuntimeState
      (serviceGraph setup .concurrent)).normalize)
    (finished : phase.Finished (phase.drain raw))
    (kind : phase.kind = .commitment)
    (missed : (((phase.drain raw).excluded \ state.entry.excluded) ∩
      phase.owners).Nonempty) :
    ∃ (closed : setup.commitRecoveryProtocol.History) (steps later : Nat),
      setup.commitRecoveryProtocol.ReachesWithin steps
        ⟨_, prior.checkpoint.trace⟩ closed ∧
      setup.recoveryJointRecall closed.trace =
        (prior.checkpoint.commitInstructionWord (phase.drain raw).native).reverse ++
          setup.recoveryJointRecall prior.checkpoint.trace ∧
      setup.commitRecoveryProtocol.ReachesWithin later closed
        ⟨_, selected.checkpoint.trace⟩ := by
  let index := state.retired.length
  let record : RetiredCommitAttempt (serviceGraph setup .concurrent) :=
    ⟨⟨phase.low, state.generation⟩, (phase.drain raw).native⟩
  have recordPrefix : state.retired ++ [record] <+: settled.retired := by
    rw [normalized]
    exact sourceReplayDirtyRecordRetained setup state phase remaining installed raw
      finished kind missed
  have inside : index < settled.retired.length := by
    have size := recordPrefix.length_le
    simp only [List.length_append, List.length_singleton] at size
    dsimp only [index]
    omega
  have recordAt : settled.retired[index] = record := by
    have taken := List.prefix_iff_eq_take.mp recordPrefix
    have indexed := congrArg (fun records : List
      (RetiredCommitAttempt (serviceGraph setup .concurrent)) => records[index]?) taken
    have selectedOption : settled.retired[index]? = some record := by
      simpa [index, record] using indexed.symm
    exact Option.some.inj ((List.getElem?_eq_getElem inside).symm.trans selectedOption)
  obtain ⟨old, checkpoint, _recall, _origins, _archive, oldAttempt, _retained,
    _cut, _agrees, _positive, closed, steps, later, path, word, onward⟩ :=
    selected.origins.get index inside
  have oldAttempt' : old.attempt = record.attempt :=
    oldAttempt.trans (congrArg RetiredCommitAttempt.attempt recordAt)
  have recordImage : settled.retired[index].state = (phase.drain raw).native := by
    simpa only [record] using congrArg RetiredCommitAttempt.state recordAt
  have attemptEq : state.attempt = record.attempt := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons,
      Option.map_some, Option.getD_some, record]
  have sameAttempt : old.attempt = state.attempt := oldAttempt'.trans attemptEq.symm
  have sameControl : setup.commitRecoveryControl (some (CommitRecoveryState.atPoint
      (checkpoint.residual.lift
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
        old.entry.excluded old.generation)) =
      setup.commitRecoveryControl (some (CommitRecoveryState.atPoint
        (prior.checkpoint.residual.lift
          (ProtocolState.entry prior.checkpoint.residual.tail prior.checkpoint.source))
          state.entry.excluded state.generation)) := by
    have generation := congrArg CommitAttemptId.generation sameAttempt
    have phase := congrArg CommitAttemptId.phase sameAttempt
    simp only [Setup.commitRecoveryControl, Option.elim_some, CommitRecoveryState.control,
      CommitRecoveryState.atPoint, checkpoint.saved_position,
      prior.checkpoint.saved_position]
    change old.generation = state.generation at generation
    rw [generation, phase]
  have sameHistory := setup.commitRecovery_ancestor_eq_of_control_eq
    (path.trans onward) retained sameControl
  have oldWord : setup.recoveryJointRecall closed.trace =
      (checkpoint.commitInstructionWord (phase.drain raw).native).reverse ++
        setup.recoveryJointRecall checkpoint.trace := by
    exact word.trans (congrArg (fun image =>
      (checkpoint.commitInstructionWord image).reverse ++
        setup.recoveryJointRecall checkpoint.trace) recordImage)
  have sameWord := sourceReplayCommitInstructionWordEq setup checkpoint
    prior.checkpoint (phase.drain raw).native
      (congrArg CommitAttemptId.phase sameAttempt) sameHistory
  have oldRecall := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    setup.recoveryJointRecall history.trace) sameHistory
  refine ⟨closed, steps, later, ?_, ?_, onward⟩
  · rw [← sameHistory]
    exact path
  · calc
      setup.recoveryJointRecall closed.trace =
          (checkpoint.commitInstructionWord (phase.drain raw).native).reverse ++
            setup.recoveryJointRecall checkpoint.trace := oldWord
      _ = (prior.checkpoint.commitInstructionWord (phase.drain raw).native).reverse ++
            setup.recoveryJointRecall prior.checkpoint.trace := by rw [sameWord, oldRecall]

/- The decoded completed source context is read against the actual selected
saved store after a clean close, including automatic phase advances. -/
omit [Fintype Player] in
private theorem sourceReplayCleanSavedAgreement
    {Γ : SourceCtx Player L}
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (source : State L Γ)
    (state : PhaseRuntimeState (serviceGraph setup .concurrent))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (remaining : List (RuntimePhase (serviceGraph setup .concurrent)))
    (installed : state.phases = phase :: remaining)
    (raw : RecoveryState (serviceGraph setup .concurrent))
    (finished : phase.Finished (phase.drain raw))
    (clean : ¬ (phase.kind = .commitment ∧
      (((phase.drain raw).excluded \ state.entry.excluded) ∩ phase.owners).Nonempty))
    (agrees : refs.Agrees source (phase.drain raw).native.config.store) :
    refs.Agrees source
      (({ state with current := raw } : PhaseRuntimeState
        (serviceGraph setup .concurrent)).normalize.entry.native.config.store) := by
  have settled : ({ state with current := raw } : PhaseRuntimeState
      (serviceGraph setup .concurrent)).normalize =
      PhaseRuntimeState.settle remaining state.generation (phase.drain raw)
        (phase.drain raw) state.retired := by
    change PhaseRuntimeState.settle state.phases state.generation state.entry raw
      state.retired = _
    rw [installed, PhaseRuntimeState.settle_clean phase remaining state.generation
      state.entry raw state.retired finished clean]
  rw [settled]
  intro name cell selected
  exact (refs.get selected).get?_preserved _ _
    (sourceReplaySettleSavedStore setup remaining state.generation
      (phase.drain raw) state.retired) _ (agrees selected)

/- Two completed attempts over the same source entry and exclusion mask read
the same entire binding word when their final typed cells agree with the
selected physical saved store. This includes accepted failures and omitted
rows, not just successful payload values. -/
omit [Fintype Player] in
private theorem sourceReplayCleanAttemptWord
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (store : Store (graphLayout setup.program))
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (actualFinished decodedFinished : SourceProgram.Config Player L Δ)
    (actualAfter decodedAfter : Finset Player)
    (actual : block.Attempt entry excluded actualFinished actualAfter)
    (decoded : block.Attempt entry excluded decodedFinished decodedAfter)
    (actualMask : actualAfter = excluded)
    (decodedMask : decodedAfter = excluded)
    (actualReads : (commitBlockRefs setup.program block suffix embedding refs).Agrees
      actualFinished.state store)
    (decodedReads : (commitBlockRefs setup.program block suffix embedding refs).Agrees
      decodedFinished.state store) :
    actual.joints = decoded.joints := by
  have actualWord := phaseProposalBindingWord_of_ordinary_attempt setup.program
    block suffix embedding refs store entry entry excluded actualFinished actualAfter
      actual actualMask actualReads
  have decodedWord := phaseProposalBindingWord_of_ordinary_attempt setup.program
    block suffix embedding refs store entry entry excluded decodedFinished decodedAfter
      decoded decodedMask decodedReads
  exact actualWord.symm.trans decodedWord

/- A real suffix-entry prefix retains its complete typed context in the
selected saved store, independently of an already constructed checkpoint at
that prefix. This is the source side of the clean close's shared-store join. -/
omit [Fintype Player] in
theorem sourceReplaySuffixSavedAgreement
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O)
    (lift : ProtocolState program → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program program lift)
    (source : SourceProgram.Config Player L Γ) (unique : (Γ.map Prod.fst).Nodup)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (aligned : CompiledReadoutSuffix setup.program program refs embedding)
    (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (point : first.point = lift (ProtocolState.entry program source))
    (saved : first.saved = lift (ProtocolState.entry program source))
    {lastState : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (last : RecoverySourceCheckpoint setup .concurrent lastState)
    (retained : TracePrefix prior last.trace) :
    refs.Agrees source.state lastState.entry.native.config.store := by
  classical
  intro name kind selected
  let terminalCell := cast (congrArg (fun context => HasVar context name kind)
    aligned.contextEq) (terminalRef program selected)
  have transport {first second : SourceCtx Player L} (same : first = second)
      (environment : ContextRefs (graphLayout setup.program) first)
      (cell : HasVar first name kind) :
      (cast (congrArg (ContextRefs (graphLayout setup.program)) same) environment).get
        (cast (congrArg (fun context => HasVar context name kind) same) cell) =
          environment.get cell := by
    cases same
    rfl
  have reference : (terminalRefs setup.program).get terminalCell = refs.get selected := by
    rw [← aligned.refsEq]
    exact (transport aligned.contextEq _ _).trans
      (terminalRefsWith_get_terminalRef program refs embedding.ref selected)
  have readback : ProtocolState.cell? setup.program first.point name kind =
      some (source.state.get selected) := by
    rw [point, origin.cell?_lift, ProtocolState.cell?_entry]
    exact SourceProgram.State.cell?_eq_of_hasVar selected unique source.state
  have actual := source_saved_cell_readback setup program lift origin source unique first
    prior point saved last retained terminalCell (source.state.get selected) readback
  rw [reference] at actual
  exact actual

/- A clean physical close determines the first completed interval of the
already selected source history. Both attempts are read at the selected saved
store, so no independently chosen closing history is substituted. -/
private theorem sourceReplayCleanSelectedOrigin
    (state settled : PhaseRuntimeState (serviceGraph setup .concurrent))
    (prior : RecoverySourceWitness setup .concurrent implementation.plan state)
    (selected : RecoverySourceWitness setup .concurrent implementation.plan settled)
    (fuel : Nat)
    (retained : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, prior.checkpoint.trace⟩ ⟨_, selected.checkpoint.trace⟩)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (remaining : List (RuntimePhase (serviceGraph setup .concurrent)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .commitment)
    (maximal : implementation.plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (normalized : settled = state.normalize)
    (changed : settled.attempt ≠ state.attempt)
    (finished : phase.Finished (phase.drain state.current))
    (clean : ¬ (((phase.drain state.current).excluded \ state.entry.excluded) ∩
      phase.owners).Nonempty) :
    ∃ (closed : setup.commitRecoveryProtocol.History) (steps later : Nat),
      setup.commitRecoveryProtocol.ReachesWithin steps
        ⟨_, prior.checkpoint.trace⟩ closed ∧
      setup.recoveryJointRecall closed.trace =
        (prior.checkpoint.commitInstructionWord (phase.drain state.current).native).reverse ++
          setup.recoveryJointRecall prior.checkpoint.trace ∧
      setup.commitRecoveryProtocol.ReachesWithin later closed
        ⟨_, selected.checkpoint.trace⟩ := by
  classical
  let start := CommitRecoveryState.atPoint
    (prior.checkpoint.residual.lift
      (ProtocolState.entry prior.checkpoint.residual.tail prior.checkpoint.source))
    state.entry.excluded state.generation
  let last := CommitRecoveryState.atPoint
    (selected.checkpoint.residual.lift
      (ProtocolState.entry selected.checkpoint.residual.tail selected.checkpoint.source))
    settled.entry.excluded settled.generation
  have geometry := source_checkpoint_binding_interval setup implementation prior maximal phase
    remaining installed kind
  have normalizedChanged : state.normalize.attempt ≠ state.attempt := by
    rw [← normalized]
    exact changed
  have masks := clean_exit_excluded setup implementation state prior phase remaining installed
    clean normalizedChanged
  have lastMask : settled.entry.excluded = state.entry.excluded := by
    rw [normalized]
    exact masks.2
  have namespaces : Function.Injective
      (fun address : CommitAttemptId => (address.generation, address.phase)) := by
    rintro ⟨firstPhase, firstGeneration⟩ ⟨lastPhase, lastGeneration⟩ equal
    rcases Prod.mk.inj equal with ⟨rfl, rfl⟩
    rfl
  have exited : (⟨some last, selected.checkpoint.trace⟩ :
      setup.commitRecoveryProtocol.History).state.map (fun current =>
        current.publicAddress.2.2) ≠ some start.publicAddress.2.2 := by
    intro equal
    have same := Option.some.inj equal
    change (settled.generation, instructionCount setup.program -
        ProtocolState.remaining setup.program
          (selected.checkpoint.residual.lift (ProtocolState.entry
            selected.checkpoint.residual.tail selected.checkpoint.source))) =
      (state.generation, instructionCount setup.program -
        ProtocolState.remaining setup.program
          (prior.checkpoint.residual.lift (ProtocolState.entry
            prior.checkpoint.residual.tail prior.checkpoint.source))) at same
    rw [selected.checkpoint.saved_position, prior.checkpoint.saved_position] at same
    exact changed (namespaces same)
  have firstRank : instructionCount setup.program -
      ProtocolState.remaining setup.program start.point = phase.low := geometry.2.1
  have lastRank : instructionCount setup.program -
      ProtocolState.commitEnd setup.program start.saved = phase.high := geometry.2.2
  obtain ⟨rowBefore, rowAfter, row, joint, legal, moved, firstKept, lastKept,
      _rowSaved, _rowGeneration, rowDepth, _rowRank⟩ :=
    source_commit_rank_before_exit setup (phase.high - phase.low - 1) start
      prior.checkpoint.trace geometry.1 (phase.high - 1)
      (by rw [firstRank]; have := phase.nonempty; omega)
      (by rw [lastRank]; have := phase.nonempty; omega)
      ⟨some last, selected.checkpoint.trace⟩ fuel retained (Or.inl exited)
  let closed := row.extend joint legal moved
  have firstClosed : TracePrefix prior.checkpoint.trace closed :=
    firstKept.extend joint legal moved
  have closedDepth : closed.length = prior.checkpoint.trace.length +
      (phase.high - phase.low) := by
    dsimp only [closed]
    simp only [Trace.length, rowDepth]
    have := phase.nonempty
    omega
  have grows : ∀ {firstState lastState : setup.commitRecoveryProtocol.State}
      (firstTrace : setup.commitRecoveryProtocol.Trace firstState)
      (lastTrace : setup.commitRecoveryProtocol.Trace lastState),
      TracePrefix firstTrace lastTrace →
        (setup.commitRecoveryPublic firstState).1 ⊆
          (setup.commitRecoveryPublic lastState).1 := by
    intro firstState lastState firstTrace lastTrace kept
    induction kept with
    | refl => exact Finset.Subset.refl _
    | extend previous actions available reached ih =>
        exact ih.trans (setup.commitRecovery_step_excluded_subset actions available reached)
  have closedMask : rowAfter.excluded = state.entry.excluded := by
    have lower := grows prior.checkpoint.trace closed firstClosed
    have upper := grows closed selected.checkpoint.trace lastKept
    change state.entry.excluded ⊆ rowAfter.excluded at lower
    change rowAfter.excluded ⊆ settled.entry.excluded at upper
    rw [lastMask] at upper
    exact Finset.Subset.antisymm upper lower
  let initializer := setup.initialConfig setup.initialLaw.support_nonempty.choose
  obtain ⟨actualLast, joints, addresses, lastEq, actualPath, actualLength, actualWord,
      _actualAddresses⟩ := source_instruction_window setup initializer start
        prior.checkpoint.trace closed firstClosed
  have endpoint : actualLast = rowAfter := (Option.some.inj lastEq).symm
  subst actualLast
  have segmentGeometry := prior.checkpoint.commit_phase_geometry phase remaining installed kind
    prior.receipts.exclusion.frontier (maximal.suffix prior.suffix)
  rcases prior with ⟨checkpoint, _aligned, _chronology, _origins, _native, binding,
    receipts, stored, _remembered, _order, _suffix, _archives, _exclusions, _failures⟩
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding,
    beforeRefs, compiled, aligned, agree, guards, failures, unique, ranks, actors, commits,
    owners, endpoints, automatic, history, memory, steps, menus, readout, sourceTrace,
    views, historyAlignment, origin⟩
  dsimp only at segmentGeometry
  dsimp only [RecoverySourceCheckpoint.commitInstructionWord]
  generalize _decomposition : commitPhase program = segment at segmentGeometry ⊢
  rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
  subst program
  dsimp only at segmentGeometry
  have size : block.length = phase.high - phase.low := segmentGeometry.1
  have positive : 0 < block.length := by
    rw [size]
    exact Nat.sub_pos_of_lt phase.nonempty
  have sourceCommit : ProtocolState.atCommit setup.program start.point = true := geometry.1
  have sourceSaved : ProtocolState.atCommit setup.program start.saved = true := sourceCommit
  have sourceEnd : ProtocolState.commitEnd setup.program start.saved ≤ instructionCount suffix := by
    change ProtocolState.commitEnd setup.program
      (lift (ProtocolState.entry (block.prepend suffix) source)) ≤ _
    rw [endpoints, block.commitEnd_entry_prepend suffix boundary]
  have length : joints.length = block.length := by
    rw [size]
    omega
  obtain ⟨actualFinal, actualExcluded, actualAttempt, attemptWord, monotone, actualClosed⟩ :=
    SourceProgram.CommitPrefix.attempt_of_instructions initializer block suffix lift origin source
      start rowAfter joints addresses rfl sourceSaved sourceEnd positive actualPath length
  have actualMask : actualExcluded = state.entry.excluded := by
    have observed := congrArg CommitRecoveryState.excluded actualClosed
    rw [CommitRecoveryState.close_excluded] at observed
    exact observed.symm.trans closedMask
  have noFailure : actualAttempt.failedOwners = ∅ := by
    rw [← actualAttempt.newly_excluded, actualMask]
    change state.entry.excluded \ state.entry.excluded = ∅
    exact Finset.sdiff_self _
  have atPoint : rowAfter = CommitRecoveryState.atPoint
      (lift (block.liftPoint suffix (ProtocolState.entry suffix actualFinal)))
      actualExcluded state.generation := by
    exact actualClosed.trans (actualAttempt.close_clean_lift setup.program suffix boundary
      positive state.generation lift ranks commits endpoints noFailure)
  obtain ⟨tailEmbedding, _tailBefore, _tailCompiled, tailAligned, _tailViews⟩ :=
    actualAttempt.compiledTail setup.program suffix refs registry embedding beforeRefs
      state.attempt.phase compiled aligned lift views
  have actualReads : (commitBlockRefs setup.program block suffix embedding refs).Agrees
      actualFinal.state settled.entry.native.config.store := by
    refine sourceReplaySuffixSavedAgreement setup suffix
      (fun point => lift (block.liftPoint suffix point))
      (origin.compose (block.protocolSuffix suffix)) actualFinal (block.names_nodup unique)
      (commitBlockRefs setup.program block suffix embedding refs) tailEmbedding tailAligned
      rowAfter closed ?_ ?_ selected.checkpoint lastKept
    · exact congrArg CommitRecoveryState.point atPoint
    · exact congrArg CommitRecoveryState.saved atPoint
  let image := phase.drain state.current
  let decoded := decodeCommitAttempt setup.program .concurrent block suffix embedding image.native
    source state.entry.excluded
  have present : phase ∈ state.phases.head? := by
    simp only [installed, List.head?_cons, Option.mem_some_iff]
  have within := receipts.exclusion.frontier.positioned
  rw [installed] at within
  have chain := maximal.suffix _suffix
  rw [installed] at chain
  have exactPhase := compiledCommitPhase_eq_of_maximal setup.program .concurrent block suffix
    embedding compiled positive boundary phase remaining
      (by simpa only [installed] using receipts.exclusion.frontier.adjacent)
      (by simpa only [installed] using receipts.exclusion.frontier.last)
      chain
      (by simp only [PhaseRuntimeState.attempt, installed, List.head?_cons,
        Option.map_some, Option.getD_some])
  subst phase
  let phase := compiledCommitPhase setup.program .concurrent block suffix embedding
    compiled positive
  have decodedPhysical : decoded.2.1 = image.excluded :=
    decodeCommitAttempt_excluded_eq_physical setup.program .concurrent block suffix embedding
      compiled positive image source state.entry.excluded
      ((receipts.exclusion.installed phase present).phase_drain phase)
      (phase.drain_within state.current within.2) finished
  have entryReads : refs.Agrees source.state image.native.config.store := by
    intro name cell selectedCell
    exact (refs.get selectedCell).get?_preserved _ _
      (fun field value recorded => phase.drain_keepsStore state.current field value
        (stored field value recorded)) _ (agree selectedCell)
  have decodedReads : (commitBlockRefs setup.program block suffix embedding refs).Agrees
      decoded.1.state settled.entry.native.config.store := by
    have nativeReads : (commitBlockRefs setup.program block suffix embedding refs).Agrees
        decoded.1.state image.native.config.store := by
      apply decodeCommitAttempt_state_agrees setup.program .concurrent block suffix embedding
        refs image.native source state.entry.excluded state.attempt.phase compiled.rankEq
        (phase.drain_bindingInvariant state.current binding.active)
        ((receipts.ordered phase present kind).congr (phase.drain_tables state.current).1)
        entryReads
      intro index inside
      exact finished ((compiledCommitPhase_mem_iff setup.program .concurrent block suffix
        embedding compiled positive _).mpr ⟨index, inside, rfl⟩)
    rw [normalized]
    intro name cell selectedCell
    exact sourceReplayCleanSavedAgreement setup
      (commitBlockRefs setup.program block suffix embedding refs) decoded.1.state state phase
      remaining installed state.current finished (fun failed => clean failed.2) nativeReads
        selectedCell
  have decodedMask : decoded.2.1 = state.entry.excluded := decodedPhysical.trans masks.1
  have sameWord := sourceReplayCleanAttemptWord setup block suffix embedding refs
    settled.entry.native.config.store source state.entry.excluded actualFinal decoded.1
      actualExcluded decoded.2.1 actualAttempt decoded.2.2 actualMask decodedMask
      actualReads decodedReads
  refine ⟨⟨some rowAfter, closed⟩, closed.length - sourceTrace.length,
    selected.checkpoint.trace.length - closed.length, firstClosed.reachesWithin, ?_,
    lastKept.reachesWithin⟩
  change setup.recoveryJointRecall closed = decoded.2.2.joints.reverse ++
    setup.recoveryJointRecall sourceTrace
  rw [actualWord, ← attemptWord, sameWord]

/- Both ends of one actual completed source visit are transported into the
same target chronology. Its literal target interval gives an actual attempt;
the source and target private instruction words need not agree. -/
omit [Fintype Player] in
theorem sourceReplayCompletedInterval
    (who : Player) (left right : setup.proposalRecoveryProtocol.History)
    (same : setup.proposalRecoveryModel.infoOf who left.trace =
      setup.proposalRecoveryModel.infoOf who right.trace)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (initializer : SourceProgram.Config Player L setup.context)
    (block : SourceProgram.CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P)
    (lift : ProtocolState (block.prepend suffix) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (block.prepend suffix) lift)
    (entry : SourceProgram.Config Player L Γ)
    (first last : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some first))
    (trace : setup.proposalRecoveryProtocol.Trace (some last))
    (interval : TracePrefix prior trace)
    (retained : TracePrefix trace left.trace)
    (point : first.point = lift (ProtocolState.entry (block.prepend suffix) entry))
    (saved : ProtocolState.atCommit setup.program first.saved = true)
    (endpoint : ProtocolState.commitEnd setup.program first.saved ≤ instructionCount suffix)
    (positive : 0 < block.length)
    (depth : trace.length = prior.length + block.length) :
    ∃ (targetFirst targetLast : CommitRecoveryState setup.program)
      (targetPrior : setup.proposalRecoveryProtocol.Trace (some targetFirst))
      (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetLast))
      (targetEntry : SourceProgram.Config Player L Γ)
      (finished : SourceProgram.Config Player L Δ) (excluded : Finset Player)
      (attempt : block.Attempt targetEntry targetFirst.excluded finished excluded)
      (addresses : List (Option Nat × (Finset Player × Nat × Nat))),
      TracePrefix targetPrior targetTrace ∧ TracePrefix targetTrace right.trace ∧
      targetPrior.length = prior.length ∧ targetTrace.length = trace.length ∧
      setup.proposalRecoveryModel.infoOf who prior =
        setup.proposalRecoveryModel.infoOf who targetPrior ∧
      setup.proposalRecoveryModel.infoOf who trace =
        setup.proposalRecoveryModel.infoOf who targetTrace ∧
      targetFirst.point = lift (ProtocolState.entry (block.prepend suffix) targetEntry) ∧
      ProtocolState.atCommit setup.program targetFirst.saved = true ∧
      ProtocolState.commitEnd setup.program targetFirst.saved ≤ instructionCount suffix ∧
      first.excluded = targetFirst.excluded ∧
      first.generation = targetFirst.generation ∧
      CommitRecoveryState.InstructionPath setup.program initializer attempt.joints addresses
        targetFirst targetLast ∧
      setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace targetTrace) =
        attempt.joints.reverse ++
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace targetPrior) ∧
      setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace targetTrace) =
        setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace targetPrior) ++ addresses ∧
      ∃ monotone : targetFirst.excluded ⊆ excluded,
        targetLast = (targetFirst.install
          (lift (block.liftPoint suffix (ProtocolState.entry suffix finished)), excluded)
          monotone).close := by
  obtain ⟨⟨lastState, targetLastTrace⟩, targetLastKept, lastDepth, lastInfo⟩ :=
    source_information_prefix setup who left right ⟨some last, trace⟩ same retained
  have lastMetadata := source_information_metadata setup who
    ⟨some last, trace⟩ ⟨lastState, targetLastTrace⟩ lastInfo
  cases lastState with
  | none => exact lastMetadata.elim
  | some targetLast =>
      obtain ⟨⟨firstState, targetPrior⟩, targetInterval, firstDepth, firstInfo⟩ :=
        source_information_prefix setup who ⟨some last, trace⟩
          ⟨some targetLast, targetLastTrace⟩ ⟨some first, prior⟩ lastInfo interval
      have firstMetadata := source_information_metadata setup who
        ⟨some first, prior⟩ ⟨firstState, targetPrior⟩ firstInfo
      cases firstState with
      | none => exact firstMetadata.elim
      | some targetFirst =>
          obtain ⟨targetEntry, targetPoint, _entryMetadata⟩ :=
            config_of_lifted_entry_metadata setup (block.prepend suffix) lift origin entry
              targetFirst.point (by rw [← point]; exact firstMetadata.1)
          have controls := ProtocolState.MetadataEq.controls setup.program first.saved
            targetFirst.saved firstMetadata.2.1
          have targetSaved : ProtocolState.atCommit setup.program targetFirst.saved = true := by
            rw [← controls.2.1]
            exact saved
          have targetEndpoint : ProtocolState.commitEnd setup.program targetFirst.saved ≤
              instructionCount suffix := by
            rw [← controls.2.2.1]
            exact endpoint
          have targetDepth : targetLastTrace.length =
              targetPrior.length + block.length := by
            rw [lastDepth, firstDepth, depth]
          obtain ⟨finished, excluded, attempt, addresses, path, word, addressWord,
              monotone, closed⟩ := source_attempt_of_literal_window setup initializer block
                suffix lift origin targetEntry targetFirst targetLast targetPrior targetLastTrace
                targetInterval targetPoint targetSaved targetEndpoint positive targetDepth
          exact ⟨targetFirst, targetLast, targetPrior, targetLastTrace, targetEntry,
            finished, excluded, attempt, addresses, targetInterval, targetLastKept,
            firstDepth, lastDepth, firstInfo, lastInfo, targetPoint, targetSaved,
            targetEndpoint, firstMetadata.2.2.1, firstMetadata.2.2.2.2, path,
            word, addressWord, monotone, closed⟩

/- A target instruction row identifies the original row at the same literal
depth, while allowing their foreign choices and private words to differ. -/
omit [Fintype Player] in
private theorem sourceReplayPairedRow
    (who : Player)
    (sourceFinal targetFinal : setup.proposalRecoveryProtocol.History)
    (same : setup.proposalRecoveryModel.infoOf who sourceFinal.trace =
      setup.proposalRecoveryModel.infoOf who targetFinal.trace)
    (targetBefore targetAfter : CommitRecoveryState setup.program)
    (targetPrior : setup.proposalRecoveryProtocol.Trace (some targetBefore))
    (targetJoint : Player → Option (ProposalRecoveryMove Player L))
    (targetLegal : setup.proposalRecoveryProtocol.Legal (some targetBefore) targetJoint)
    (targetMoved : some targetAfter ∈
      (setup.proposalRecoveryProtocol.step (some targetBefore)
        ⟨targetJoint, targetLegal⟩).support)
    (targetKept : TracePrefix
      (targetPrior.extend targetJoint targetLegal targetMoved) targetFinal.trace) :
    ∃ (sourceBefore sourceAfter : CommitRecoveryState setup.program)
      (sourcePrior : setup.proposalRecoveryProtocol.Trace (some sourceBefore))
      (sourceJoint : Player → Option (ProposalRecoveryMove Player L))
      (sourceLegal : setup.proposalRecoveryProtocol.Legal (some sourceBefore) sourceJoint)
      (sourceMoved : some sourceAfter ∈
        (setup.proposalRecoveryProtocol.step (some sourceBefore)
          ⟨sourceJoint, sourceLegal⟩).support),
      TracePrefix (sourcePrior.extend sourceJoint sourceLegal sourceMoved) sourceFinal.trace ∧
      sourcePrior.length = targetPrior.length ∧
      setup.proposalRecoveryModel.infoOf who sourcePrior =
        setup.proposalRecoveryModel.infoOf who targetPrior ∧
      setup.proposalRecoveryModel.infoOf who
          (sourcePrior.extend sourceJoint sourceLegal sourceMoved) =
        setup.proposalRecoveryModel.infoOf who
          (targetPrior.extend targetJoint targetLegal targetMoved) ∧
      sourceJoint who = targetJoint who := by
  obtain ⟨sourceBeforeState, sourceAfterState, sourcePrior, sourceJoint,
    sourceLegal, sourceMoved, sourceKept, beforeInfo, afterInfo, own⟩ :=
    source_information_row setup who targetPrior targetJoint targetLegal targetMoved
      targetFinal.trace sourceFinal.trace targetKept same.symm
  have beforeMetadata := source_information_metadata setup who
    ⟨some targetBefore, targetPrior⟩ ⟨sourceBeforeState, sourcePrior⟩ beforeInfo
  cases sourceBeforeState with
  | none => exact beforeMetadata.elim
  | some sourceBefore =>
      have afterMetadata := source_information_metadata setup who
        ⟨some targetAfter, targetPrior.extend targetJoint targetLegal targetMoved⟩
        ⟨sourceAfterState, sourcePrior.extend sourceJoint sourceLegal sourceMoved⟩ afterInfo
      cases sourceAfterState with
      | none => exact afterMetadata.elim
      | some sourceAfter =>
          have depths := congrArg (fun information => information.1.2.length) beforeInfo
          change (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who
            targetPrior).1.2.length =
              (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who
                sourcePrior).1.2.length at depths
          rw [InfoSignals.withOwnPlayRecall_infoOf,
            InfoSignals.withOwnPlayRecall_infoOf] at depths
          have length : sourcePrior.length = targetPrior.length := by
            simpa only [setup.source_signal_depth] using depths.symm
          exact ⟨sourceBefore, sourceAfter, sourcePrior, sourceJoint, sourceLegal,
            sourceMoved, sourceKept, length, beforeInfo.symm, afterInfo.symm, own.symm⟩

/- The paired original row is decoded against the very same drained physical
snapshot as the selected completed interval. The target and original private
joint words remain independent; equality of enriched focal information pairs
their actual rows at one literal depth. -/
omit [Fintype Player] in
theorem sourceReplayPhysicalPairedRow
    {state : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (checkpoint : RecoverySourceCheckpoint setup .concurrent state)
    (native : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (closed : setup.commitRecoveryProtocol.History) {fuel : Nat}
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, checkpoint.trace⟩ closed)
    (instructions : setup.recoveryJointRecall closed.trace =
      (checkpoint.commitInstructionWord native).reverse ++
        setup.recoveryJointRecall checkpoint.trace)
    (who : Player)
    (sourceFinal targetFinal : setup.proposalRecoveryProtocol.History)
    (closedKept : TracePrefix closed.trace
      (setup.proposalRecoveryEraseTrace sourceFinal.trace))
    (same : setup.proposalRecoveryModel.infoOf who sourceFinal.trace =
      setup.proposalRecoveryModel.infoOf who targetFinal.trace)
    (sourceGood : setup.proposalRecoveryForeignGood who sourceFinal)
    (targetGood : setup.proposalRecoveryForeignGood who targetFinal)
    (targetBefore targetAfter : CommitRecoveryState setup.program)
    (targetPrior : setup.proposalRecoveryProtocol.Trace (some targetBefore))
    (targetJoint : Player → Option (ProposalRecoveryMove Player L))
    (targetLegal : setup.proposalRecoveryProtocol.Legal (some targetBefore) targetJoint)
    (targetMoved : some targetAfter ∈
      (setup.proposalRecoveryProtocol.step (some targetBefore)
        ⟨targetJoint, targetLegal⟩).support)
    (targetKept : TracePrefix
      (targetPrior.extend targetJoint targetLegal targetMoved) targetFinal.trace)
    (targetEvent : (serviceGraph setup .concurrent).EventId)
    (targetOwner : Player) (targetPayload : L.Ty)
    (targetBinding : (serviceGraph setup .concurrent).outputLayout targetEvent =
      .binding targetOwner targetPayload)
    (targetPosition : targetEvent.val = instructionCount setup.program -
      ProtocolState.remaining setup.program targetBefore.point)
    (lower : checkpoint.trace.length ≤ targetPrior.length)
    (upper : targetPrior.length < closed.trace.length) :
    ∃ (sourceBefore sourceAfter : CommitRecoveryState setup.program)
      (sourcePrior : setup.proposalRecoveryProtocol.Trace (some sourceBefore))
      (sourceJoint : Player → Option (ProposalRecoveryMove Player L))
      (sourceLegal : setup.proposalRecoveryProtocol.Legal (some sourceBefore) sourceJoint)
      (sourceMoved : some sourceAfter ∈
        (setup.proposalRecoveryProtocol.step (some sourceBefore)
          ⟨sourceJoint, sourceLegal⟩).support),
      TracePrefix (sourcePrior.extend sourceJoint sourceLegal sourceMoved)
        sourceFinal.trace ∧
      sourcePrior.length = targetPrior.length ∧
      setup.proposalRecoveryModel.infoOf who sourcePrior =
        setup.proposalRecoveryModel.infoOf who targetPrior ∧
      setup.proposalRecoveryModel.infoOf who
          (sourcePrior.extend sourceJoint sourceLegal sourceMoved) =
        setup.proposalRecoveryModel.infoOf who
          (targetPrior.extend targetJoint targetLegal targetMoved) ∧
      sourceJoint who = targetJoint who ∧
      sourceBefore.saved = checkpoint.residual.lift
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source) ∧
      sourceBefore.generation = state.generation ∧
      (targetOwner ∉ sourceBefore.excluded →
        phaseRecoveryBindingData setup .concurrent targetEvent targetOwner targetPayload
            targetBinding ((sourceJoint targetOwner).map (·.semantic)) =
          ((native.accepted (.inr targetEvent)).elim PublicationResult.failure
            (fun handle => native.bindingResult handle targetPayload),
            (native.accepted (.inr targetEvent)).isNone)) ∧
      (targetOwner ∉ sourceBefore.excluded →
        phaseRecoveryBindingData setup .concurrent targetEvent targetOwner targetPayload
            targetBinding ((targetJoint targetOwner).map (·.semantic)) =
          ((if (native.accepted (.inr targetEvent)).isNone then .failure else
            match (native.accepted (.inr targetEvent)).elim PublicationResult.failure
                (fun handle => native.bindingResult handle targetPayload) with
            | .failure => .failure
            | .success _ =>
                (sourceBindingAt setup state.attempt targetEvent targetOwner targetPayload
                  targetBinding targetFinal.trace).elim .failure .success),
            (native.accepted (.inr targetEvent)).isNone)) ∧
      (targetOwner ∉ sourceBefore.excluded →
        ∀ old : L.Val targetPayload,
          phaseRecoveryBindingData setup .concurrent targetEvent targetOwner targetPayload
              targetBinding ((sourceJoint targetOwner).map (·.semantic)) =
                (.success old, false) →
          ∃ value : L.Val targetPayload,
            sourceBindingAt setup state.attempt targetEvent targetOwner targetPayload
              targetBinding targetFinal.trace = some value ∧
            phaseRecoveryBindingData setup .concurrent targetEvent targetOwner targetPayload
              targetBinding ((targetJoint targetOwner).map (·.semantic)) =
                (.success value, false)) ∧
      (targetOwner ∉ sourceBefore.excluded →
        phaseRecoveryBindingData setup .concurrent targetEvent targetOwner targetPayload
            targetBinding ((sourceJoint targetOwner).map (·.semantic)) =
              (.failure, false) →
        phaseRecoveryBindingData setup .concurrent targetEvent targetOwner targetPayload
            targetBinding ((targetJoint targetOwner).map (·.semantic)) =
              (.failure, false) ∧
        sourceBindingAt setup state.attempt targetEvent targetOwner targetPayload
          targetBinding targetFinal.trace = none) := by
  obtain ⟨sourceBefore, sourceAfter, sourcePrior, sourceJoint, sourceLegal,
    sourceMoved, sourceKept, sourceLength, beforeInfo, afterInfo, own⟩ :=
    sourceReplayPairedRow setup who sourceFinal targetFinal same targetBefore targetAfter
      targetPrior targetJoint targetLegal targetMoved targetKept
  have sourceLower : checkpoint.trace.length ≤ sourcePrior.length := by
    rw [sourceLength]
    exact lower
  have sourceUpper : sourcePrior.length < closed.trace.length := by
    rw [sourceLength]
    exact upper
  obtain ⟨saved, generation, geometry⟩ := source_decoded_binding_row setup
    checkpoint native closed path instructions sourceFinal closedKept sourceBefore
      sourceAfter sourcePrior sourceJoint sourceLegal sourceMoved sourceKept
        sourceLower sourceUpper
  generalize decomposition : commitPhase checkpoint.residual.tail = segment at geometry
  rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
  dsimp only at geometry
  obtain ⟨event, owner, payload, binding, position, _receiptActive, activeRow⟩ := geometry
  have metadata := source_information_metadata setup who
    ⟨some sourceBefore, sourcePrior⟩ ⟨some targetBefore, targetPrior⟩ beforeInfo
  have controls := ProtocolState.MetadataEq.controls setup.program sourceBefore.point
    targetBefore.point metadata.1
  have targetRank : targetEvent.val = instructionCount setup.program -
      ProtocolState.remaining setup.program sourceBefore.point := by
    rw [controls.1]
    exact targetPosition
  have sameEvent : event = targetEvent := Fin.ext (position.trans targetRank.symm)
  subst event
  obtain ⟨sameOwner, samePayload⟩ :=
    EventField.binding.inj (binding.symm.trans targetBinding)
  subst owner
  subst payload
  refine ⟨sourceBefore, sourceAfter, sourcePrior, sourceJoint, sourceLegal,
    sourceMoved, sourceKept, sourceLength, beforeInfo, afterInfo, own, saved,
    generation, ?_, ?_, ?_, ?_⟩
  · intro active
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, data, _⟩ := activeRow active
    exact data
  · intro active
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, data, _⟩ := activeRow active
    have sourceRowGood := source_good_prefix setup who
      (sourcePrior.extend sourceJoint sourceLegal sourceMoved) sourceFinal.trace
        sourceKept sourceGood
    have targetRowGood := source_good_prefix setup who
      (targetPrior.extend targetJoint targetLegal targetMoved) targetFinal.trace
        targetKept targetGood
    have generationAt : sourceBefore.generation = state.attempt.generation := by
      simpa only [PhaseRuntimeState.attempt] using generation
    have savedAt : instructionCount setup.program -
        ProtocolState.remaining setup.program sourceBefore.saved = state.attempt.phase := by
      rw [saved, checkpoint.saved_position]
    have transported := source_binding_data_transport setup who targetOwner targetEvent
      targetPayload targetBinding sourceBefore sourceAfter targetBefore targetAfter sourcePrior
      targetPrior sourceJoint targetJoint sourceLegal targetLegal sourceMoved targetMoved
      beforeInfo afterInfo own sourceRowGood targetRowGood state.attempt generationAt
      savedAt position active targetFinal targetKept
    dsimp only at transported
    rw [data] at transported
    exact transported
  · intro active old original
    have targetBeforeActive : targetOwner ∉ targetBefore.excluded := by
      rw [← metadata.2.2.1]
      exact active
    have sourceAfterActive : targetOwner ∉ sourceAfter.excluded := by
      intro excluded
      have missing := (source_binding_missing_iff setup sourceBefore sourceAfter
        sourceJoint sourceLegal sourceMoved targetOwner targetEvent targetPayload
          targetBinding position active).mpr excluded
      rw [original] at missing
      cases missing
    have targetAfterActive : targetOwner ∉ targetAfter.excluded := by
      have last := source_information_metadata setup who
        ⟨some sourceAfter, sourcePrior.extend sourceJoint sourceLegal sourceMoved⟩
        ⟨some targetAfter, targetPrior.extend targetJoint targetLegal targetMoved⟩ afterInfo
      rw [← last.2.2.1]
      exact sourceAfterActive
    obtain ⟨value, targetRead⟩ : ∃ value : L.Val targetPayload,
        phaseRecoveryBindingData setup .concurrent targetEvent targetOwner targetPayload
          targetBinding ((targetJoint targetOwner).map (·.semantic)) =
            (.success value, false) := by
      by_cases focal : targetOwner = who
      · refine ⟨old, ?_⟩
        have sameOwn : sourceJoint targetOwner = targetJoint targetOwner := by
          simpa only [focal] using own
        rw [← sameOwn]
        exact original
      · exact source_foreign_binding_success setup who targetOwner focal targetEvent
          targetPayload targetBinding targetBefore targetPrior targetJoint targetLegal
            targetAfter targetMoved targetPosition targetBeforeActive targetAfterActive
              (source_good_prefix setup who
                (targetPrior.extend targetJoint targetLegal targetMoved)
                  targetFinal.trace targetKept targetGood)
    have generationAt : targetBefore.generation = state.attempt.generation := by
      have sourceAt : sourceBefore.generation = state.attempt.generation := by
        simpa only [PhaseRuntimeState.attempt] using generation
      rw [← metadata.2.2.2.2]
      exact sourceAt
    have savedAt : instructionCount setup.program -
        ProtocolState.remaining setup.program targetBefore.saved = state.attempt.phase := by
      rw [← (ProtocolState.MetadataEq.controls setup.program sourceBefore.saved
        targetBefore.saved metadata.2.1).1, saved, checkpoint.saved_position]
    have read := sourceBindingAt_of_origin setup state.attempt targetEvent targetOwner
      targetPayload targetBinding targetBefore targetPrior targetJoint targetLegal
        (some targetAfter) targetMoved generationAt savedAt targetPosition.symm
          (.success value, false) targetRead targetFinal.trace targetKept
    exact ⟨value, read, targetRead⟩
  · intro active original
    have sourceRowGood := source_good_prefix setup who
      (sourcePrior.extend sourceJoint sourceLegal sourceMoved) sourceFinal.trace
        sourceKept sourceGood
    have targetRowGood := source_good_prefix setup who
      (targetPrior.extend targetJoint targetLegal targetMoved) targetFinal.trace
        targetKept targetGood
    have generationAt : sourceBefore.generation = state.attempt.generation := by
      simpa only [PhaseRuntimeState.attempt] using generation
    have savedAt : instructionCount setup.program -
        ProtocolState.remaining setup.program sourceBefore.saved = state.attempt.phase := by
      rw [saved, checkpoint.saved_position]
    have transported := source_binding_data_transport setup who targetOwner targetEvent
      targetPayload targetBinding sourceBefore sourceAfter targetBefore targetAfter sourcePrior
      targetPrior sourceJoint targetJoint sourceLegal targetLegal sourceMoved targetMoved
      beforeInfo afterInfo own sourceRowGood targetRowGood state.attempt generationAt
      savedAt position active targetFinal targetKept
    dsimp only at transported
    rw [original] at transported
    have targetRow : phaseRecoveryBindingData setup .concurrent targetEvent targetOwner
        targetPayload targetBinding ((targetJoint targetOwner).map (·.semantic)) =
          (.failure, false) := by
      simpa only [Bool.false_eq_true, ↓reduceIte] using transported
    have targetGeneration : targetBefore.generation = state.attempt.generation := by
      rw [← metadata.2.2.2.2]
      exact generationAt
    have targetSaved : instructionCount setup.program -
        ProtocolState.remaining setup.program targetBefore.saved = state.attempt.phase := by
      rw [← (ProtocolState.MetadataEq.controls setup.program sourceBefore.saved
        targetBefore.saved metadata.2.1).1, saved, checkpoint.saved_position]
    have read := sourceBindingAt_of_origin setup state.attempt targetEvent targetOwner
      targetPayload targetBinding targetBefore targetPrior targetJoint targetLegal
        (some targetAfter) targetMoved targetGeneration targetSaved targetPosition.symm
          (.failure, false) targetRow targetFinal.trace targetKept
    exact ⟨targetRow, read⟩

/- The ranked row of an actual target interval starts at its retained running
prefix. Equality of prefixes at the same depth identifies the whole state,
including the exclusion mask; rank and saved metadata alone do not. -/
omit [Fintype Player] in
private theorem sourceReplayHeadRow
    (start : CommitRecoveryState setup.program)
    (entry : setup.proposalRecoveryProtocol.Trace (some start))
    (committing : ProtocolState.atCommit setup.program start.point = true)
    (final : setup.proposalRecoveryProtocol.History)
    (retained : TracePrefix entry final.trace)
    (word : List (Player → Option (CommitRecoveryMove Player L)))
    (instructions : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace final.trace) =
      word.reverse ++ setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace entry))
    (inside : 0 < word.length)
    (rank : Nat)
    (position : rank = instructionCount setup.program -
      ProtocolState.remaining setup.program start.point)
    (within : rank < instructionCount setup.program -
      ProtocolState.commitEnd setup.program start.saved) :
    ∃ (next : CommitRecoveryState setup.program)
      (joint : Player → Option (ProposalRecoveryMove Player L))
      (legal : setup.proposalRecoveryProtocol.Legal (some start) joint)
      (moved : some next ∈
        (setup.proposalRecoveryProtocol.step (some start) ⟨joint, legal⟩).support),
      TracePrefix (entry.extend joint legal moved) final.trace ∧
      SourceProgram.Setup.proposalRecoveryJoint joint = word[0] ∧
      instructionCount setup.program -
        ProtocolState.remaining setup.program start.point = rank := by
  obtain ⟨current, next, prior, joint, legal, moved, rowKept, depth, row,
      _saved, _generation, atRank⟩ :=
    source_commit_chunk_at_rank setup start entry committing final retained word
      instructions 0 inside rank (by simpa only [Nat.add_zero] using position)
      within
  have beforeKept : TracePrefix prior final.trace :=
    (TracePrefix.extend .refl joint legal moved).trans rowKept
  have same := beforeKept.eq_of_same_length retained (by
    simpa only [Nat.add_zero] using depth)
  cases same
  refine ⟨next, joint, legal, moved, rowKept, ?_, atRank⟩
  exact row

/- Removing the first actual instruction leaves the same endpoint with the
remaining source word based at the one-step extended target prefix. -/
omit [Fintype Player] in
private theorem sourceReplayTailWord
    (final : setup.proposalRecoveryProtocol.History)
    (start : CommitRecoveryState setup.program)
    (entry : setup.proposalRecoveryProtocol.Trace (some start))
    (next : CommitRecoveryState setup.program)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some start) joint)
    (moved : some next ∈
      (setup.proposalRecoveryProtocol.step (some start) ⟨joint, legal⟩).support)
    (head : Player → Option (CommitRecoveryMove Player L))
    (tail : List (Player → Option (CommitRecoveryMove Player L)))
    (semantic : SourceProgram.Setup.proposalRecoveryJoint joint = head)
    (word : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace final.trace) =
      (head :: tail).reverse ++
        setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace entry)) :
    setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace final.trace) =
      tail.reverse ++ setup.recoveryJointRecall
        (setup.proposalRecoveryEraseTrace (entry.extend joint legal moved)) := by
  calc
    setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace final.trace) =
        (head :: tail).reverse ++
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace entry) := word
    _ = tail.reverse ++
          (head :: setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace entry)) := by
            simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    _ = tail.reverse ++ setup.recoveryJointRecall
          (setup.proposalRecoveryEraseTrace (entry.extend joint legal moved)) := by
            rw [← semantic]
            rfl

/- A nonfinal active target instruction has the literal successor indexed by
its given Attempt. The supported proposal step is decoded directly at that
head; no second target Attempt is selected. -/
omit [Fintype Player] in
private theorem sourceReplayActiveHeadStep
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {rest : SourceProgram.CommitPrefix
      ((name, .commitment owner payload) :: Γ) (insert name O) Δ P}
    {entry : SourceProgram.Config Player L Γ} {excluded : Finset Player}
    {finished : SourceProgram.Config Player L Δ} {after : Finset Player}
    (active : owner ∉ excluded) (choice : PublicationResult (L.Val payload))
    (missed : Bool) (_missingFailure : missed = true → choice = .failure)
    (later : rest.Attempt (commitSuccessor name guard entry choice)
      (excludeCommit excluded owner missed) finished after)
    (suffix : SourceProgram Player L Δ P)
    (lift : ProtocolState
      ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix) →
        ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program
      ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix) lift)
    (start : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some start))
    (final : setup.proposalRecoveryProtocol.History)
    (point : start.point = lift (ProtocolState.entry
      ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix) entry))
    (mask : start.excluded = excluded)
    (saved : ProtocolState.atCommit setup.program start.saved = true)
    (endpoint : ProtocolState.commitEnd setup.program start.saved ≤ instructionCount suffix)
    (retained : TracePrefix prior final.trace)
    (word : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace final.trace) =
      ((fun who : Player => if who = owner then
        some ⟨OwnAction.commit owner name payload choice, missed⟩ else none) ::
          later.joints).reverse ++
        setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace prior))
    (nonfinal : 0 < rest.length) :
    ∃ (next : CommitRecoveryState setup.program)
      (joint : Player → Option (ProposalRecoveryMove Player L))
      (legal : setup.proposalRecoveryProtocol.Legal (some start) joint)
      (moved : some next ∈
        (setup.proposalRecoveryProtocol.step (some start) ⟨joint, legal⟩).support),
      TracePrefix (prior.extend joint legal moved) final.trace ∧
      next.point = lift (.inr (ProtocolState.entry (rest.prepend suffix)
        (commitSuccessor name guard entry choice))) ∧
      next.excluded = excludeCommit excluded owner missed ∧
      next.saved = start.saved ∧ next.generation = start.generation ∧
      SourceProgram.Setup.proposalRecoveryJoint joint =
        (fun who => if who = owner then
          some ⟨OwnAction.commit owner name payload choice, missed⟩ else none) := by
  have committing : ProtocolState.atCommit setup.program start.point = true := by
    rw [point, origin.atCommit_lift]
    rfl
  have within : instructionCount setup.program -
      ProtocolState.remaining setup.program start.point <
        instructionCount setup.program - ProtocolState.commitEnd setup.program start.saved := by
    have bounded := ProtocolState.remaining_le_instructionCount setup.program start.point
    rw [point, origin.remaining_lift] at bounded
    rw [point, origin.remaining_lift]
    simp only [ProtocolState.remaining_entry,
      SourceProgram.CommitPrefix.instructionCount_prepend,
      SourceProgram.CommitPrefix.length] at bounded ⊢
    omega
  have headInside : 0 < ((fun who : Player => if who = owner then
      some ⟨OwnAction.commit owner name payload choice, missed⟩ else none) ::
        later.joints).length := by
    simp only [List.length_cons]
    omega
  obtain ⟨next, joint, legal, moved, rowKept, semantic, _rank⟩ :=
    sourceReplayHeadRow setup start prior committing final retained
      ((fun who : Player => if who = owner then
        some ⟨OwnAction.commit owner name payload choice, missed⟩ else none) ::
          later.joints) word headInside _ rfl within
  have canonical : SourceProgram.Setup.proposalRecoveryJoint joint =
      (fun who => if who = owner then
        some ⟨OwnAction.commit owner name payload choice, missed⟩ else none) := by
    simpa only [List.getElem_cons_zero] using semantic
  have rawReached : next ∈
      (start.step (SourceProgram.Setup.proposalRecoveryJoint joint)).support := by
    change some next ∈
      ((start.step (SourceProgram.Setup.proposalRecoveryJoint joint)).map some).support at moved
    obtain ⟨actual, supported, equal⟩ := (PMF.mem_support_map_iff ..).mp moved
    cases Option.some.inj equal
    exact supported
  obtain ⟨result, rawSupported, nextEq⟩ :=
    start.step_raw_result (SourceProgram.Setup.proposalRecoveryJoint joint) next rawReached
  have activeStart : owner ∉ start.excluded := by rwa [mask]
  have rawEqOriginal : result.1 =
      (lift (.inr (ProtocolState.entry (rest.prepend suffix)
        (commitSuccessor name guard entry choice))),
        excludeCommit start.excluded owner missed) := by
    rw [canonical, point, origin.recoveryStep_lift] at rawSupported
    obtain ⟨raw, supported, equal⟩ := (PMF.mem_support_map_iff ..).mp rawSupported
    have rawValue : raw =
        (.inr (ProtocolState.entry (rest.prepend suffix)
          (commitSuccessor name guard entry choice)),
          excludeCommit start.excluded owner missed) := by
      simpa only [SourceProgram.CommitPrefix.prepend, ProtocolState.entry,
        ProtocolState.recoveryStep, Sum.elim_inl, activeStart, ↓reduceIte,
        Option.map_some, OwnAction.binding_commit, CommitRecoveryMove.missed,
        Option.elim_some, excludeCommit, PMF.mem_support_pure_iff] using supported
    simpa only [rawValue] using equal.symm
  have rawEq : result.1 =
      (lift (.inr (ProtocolState.entry (rest.prepend suffix)
        (commitSuccessor name guard entry choice))),
        excludeCommit excluded owner missed) := by
    simpa only [mask] using rawEqOriginal
  let installed := start.install result.1 result.2
  have installedPoint : installed.point = lift (.inr
      (ProtocolState.entry (rest.prepend suffix)
        (commitSuccessor name guard entry choice))) := congrArg Prod.fst rawEq
  have installedExcluded : installed.excluded = excludeCommit excluded owner missed :=
    congrArg Prod.snd rawEq
  have beforeEnd : ProtocolState.commitEnd setup.program installed.saved <
      ProtocolState.remaining setup.program installed.point := by
    rw [installedPoint, origin.remaining_lift]
    change ProtocolState.commitEnd setup.program start.saved <
      ProtocolState.remaining (rest.prepend suffix)
        (ProtocolState.entry (rest.prepend suffix)
          (commitSuccessor name guard entry choice))
    rw [ProtocolState.remaining_entry, rest.instructionCount_prepend]
    omega
  have noClose := installed.close_eq_self_of_remaining_gt saved beforeEnd
  have actual : next = installed := nextEq.trans noClose
  refine ⟨next, joint, legal, moved, rowKept, ?_, ?_, ?_, ?_, canonical⟩
  · rw [actual]
    exact installedPoint
  · rw [actual]
    exact installedExcluded
  · rw [actual]
    rfl
  · rw [actual]
    rfl

/- The inherited-owner head uses the literal automatic commitment. Before
the last slot its supported close is inert, leaving the indexed tail point. -/
omit [Fintype Player] in
private theorem sourceReplayExcludedHeadStep
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {rest : SourceProgram.CommitPrefix
      ((name, .commitment owner payload) :: Γ) (insert name O) Δ P}
    {entry : SourceProgram.Config Player L Γ} {excluded : Finset Player}
    {finished : SourceProgram.Config Player L Δ} {after : Finset Player}
    (inactive : owner ∈ excluded)
    (later : rest.Attempt (automaticCommit name owner payload entry)
      excluded finished after)
    (suffix : SourceProgram Player L Δ P)
    (lift : ProtocolState
      ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix) →
        ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program
      ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix) lift)
    (start : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some start))
    (final : setup.proposalRecoveryProtocol.History)
    (point : start.point = lift (ProtocolState.entry
      ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix) entry))
    (mask : start.excluded = excluded)
    (saved : ProtocolState.atCommit setup.program start.saved = true)
    (endpoint : ProtocolState.commitEnd setup.program start.saved ≤ instructionCount suffix)
    (retained : TracePrefix prior final.trace)
    (word : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace final.trace) =
      ((fun _ : Player => (none : Option (CommitRecoveryMove Player L))) ::
        later.joints).reverse ++
        setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace prior))
    (nonfinal : 0 < rest.length) :
    ∃ (next : CommitRecoveryState setup.program)
      (joint : Player → Option (ProposalRecoveryMove Player L))
      (legal : setup.proposalRecoveryProtocol.Legal (some start) joint)
      (moved : some next ∈
        (setup.proposalRecoveryProtocol.step (some start) ⟨joint, legal⟩).support),
      TracePrefix (prior.extend joint legal moved) final.trace ∧
      next.point = lift (.inr (ProtocolState.entry (rest.prepend suffix)
        (automaticCommit name owner payload entry))) ∧
      next.excluded = excluded ∧
      next.saved = start.saved ∧ next.generation = start.generation ∧
      SourceProgram.Setup.proposalRecoveryJoint joint = fun _ => none := by
  have committing : ProtocolState.atCommit setup.program start.point = true := by
    rw [point, origin.atCommit_lift]
    rfl
  have within : instructionCount setup.program -
      ProtocolState.remaining setup.program start.point <
        instructionCount setup.program - ProtocolState.commitEnd setup.program start.saved := by
    have bounded := ProtocolState.remaining_le_instructionCount setup.program start.point
    rw [point, origin.remaining_lift] at bounded
    rw [point, origin.remaining_lift]
    simp only [ProtocolState.remaining_entry,
      SourceProgram.CommitPrefix.instructionCount_prepend,
      SourceProgram.CommitPrefix.length] at bounded ⊢
    omega
  have headInside : 0 < ((fun _ : Player =>
      (none : Option (CommitRecoveryMove Player L))) :: later.joints).length := by
    simp only [List.length_cons]
    omega
  obtain ⟨next, joint, legal, moved, rowKept, semantic, _rank⟩ :=
    sourceReplayHeadRow setup start prior committing final retained
      ((fun _ : Player => (none : Option (CommitRecoveryMove Player L))) ::
        later.joints) word
        headInside _ rfl within
  have empty : SourceProgram.Setup.proposalRecoveryJoint joint = fun _ => none := by
    simpa only [List.getElem_cons_zero] using semantic
  have rawReached : next ∈
      (start.step (SourceProgram.Setup.proposalRecoveryJoint joint)).support := by
    change some next ∈
      ((start.step (SourceProgram.Setup.proposalRecoveryJoint joint)).map some).support at moved
    obtain ⟨actual, supported, equal⟩ := (PMF.mem_support_map_iff ..).mp moved
    cases Option.some.inj equal
    exact supported
  obtain ⟨result, rawSupported, nextEq⟩ :=
    start.step_raw_result (SourceProgram.Setup.proposalRecoveryJoint joint) next rawReached
  have inactiveStart : owner ∈ start.excluded := by rwa [mask]
  have rawEqOriginal : result.1 =
      (lift (.inr (ProtocolState.entry (rest.prepend suffix)
        (automaticCommit name owner payload entry))), start.excluded) := by
    rw [empty, point, origin.recoveryStep_lift] at rawSupported
    obtain ⟨raw, supported, equal⟩ := (PMF.mem_support_map_iff ..).mp rawSupported
    have rawValue : raw =
        (.inr (ProtocolState.entry (rest.prepend suffix)
          (automaticCommit name owner payload entry)), start.excluded) := by
      simpa only [SourceProgram.CommitPrefix.prepend, ProtocolState.entry,
        ProtocolState.recoveryStep, Sum.elim_inl, inactiveStart, ↓reduceIte,
        PMF.mem_support_pure_iff] using supported
    simpa only [rawValue] using equal.symm
  have rawEq : result.1 =
      (lift (.inr (ProtocolState.entry (rest.prepend suffix)
        (automaticCommit name owner payload entry))), excluded) := by
    simpa only [mask] using rawEqOriginal
  let installed := start.install result.1 result.2
  have installedPoint : installed.point = lift (.inr
      (ProtocolState.entry (rest.prepend suffix)
        (automaticCommit name owner payload entry))) := congrArg Prod.fst rawEq
  have installedExcluded : installed.excluded = excluded := congrArg Prod.snd rawEq
  have beforeEnd : ProtocolState.commitEnd setup.program installed.saved <
      ProtocolState.remaining setup.program installed.point := by
    rw [installedPoint, origin.remaining_lift]
    change ProtocolState.commitEnd setup.program start.saved <
      ProtocolState.remaining (rest.prepend suffix)
        (ProtocolState.entry (rest.prepend suffix)
          (automaticCommit name owner payload entry))
    rw [ProtocolState.remaining_entry, rest.instructionCount_prepend]
    omega
  have noClose := installed.close_eq_self_of_remaining_gt saved beforeEnd
  have actual : next = installed := nextEq.trans noClose
  refine ⟨next, joint, legal, moved, rowKept, ?_, ?_, ?_, ?_, empty⟩
  · rw [actual]
    exact installedPoint
  · rw [actual]
    exact installedExcluded
  · rw [actual]
    rfl
  · rw [actual]
    rfl

/- A completed source visit retains its literal target row decoder and
compiler reference interpretation at the assigned drained snapshot. -/
structure SourceReplayVisitImage
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix))
    {entry : SourceProgram.Config Player L Γ} {excluded : Finset Player}
    {finished : SourceProgram.Config Player L Δ} {after : Finset Player}
    (attempt : block.Attempt entry excluded finished after)
    (native : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (refs : ContextRefs (graphLayout setup.program) Γ) : Prop where
  entryAgrees : refs.Agrees entry.state native.config.store
  tableReads : sourceAttemptTableReads setup attempt suffix embedding native
  rawFinal : decodeCommitAttempt setup.program .concurrent block suffix embedding native
    entry excluded = ⟨finished, after, attempt⟩
  finalAgrees : (commitBlockRefs setup.program block suffix embedding refs).Agrees
    finished.state native.config.store

omit [Fintype Player] in
theorem sourceReplayVisitImage_empty
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (suffix : SourceProgram Player L Γ O)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      ((SourceProgram.CommitPrefix.nil : SourceProgram.CommitPrefix Γ O Γ O).prepend suffix))
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (native : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (agrees : refs.Agrees entry.state native.config.store) :
    SourceReplayVisitImage setup (.nil : SourceProgram.CommitPrefix Γ O Γ O) suffix
      embedding (.nil entry excluded) native refs := by
  exact ⟨agrees, trivial, rfl, agrees⟩

/- An actual completed binding with no accepted handle stays a failed row in
the assigned physical snapshot, including its typed store and missing bit. -/
omit [Fintype Player] in
private theorem sourceReplayUnacceptedRow
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (valid : snapshot.BindingInvariant)
    (completed : event ∈ snapshot.config.cut.completed)
    (unaccepted : snapshot.accepted (.inr event) = none) :
    (sourceSnapshotState setup implementation target reference lost snapshot).accepted
      (.inr event) = none ∧
    (⟨.inr event, binding⟩ : FieldRef (serviceGraph setup .concurrent).layout
      (.binding owner payload)).get?
        (sourceSnapshotState setup implementation target reference lost snapshot).config.store =
          some .failure := by
  let field : FieldRef (serviceGraph setup .concurrent).layout
      (.binding owner payload) := ⟨.inr event, binding⟩
  have original : field.get? snapshot.config.store = some .failure := by
    have read := valid.binding_read field event rfl completed
    dsimp only [field] at read
    simpa only [unaccepted, Option.elim_none] using read
  have stored : snapshot.config.store (.inr event) =
      some (cast (congrArg EventField.Value binding.symm) .failure) := by
    have castSome {α β : Type} (typeEq : α = β) (item : α) :
        cast (congrArg Option typeEq) (some item) = some (cast typeEq item) := by
      cases typeEq
      rfl
    have uncast := congrArg
      (cast (congrArg (fun kind : EventField Player L => Option kind.Value) binding.symm))
        original
    change cast (congrArg Option (congrArg EventField.Value binding.symm))
      (cast (congrArg Option (congrArg EventField.Value binding))
        (snapshot.config.store (.inr event))) =
          cast (congrArg Option (congrArg EventField.Value binding.symm))
            (some .failure) at uncast
    have rawEq : snapshot.config.store (.inr event) =
        cast (congrArg Option (congrArg EventField.Value binding.symm))
          (some .failure) := by
      simpa only [cast_cast, cast_eq] using uncast
    exact rawEq.trans (castSome (congrArg EventField.Value binding.symm) .failure)
  have assigned := assigned_failed_binding_store setup implementation target reference lost
    snapshot event owner payload binding stored
  have acceptedAssigned :
      (sourceSnapshotState setup implementation target reference lost snapshot).accepted
        (.inr event) = none := by
    simpa only [sourceSnapshotState, EventGraphRuntime.State.swap_accepted] using unaccepted
  refine ⟨acceptedAssigned, ?_⟩
  change field.get?
    (sourceSnapshotState setup implementation target reference lost snapshot).config.store =
      some .failure
  have castSome {α β : Type} (typeEq : α = β) (item : α) :
      cast (congrArg Option typeEq) (some item) = some (cast typeEq item) := by
    cases typeEq
    rfl
  have castInverse {α β : Type} (typeEq : α = β) (item : β) :
      cast typeEq (cast typeEq.symm item) = item := by
    cases typeEq
    rfl
  unfold FieldRef.get?
  rw [assigned]
  change cast (congrArg Option (congrArg EventField.Value binding))
    (some (cast (congrArg EventField.Value binding.symm) .failure)) = some .failure
  exact (castSome (congrArg EventField.Value binding)
    (cast (congrArg EventField.Value binding.symm) .failure)).trans
      (congrArg some (castInverse (congrArg EventField.Value binding) .failure))

/- An accepted focal failure still has a true receipt. Its candidate and
stored field remain failed after assignment, so its omission bit stays false. -/
omit [Fintype Player] in
private theorem sourceReplayAcceptedFailureRow
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (handle : Handle (serviceGraph setup .concurrent))
    (accepted : snapshot.accepted (.inr event) = some handle)
    (failed : snapshot.bindingResult handle payload = .failure)
    (unchanged : sourceHandlePairs setup implementation target reference lost handle = none)
    (valid : snapshot.BindingInvariant)
    (completed : event ∈ snapshot.config.cut.completed) :
    ((sourceSnapshotState setup implementation target reference lost snapshot).accepted
      (.inr event)).elim PublicationResult.failure
        (fun candidate => (sourceSnapshotState setup implementation target reference lost
          snapshot).bindingResult candidate payload) = .failure ∧
    ((sourceSnapshotState setup implementation target reference lost snapshot).accepted
      (.inr event)).isNone = false ∧
    (⟨.inr event, binding⟩ : FieldRef (serviceGraph setup .concurrent).layout
      (.binding owner payload)).get?
        (sourceSnapshotState setup implementation target reference lost snapshot).config.store =
          some .failure := by
  let field : FieldRef (serviceGraph setup .concurrent).layout
      (.binding owner payload) := ⟨.inr event, binding⟩
  have original : field.get? snapshot.config.store = some .failure := by
    have read := valid.binding_read field event rfl completed
    dsimp only [field] at read
    simpa only [accepted, Option.elim_some, failed] using read
  have stored : snapshot.config.store (.inr event) =
      some (cast (congrArg EventField.Value binding.symm) .failure) := by
    have castSome {α β : Type} (typeEq : α = β) (item : α) :
        cast (congrArg Option typeEq) (some item) = some (cast typeEq item) := by
      cases typeEq
      rfl
    have uncast := congrArg
      (cast (congrArg (fun kind : EventField Player L => Option kind.Value) binding.symm))
        original
    change cast (congrArg Option (congrArg EventField.Value binding.symm))
      (cast (congrArg Option (congrArg EventField.Value binding))
        (snapshot.config.store (.inr event))) =
          cast (congrArg Option (congrArg EventField.Value binding.symm))
            (some .failure) at uncast
    have rawEq : snapshot.config.store (.inr event) =
        cast (congrArg Option (congrArg EventField.Value binding.symm))
          (some .failure) := by
      simpa only [cast_cast, cast_eq] using uncast
    exact rawEq.trans (castSome (congrArg EventField.Value binding.symm) .failure)
  have acceptedAssigned :
      (sourceSnapshotState setup implementation target reference lost snapshot).accepted
        (.inr event) = some handle := by
    simpa only [sourceSnapshotState, EventGraphRuntime.State.swap_accepted] using accepted
  have failedAssigned := assigned_failed_binding_result setup implementation target reference
    lost snapshot handle payload failed unchanged
  have storedAssigned := assigned_failed_binding_store setup implementation target reference
    lost snapshot event owner payload binding stored
  refine ⟨?_, ?_, ?_⟩
  · rw [acceptedAssigned]
    exact failedAssigned
  · rw [acceptedAssigned]
    rfl
  · have castSome {α β : Type} (typeEq : α = β) (item : α) :
        cast (congrArg Option typeEq) (some item) = some (cast typeEq item) := by
      cases typeEq
      rfl
    have castInverse {α β : Type} (typeEq : α = β) (item : β) :
        cast typeEq (cast typeEq.symm item) = item := by
      cases typeEq
      rfl
    unfold FieldRef.get?
    rw [storedAssigned]
    exact (castSome (congrArg EventField.Value binding)
      (cast (congrArg EventField.Value binding.symm) .failure)).trans
        (congrArg some (castInverse (congrArg EventField.Value binding) .failure))

/- An inherited owner has no accepted receipt in the visit. The actual
completed field and its assigned image therefore both contain failure. -/
omit [Fintype Player] in
theorem sourceReplayInheritedRow
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (valid : snapshot.BindingInvariant)
    (completed : event ∈ snapshot.config.cut.completed)
    (low : Nat) (inherited : Finset Player)
    (receipts : BindingReceiptOrder low inherited snapshot.accepted)
    (lower : low ≤ event.val) (inactive : owner ∈ inherited) :
    (⟨.inr event, binding⟩ : FieldRef (serviceGraph setup .concurrent).layout
      (.binding owner payload)).get?
        (sourceSnapshotState setup implementation target reference lost snapshot).config.store =
          some .failure := by
  have unaccepted : snapshot.accepted (.inr event) = none := by
    cases accepted : snapshot.accepted (.inr event) with
    | none => rfl
    | some candidate =>
        exact ((receipts event owner payload candidate lower binding accepted).1 inactive).elim
  exact (sourceReplayUnacceptedRow setup implementation target reference lost snapshot event
    owner payload binding valid completed unaccepted).2

/- An excluded visit row is read from the actual completed physical snapshot.
The recursive target attempt supplies the remaining rows; no assigned native
trace endpoint is required for either the decoder or compiler references. -/
omit [Fintype Player] in
theorem sourceReplayExcludedVisit
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {rest : SourceProgram.CommitPrefix
      ((name, .commitment owner payload) :: Γ) (insert name O) Δ P}
    {entry : SourceProgram.Config Player L Γ} {excluded : Finset Player}
    {finished : SourceProgram.Config Player L Δ} {after : Finset Player}
    (inactive : owner ∈ excluded)
    (later : rest.Attempt (automaticCommit name owner payload entry) excluded finished after)
    (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix))
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (valid : snapshot.BindingInvariant)
    (completed : embedding.event ⟨0, by
      simp only [SourceProgram.CommitPrefix.prepend, eventCount]
      omega⟩ ∈ snapshot.config.cut.completed)
    (low : Nat) (inherited : Finset Player)
    (receipts : BindingReceiptOrder low inherited snapshot.accepted)
    (lower : low ≤ (embedding.event ⟨0, by
      simp only [SourceProgram.CommitPrefix.prepend, eventCount]
      omega⟩).val)
    (ownerInherited : owner ∈ inherited)
    (entryAgrees : refs.Agrees entry.state
      (sourceSnapshotState setup implementation target reference lost snapshot).config.store)
    (tailReads : sourceAttemptTableReads setup later suffix
      (embedding.tail (rest.prepend suffix) (by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl))
      (sourceSnapshotState setup implementation target reference lost snapshot)) :
    SourceReplayVisitImage setup
      (SourceProgram.CommitPrefix.commit name owner fresh guard rest) suffix embedding
      (.excluded inactive later)
      (sourceSnapshotState setup implementation target reference lost snapshot) refs := by
  let event := embedding.event ⟨0, by
    simp only [SourceProgram.CommitPrefix.prepend, eventCount]
    omega⟩
  have binding : (serviceGraph setup .concurrent).outputLayout event =
      .binding owner payload := by
    change outputLayout setup.program event = _
    simpa only [event, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
      Fin.cases_zero] using embedding.layout_eq ⟨0, by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]
        omega⟩
  have failure := sourceReplayInheritedRow setup implementation target reference lost
    snapshot event owner payload binding valid completed low inherited receipts lower
      ownerInherited
  have reads : sourceAttemptTableReads setup (.excluded inactive later) suffix embedding
      (sourceSnapshotState setup implementation target reference lost snapshot) := by
    change (⟨.inr event, binding⟩ : FieldRef (serviceGraph setup .concurrent).layout
        (.binding owner payload)).get?
          (sourceSnapshotState setup implementation target reference lost snapshot).config.store =
            some .failure ∧ _
    exact ⟨failure, tailReads⟩
  exact ⟨entryAgrees, reads,
    decodeCommitAttempt_eq_of_target_rows setup (.excluded inactive later) suffix embedding
      _ reads,
    target_attempt_state_agrees setup (.excluded inactive later) suffix embedding _ refs
      entryAgrees reads⟩

/- The physical visit's accepted stamp identifies the exact source attempt
namespace of its authored packet. A target value at that address is therefore
the assigned meaning of the same physical handle. -/
private theorem sourceReplayStampedMeaning
    (reference : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some reference))
    (target : setup.proposalRecoveryProtocol.History)
    (attempt : CommitAttemptId)
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (stamp : BindingStamp
      (fun who => (nativeApplication).outputs (reference.execution.recall who))
      attempt snapshot)
    (event : (serviceGraph setup .concurrent).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (handle : Handle (serviceGraph setup .concurrent))
    (lower : attempt.phase ≤ event.val)
    (accepted : snapshot.accepted (.inr event) = some handle)
    (value : L.Val payload)
    (read : sourceBindingAt setup attempt event owner payload binding target.trace =
      some value) :
    sourceHandleMeaning setup implementation target reference handle =
      some (⟨payload, value⟩ : Raw L) := by
  rcases stamp event handle accepted with earlier |
    ⟨message, authored, _sender, call, attemptEq⟩
  · omega
  · obtain ⟨record, recalled, emitted⟩ := List.mem_filterMap.mp authored
    have atMessage : sourceBindingAt setup message.payload.attempt event owner payload
        binding target.trace = some value := by
      rwa [attemptEq]
    exact sourceHandleMeaning_of_emission setup implementation target reference trace
      handle record recalled message emitted event call owner payload binding (some value)
        atMessage

/- A signed accepted failure reads no target binding even if its original
receipt was subsequently canceled from the current catalogue. -/
private theorem sourceReplayStampedFailure
    (reference : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some reference))
    (target : setup.proposalRecoveryProtocol.History)
    (attempt : CommitAttemptId)
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (stamp : BindingStamp
      (fun who => (nativeApplication).outputs (reference.execution.recall who))
      attempt snapshot)
    (event : (serviceGraph setup .concurrent).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (handle : Handle (serviceGraph setup .concurrent))
    (lower : attempt.phase ≤ event.val)
    (accepted : snapshot.accepted (.inr event) = some handle)
    (read : sourceBindingAt setup attempt event owner payload binding target.trace = none) :
    sourceHandleMeaning setup implementation target reference handle = none := by
  rcases stamp event handle accepted with earlier |
    ⟨message, authored, _sender, call, attemptEq⟩
  · omega
  · obtain ⟨record, recalled, emitted⟩ := List.mem_filterMap.mp authored
    have atMessage : sourceBindingAt setup message.payload.attempt event owner payload
        binding target.trace = none := by
      rwa [attemptEq]
    simpa only [Option.map_none] using
      sourceHandleMeaning_of_emission setup implementation target reference trace
        handle record recalled message emitted event call owner payload binding none atMessage

/- A completed accepted row reads the value at its literal target source
address in the assigned physical snapshot. The stamp, rather than event rank
alone, identifies the packet's attempt across retries. -/
private theorem sourceReplayAcceptedRow
    (reference : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some reference))
    (target : setup.proposalRecoveryProtocol.History)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (attempt : CommitAttemptId)
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (stamp : BindingStamp
      (fun who => (nativeApplication).outputs (reference.execution.recall who))
      attempt snapshot)
    (event : (serviceGraph setup .concurrent).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (handle : Handle (serviceGraph setup .concurrent))
    (lower : attempt.phase ≤ event.val)
    (accepted : snapshot.accepted (.inr event) = some handle)
    (next : L.Val payload)
    (meaning : sourceHandleMeaning setup implementation target reference handle =
      some (⟨payload, next⟩ : Raw L))
    (stored : (sourceSnapshotState setup implementation target reference lost snapshot).config.store
      (.inr event) =
        some (cast (congrArg EventField.Value binding.symm) (.success next)))
    (result :
      (sourceSnapshotState setup implementation target reference lost snapshot).bindingResult
        handle payload = .success next)
    (value : L.Val payload)
    (read : sourceBindingAt setup attempt event owner payload binding target.trace =
      some value) :
    ((sourceSnapshotState setup implementation target reference lost snapshot).accepted
      (.inr event)).elim PublicationResult.failure
        (fun candidate => (sourceSnapshotState setup implementation target reference lost
          snapshot).bindingResult candidate payload) = .success value ∧
    ((sourceSnapshotState setup implementation target reference lost snapshot).accepted
      (.inr event)).isNone = false ∧
    (⟨.inr event, binding⟩ : FieldRef (serviceGraph setup .concurrent).layout
      (.binding owner payload)).get?
        (sourceSnapshotState setup implementation target reference lost snapshot).config.store =
          some (.success value) := by
  have targetMeaning := sourceReplayStampedMeaning setup implementation reference trace
    target attempt snapshot stamp event owner payload binding handle lower accepted value read
  have sameRaw : (⟨payload, next⟩ : Raw L) = ⟨payload, value⟩ :=
    Option.some.inj (meaning.symm.trans targetMeaning)
  have sameValue : next = value := by
    have decoded := congrArg (fun raw : Raw L => raw.as? payload) sameRaw
    simpa only [Raw.as?_mk, Option.some.injEq] using decoded
  subst next
  have assignedAccepted :
      (sourceSnapshotState setup implementation target reference lost snapshot).accepted
        (.inr event) = some handle := by
    simpa only [sourceSnapshotState, EventGraphRuntime.State.swap_accepted] using accepted
  refine ⟨?_, ?_, ?_⟩
  · rw [assignedAccepted]
    exact result
  · rw [assignedAccepted]
    rfl
  · have castSome {α β : Type} (typeEq : α = β) (item : α) :
        cast (congrArg Option typeEq) (some item) = some (cast typeEq item) := by
      cases typeEq
      rfl
    have castInverse {α β : Type} (typeEq : α = β) (item : β) :
        cast typeEq (cast typeEq.symm item) = item := by
      cases typeEq
      rfl
    unfold FieldRef.get?
    rw [stored]
    change cast (congrArg Option (congrArg EventField.Value binding))
      (some (cast (congrArg EventField.Value binding.symm) (.success value))) =
        some (.success value)
    exact (castSome (congrArg EventField.Value binding)
      (cast (congrArg EventField.Value binding.symm) (.success value))).trans
        (congrArg some (castInverse (congrArg EventField.Value binding) (.success value)))

/- A completed accepted source row uses its real packet namespace. Once the
paired source step identifies its target choice and missing bit, the assigned
physical snapshot decodes the entire active visit, including its references. -/
theorem sourceReplayActiveVisit
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {rest : SourceProgram.CommitPrefix
      ((name, .commitment owner payload) :: Γ) (insert name O) Δ P}
    {entry : SourceProgram.Config Player L Γ} {excluded : Finset Player}
    {finished : SourceProgram.Config Player L Δ} {after : Finset Player}
    (active : owner ∉ excluded) (choice : PublicationResult (L.Val payload))
    (missed : Bool) (missingFailure : missed = true → choice = .failure)
    (later : rest.Attempt (commitSuccessor name guard entry choice)
      (excludeCommit excluded owner missed) finished after)
    (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix))
    (reference : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some reference))
    (target : setup.proposalRecoveryProtocol.History)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (attempt : CommitAttemptId)
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (stamp : BindingStamp
      (fun who => (nativeApplication).outputs (reference.execution.recall who))
      attempt snapshot)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (event : (serviceGraph setup .concurrent).EventId)
    (eventEq : event = embedding.event ⟨0, by
      simp only [SourceProgram.CommitPrefix.prepend, eventCount]
      omega⟩)
    (binding : (serviceGraph setup .concurrent).outputLayout event =
      .binding owner payload)
    (handle : Handle (serviceGraph setup .concurrent))
    (lower : attempt.phase ≤ event.val)
    (accepted : snapshot.accepted (.inr event) = some handle)
    (next : L.Val payload)
    (meaning : sourceHandleMeaning setup implementation target reference handle =
      some (⟨payload, next⟩ : Raw L))
    (stored : (sourceSnapshotState setup implementation target reference lost snapshot).config.store
      (.inr event) =
        some (cast (congrArg EventField.Value binding.symm) (.success next)))
    (result :
      (sourceSnapshotState setup implementation target reference lost snapshot).bindingResult
        handle payload = .success next)
    (value : L.Val payload)
    (read : sourceBindingAt setup attempt event owner payload binding target.trace =
      some value)
    (who : Player)
    (sourceBefore sourceAfter targetBefore targetAfter : CommitRecoveryState setup.program)
    (sourcePrior : setup.proposalRecoveryProtocol.Trace (some sourceBefore))
    (targetPrior : setup.proposalRecoveryProtocol.Trace (some targetBefore))
    (sourceJoint targetJoint : Player → Option (ProposalRecoveryMove Player L))
    (sourceLegal : setup.proposalRecoveryProtocol.Legal (some sourceBefore) sourceJoint)
    (targetLegal : setup.proposalRecoveryProtocol.Legal (some targetBefore) targetJoint)
    (sourceMoved : some sourceAfter ∈
      (setup.proposalRecoveryProtocol.step (some sourceBefore)
        ⟨sourceJoint, sourceLegal⟩).support)
    (targetMoved : some targetAfter ∈
      (setup.proposalRecoveryProtocol.step (some targetBefore)
        ⟨targetJoint, targetLegal⟩).support)
    (beforeInfo : setup.proposalRecoveryModel.infoOf who sourcePrior =
      setup.proposalRecoveryModel.infoOf who targetPrior)
    (afterInfo : setup.proposalRecoveryModel.infoOf who
      (sourcePrior.extend sourceJoint sourceLegal sourceMoved) =
      setup.proposalRecoveryModel.infoOf who
        (targetPrior.extend targetJoint targetLegal targetMoved))
    (own : sourceJoint who = targetJoint who)
    (sourceGood : setup.proposalRecoveryForeignGood who
      ⟨some sourceAfter, sourcePrior.extend sourceJoint sourceLegal sourceMoved⟩)
    (targetGood : setup.proposalRecoveryForeignGood who
      ⟨some targetAfter, targetPrior.extend targetJoint targetLegal targetMoved⟩)
    (generation : sourceBefore.generation = attempt.generation)
    (saved : instructionCount setup.program -
      ProtocolState.remaining setup.program sourceBefore.saved = attempt.phase)
    (position : event.val = instructionCount setup.program -
      ProtocolState.remaining setup.program sourceBefore.point)
    (sourceActive : owner ∉ sourceBefore.excluded)
    (targetRetained : TracePrefix
      (targetPrior.extend targetJoint targetLegal targetMoved) target.trace)
    (old : L.Val payload)
    (sourceRow : phaseRecoveryBindingData setup .concurrent event owner payload binding
      ((sourceJoint owner).map (·.semantic)) = (.success old, false))
    (attemptRow : (choice, missed) =
      phaseRecoveryBindingData setup .concurrent event owner payload binding
        ((targetJoint owner).map (·.semantic)))
    (entryAgrees : refs.Agrees entry.state
      (sourceSnapshotState setup implementation target reference lost snapshot).config.store)
    (tailReads : sourceAttemptTableReads setup later suffix
      (embedding.tail (rest.prepend suffix) (by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl))
      (sourceSnapshotState setup implementation target reference lost snapshot)) :
    SourceReplayVisitImage setup
      (SourceProgram.CommitPrefix.commit name owner fresh guard rest) suffix embedding
      (.active active choice missed missingFailure later)
      (sourceSnapshotState setup implementation target reference lost snapshot) refs := by
  have head := sourceReplayAcceptedRow setup implementation reference trace target lost attempt
    snapshot stamp event owner payload binding handle lower accepted next meaning stored result
      value read
  have paired : phaseRecoveryBindingData setup .concurrent event owner payload binding
      ((targetJoint owner).map (·.semantic)) = (.success value, false) := by
    have transported := source_binding_data_transport setup who owner event payload binding
      sourceBefore sourceAfter targetBefore targetAfter sourcePrior targetPrior sourceJoint
      targetJoint sourceLegal targetLegal sourceMoved targetMoved beforeInfo afterInfo own
      sourceGood targetGood attempt generation saved position sourceActive target
      targetRetained
    dsimp only at transported
    simpa only [sourceRow, Bool.false_eq_true, ↓reduceIte, read, Option.elim_some]
      using transported
  have targetRow : (choice, missed) = (.success value, false) :=
    attemptRow.trans paired
  have targetChoice : choice = .success value := (Prod.mk.inj targetRow).1
  have targetMissed : missed = false := (Prod.mk.inj targetRow).2
  subst event
  have reads : sourceAttemptTableReads setup
      (.active active choice missed missingFailure later) suffix embedding
      (sourceSnapshotState setup implementation target reference lost snapshot) := by
    change _ ∧ _ ∧ _ ∧ _
    refine ⟨head.1.trans targetChoice.symm, head.2.1.trans targetMissed.symm, ?_, tailReads⟩
    simpa only [targetChoice] using head.2.2
  exact ⟨entryAgrees, reads,
    decodeCommitAttempt_eq_of_target_rows setup
      (.active active choice missed missingFailure later) suffix embedding _ reads,
    target_attempt_state_agrees setup (.active active choice missed missingFailure later)
      suffix embedding _ refs entryAgrees reads⟩

/- A focal accepted failure has an accepted handle but a failed stored result.
It is a real attempted row, with omission bit false, including when a later
retry cancels the handle from the current catalogue. -/
omit [Fintype Player] in
theorem sourceReplayFocalFailureVisit
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {rest : SourceProgram.CommitPrefix
      ((name, .commitment owner payload) :: Γ) (insert name O) Δ P}
    {entry : SourceProgram.Config Player L Γ} {excluded : Finset Player}
    {finished : SourceProgram.Config Player L Δ} {after : Finset Player}
    (active : owner ∉ excluded) (choice : PublicationResult (L.Val payload))
    (missed : Bool) (missingFailure : missed = true → choice = .failure)
    (later : rest.Attempt (commitSuccessor name guard entry choice)
      (excludeCommit excluded owner missed) finished after)
    (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix))
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (valid : snapshot.BindingInvariant)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (event : (serviceGraph setup .concurrent).EventId)
    (eventEq : event = embedding.event ⟨0, by
      simp only [SourceProgram.CommitPrefix.prepend, eventCount]
      omega⟩)
    (binding : (serviceGraph setup .concurrent).outputLayout event =
      .binding owner payload)
    (completed : event ∈ snapshot.config.cut.completed)
    (handle : Handle (serviceGraph setup .concurrent))
    (accepted : snapshot.accepted (.inr event) = some handle)
    (failed : snapshot.bindingResult handle payload = .failure)
    (unchanged : sourceHandlePairs setup implementation target reference lost handle = none)
    (targetRow : (choice, missed) = (.failure, false))
    (entryAgrees : refs.Agrees entry.state
      (sourceSnapshotState setup implementation target reference lost snapshot).config.store)
    (tailReads : sourceAttemptTableReads setup later suffix
      (embedding.tail (rest.prepend suffix) (by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl))
      (sourceSnapshotState setup implementation target reference lost snapshot)) :
    SourceReplayVisitImage setup
      (SourceProgram.CommitPrefix.commit name owner fresh guard rest) suffix embedding
      (.active active choice missed missingFailure later)
      (sourceSnapshotState setup implementation target reference lost snapshot) refs := by
  subst event
  have head := sourceReplayAcceptedFailureRow setup implementation target reference lost
    snapshot _ owner payload binding handle accepted failed unchanged valid completed
  have targetChoice : choice = .failure := (Prod.mk.inj targetRow).1
  have targetMissed : missed = false := (Prod.mk.inj targetRow).2
  have reads : sourceAttemptTableReads setup
      (.active active choice missed missingFailure later) suffix embedding
      (sourceSnapshotState setup implementation target reference lost snapshot) := by
    change _ ∧ _ ∧ _ ∧ _
    refine ⟨?_, ?_, ?_, tailReads⟩
    · rw [targetChoice]
      exact head.1
    · rw [targetMissed]
      exact head.2.1
    · simpa only [targetChoice] using head.2.2
  exact ⟨entryAgrees, reads,
    decodeCommitAttempt_eq_of_target_rows setup
      (.active active choice missed missingFailure later) suffix embedding _ reads,
    target_attempt_state_agrees setup (.active active choice missed missingFailure later)
      suffix embedding _ refs entryAgrees reads⟩

/- A missing active row is a physical completed failure. Its assigned typed
field and missing bit determine the whole target visit without an accepted
handle or a synthetic source value. -/
omit [Fintype Player] in
theorem sourceReplayMissingVisit
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {rest : SourceProgram.CommitPrefix
      ((name, .commitment owner payload) :: Γ) (insert name O) Δ P}
    {entry : SourceProgram.Config Player L Γ} {excluded : Finset Player}
    {finished : SourceProgram.Config Player L Δ} {after : Finset Player}
    (active : owner ∉ excluded) (choice : PublicationResult (L.Val payload))
    (missed : Bool) (missingFailure : missed = true → choice = .failure)
    (later : rest.Attempt (commitSuccessor name guard entry choice)
      (excludeCommit excluded owner missed) finished after)
    (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix))
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (valid : snapshot.BindingInvariant)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (event : (serviceGraph setup .concurrent).EventId)
    (eventEq : event = embedding.event ⟨0, by
      simp only [SourceProgram.CommitPrefix.prepend, eventCount]
      omega⟩)
    (binding : (serviceGraph setup .concurrent).outputLayout event =
      .binding owner payload)
    (completed : event ∈ snapshot.config.cut.completed)
    (unaccepted : snapshot.accepted (.inr event) = none)
    (targetMissed : missed = true)
    (entryAgrees : refs.Agrees entry.state
      (sourceSnapshotState setup implementation target reference lost snapshot).config.store)
    (tailReads : sourceAttemptTableReads setup later suffix
      (embedding.tail (rest.prepend suffix) (by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl))
      (sourceSnapshotState setup implementation target reference lost snapshot)) :
    SourceReplayVisitImage setup
      (SourceProgram.CommitPrefix.commit name owner fresh guard rest) suffix embedding
      (.active active choice missed missingFailure later)
      (sourceSnapshotState setup implementation target reference lost snapshot) refs := by
  subst event
  have head := sourceReplayUnacceptedRow setup implementation target reference lost snapshot
    _ owner payload binding valid completed unaccepted
  have targetChoice : choice = .failure := missingFailure targetMissed
  have reads : sourceAttemptTableReads setup
      (.active active choice missed missingFailure later) suffix embedding
      (sourceSnapshotState setup implementation target reference lost snapshot) := by
    change _ ∧ _ ∧ _ ∧ _
    refine ⟨?_, ?_, ?_, tailReads⟩
    · rw [head.1, targetChoice]
      rfl
    · rw [head.1, targetMissed]
      rfl
    · simpa only [targetChoice] using head.2
  exact ⟨entryAgrees, reads,
    decodeCommitAttempt_eq_of_target_rows setup
      (.active active choice missed missingFailure later) suffix embedding _ reads,
    target_attempt_state_agrees setup (.active active choice missed missingFailure later)
      suffix embedding _ refs entryAgrees reads⟩

/- A partial auxiliary value map is confined to signed historical foreign
preparations that never received a true accepting receipt. The receipt test
persists across close and restore, so canceled accepted values are excluded. -/
def SourceReplayLostRestricted
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (who : Player)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L)) : Prop :=
  ∀ handle raw, lost handle = some raw →
    handle.1 ≠ who ∧
    (∃ serial, handle.2 = .prepared serial) ∧
    sourceHandleMeaning setup implementation target reference handle = none ∧
    ∃ (record : (nativeApplication).PlayerEntry)
      (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
      (event : (serviceGraph setup .concurrent).EventId)
      (payload : L.Ty) (old : L.Val payload),
      record ∈ reference.execution.recall handle.1 ∧
      record.emitted = some message ∧
      message.sender = handle.1 ∧
      message.payload.packet.call = .commitment event handle ∧
      message.payload.attempt ≠ reference.execution.application.attempt ∧
      (serviceGraph setup .concurrent).outputLayout event = .binding handle.1 payload ∧
      raw.1 = payload ∧
      record.action.transmission.bind PhaseProposal.bindingPreparation =
        some ⟨payload, old⟩ ∧
      ¬ PhaseService.BindingAccepted implementation.runtime implementation.leaks
        ⟨message.payload.attempt, event⟩ handle.1 reference.execution

theorem sourceReplayCloseEvidence
    (reference before after : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (beforeTrace : (nativeProtocol).Trace (some before))
    (retained : TracePrefix beforeTrace referenceTrace)
    (witness : RecoverySourceWitness setup .concurrent implementation.plan
      before.execution.application)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (installed : phase ∈ before.execution.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (current : RecoveryState (serviceGraph setup .concurrent))
    (effect : PhaseClosingEffect implementation.runtime implementation.leaks
      before.execution after.execution current)
    (changed : after.execution.application.attempt ≠ before.execution.application.attempt)
    (stamp : BindingStamp (fun owner =>
      (nativeApplication).outputs (before.execution.recall owner))
        before.execution.application.attempt (phase.drain current).native) :
    BindingReceiptOrder phase.low before.execution.application.entry.excluded
        (phase.drain current).native.accepted ∧
      BindingStamp (fun owner => (nativeApplication).outputs (reference.execution.recall owner))
        before.execution.application.attempt (phase.drain current).native := by
  obtain ⟨raw, _checkpoint, _history⟩ := RecoverySourceWitness.raw_closing_checkpoint setup
    .concurrent implementation.runtime implementation.leaks implementation.plan before after
      witness current effect changed
  have present : phase ∈ ({ before.execution.application with current := current } :
      PhaseRuntimeState (serviceGraph setup .concurrent)).phases.head? := installed
  have receipts := (raw.receipts.ordered phase present commitment).congr
    (phase.drain_tables current).1
  refine ⟨receipts, stamp.mono ?_⟩
  intro owner message emitted
  have recalled := (nativeApplication).reaches_recall_prefix nativeInitial implementation.horizon
    implementation.scheduler ((nativeMenu).reaches_raw nativeInitial implementation.horizon
      implementation.scheduler retained.reachesWithin) before reference rfl rfl owner
  obtain ⟨record, member, sent⟩ := List.mem_filterMap.mp emitted
  exact List.mem_filterMap.mpr ⟨record, recalled.subset member, sent⟩

private theorem sourceReplayAssignedActiveRow
    (operational : implementation.Operational)
    (reference : (nativeApplication).Control)
    (trace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some reference))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
      implementation.horizon implementation.scheduler reference trace who event)
    (g : setup.proposalRecoveryProtocol.History)
    (sameInfo : setup.proposalRecoveryModel.infoOf who g.trace =
      setup.proposalRecoveryModel.infoOf who cut.trace)
    (good : setup.proposalRecoveryForeignGood who g)
    (choice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (properChoice : ∀ move, choice.val.map (·.semantic) = some move →
      move.missing = false ∧ ¬ move.action.IsFailure)
    (G : setup.proposalRecoveryProtocol.History)
    (supported : G ∈ (sourceForcedBlock setup values who g choice).support)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (after : (nativeApplication).Control)
    (afterTrace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some after))
    (afterRetained : TracePrefix afterTrace trace)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (remaining : List (RuntimePhase (serviceGraph setup .concurrent))) (generation : Nat)
    (entry current : RecoveryState (serviceGraph setup .concurrent))
    (retired : List (RetiredCommitAttempt (serviceGraph setup .concurrent)))
    (finished : phase.Finished (phase.drain current))
    (normalized : after.execution.application =
      PhaseRuntimeState.settle (phase :: remaining) generation entry current retired)
    (valid : (phase.drain current).native.BindingInvariant)
    (restricted : SourceReplayLostRestricted setup implementation G reference who lost)
    {state : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (checkpoint : RecoverySourceCheckpoint setup .concurrent state)
    (closed : setup.commitRecoveryProtocol.History) {fuel : Nat}
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, checkpoint.trace⟩ closed)
    (instructions : setup.recoveryJointRecall closed.trace =
      (checkpoint.commitInstructionWord (phase.drain current).native).reverse ++
        setup.recoveryJointRecall checkpoint.trace)
    (sourceFinal : setup.proposalRecoveryProtocol.History)
    (closedKept : TracePrefix closed.trace (setup.proposalRecoveryEraseTrace sourceFinal.trace))
    (same : setup.proposalRecoveryModel.infoOf who sourceFinal.trace =
      setup.proposalRecoveryModel.infoOf who g.trace)
    (sourceGood : setup.proposalRecoveryForeignGood who sourceFinal)
    (stamp : BindingStamp (fun owner =>
      (nativeApplication).outputs (reference.execution.recall owner))
        state.attempt (phase.drain current).native)
    (targetBefore targetAfter : CommitRecoveryState setup.program)
    (targetPrior : setup.proposalRecoveryProtocol.Trace (some targetBefore))
    (targetJoint : Player → Option (ProposalRecoveryMove Player L))
    (targetLegal : setup.proposalRecoveryProtocol.Legal (some targetBefore) targetJoint)
    (targetMoved : some targetAfter ∈
      (setup.proposalRecoveryProtocol.step (some targetBefore) ⟨targetJoint, targetLegal⟩).support)
    (targetKept : TracePrefix (targetPrior.extend targetJoint targetLegal targetMoved) g.trace)
    (named : (serviceGraph setup .concurrent).EventId) (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout named = .binding owner payload)
    (eventLower : state.attempt.phase ≤ named.val)
    (position : named.val = instructionCount setup.program -
      ProtocolState.remaining setup.program targetBefore.point)
    (active : owner ∉ targetBefore.excluded)
    (completed : named ∈ (phase.drain current).native.config.cut.completed)
    (lower : checkpoint.trace.length ≤ targetPrior.length)
    (upper : targetPrior.length < closed.trace.length) :
    let data := phaseRecoveryBindingData setup .concurrent named owner payload binding
      ((targetJoint owner).map (·.semantic))
    let assigned := sourceSnapshotState setup implementation G reference lost
      (phase.drain current).native
    (assigned.accepted (.inr named)).elim PublicationResult.failure
        (fun handle => assigned.bindingResult handle payload) = data.1 ∧
      (assigned.accepted (.inr named)).isNone = data.2 ∧
      (⟨.inr named, binding⟩ : FieldRef (serviceGraph setup .concurrent).layout
        (.binding owner payload)).get?
        assigned.config.store = some data.1 := by
  classical
  intro data assigned
  have initialEq : nativeInitial = (setup.initialLaw.map encodeInputs).map
      (PhaseRuntimeState.initial implementation.plan) := by
    simp only [ReservedConcurrentImplementation.initial, PMF.map_comp, Function.comp_def]
  have nativeTrace : (nativeProtocol).Trace (some reference) := by
    rw [initialEq]
    exact trace
  obtain ⟨sourceBefore, sourceAfter, sourcePrior, sourceJoint, sourceLegal, sourceMoved,
      sourceKept, _length, beforeInfo, _afterInfo, _own, sourceSaved, sourceGeneration, physical,
      transported, successful, failed⟩ := sourceReplayPhysicalPairedRow setup checkpoint
    (phase.drain current).native closed path instructions who sourceFinal g closedKept same
      sourceGood good targetBefore targetAfter targetPrior targetJoint targetLegal
        targetMoved targetKept named owner payload binding position lower upper
  have metadata := source_information_metadata setup who ⟨some sourceBefore, sourcePrior⟩
    ⟨some targetBefore, targetPrior⟩ beforeInfo
  have continuation : TracePrefix g.trace G.trace := by
    have support := supported
    unfold sourceForcedBlock at support
    obtain ⟨middle, first, last⟩ := (PMF.mem_support_bind_iff ..).mp support
    exact ((setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ 1
      g middle first).tracePrefix).trans
        ((setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ _
          middle G last).tracePrefix)
  have targetGeneration : targetBefore.generation = state.attempt.generation := by
    rw [← metadata.2.2.2.2]
    simpa only [PhaseRuntimeState.attempt] using sourceGeneration
  have targetSaved : instructionCount setup.program -
      ProtocolState.remaining setup.program targetBefore.saved = state.attempt.phase := by
    rw [← (ProtocolState.MetadataEq.controls setup.program sourceBefore.saved
      targetBefore.saved metadata.2.1).1, sourceSaved, checkpoint.saved_position]
  have readAtFinal (result : PublicationResult (L.Val payload) × Bool)
      (literal : data = result) :
      sourceBindingAt setup state.attempt named owner payload binding G.trace =
        (match result with
        | (.success value, false) => some value
        | _ => none) := by
    have actual := sourceBindingAt_of_origin setup state.attempt named owner payload binding
      targetBefore
      targetPrior targetJoint targetLegal (some targetAfter) targetMoved targetGeneration
        targetSaved position.symm result literal G.trace (targetKept.trans continuation)
    rcases result with ⟨publication, missing⟩
    cases publication <;> cases missing <;> exact actual
  have sourceActive : owner ∉ sourceBefore.excluded := by
    rw [metadata.2.2.1]
    exact active
  have sourcePosition : named.val = instructionCount setup.program -
      ProtocolState.remaining setup.program sourceBefore.point := by
    rw [(ProtocolState.MetadataEq.controls setup.program sourceBefore.point
      targetBefore.point metadata.1).1]
    exact position
  cases accepted : (phase.drain current).native.accepted (.inr named) with
  | none =>
    have targetData := transported sourceActive
    change data = _ at targetData
    simp only [accepted, Option.isNone_none, ↓reduceIte] at targetData
    have head := sourceReplayUnacceptedRow setup implementation G reference lost
      (phase.drain current).native named owner payload binding valid completed accepted
    rw [targetData]
    exact ⟨by rw [head.1]; rfl, by rw [head.1]; rfl, head.2⟩
  | some handle =>
    cases originalResult : (phase.drain current).native.bindingResult handle payload with
    | failure =>
      have sourceRow := physical sourceActive
      simp only [accepted, Option.elim_some, originalResult, Option.isNone_some] at sourceRow
      obtain ⟨targetData, _absentAtRequest⟩ := failed sourceActive sourceRow
      change data = _ at targetData
      have absent := readAtFinal (.failure, false) targetData
      have sourceRetained : owner ∉ sourceAfter.excluded := by
        intro excluded
        have missing := (source_binding_missing_iff setup sourceBefore sourceAfter sourceJoint
          sourceLegal sourceMoved owner named payload binding sourcePosition sourceActive).mpr
            excluded
        rw [sourceRow] at missing
        cases missing
      have focal : owner = who := by
        by_contra foreign
        obtain ⟨value, proper⟩ := source_foreign_binding_success setup who owner foreign named
          payload binding sourceBefore sourcePrior sourceJoint sourceLegal sourceAfter sourceMoved
            sourcePosition sourceActive sourceRetained
              (source_good_prefix setup who _ sourceFinal.trace sourceKept sourceGood)
        rw [sourceRow] at proper
        cases proper
      have owned : handle.1 = owner := by
        obtain ⟨_payload, typed⟩ := valid.accepted_typed (.inr named) handle accepted
        exact (EventField.binding.inj (typed.symm.trans binding)).1
      have noLost : lost handle = none := by
        cases drawn : lost handle with
        | none => rfl
        | some raw => exact ((restricted handle raw drawn).1 (owned.trans focal)).elim
      have noMeaning := sourceReplayStampedFailure setup implementation reference nativeTrace G
        state.attempt (phase.drain current).native stamp named owner payload binding handle
          eventLower accepted absent
      have unchanged : sourceHandlePairs setup implementation G reference lost handle = none := by
        unfold sourceHandlePairs
        cases reference.execution.application.current.native.candidates.lookup handle <;>
          simp only [noMeaning, noLost, Option.orElse_none, Option.map_none]
      have head := sourceReplayAcceptedFailureRow setup implementation G reference lost
        (phase.drain current).native named owner payload binding handle accepted originalResult
          unchanged valid completed
      simpa only [targetData] using head
    | success old =>
      have sourceRow := physical sourceActive
      simp only [accepted, Option.elim_some, originalResult, Option.isNone_some] at sourceRow
      obtain ⟨value, _readAtRequest, targetData⟩ := successful sourceActive old sourceRow
      change data = _ at targetData
      have read := readAtFinal (.success value, false) targetData
      have castSome {A B : Type} (same : A = B) (item : A) :
          cast (congrArg Option same) (some item) = some (cast same item) := by
        cases same
        rfl
      have typed := valid.binding_read (⟨.inr named, binding⟩ :
        FieldRef (serviceGraph setup .concurrent).layout (.binding owner payload)) named rfl
          completed
      simp only [accepted, Option.elim_some, originalResult] at typed
      have rawRead := congrArg
        (cast (congrArg (fun kind : EventField Player L => Option kind.Value) binding.symm)) typed
      have stored : (phase.drain current).native.config.store (.inr named) =
          some (cast (congrArg EventField.Value binding.symm) (.success old)) := by
        have rawEq : (phase.drain current).native.config.store (.inr named) =
            cast (congrArg Option (congrArg EventField.Value binding.symm))
              (some (.success old)) := by
          simpa only [FieldRef.get?, cast_cast, cast_eq] using rawRead
        exact rawEq.trans (castSome (congrArg EventField.Value binding.symm) (.success old))
      obtain ⟨next, meaning, assignedStore, assignedResult, _ownValue⟩ :=
        assigned_completed_binding_read setup values implementation operational reference trace who
          event cut g sameInfo good choice properChoice G supported lost after afterTrace
            afterRetained phase remaining generation entry current retired finished normalized
              valid owner payload named binding handle old accepted stored
      have head := sourceReplayAcceptedRow setup implementation reference nativeTrace G lost
        state.attempt (phase.drain current).native stamp named owner payload binding handle
          eventLower accepted next meaning assignedStore assignedResult value read
      simpa only [targetData] using head

omit [Fintype Player] in
private theorem sourceReplayCompiledHeadData
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (name : VarId) (owner : Player) (payload : L.Ty)
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (rest : SourceProgram.CommitPrefix
      ((name, .commitment owner payload) :: Γ) (insert name O) Δ P)
    (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix))
    (actions : ∀ index action,
      decodeEventAction setup.program (embedding.event index) action =
        decodeEventAction
          ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix) index
          (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (choice : PublicationResult (L.Val payload)) (missed : Bool)
    (missingFailure : missed = true → choice = .failure)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (semantic : SourceProgram.Setup.proposalRecoveryJoint joint = fun player =>
      if player = owner then some ⟨OwnAction.commit owner name payload choice, missed⟩ else none) :
    let index : Fin (eventCount
      ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix)) :=
        ⟨0, by simp only [SourceProgram.CommitPrefix.prepend, eventCount]; omega⟩
    let named := embedding.event index
    ∀ binding : (serviceGraph setup .concurrent).outputLayout named = .binding owner payload,
      phaseRecoveryBindingData setup .concurrent named owner payload binding
        ((joint owner).map (·.semantic)) = (choice, missed) := by
  classical
  intro index named binding
  have own := congrFun semantic owner
  change (joint owner).map ProposalRecoveryMove.semantic =
    (if owner = owner then some ⟨OwnAction.commit owner name payload choice, missed⟩ else none)
      at own
  simp only [ite_true] at own
  let encoded := cast (congrArg EventField.Action binding.symm) choice
  have decoded : decodeEventAction setup.program named encoded =
      some (OwnAction.commit owner name payload choice) := by
    rw [actions]
    simp only [encoded, index, named, SourceProgram.CommitPrefix.prepend, decodeEventAction,
      Fin.mk_zero, Fin.cases_zero, cast_cast, cast_eq]
  have encoding := encodeEventAction?_decodeEventAction_eq_some setup.program named encoded
    (OwnAction.commit owner name payload choice) decoded
  cases missed with
  | false =>
    simp only [phaseRecoveryBindingData, own, Option.elim_some, Bool.false_eq_true, ↓reduceIte,
      Option.bind_some, encoding, Option.map_some, Option.getD_some, encoded, cast_cast, cast_eq]
  | true =>
    simp only [phaseRecoveryBindingData, own, Option.elim_some, ↓reduceIte, missingFailure rfl]

private theorem sourceReplayTargetTableReads
    (operational : implementation.Operational)
    (reference : (nativeApplication).Control)
    (trace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some reference))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
      implementation.horizon implementation.scheduler reference trace who event)
    (g : setup.proposalRecoveryProtocol.History)
    (sameInfo : setup.proposalRecoveryModel.infoOf who g.trace =
      setup.proposalRecoveryModel.infoOf who cut.trace)
    (good : setup.proposalRecoveryForeignGood who g)
    (choice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (properChoice : ∀ move, choice.val.map (·.semantic) = some move →
      move.missing = false ∧ ¬ move.action.IsFailure)
    (G : setup.proposalRecoveryProtocol.History)
    (supported : G ∈ (sourceForcedBlock setup values who g choice).support)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (after : (nativeApplication).Control)
    (afterTrace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some after))
    (afterRetained : TracePrefix afterTrace trace)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (remaining : List (RuntimePhase (serviceGraph setup .concurrent))) (generation : Nat)
    (entry current : RecoveryState (serviceGraph setup .concurrent))
    (retired : List (RetiredCommitAttempt (serviceGraph setup .concurrent)))
    (finished : phase.Finished (phase.drain current))
    (normalized : after.execution.application =
      PhaseRuntimeState.settle (phase :: remaining) generation entry current retired)
    (valid : (phase.drain current).native.BindingInvariant)
    (restricted : SourceReplayLostRestricted setup implementation G reference who lost)
    {state : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (checkpoint : RecoverySourceCheckpoint setup .concurrent state)
    (closed : setup.commitRecoveryProtocol.History) {fuel : Nat}
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, checkpoint.trace⟩ closed)
    (instructions : setup.recoveryJointRecall closed.trace =
      (checkpoint.commitInstructionWord (phase.drain current).native).reverse ++
        setup.recoveryJointRecall checkpoint.trace)
    (sourceFinal : setup.proposalRecoveryProtocol.History)
    (closedKept : TracePrefix closed.trace (setup.proposalRecoveryEraseTrace sourceFinal.trace))
    (same : setup.proposalRecoveryModel.infoOf who sourceFinal.trace =
      setup.proposalRecoveryModel.infoOf who g.trace)
    (sourceGood : setup.proposalRecoveryForeignGood who sourceFinal)
    (stamp : BindingStamp (fun owner =>
      (nativeApplication).outputs (reference.execution.recall owner))
        state.attempt (phase.drain current).native)
    (phaseLow : phase.low = state.attempt.phase) :
    ∀ {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
      {block : SourceProgram.CommitPrefix Γ O Δ P}
      {targetEntry : SourceProgram.Config Player L Γ} {excluded : Finset Player}
      {result : SourceProgram.Config Player L Δ} {finalExcluded : Finset Player}
      (attempt : block.Attempt targetEntry excluded result finalExcluded)
      (suffix : SourceProgram Player L Δ P)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (block.prepend suffix))
      (_actions : ∀ index action,
        decodeEventAction setup.program (embedding.event index) action =
          decodeEventAction (block.prepend suffix) index
            (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
      (low : Nat)
      (_ranking : ∀ index, (embedding.event index).val = low + index.val)
      (_clock : low + instructionCount (block.prepend suffix) = instructionCount setup.program)
      (_interval : ∀ index, index.val < block.length → embedding.event index ∈ phase.events)
      (lift : ProtocolState (block.prepend suffix) → ProtocolState setup.program)
      (_origin : ProtocolSuffix setup.program (block.prepend suffix) lift)
      (start : CommitRecoveryState setup.program)
      (prior : setup.proposalRecoveryProtocol.Trace (some start))
      (targetEnd : setup.proposalRecoveryProtocol.History)
      (_endKept : TracePrefix targetEnd.trace g.trace)
      (_retained : TracePrefix prior targetEnd.trace)
      (_point : start.point = lift (ProtocolState.entry (block.prepend suffix) targetEntry))
      (_mask : start.excluded = excluded)
      (_saved : ProtocolState.atCommit setup.program start.saved = true)
      (_endpoint : ProtocolState.commitEnd setup.program start.saved ≤ instructionCount suffix)
      (_word : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace targetEnd.trace) =
        attempt.joints.reverse ++
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace prior))
      (_lower : checkpoint.trace.length ≤ prior.length)
      (_upper : prior.length + block.length ≤ closed.trace.length)
      (_receipts : BindingReceiptOrder low excluded (phase.drain current).native.accepted),
      sourceAttemptTableReads setup attempt suffix embedding
        (sourceSnapshotState setup implementation G reference lost
          (phase.drain current).native) := by
  classical
  intro Γ Δ O P block targetEntry excluded result finalExcluded attempt
  induction attempt with
  | nil => intros; trivial
  | @active Γ Δ O P name owner payload fresh guard rest targetEntry excluded result finalExcluded
      active resultChoice missed missing later ih =>
    intro suffix embedding actions low ranking clock interval lift origin start prior targetEnd
      endKept retained point mask saved endpoint word lower upper receipts
    let index : Fin (eventCount
        ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix)) :=
      ⟨0, by simp only [SourceProgram.CommitPrefix.prepend, eventCount]; omega⟩
    let named := embedding.event index
    have binding : (serviceGraph setup .concurrent).outputLayout named =
        .binding owner payload := by
      change outputLayout setup.program named = .binding owner payload
      simpa only [named, index, SourceProgram.CommitPrefix.prepend, outputLayout,
        Fin.mk_zero, Fin.cases_zero] using embedding.layout_eq index
    have eventRank : named.val = low := by
      simpa only [named, index, Nat.add_zero] using ranking index
    have inside : named ∈ phase.events := interval index (by
      simp only [index, SourceProgram.CommitPrefix.length]; omega)
    have completed := finished inside
    have eventLower : state.attempt.phase ≤ named.val := by
      rw [← phaseLow]
      exact ((phase.mem_events named).mp inside).1
    have position : named.val = instructionCount setup.program -
        ProtocolState.remaining setup.program start.point := by
      rw [point, origin.remaining_lift, ProtocolState.remaining_entry, eventRank]
      omega
    have committing : ProtocolState.atCommit setup.program start.point = true := by
      rw [point, origin.atCommit_lift]
      rfl
    have within : named.val < instructionCount setup.program -
        ProtocolState.commitEnd setup.program start.saved := by
      simp only [SourceProgram.CommitPrefix.prepend, instructionCount,
        rest.instructionCount_prepend] at clock
      omega
    obtain ⟨next, joint, legal, moved, rowKept, semantic, _rank⟩ := sourceReplayHeadRow setup start
      prior committing targetEnd retained _ word (by
        simp only [SourceProgram.CommitPrefix.Attempt.joints, List.length_cons]; omega)
          named.val position within
    have canonical : SourceProgram.Setup.proposalRecoveryJoint joint = fun player =>
        if player = owner then some ⟨OwnAction.commit owner name payload resultChoice, missed⟩
          else none := by
      simpa only [SourceProgram.CommitPrefix.Attempt.joints, List.getElem_cons_zero] using semantic
    have read := sourceReplayCompiledHeadData setup name owner payload fresh guard rest suffix
      embedding actions resultChoice missed missing joint canonical binding
    have targetActive : owner ∉ start.excluded := by rwa [mask]
    have head := sourceReplayAssignedActiveRow setup values implementation operational reference
      trace who event cut g sameInfo good choice properChoice G supported lost after afterTrace
        afterRetained phase remaining generation entry current retired finished normalized valid
          restricted checkpoint closed path instructions sourceFinal closedKept same sourceGood
            stamp start next prior joint legal moved (rowKept.trans endKept) named owner
              payload binding eventLower position targetActive completed lower (by
                simp only [SourceProgram.CommitPrefix.length] at upper; omega)
    rw [read] at head
    have tailReads : sourceAttemptTableReads setup later suffix
        (embedding.tail (rest.prepend suffix) (by
          simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl))
        (sourceSnapshotState setup implementation G reference lost
          (phase.drain current).native) := by
      by_cases nonfinal : 0 < rest.length
      · obtain ⟨nextActual, nextJoint, nextLegal, nextMoved, nextKept, nextPoint, nextMask,
          nextSaved, _nextGeneration, nextSemantic⟩ := sourceReplayActiveHeadStep setup active
            resultChoice missed missing later suffix lift origin start prior targetEnd point mask
              saved endpoint retained word nonfinal
        have nextWord := sourceReplayTailWord setup targetEnd start prior nextActual nextJoint
          nextLegal nextMoved _ later.joints nextSemantic word
        have tailReceipts : BindingReceiptOrder (low + 1)
            (excludeCommit excluded owner missed) (phase.drain current).native.accepted := by
          have missedEq : ((phase.drain current).native.accepted (.inr named)).isNone = missed := by
            simpa only [sourceSnapshotState, State.swap_accepted] using head.2.1
          cases missed with
          | false =>
            simpa only [excludeCommit, Bool.false_eq_true, ↓reduceIte] using
              receipts.raise_low (show low ≤ low + 1 by omega)
          | true =>
            have absent : (phase.drain current).native.accepted (.inr named) = none := by
              cases accepted : (phase.drain current).native.accepted (.inr named) with
              | none => rfl
              | some handle =>
                simp only [accepted, Option.isNone_some] at missedEq
                cases missedEq
            simpa only [excludeCommit, ↓reduceIte] using receipts.after_missing named eventRank
              owner payload binding absent
        apply ih suffix _ (fun index action => ?_) (low + 1) (fun index => ?_) (by
          simp only [SourceProgram.CommitPrefix.prepend, instructionCount] at clock ⊢; omega)
          (fun index bound => ?_) (fun point => lift (.inr point))
          (ProtocolSuffix.commitTail fresh guard (rest.prepend suffix) origin) nextActual
          (prior.extend nextJoint nextLegal nextMoved) targetEnd endKept nextKept nextPoint nextMask
          (by rw [nextSaved]; exact saved) (by rw [nextSaved]; exact endpoint) nextWord
          (by simp only [Trace.length]; omega)
          (by simp only [Trace.length, SourceProgram.CommitPrefix.length] at upper ⊢; omega)
          tailReceipts
        · simpa only [OutputEmbedding.tail, Fin.cast_eq_self, SourceProgram.CommitPrefix.prepend,
            decodeEventAction, Fin.cases_succ] using actions index.succ action
        · have rank := ranking index.succ
          dsimp only [OutputEmbedding.tail] at rank ⊢
          simp only [Fin.cast_eq_self, Fin.val_succ] at rank ⊢
          omega
        · simpa only [OutputEmbedding.tail, Fin.cast_eq_self] using interval index.succ (by
            simp only [Fin.val_succ, SourceProgram.CommitPrefix.length]; omega)
      · cases rest with
        | nil => cases later; trivial
        | commit => simp only [SourceProgram.CommitPrefix.length] at nonfinal; omega
    exact ⟨head.1, head.2.1, head.2.2, tailReads⟩
  | @excluded Γ Δ O P name owner payload fresh guard rest targetEntry excluded result
      finalExcluded inactive later ih =>
    intro suffix embedding actions low ranking clock interval lift origin start prior targetEnd
      endKept retained point mask saved endpoint word lower upper receipts
    let index : Fin (eventCount
        ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix)) :=
      ⟨0, by simp only [SourceProgram.CommitPrefix.prepend, eventCount]; omega⟩
    let named := embedding.event index
    have binding : (serviceGraph setup .concurrent).outputLayout named =
        .binding owner payload := by
      change outputLayout setup.program named = .binding owner payload
      simpa only [named, index, SourceProgram.CommitPrefix.prepend, outputLayout,
        Fin.mk_zero, Fin.cases_zero] using embedding.layout_eq index
    have eventRank : named.val = low := by
      simpa only [named, index, Nat.add_zero] using ranking index
    have inside : named ∈ phase.events := interval index (by
      simp only [index, SourceProgram.CommitPrefix.length]; omega)
    have head := sourceReplayInheritedRow setup implementation G reference lost
      (phase.drain current).native named owner payload binding valid (finished inside) low excluded
        receipts eventRank.ge inactive
    have tailReads : sourceAttemptTableReads setup later suffix
        (embedding.tail (rest.prepend suffix) (by
          simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl))
        (sourceSnapshotState setup implementation G reference lost
          (phase.drain current).native) := by
      by_cases nonfinal : 0 < rest.length
      · obtain ⟨next, joint, legal, moved, rowKept, nextPoint, nextMask, nextSaved,
          _nextGeneration, semantic⟩ := sourceReplayExcludedHeadStep setup inactive later suffix
            lift origin start prior targetEnd point mask saved endpoint retained word nonfinal
        have nextWord := sourceReplayTailWord setup targetEnd start prior next joint legal moved
          _ later.joints semantic word
        apply ih suffix _ (fun index action => ?_) (low + 1) (fun index => ?_) (by
          simp only [SourceProgram.CommitPrefix.prepend, instructionCount] at clock ⊢; omega)
          (fun index bound => ?_) (fun point => lift (.inr point))
          (ProtocolSuffix.commitTail fresh guard (rest.prepend suffix) origin) next
          (prior.extend joint legal moved) targetEnd endKept rowKept nextPoint nextMask
          (by rw [nextSaved]; exact saved) (by rw [nextSaved]; exact endpoint) nextWord
          (by simp only [Trace.length]; omega)
          (by simp only [Trace.length, SourceProgram.CommitPrefix.length] at upper ⊢; omega)
          (receipts.raise_low (show low ≤ low + 1 by omega))
        · simpa only [OutputEmbedding.tail, Fin.cast_eq_self, SourceProgram.CommitPrefix.prepend,
            decodeEventAction, Fin.cases_succ] using actions index.succ action
        · have rank := ranking index.succ
          dsimp only [OutputEmbedding.tail] at rank ⊢
          simp only [Fin.cast_eq_self, Fin.val_succ] at rank ⊢
          omega
        · simpa only [OutputEmbedding.tail, Fin.cast_eq_self] using interval index.succ (by
            simp only [Fin.val_succ, SourceProgram.CommitPrefix.length]; omega)
      · cases rest with
        | nil => cases later; trivial
        | commit => simp only [SourceProgram.CommitPrefix.length] at nonfinal; omega
    exact ⟨head, tailReads⟩

theorem sourceReplayFixedSnapshotTableReads
    (operational : implementation.Operational)
    (reference : (nativeApplication).Control)
    (trace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some reference))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
      implementation.horizon implementation.scheduler reference trace who event)
    (g : setup.proposalRecoveryProtocol.History)
    (sameInfo : setup.proposalRecoveryModel.infoOf who g.trace =
      setup.proposalRecoveryModel.infoOf who cut.trace)
    (good : setup.proposalRecoveryForeignGood who g)
    (choice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (properChoice : ∀ move, choice.val.map (·.semantic) = some move →
      move.missing = false ∧ ¬ move.action.IsFailure)
    (G : setup.proposalRecoveryProtocol.History)
    (supported : G ∈ (sourceForcedBlock setup values who g choice).support)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (after : (nativeApplication).Control)
    (afterTrace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some after))
    (afterRetained : TracePrefix afterTrace trace)
    (before : (nativeApplication).Control)
    (beforeTrace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some before))
    (beforeRetained : TracePrefix beforeTrace trace)
    (witness : RecoverySourceWitness setup .concurrent implementation.plan
      before.execution.application)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (remaining : List (RuntimePhase (serviceGraph setup .concurrent)))
    (installed : before.execution.application.phases = phase :: remaining)
    (commitment : phase.kind = .commitment)
    (current : RecoveryState (serviceGraph setup .concurrent))
    (finished : phase.Finished (phase.drain current))
    (normalized : after.execution.application = PhaseRuntimeState.settle (phase :: remaining)
      before.execution.application.generation before.execution.application.entry current
        before.execution.application.retired)
    (valid : (phase.drain current).native.BindingInvariant)
    (effect : PhaseClosingEffect implementation.runtime implementation.leaks
      before.execution after.execution current)
    (changed : after.execution.application.attempt ≠ before.execution.application.attempt)
    (rawStamp : BindingStamp (fun owner =>
      (nativeApplication).outputs (before.execution.recall owner))
        before.execution.application.attempt (phase.drain current).native)
    (restricted : SourceReplayLostRestricted setup implementation G reference who lost)
    (checkpoint : RecoverySourceCheckpoint setup .concurrent before.execution.application)
    (closed : setup.commitRecoveryProtocol.History) {fuel : Nat}
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, checkpoint.trace⟩ closed)
    (instructions : setup.recoveryJointRecall closed.trace =
      (checkpoint.commitInstructionWord (phase.drain current).native).reverse ++
        setup.recoveryJointRecall checkpoint.trace)
    (sourceFinal : setup.proposalRecoveryProtocol.History)
    (closedKept : TracePrefix closed.trace (setup.proposalRecoveryEraseTrace sourceFinal.trace))
    (same : setup.proposalRecoveryModel.infoOf who sourceFinal.trace =
      setup.proposalRecoveryModel.infoOf who g.trace)
    (sourceGood : setup.proposalRecoveryForeignGood who sourceFinal) :
    match SourceProgram.commitPhase checkpoint.residual.tail with
    | ⟨Δ, _P, suffix, block, reconstruct, _⟩ =>
      let embedding := cast (congrArg (fun program => OutputEmbedding
        (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
          checkpoint.embedding
      ∀ (targetEntry : SourceProgram.Config Player L checkpoint.residual.context)
        (start : CommitRecoveryState setup.program)
        (prior : setup.proposalRecoveryProtocol.Trace (some start))
        (result : SourceProgram.Config Player L Δ) (finalExcluded : Finset Player)
        (attempt : block.Attempt targetEntry start.excluded result finalExcluded)
        (targetEnd : setup.proposalRecoveryProtocol.History)
        (_endKept : TracePrefix targetEnd.trace g.trace)
        (_retained : TracePrefix prior targetEnd.trace)
        (_point : start.point = checkpoint.residual.lift
          (cast (congrArg ProtocolState reconstruct)
            (ProtocolState.entry (block.prepend suffix) targetEntry)))
        (_mask : start.excluded = before.execution.application.entry.excluded)
        (_saved : ProtocolState.atCommit setup.program start.saved = true)
        (_endpoint : ProtocolState.commitEnd setup.program start.saved ≤ instructionCount suffix)
        (_word : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace targetEnd.trace) =
          attempt.joints.reverse ++
            setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace prior))
        (_lower : checkpoint.trace.length ≤ prior.length)
        (_upper : prior.length + block.length ≤ closed.trace.length),
        sourceAttemptTableReads setup attempt suffix embedding
          (sourceSnapshotState setup implementation G reference lost
            (phase.drain current).native) := by
  classical
  have initialEq : nativeInitial = (setup.initialLaw.map encodeInputs).map
      (PhaseRuntimeState.initial implementation.plan) := by
    simp only [ReservedConcurrentImplementation.initial, PMF.map_comp, Function.comp_def]
  obtain ⟨referenceNative, beforeNative, nativeKept⟩ :
      ∃ (referenceNative : (nativeProtocol).Trace (some reference))
        (beforeNative : (nativeProtocol).Trace (some before)),
        TracePrefix beforeNative referenceNative := by
    rw [initialEq]
    exact ⟨trace, beforeTrace, beforeRetained⟩
  have present : phase ∈ before.execution.application.phases.head? := by
    simp only [installed, List.head?_cons, Option.mem_some_iff]
  obtain ⟨receipts, stamp⟩ := sourceReplayCloseEvidence setup implementation reference before after
    referenceNative beforeNative nativeKept witness phase present commitment current effect changed
      rawStamp
  have phaseLow : phase.low = before.execution.application.attempt.phase := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have geometry := checkpoint.commit_phase_geometry phase remaining installed commitment
    witness.order.frontier (operational.maximalPhases.suffix witness.suffix)
  have table := fun {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
      {block : SourceProgram.CommitPrefix Γ O Δ P}
      {targetEntry : SourceProgram.Config Player L Γ} {excluded : Finset Player}
      {result : SourceProgram.Config Player L Δ} {finalExcluded : Finset Player}
      (attempt : block.Attempt targetEntry excluded result finalExcluded) =>
    sourceReplayTargetTableReads setup values implementation operational reference trace who event
      cut g sameInfo good choice properChoice G supported lost after afterTrace afterRetained phase
        remaining before.execution.application.generation before.execution.application.entry current
          before.execution.application.retired finished normalized valid restricted checkpoint
            closed path instructions sourceFinal closedKept same sourceGood stamp
              phaseLow attempt
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, beforeRefs,
    compiled, alignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, histories, memories, steps, menus, readout, checkpointTrace, views,
    historyAlignment, origin⟩
  dsimp only at geometry table ⊢
  generalize decomposition : SourceProgram.commitPhase program = segment at geometry ⊢
  rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
  subst program
  dsimp only [cast_eq] at geometry ⊢
  intro targetEntry start prior result finalExcluded attempt targetEnd endKept retained point mask
    saved endpoint word lower upper
  have clock : before.execution.application.attempt.phase +
      instructionCount (block.prepend suffix) = instructionCount setup.program := by
    simpa only [eventCount_eq_instructionCount] using compiled.countEq
  apply table attempt suffix embedding views.actionEq before.execution.application.attempt.phase
    compiled.rankEq clock geometry.2 lift origin start prior targetEnd endKept retained point rfl
      saved endpoint word lower upper
  simpa only [phaseLow, mask] using receipts

structure SourceReplayImage
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some reference))
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (who : Player) (before : (nativeApplication).Control) : Prop where
  handling : ∀ id message, before.execution.network.lookup id = some message →
    (nativeApplication).handle
        (sourceSnapshotAssignment setup implementation target reference lost
          before.execution.application) message =
      ((nativeApplication).handle before.execution.application message).map
        (sourceSnapshotAssignment setup implementation target reference lost)
  openingFixed : ∀ (message : Message Player
      (CommitAttemptPacket (serviceGraph setup .concurrent)))
      (event : (serviceGraph setup .concurrent).EventId)
      (handle : Handle (serviceGraph setup .concurrent)) (raw : Raw L),
      before.execution.network.lookup message.id = some message →
      message.payload.packet.call = .opening event handle raw →
      (message.payload.tokenValid before.execution.application.attempt &&
        before.execution.application.allows message.payload.packet.call &&
        !before.execution.application.current.excludedCall message.payload.packet.call) = true →
      before.execution.application.current.native.config.cut.Ready event →
      RevealFixed (HiddenSwap.ofPairs
        (sourceSnapshotPairs setup implementation target reference lost
          before.execution.application.current.native)
        (sourceHandlePairs setup implementation target reference lost))
          before.execution.application.current.native event
  focalView : ∀ recalls : Player → List (nativeApplication).PlayerEntry,
      recalls who = before.execution.recall who →
      (sourceReplayExecution setup implementation target reference lost recalls
        before.execution).observe nativeApplication who =
          before.execution.observe nativeApplication who
  focalAction : ∀ (prior : (nativeProtocol).Trace (some before))
      (after : (nativeProtocol).State)
      (joint : Player → Option (nativeApplication).Action)
      (legal : (nativeProtocol).Legal (some before) joint)
      (moved : after ∈ ((nativeProtocol).step (some before) ⟨joint, legal⟩).support)
      (_kept : TracePrefix (prior.extend joint legal moved) trace)
      (action : (nativeApplication).Action),
      before.actor = some who → joint who = some action →
      (HiddenSwap.ofPairs
        (sourceSnapshotPairs setup implementation target reference lost
          before.execution.application.current.native)
        (sourceHandlePairs setup implementation target reference lost)).phaseAction action = action
  query : ∀ (actual : (nativeApplication).Control)
      (_actualTrace : (nativeProtocol).Trace (some actual))
      (owner : Player) (_foreign : owner ≠ who)
      (event : (serviceGraph setup .concurrent).EventId)
      (payload : L.Ty),
      (serviceGraph setup .concurrent).outputLayout event = .binding owner payload →
      actual.actor = some owner →
      actual.execution.application = sourceSnapshotAssignment setup implementation
        target reference lost before.execution.application →
      actual.execution.network = before.execution.network →
      actual.execution.receipts = before.execution.receipts →
      actual.execution.environmentRecall = before.execution.environmentRecall →
      actual.execution.recall who = before.execution.recall who →
      actual.execution.application.SeedRequest owner
        ⟨actual.execution.application.attempt, event⟩ →
      ∃ (current : CommitRecoveryState setup.program)
        (prior : setup.proposalRecoveryProtocol.Trace (some current)),
        TracePrefix prior target.trace ∧
        event.val = instructionCount setup.program -
          ProtocolState.remaining setup.program current.point ∧
        current.generation = before.execution.application.generation ∧
        instructionCount setup.program -
          ProtocolState.remaining setup.program current.saved =
            before.execution.application.attempt.phase ∧
        owner ∉ current.excluded ∧
        phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
            implementation.plan owner event (actual.execution.recall owner)
              (actual.execution.observe nativeApplication owner) =
          some (setup.proposalRecoveryQuery owner
            (setup.proposalRecoveryModel.infoOf owner prior))

/- The simultaneous source image consumed by literal raw replay. Every image
uses the same completed target and reference checkpoint; auxiliary values may
be assigned only to factual, signed, historically unaccepted preparations. -/
structure SourceReplayAlignment
    (operational : implementation.Operational)
    (who : Player)
    (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (event : (serviceGraph setup .concurrent).EventId)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
      implementation.horizon implementation.scheduler reference
      (sourceCutTrace setup implementation referenceTrace) who event)
    (g : setup.proposalRecoveryProtocol.History)
    (choice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent)) where
  canonical : (⟨some cut.cursor.current, cut.cursor.trace⟩ :
    setup.proposalRecoveryProtocol.History) =
      canonicalSource setup implementation operational
        ⟨some reference, referenceTrace⟩
  sameInfo : setup.proposalRecoveryModel.infoOf who g.trace =
    setup.proposalRecoveryModel.infoOf who cut.trace
  cutGood : setup.proposalRecoveryForeignGood who ⟨some cut.current, cut.trace⟩
  good : setup.proposalRecoveryForeignGood who g
  properChoice : ∀ move, choice.val.map (·.semantic) = some move →
    move.missing = false ∧ ¬ move.action.IsFailure
  supported : (⟨some targetCurrent, targetTrace⟩ :
    setup.proposalRecoveryProtocol.History) ∈
      (sourceForcedBlock setup values who g choice).support
  selectedAgreement : ∀ lost, SourceReplayLostRestricted setup implementation
      ⟨some targetCurrent, targetTrace⟩ reference who lost →
    ∀ (before : (nativeApplication).Control)
      (prior : (nativeProtocol).Trace (some before)),
      TracePrefix prior referenceTrace →
      let selected := (checkpointSelection setup implementation operational prior).val.checkpoint
      ∃ (mapped : setup.proposalRecoveryProtocol.History)
        (current : CommitRecoveryState setup.program)
        (live saved : SourceProgram.Config Player L selected.residual.context),
        TracePrefix mapped.trace g.trace ∧
        TracePrefix mapped.trace targetTrace ∧
        mapped.trace.length = selected.trace.length ∧
        setup.proposalRecoveryModel.infoOf who mapped.trace =
          setup.proposalRecoveryModel.infoOf who
            (setup.proposalRecoveryLiftTrace
              (nativeArchiveLabels setup
                (PhaseProposal.sourceArchive reference.execution.network.inputs))
              selected.trace) ∧
        mapped.state = some current ∧
        current.point = selected.residual.lift
          (ProtocolState.entry selected.residual.tail live) ∧
        current.saved = selected.residual.lift
          (ProtocolState.entry selected.residual.tail saved) ∧
        current.excluded = before.execution.application.entry.excluded ∧
        current.generation = before.execution.application.generation ∧
        selected.refs.Agrees saved.state
          (sourceSnapshotState setup implementation
            ⟨some targetCurrent, targetTrace⟩ reference lost
              before.execution.application.entry.native).config.store
  completedVisit : ∀ lost, SourceReplayLostRestricted setup implementation
      ⟨some targetCurrent, targetTrace⟩ reference who lost →
    ∀ (before after : (nativeApplication).Control)
      (prior : (nativeProtocol).Trace (some before))
      (afterTrace : (nativeProtocol).Trace (some after)),
      TracePrefix prior afterTrace → TracePrefix afterTrace referenceTrace →
    ∀ (phase : RuntimePhase (serviceGraph setup .concurrent))
      (remaining : List (RuntimePhase (serviceGraph setup .concurrent))),
      before.execution.application.phases = phase :: remaining →
    ∀ (physical : RecoveryState (serviceGraph setup .concurrent)),
      after.execution.application =
        ({ before.execution.application with current := physical } :
          PhaseRuntimeState (serviceGraph setup .concurrent)).normalize →
      phase.Finished (phase.drain physical) → phase.kind = .commitment →
      PhaseClosingEffect implementation.runtime implementation.leaks
        before.execution after.execution physical →
      after.execution.application.attempt ≠ before.execution.application.attempt →
      (phase.drain physical).native.BindingInvariant →
      BindingStamp (fun owner => (nativeApplication).outputs
        (before.execution.recall owner)) before.execution.application.attempt
          (phase.drain physical).native →
      let first := (checkpointSelection setup implementation operational prior).val.checkpoint
      let last := (checkpointSelection setup implementation operational afterTrace).val.checkpoint
      let segment := SourceProgram.commitPhase first.residual.tail
      let embedding := cast (congrArg (fun program => OutputEmbedding
        (inputLayout setup.context) (outputLayout setup.program) program)
          segment.reconstruct.symm) first.embedding
      ∃ (sourceLast : CommitRecoveryState setup.program)
        (closed : setup.commitRecoveryProtocol.Trace (some sourceLast))
        (labeled : setup.proposalRecoveryProtocol.Trace (some sourceLast))
        (fuel : Nat)
        (targetFirst targetLast : CommitRecoveryState setup.program)
        (targetPrior : setup.proposalRecoveryProtocol.Trace (some targetFirst))
        (targetEnd : setup.proposalRecoveryProtocol.Trace (some targetLast))
        (targetEntry : SourceProgram.Config Player L first.residual.context)
        (finished : SourceProgram.Config Player L segment.context)
        (excluded : Finset Player)
        (attempt : segment.block.Attempt targetEntry targetFirst.excluded
          finished excluded)
        (monotone : targetFirst.excluded ⊆ excluded),
        setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, first.trace⟩
          ⟨some sourceLast, closed⟩ ∧
        setup.recoveryJointRecall closed =
          (first.commitInstructionWord (phase.drain physical).native).reverse ++
            setup.recoveryJointRecall first.trace ∧
        TracePrefix closed last.trace ∧
        TracePrefix labeled
          (canonicalSource setup implementation operational
            ⟨some reference, referenceTrace⟩).trace ∧
        setup.proposalRecoveryEraseTrace labeled = closed ∧
        TracePrefix targetPrior targetEnd ∧
        TracePrefix targetEnd g.trace ∧
        TracePrefix targetEnd targetTrace ∧
        targetPrior.length = first.trace.length ∧
        targetEnd.length = closed.length ∧
        targetFirst.point = first.residual.lift
          (cast (congrArg ProtocolState segment.reconstruct)
            (ProtocolState.entry (segment.block.prepend segment.suffix) targetEntry)) ∧
        ProtocolState.atCommit setup.program targetFirst.saved = true ∧
        ProtocolState.commitEnd setup.program targetFirst.saved ≤
          instructionCount segment.suffix ∧
        setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace targetEnd) =
          attempt.joints.reverse ++
            setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace targetPrior) ∧
        targetLast = (targetFirst.install
          (first.residual.lift
            (cast (congrArg ProtocolState segment.reconstruct)
              (segment.block.liftPoint segment.suffix
                (ProtocolState.entry segment.suffix finished))), excluded)
          monotone).close ∧
        SourceReplayVisitImage setup segment.block segment.suffix embedding attempt
          (sourceSnapshotState setup implementation
            ⟨some targetCurrent, targetTrace⟩ reference lost
              (phase.drain physical).native) first.refs ∧
        BindingStamp (fun owner => (nativeApplication).outputs
          (reference.execution.recall owner)) before.execution.application.attempt
            (phase.drain physical).native
  initialized : ∀ lost, SourceReplayLostRestricted setup implementation
      ⟨some targetCurrent, targetTrace⟩ reference who lost →
    sourceSnapshotAssignment setup implementation ⟨some targetCurrent, targetTrace⟩
      reference lost
      (PhaseRuntimeState.initial implementation.plan (encodeInputs cut.theta)) =
        PhaseRuntimeState.initial implementation.plan
          (encodeInputs (ProtocolState.base setup.program targetCurrent.point))
  images : ∀ lost, SourceReplayLostRestricted setup implementation
      ⟨some targetCurrent, targetTrace⟩ reference who lost →
    ∀ (before : (nativeApplication).Control)
      (prior : (nativeProtocol).Trace (some before)),
      TracePrefix prior referenceTrace →
      SourceReplayImage setup implementation ⟨some targetCurrent, targetTrace⟩
        reference referenceTrace lost who before
  proper : ∀ lost, SourceReplayLostRestricted setup implementation
      ⟨some targetCurrent, targetTrace⟩ reference who lost →
    ∀ (before : (nativeApplication).Control)
      (prior : (nativeProtocol).Trace (some before)),
      TracePrefix prior referenceTrace →
      ∀ (owner : Player) (handle : Handle (serviceGraph setup .concurrent))
        (raw : Raw L) (record : (nativeApplication).PlayerEntry)
        (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
        (event : (serviceGraph setup .concurrent).EventId)
        (payload : L.Ty) (old : L.Val payload),
      owner ≠ who → handle.1 = owner →
      before.execution.application.current.native.candidates.lookup handle = .fresh →
      lost handle = none →
      record ∈ reference.execution.recall owner →
      record.emitted = some message →
      message.sender = owner →
      message.payload.packet.call = .commitment event handle →
      (serviceGraph setup .concurrent).outputLayout event = .binding owner payload →
      raw.1 = payload →
      record.action.transmission.bind PhaseProposal.bindingPreparation =
        some ⟨payload, old⟩ →
      (∃ next : L.Val payload,
        sourceHandleMeaning setup implementation ⟨some targetCurrent, targetTrace⟩
          reference handle = some ⟨payload, next⟩) ∨
      (sourceHandleMeaning setup implementation ⟨some targetCurrent, targetTrace⟩
          reference handle = none ∧
        message.payload.attempt ≠ reference.execution.application.attempt ∧
        SourceReplayLostRestricted setup implementation
          ⟨some targetCurrent, targetTrace⟩ reference who
          (Function.update lost handle (some raw)))

/- Every factual native prefix selects an original source prefix. Full focal
information maps that literal prefix to the same completed target chronology;
the target private actions may differ, while its depth and enriched focal
information agree. -/
theorem sourceReplayTargetPrefix
    (operational : implementation.Operational)
    (who : Player)
    (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (target : setup.proposalRecoveryProtocol.History)
    (same : setup.proposalRecoveryModel.infoOf who
        (canonicalSource setup implementation operational
          ⟨some reference, referenceTrace⟩).trace =
      setup.proposalRecoveryModel.infoOf who target.trace)
    (completed : setup.proposalRecoveryProtocol.History)
    (targetKept : TracePrefix target.trace completed.trace)
    (before : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before))
    (retained : TracePrefix prior referenceTrace) :
    ∃ earlier : setup.proposalRecoveryProtocol.History,
      earlier = ⟨_, setup.proposalRecoveryLiftTrace
        (nativeArchiveLabels setup
          (PhaseProposal.sourceArchive reference.execution.network.inputs))
        (checkpointSelection setup implementation operational prior).val.checkpoint.trace⟩ ∧
      ∃ mapped : setup.proposalRecoveryProtocol.History,
        TracePrefix mapped.trace target.trace ∧
        TracePrefix mapped.trace completed.trace ∧
        mapped.trace.length = earlier.trace.length ∧
        setup.proposalRecoveryModel.infoOf who earlier.trace =
          setup.proposalRecoveryModel.infoOf who mapped.trace ∧
        ∃ (mappedCurrent : CommitRecoveryState setup.program)
          (mappedLive mappedSaved : SourceProgram.Config Player L
          ((checkpointSelection setup implementation operational
            prior).val.checkpoint.residual.context)),
          mapped.state = some mappedCurrent ∧
          mappedCurrent.point =
            (checkpointSelection setup implementation operational
              prior).val.checkpoint.residual.lift
              (ProtocolState.entry
                (checkpointSelection setup implementation operational
                  prior).val.checkpoint.residual.tail
                mappedLive) ∧
          mappedCurrent.saved =
            (checkpointSelection setup implementation operational
              prior).val.checkpoint.residual.lift
              (ProtocolState.entry
                (checkpointSelection setup implementation operational
                  prior).val.checkpoint.residual.tail
                mappedSaved) ∧
          mappedCurrent.excluded = before.execution.application.entry.excluded ∧
          mappedCurrent.generation = before.execution.application.generation := by
  let labels := nativeArchiveLabels setup
    (PhaseProposal.sourceArchive reference.execution.network.inputs)
  let selected := (checkpointSelection setup implementation operational prior).val
  let earlier : setup.proposalRecoveryProtocol.History :=
    ⟨some (CommitRecoveryState.atPoint
      (selected.checkpoint.residual.lift
        (ProtocolState.entry selected.checkpoint.residual.tail selected.checkpoint.source))
      before.execution.application.entry.excluded before.execution.application.generation),
      setup.proposalRecoveryLiftTrace labels selected.checkpoint.trace⟩
  have originalPrefix := checkpointSelection_prefix setup implementation operational
    before reference prior referenceTrace retained
  have labeledPrefix := setup.proposalRecoveryLiftTrace_prefix labels originalPrefix
  have kept : TracePrefix earlier.trace
      (canonicalSource setup implementation operational
        ⟨some reference, referenceTrace⟩).trace := by
    exact labeledPrefix
  obtain ⟨mapped, mappedKept, length, information⟩ :=
    source_information_prefix setup who
      (canonicalSource setup implementation operational
        ⟨some reference, referenceTrace⟩) target earlier same kept
  obtain ⟨mappedCurrent, mappedLive, mappedSaved, mappedState, livePoint,
    savedPoint, _liveMetadata, _savedMetadata, mask, _entryMask, generation⟩ :=
    source_target_entries setup who
      (CommitRecoveryState.atPoint
        (selected.checkpoint.residual.lift
          (ProtocolState.entry selected.checkpoint.residual.tail
            selected.checkpoint.source)) before.execution.application.entry.excluded
          before.execution.application.generation)
      earlier.trace mapped information selected.checkpoint.residual.tail
        selected.checkpoint.residual.tail selected.checkpoint.residual.lift
          selected.checkpoint.residual.lift selected.checkpoint.origin
            selected.checkpoint.origin selected.checkpoint.source selected.checkpoint.source
              rfl rfl
  exact ⟨earlier, rfl, mapped, mappedKept, mappedKept.trans targetKept,
    length, information,
    mappedCurrent, mappedLive, mappedSaved, mappedState, livePoint, savedPoint,
    mask.symm, generation.symm⟩

/- Within one factual native attempt, the selected source entry cannot move.
Both mapped target entries are actual prefixes of the same target history, and
the original selected checkpoint keeps its literal depth. -/
private theorem sourceReplayTargetPrefix_same_attempt
    (operational : implementation.Operational)
    (first second : (nativeApplication).Control)
    (firstTrace : (nativeProtocol).Trace (some first))
    (secondTrace : (nativeProtocol).Trace (some second))
    (retained : TracePrefix firstTrace secondTrace)
    (same : first.execution.application.attempt = second.execution.application.attempt)
    (target firstTarget secondTarget : setup.proposalRecoveryProtocol.History)
    (firstKept : TracePrefix firstTarget.trace target.trace)
    (secondKept : TracePrefix secondTarget.trace target.trace)
    (firstLength : firstTarget.trace.length =
      (checkpointSelection setup implementation operational
        firstTrace).val.checkpoint.trace.length)
    (secondLength : secondTarget.trace.length =
      (checkpointSelection setup implementation operational
        secondTrace).val.checkpoint.trace.length) :
    firstTarget = secondTarget := by
  have selected := checkpointSelection_eq_of_attempt setup implementation operational
    first second firstTrace secondTrace retained same
  have depth := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    history.trace.length) selected
  exact firstKept.eq_of_same_length secondKept
    (firstLength.trans (depth.trans secondLength.symm))

/- Equal actual phase addresses select the same typed reference environment.
Both compiled readouts identify each old reference through its terminal cell;
no equality of the mutable checkpoint records is needed. -/
omit [Fintype Player] in
theorem sourceReplayCheckpointRefsEq
    {first second : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (left : RecoverySourceCheckpoint setup .concurrent first)
    (right : RecoverySourceCheckpoint setup .concurrent second)
    (phase : first.attempt.phase = second.attempt.phase) :
    cast (congrArg (fun residual : ResidualProgram setup.program =>
      ContextRefs (graphLayout setup.program) residual.context)
        (left.residual_eq_of_phase_eq right phase)) left.refs = right.refs := by
  classical
  have sameResidual := left.residual_eq_of_phase_eq right phase
  rcases left with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, alignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, history, memory, steps, menus, readout, leftTrace, views,
    historyAlignment, origin⟩
  rcases right with ⟨otherResidual, otherSource, otherRefs, otherRegistry,
    otherEmbedding, otherBefore, otherCompiled, otherAlignment, otherAgrees,
    otherGuards, otherFailures, otherUnique, otherRanks, otherActors,
    otherCommits, otherOwners, otherEndpoints, otherAutomatic, otherHistory,
    otherMemory, otherSteps, otherMenus, otherReadout, rightTrace, otherViews,
    otherHistoryAlignment, otherOrigin⟩
  change (⟨Γ, O, program, lift⟩ : ResidualProgram setup.program) =
    otherResidual at sameResidual
  subst otherResidual
  change refs = otherRefs
  exact CompiledReadoutSuffix.refs_eq setup.program alignment otherAlignment

/- On one factual native attempt the saved physical entry is literally the
same. The selected residual syntax and typed references also agree, so the
target entry's assigned-store agreement transports without replaying raw
operator cases or selecting another source prefix. -/
private theorem sourceReplaySameAttemptSavedAgreement
    (operational : implementation.Operational)
    (before after : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before))
    (trace : (nativeProtocol).Trace (some after))
    (retained : TracePrefix prior trace)
    (same : before.execution.application.attempt =
      after.execution.application.attempt)
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (entry : SourceProgram.Config Player L
      (checkpointSelection setup implementation operational prior).val.checkpoint.residual.context)
    (nextEntry : SourceProgram.Config Player L
      (checkpointSelection setup implementation operational trace).val.checkpoint.residual.context)
    (samePoint :
      (checkpointSelection setup implementation operational prior).val.checkpoint.residual.lift
        (ProtocolState.entry
          (checkpointSelection setup implementation operational prior).val.checkpoint.residual.tail
          entry) =
      (checkpointSelection setup implementation operational trace).val.checkpoint.residual.lift
        (ProtocolState.entry
          (checkpointSelection setup implementation operational trace).val.checkpoint.residual.tail
          nextEntry))
    (agrees : (checkpointSelection setup implementation
      operational prior).val.checkpoint.refs.Agrees
      entry.state (sourceSnapshotState setup implementation target reference lost
        before.execution.application.entry.native).config.store) :
    let first := (checkpointSelection setup implementation operational prior).val.checkpoint
    let last := (checkpointSelection setup implementation operational trace).val.checkpoint
    let contextEq := congrArg (fun residual : ResidualProgram setup.program => residual.context)
      (first.residual_eq_of_phase_eq last (congrArg CommitAttemptId.phase same))
    cast (congrArg (SourceProgram.Config Player L) contextEq) entry = nextEntry ∧
      last.refs.Agrees nextEntry.state
        (sourceSnapshotState setup implementation target reference lost
          after.execution.application.entry.native).config.store := by
  dsimp only
  have residualEq :=
    (checkpointSelection setup implementation
      operational prior).val.checkpoint.residual_eq_of_phase_eq
      (checkpointSelection setup implementation operational trace).val.checkpoint
        (congrArg CommitAttemptId.phase same)
  have transportConfig {left right : ResidualProgram setup.program}
      (equal : left = right)
      (origin : ProtocolSuffix setup.program left.tail left.lift)
      (source : SourceProgram.Config Player L left.context)
      (result : SourceProgram.Config Player L right.context)
      (point : left.lift (ProtocolState.entry left.tail source) =
        right.lift (ProtocolState.entry right.tail result)) :
      cast (congrArg (fun residual : ResidualProgram setup.program =>
        SourceProgram.Config Player L residual.context) equal) source = result := by
    cases equal
    exact ProtocolState.entry_injective left.tail
      (sourceReplaySuffixInjective setup origin point)
  have entryEq := transportConfig residualEq
    (checkpointSelection setup implementation operational prior).val.checkpoint.origin
      entry nextEntry samePoint
  obtain ⟨_witness, _archived, _history, savedEq, _transfer⟩ :=
    checkpointSelection_at_entry setup implementation operational before after prior trace
      retained same
  have refsEq := sourceReplayCheckpointRefsEq setup
    (checkpointSelection setup implementation operational prior).val.checkpoint
    (checkpointSelection setup implementation operational trace).val.checkpoint
      (congrArg CommitAttemptId.phase same)
  have transport {left right : ResidualProgram setup.program}
      (equal : left = right)
      (leftRefs : ContextRefs (graphLayout setup.program) left.context)
      (rightRefs : ContextRefs (graphLayout setup.program) right.context)
      (refsEqual : cast (congrArg (fun residual : ResidualProgram setup.program =>
        ContextRefs (graphLayout setup.program) residual.context) equal) leftRefs = rightRefs)
      (source : SourceProgram.Config Player L left.context)
      (store : Store (graphLayout setup.program)) :
      leftRefs.Agrees source.state store →
        rightRefs.Agrees
          (cast (congrArg (fun residual : ResidualProgram setup.program =>
            SourceProgram.Config Player L residual.context) equal) source).state store := by
    cases equal
    cases refsEqual
    exact id
  refine ⟨entryEq, ?_⟩
  rw [← entryEq, ← savedEq]
  intro name cell source
  exact (transport residualEq _ _ refsEq entry
    (sourceSnapshotState setup implementation target reference lost
      before.execution.application.entry.native).config.store agrees) source

/- A factual native extension within the same attempt carries its particular
target prefix and saved typed entry forward. The two independently mapped
prefixes are the same history, so their saved points identify the complete
typed Config before transporting its physical agreement. -/
theorem sourceReplaySameAttemptSelectedEntry
    (operational : implementation.Operational)
    (before after : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before))
    (trace : (nativeProtocol).Trace (some after))
    (retained : TracePrefix prior trace)
    (same : before.execution.application.attempt =
      after.execution.application.attempt)
    (target firstTarget secondTarget : setup.proposalRecoveryProtocol.History)
    (firstKept : TracePrefix firstTarget.trace target.trace)
    (secondKept : TracePrefix secondTarget.trace target.trace)
    (firstLength : firstTarget.trace.length =
      (checkpointSelection setup implementation operational prior).val.checkpoint.trace.length)
    (secondLength : secondTarget.trace.length =
      (checkpointSelection setup implementation operational trace).val.checkpoint.trace.length)
    (firstCurrent secondCurrent : CommitRecoveryState setup.program)
    (firstState : firstTarget.state = some firstCurrent)
    (secondState : secondTarget.state = some secondCurrent)
    (firstLive : SourceProgram.Config Player L
      (checkpointSelection setup implementation operational prior).val.checkpoint.residual.context)
    (secondLive : SourceProgram.Config Player L
      (checkpointSelection setup implementation operational trace).val.checkpoint.residual.context)
    (firstSaved : SourceProgram.Config Player L
      (checkpointSelection setup implementation operational prior).val.checkpoint.residual.context)
    (secondSaved : SourceProgram.Config Player L
      (checkpointSelection setup implementation operational trace).val.checkpoint.residual.context)
    (firstLivePoint : firstCurrent.point =
      (checkpointSelection setup implementation operational prior).val.checkpoint.residual.lift
        (ProtocolState.entry
          (checkpointSelection setup implementation operational prior).val.checkpoint.residual.tail
          firstLive))
    (secondLivePoint : secondCurrent.point =
      (checkpointSelection setup implementation operational trace).val.checkpoint.residual.lift
        (ProtocolState.entry
          (checkpointSelection setup implementation operational trace).val.checkpoint.residual.tail
          secondLive))
    (firstPoint : firstCurrent.saved =
      (checkpointSelection setup implementation operational prior).val.checkpoint.residual.lift
        (ProtocolState.entry
          (checkpointSelection setup implementation operational prior).val.checkpoint.residual.tail
          firstSaved))
    (secondPoint : secondCurrent.saved =
      (checkpointSelection setup implementation operational trace).val.checkpoint.residual.lift
        (ProtocolState.entry
          (checkpointSelection setup implementation operational trace).val.checkpoint.residual.tail
          secondSaved))
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (agrees : (checkpointSelection setup implementation
      operational prior).val.checkpoint.refs.Agrees
      firstSaved.state (sourceSnapshotState setup implementation target reference lost
        before.execution.application.entry.native).config.store) :
    firstTarget = secondTarget ∧
      let first := (checkpointSelection setup implementation operational prior).val.checkpoint
      let last := (checkpointSelection setup implementation operational trace).val.checkpoint
      let contextEq := congrArg (fun residual : ResidualProgram setup.program => residual.context)
        (first.residual_eq_of_phase_eq last (congrArg CommitAttemptId.phase same))
      cast (congrArg (SourceProgram.Config Player L) contextEq) firstLive = secondLive ∧
        cast (congrArg (SourceProgram.Config Player L) contextEq) firstSaved = secondSaved ∧
          last.refs.Agrees secondSaved.state
            (sourceSnapshotState setup implementation target reference lost
              after.execution.application.entry.native).config.store := by
  have targetEq := sourceReplayTargetPrefix_same_attempt setup implementation operational
    before after prior trace retained same target firstTarget secondTarget firstKept secondKept
      firstLength secondLength
  have currentEq : firstCurrent = secondCurrent := by
    have states := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
      history.state) targetEq
    rw [firstState, secondState] at states
    exact Option.some.inj states
  have residualEq :=
    (checkpointSelection setup implementation
      operational prior).val.checkpoint.residual_eq_of_phase_eq
      (checkpointSelection setup implementation operational trace).val.checkpoint
        (congrArg CommitAttemptId.phase same)
  have transportConfig {left right : ResidualProgram setup.program}
      (equal : left = right)
      (origin : ProtocolSuffix setup.program left.tail left.lift)
      (source : SourceProgram.Config Player L left.context)
      (result : SourceProgram.Config Player L right.context)
      (point : left.lift (ProtocolState.entry left.tail source) =
        right.lift (ProtocolState.entry right.tail result)) :
      cast (congrArg (fun residual : ResidualProgram setup.program =>
        SourceProgram.Config Player L residual.context) equal) source = result := by
    cases equal
    exact ProtocolState.entry_injective left.tail
      (sourceReplaySuffixInjective setup origin point)
  have livePointEq :
      (checkpointSelection setup implementation operational prior).val.checkpoint.residual.lift
        (ProtocolState.entry
          (checkpointSelection setup implementation operational prior).val.checkpoint.residual.tail
          firstLive) =
      (checkpointSelection setup implementation operational trace).val.checkpoint.residual.lift
        (ProtocolState.entry
          (checkpointSelection setup implementation operational trace).val.checkpoint.residual.tail
          secondLive) := by
    calc
      _ = firstCurrent.point := firstLivePoint.symm
      _ = secondCurrent.point := congrArg CommitRecoveryState.point currentEq
      _ = _ := secondLivePoint
  have liveEq := transportConfig residualEq
    (checkpointSelection setup implementation operational prior).val.checkpoint.origin
      firstLive secondLive livePointEq
  have pointEq :
      (checkpointSelection setup implementation operational prior).val.checkpoint.residual.lift
        (ProtocolState.entry
          (checkpointSelection setup implementation operational prior).val.checkpoint.residual.tail
          firstSaved) =
      (checkpointSelection setup implementation operational trace).val.checkpoint.residual.lift
        (ProtocolState.entry
          (checkpointSelection setup implementation operational trace).val.checkpoint.residual.tail
          secondSaved) := by
    calc
      _ = firstCurrent.saved := firstPoint.symm
      _ = secondCurrent.saved := congrArg CommitRecoveryState.saved currentEq
      _ = _ := secondPoint
  obtain ⟨savedEq, nextAgrees⟩ := sourceReplaySameAttemptSavedAgreement setup implementation
    operational before after prior trace retained same target reference lost firstSaved secondSaved
      pointEq agrees
  exact ⟨targetEq, liveEq, savedEq, nextAgrees⟩

/- The factual close retains the original drained word in the selected
source history. Clean and dirty exits share the same literal labeled interval;
no separately normalized checkpoint is substituted. -/
theorem sourceReplayFactualCommitInterval
    (operational : implementation.Operational)
    (before after reference : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before))
    (trace : (nativeProtocol).Trace (some after))
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (retained : TracePrefix prior trace)
    (toReference : TracePrefix trace referenceTrace)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (remaining : List (RuntimePhase (serviceGraph setup .concurrent)))
    (installed : before.execution.application.phases = phase :: remaining)
    (current : RecoveryState (serviceGraph setup .concurrent))
    (normalized : after.execution.application =
      ({ before.execution.application with current := current } :
        PhaseRuntimeState (serviceGraph setup .concurrent)).normalize)
    (finished : phase.Finished (phase.drain current))
    (commitment : phase.kind = .commitment)
    (effect : PhaseClosingEffect implementation.runtime implementation.leaks
      before.execution after.execution current)
    (changed : after.execution.application.attempt ≠ before.execution.application.attempt) :
    let first := (checkpointSelection setup implementation operational prior).val.checkpoint
    let final := canonicalSource setup implementation operational
      ⟨some reference, referenceTrace⟩
    let startState := CommitRecoveryState.atPoint
      (first.residual.lift
        (ProtocolState.entry first.residual.tail first.source))
      before.execution.application.entry.excluded before.execution.application.generation
    ∃ (lastState : CommitRecoveryState setup.program)
      (closed : setup.commitRecoveryProtocol.Trace (some lastState))
      (starting : setup.proposalRecoveryProtocol.Trace (some startState))
      (labeled : setup.proposalRecoveryProtocol.Trace (some lastState))
      (fuel : Nat),
      setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, first.trace⟩
        ⟨some lastState, closed⟩ ∧
      setup.recoveryJointRecall closed =
        (first.commitInstructionWord (phase.drain current).native).reverse ++
          setup.recoveryJointRecall first.trace ∧
      labeled.length = starting.length +
        (first.commitInstructionWord (phase.drain current).native).length ∧
      TracePrefix starting labeled ∧
      setup.proposalRecoveryEraseTrace starting = first.trace ∧
      setup.proposalRecoveryEraseTrace labeled = closed ∧
      TracePrefix labeled final.trace ∧
      TracePrefix closed
        (checkpointSelection setup implementation operational trace).val.checkpoint.trace ∧
      TracePrefix labeled
        (setup.proposalRecoveryLiftTrace
          (nativeArchiveLabels setup (PhaseProposal.sourceArchive
            reference.execution.network.inputs))
          (checkpointSelection setup implementation operational trace).val.checkpoint.trace) ∧
      closed.transitionMass = first.trace.transitionMass := by
  dsimp only
  let first := (checkpointSelection setup implementation operational prior).val
  let last := (checkpointSelection setup implementation operational trace).val
  have selected := checkpointSelection_prefix setup implementation operational before after
    prior trace retained
  have selectedOrigin : ∃ (closed : setup.commitRecoveryProtocol.History) (steps later : Nat),
      setup.commitRecoveryProtocol.ReachesWithin steps ⟨_, first.checkpoint.trace⟩ closed ∧
      setup.recoveryJointRecall closed.trace =
        (first.checkpoint.commitInstructionWord (phase.drain current).native).reverse ++
          setup.recoveryJointRecall first.checkpoint.trace ∧
      setup.commitRecoveryProtocol.ReachesWithin later closed ⟨_, last.checkpoint.trace⟩ := by
    by_cases missed : (((phase.drain current).excluded \
        before.execution.application.entry.excluded) ∩ phase.owners).Nonempty
    · exact sourceReplayDirtySelectedOrigin setup implementation before.execution.application
        after.execution.application first last _ selected.reachesWithin phase remaining installed
          current normalized finished commitment missed
    · obtain ⟨raw, rawCheckpoint, rawHistory⟩ := RecoverySourceWitness.raw_closing_checkpoint
        setup .concurrent implementation.runtime implementation.leaks implementation.plan
          before after first current effect changed
      have rawPath : setup.commitRecoveryProtocol.ReachesWithin
          (last.checkpoint.trace.length - first.checkpoint.trace.length)
          ⟨_, raw.checkpoint.trace⟩ ⟨_, last.checkpoint.trace⟩ := by
        rw [rawHistory]
        exact selected.reachesWithin
      obtain ⟨closed, steps, later, path, word, onward⟩ :=
        sourceReplayCleanSelectedOrigin setup implementation
          ({ before.execution.application with current := current } :
            PhaseRuntimeState (serviceGraph setup .concurrent))
          after.execution.application raw last _ rawPath phase remaining installed commitment
            operational.maximalPhases normalized changed finished missed
      have sameWord : raw.checkpoint.commitInstructionWord (phase.drain current).native =
          first.checkpoint.commitInstructionWord (phase.drain current).native := by
        rw [rawCheckpoint]
        rfl
      have sameRecall := congrArg (fun history : setup.commitRecoveryProtocol.History =>
        setup.recoveryJointRecall history.trace) rawHistory
      refine ⟨closed, steps, later, ?_, ?_, onward⟩
      · rw [rawHistory] at path
        exact path
      · calc
          setup.recoveryJointRecall closed.trace =
              (raw.checkpoint.commitInstructionWord (phase.drain current).native).reverse ++
                setup.recoveryJointRecall raw.checkpoint.trace := word
          _ = _ := by rw [sameWord, sameRecall]
  obtain ⟨closed, steps, _later, path, word, onward⟩ := selectedOrigin
  rcases closed with ⟨closedState, closedTrace⟩
  have finalPrefix := checkpointSelection_prefix setup implementation operational after
    reference trace referenceTrace toReference
  have closedPrefix : TracePrefix closedTrace
      (setup.proposalRecoveryEraseTrace
        (canonicalSource setup implementation operational
          ⟨some reference, referenceTrace⟩).trace) := by
    have chain := onward.tracePrefix.trans finalPrefix
    simpa only [canonicalSource, setup.proposalRecoveryEraseTrace_lift] using chain
  obtain ⟨lastState, _joints, _addresses, stateEq, _instructionPath, _length,
    _instructionWord, _addressWord⟩ := source_instruction_window setup
      (setup.initialConfig setup.initialLaw.support_nonempty.choose)
        _ first.checkpoint.trace closedTrace path.tracePrefix
  cases stateEq
  obtain ⟨labeled, labeledKept, erased⟩ :=
    setup.proposalRecoveryEraseTrace_prefix_inverse
      (canonicalSource setup implementation operational
        ⟨some reference, referenceTrace⟩).trace closedTrace closedPrefix
  have rawKept : TracePrefix first.checkpoint.trace
      (setup.proposalRecoveryEraseTrace labeled) := by
    rw [erased]
    exact path.tracePrefix
  obtain ⟨starting, startKept, startErase⟩ :=
    setup.proposalRecoveryEraseTrace_prefix_inverse labeled first.checkpoint.trace rawKept
  have wordLength := congrArg List.length word
  have startLength := congrArg (fun trace => trace.length) startErase
  have endLength := congrArg (fun trace => trace.length) erased
  have intervalLength : labeled.length = starting.length +
      (first.checkpoint.commitInstructionWord (phase.drain current).native).length := by
    simp only [setup.recoveryJointRecall_length, List.length_append,
      List.length_reverse] at wordLength
    simp only [setup.proposalRecoveryEraseTrace_length] at startLength endLength
    omega
  let labels := nativeArchiveLabels setup
    (PhaseProposal.sourceArchive reference.execution.network.inputs)
  have selectedClosed : TracePrefix closedTrace
      (setup.proposalRecoveryEraseTrace
        (setup.proposalRecoveryLiftTrace labels last.checkpoint.trace)) := by
    rw [setup.proposalRecoveryEraseTrace_lift]
    exact onward.tracePrefix
  obtain ⟨selectedLabeled, selectedKept, selectedErased⟩ :=
    setup.proposalRecoveryEraseTrace_prefix_inverse
      (setup.proposalRecoveryLiftTrace labels last.checkpoint.trace) closedTrace selectedClosed
  have selectedToFinal : TracePrefix
      (setup.proposalRecoveryLiftTrace labels last.checkpoint.trace)
      (canonicalSource setup implementation operational
        ⟨some reference, referenceTrace⟩).trace :=
    setup.proposalRecoveryLiftTrace_prefix labels finalPrefix
  have labeledEq := labeledKept.eq_of_same_length (selectedKept.trans selectedToFinal) (by
    have count := congrArg (fun trace => trace.length) selectedErased
    simp only [setup.proposalRecoveryEraseTrace_length] at count endLength
    omega)
  have sameTrace : labeled = selectedLabeled := eq_of_heq (History.mk.inj labeledEq).2
  have geometry := source_checkpoint_binding_interval setup implementation first
    operational.maximalPhases phase remaining installed commitment
  have duration : closedTrace.length = first.checkpoint.trace.length +
      (first.checkpoint.commitInstructionWord (phase.drain current).native).length := by
    simp only [setup.recoveryJointRecall_length, List.length_append,
      List.length_reverse] at wordLength
    omega
  have count := source_commit_instruction_word_length setup first.checkpoint
    (phase.drain current).native
  have below := ProtocolState.commitEnd_lt_remaining setup.program
    (first.checkpoint.residual.lift
      (ProtocolState.entry first.checkpoint.residual.tail first.checkpoint.source)) geometry.1
  have within :
      (first.checkpoint.commitInstructionWord (phase.drain current).native).length +
          ProtocolState.commitEnd setup.program (first.checkpoint.residual.lift
            (ProtocolState.entry first.checkpoint.residual.tail first.checkpoint.source)) ≤
        ProtocolState.remaining setup.program (first.checkpoint.residual.lift
          (ProtocolState.entry first.checkpoint.residual.tail first.checkpoint.source)) := by
    omega
  have closedMass := setup.commitRecovery_commit_interval_mass
    (first.checkpoint.commitInstructionWord (phase.drain current).native).length
    (CommitRecoveryState.atPoint (first.checkpoint.residual.lift
      (ProtocolState.entry first.checkpoint.residual.tail first.checkpoint.source))
        before.execution.application.entry.excluded before.execution.application.generation)
    first.checkpoint.trace geometry.1 ⟨some lastState, closedTrace⟩ path.tracePrefix duration within
  exact ⟨lastState, closedTrace, starting, labeled, steps, path, word,
    intervalLength, startKept, startErase, erased, labeledKept, onward.tracePrefix,
    (by rw [sameTrace]; exact selectedKept), closedMass⟩

omit [Fintype Player] in
/-- An actual commitment history whose saved and live ranks coincide is its
literal saved-entry state, including the whole retained source history. -/
theorem source_commit_entry_eq_atPoint
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (rank : ProtocolState.remaining setup.program current.point =
      ProtocolState.remaining setup.program current.saved) :
    current = CommitRecoveryState.atPoint current.point current.excluded current.generation := by
  obtain ⟨prior, retained, clock⟩ := setup.commitRecovery_attempt_entry current
    (setup.proposalRecoveryEraseTrace trace) committing
  have same : (⟨_, prior⟩ : setup.commitRecoveryProtocol.History) =
      ⟨some current, setup.proposalRecoveryEraseTrace trace⟩ :=
    retained.eq_of_same_length TracePrefix.refl (by omega)
  have states : CommitRecoveryState.atPoint current.saved current.entryExcluded
      current.generation = current := Option.some.inj (congrArg History.state same)
  have point : current.saved = current.point := congrArg CommitRecoveryState.point states
  have excluded : current.entryExcluded = current.excluded :=
    congrArg CommitRecoveryState.excluded states
  simpa only [point, excluded] using states.symm

omit [Fintype Player] in
private theorem sourceReplay_public_cell_observed_eq
    [DecidableEq (CellTy Player L)]
    (who : Player) (name : VarId) (kind : CellTy Player L)
    (visible : (cellField kind).IsPublic) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (first second : ProtocolState program),
      ProtocolState.observe who program first = ProtocolState.observe who program second →
      ProtocolState.cell? program first name kind =
        ProtocolState.cell? program second name kind := by
  classical
  have lookup : ∀ (Γ : SourceCtx Player L) (first second : State L Γ),
      (∀ member : HasVar Γ name kind, first.get member = second.get member) →
      State.cell? first name kind = State.cell? second name kind := by
    intro Γ
    induction Γ with
    | nil => intro first second equal; rfl
    | cons head tail ih =>
        rcases head with ⟨headName, headKind⟩
        intro first second equal
        rw [State.cell?.eq_2, State.cell?.eq_2]
        split_ifs with same
        · obtain ⟨rfl, rfl⟩ := same
          exact congrArg some (equal .here)
        · exact ih _ _ (fun member => equal (.there member))
  have entryLookup {Γ : SourceCtx Player L} (first second : SourceProgram.Config Player L Γ)
      (same : first.view who = second.view who) :
      State.cell? first.state name kind = State.cell? second.state name kind := by
    apply lookup
    intro member
    have observed : sourceObserve who first.state = sourceObserve who second.state :=
      congrArg Prod.fst same
    cases kind with
    | publicData payload =>
        exact congrArg (fun view => view.cells name (.publicData payload) member) observed
    | publication payload =>
        exact congrArg (fun view => view.cells name (.publication payload) member) observed
    | privateInput owner payload => exact False.elim visible
    | commitment owner payload => exact False.elim visible
  intro Γ O program
  induction program with
  | ret payoffs =>
      intro first second same
      exact entryLookup first second same
  | sample selected fresh law suffix ih =>
      intro first second same
      cases first with
      | inl first =>
          cases second with
          | inl second => exact entryLookup first second (Sum.inl.inj same)
          | inr second => cases same
      | inr first =>
          cases second with
          | inl second => cases same
          | inr second => exact ih first second (Sum.inr.inj same)
  | commit selected owner fresh guard suffix ih =>
      intro first second same
      cases first with
      | inl first =>
          cases second with
          | inl second => exact entryLookup first second (Sum.inl.inj same)
          | inr second => cases same
      | inr first =>
          cases second with
          | inl second => cases same
          | inr second => exact ih first second (Sum.inr.inj same)
  | reveal published owner selected fresh source unresolved suffix ih =>
      intro first second same
      cases first with
      | inl first =>
          cases second with
          | inl second => exact entryLookup first second (Sum.inl.inj same)
          | inr second => cases same
      | inr first =>
          cases second with
          | inl second => cases same
          | inr second => exact ih first second (Sum.inr.inj same)

omit [Fintype Player] in
theorem sourceReplay_public_prefix_read
    {native : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (checkpoint : RecoverySourceCheckpoint setup .concurrent native)
    (who : Player) (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (information : setup.proposalRecoveryModel.infoOf who
        (setup.proposalRecoveryLiftTrace labels checkpoint.trace) =
      setup.proposalRecoveryModel.infoOf who targetTrace)
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O)
    (lift : ProtocolState program → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program program lift)
    (unique : (Γ.map Prod.fst).Nodup)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (aligned : CompiledReadoutSuffix setup.program program refs embedding)
    (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (live saved : ProtocolState program)
    (firstPoint : first.point = lift live) (firstSaved : first.saved = lift saved)
    (sameBase : ProtocolState.base program saved = ProtocolState.base program live)
    (retained : TracePrefix prior (setup.proposalRecoveryEraseTrace targetTrace))
    {name : VarId} {kind : CellTy Player L} (member : HasVar Γ name kind)
    (visible : (cellField kind).IsPublic) :
    (refs.get member).get? native.entry.native.config.store =
      some (cellValue ((ProtocolState.base program live).get member)) := by
  classical
  obtain ⟨current, nextLive, nextSaved, ending, point, _saved, cells, _kept⟩ :=
    source_suffix_cells_of_prefix setup program lift origin _ prior
      live saved firstPoint firstSaved sameBase
        (setup.proposalRecoveryEraseTrace targetTrace) retained
  have currentEq : current = targetCurrent := (Option.some.inj ending).symm
  subst current
  let selectedCurrent : CommitRecoveryState setup.program := CommitRecoveryState.atPoint
    (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
      native.entry.excluded native.generation
  have signals := congrArg Prod.fst information
  change (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who
      (setup.proposalRecoveryLiftTrace labels checkpoint.trace)).1 =
    (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who targetTrace).1 at signals
  rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf] at signals
  have semantic := congrArg (setup.proposalRecoveryEraseBaseInfo who) signals
  rw [setup.proposalRecoveryEraseBaseInfo_observed,
    setup.proposalRecoveryEraseBaseInfo_observed] at semantic
  have observed := congrArg (fun information => information.1.1) semantic
  have privateEq : setup.commitRecoveryPrivate who (some selectedCurrent) =
      setup.commitRecoveryPrivate who (some targetCurrent) := by
    simpa only [setup.commitRecoverySignals_current] using observed
  have views : ProtocolState.observe who setup.program selectedCurrent.point =
      ProtocolState.observe who setup.program targetCurrent.point := Option.some.inj privateEq
  have targetRead : ProtocolState.cell? setup.program targetCurrent.point name kind =
      some ((ProtocolState.base program live).get member) := by
    rw [point, origin.cell?_lift,
      ProtocolState.cell?_eq_of_base name kind program nextLive unique member, cells]
  have sourceRead : ProtocolState.cell? setup.program selectedCurrent.point name kind =
      some ((ProtocolState.base program live).get member) :=
    (sourceReplay_public_cell_observed_eq who name kind visible setup.program
      selectedCurrent.point targetCurrent.point views).trans targetRead
  let terminalCell := cast (congrArg (fun context => HasVar context name kind)
    aligned.contextEq) (terminalRef program member)
  have transport {first second : SourceCtx Player L} (same : first = second)
      (environment : ContextRefs (graphLayout setup.program) first)
      (cell : HasVar first name kind) :
      (cast (congrArg (ContextRefs (graphLayout setup.program)) same) environment).get
        (cast (congrArg (fun context => HasVar context name kind) same) cell) =
          environment.get cell := by
    cases same
    rfl
  have referenceEq : (terminalRefs setup.program).get terminalCell = refs.get member := by
    rw [← aligned.refsEq]
    exact (transport aligned.contextEq _ _).trans
      (terminalRefsWith_get_terminalRef program refs embedding.ref member)
  have readback := source_saved_cell_readback setup checkpoint.residual.tail
    checkpoint.residual.lift checkpoint.origin checkpoint.source checkpoint.unique
      selectedCurrent checkpoint.trace rfl rfl checkpoint .refl terminalCell
        ((ProtocolState.base program live).get member) sourceRead
  rwa [referenceEq] at readback

omit [Fintype Player] in
theorem sourceReplay_reveal_prefix_state :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (prefixed : RevealPrefix program count)
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program)
      (lift : ProtocolState program → ProtocolState setup.program)
      (_origin : ProtocolSuffix setup.program program lift)
      (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player) (generation : Nat)
      (last : CommitRecoveryState setup.program)
      (joints : List (Player → Option (CommitRecoveryMove Player L)))
      (addresses : List (Option Nat × (Finset Player × Nat × Nat))),
      CommitRecoveryState.InstructionPath setup.program
        (setup.initialConfig setup.initialLaw.support_nonempty.choose) joints addresses
        (CommitRecoveryState.atPoint (lift (ProtocolState.entry program entry))
          excluded generation) last →
      joints.length = count →
      ∃ final : SourceProgram.Config Player L (revealTail count program prefixed).context,
        last = CommitRecoveryState.atPoint
          (lift ((revealTail count program prefixed).lift
            (ProtocolState.entry (revealTail count program prefixed).tail final)))
          last.excluded generation ∧
        ∀ {name : VarId} {kind : CellTy Player L}
          (member : HasVar (revealTail count program prefixed).context name kind),
          ¬ (cellField kind).IsPublic →
          ∃ original : HasVar Γ name kind,
            (revealTailRefs setup count program prefixed refs embedding).get member =
              refs.get original ∧ final.state.get member = entry.state.get original := by
  intro count
  induction count with
  | zero =>
      intro Γ O program prefixed refs embedding lift origin entry excluded generation last
        joints addresses path
        length
      have empty : joints = [] := List.length_eq_zero_iff.mp length
      subst joints
      cases path with
      | refl => exact ⟨entry, rfl, fun member _ => ⟨member, rfl, rfl⟩⟩
  | succ count ih =>
      intro Γ O program prefixed refs embedding lift origin entry excluded generation last
        joints addresses path
        length
      cases program with
      | ret payoffs => exact prefixed.elim
      | sample name fresh law suffix => exact prefixed.elim
      | commit name owner fresh guard suffix => exact prefixed.elim
      | reveal published owner name fresh selected unresolved suffix =>
          cases path with
          | refl => simp only [List.length_nil] at length; omega
          | @step first middle last joint rest addresses legal supported later =>
              let result := revealSuccessor published selected entry
                (if owner ∈ excluded then false else
                  OwnAction.disclosure ((joint owner).map (·.action)))
              let kept := if owner ∈ excluded then { result with history := entry.history }
                else result
              let after := match result.state.get .here with
                | .failure => insert owner excluded
                | .success _ => excluded
              have notCommit : ProtocolState.atCommit setup.program
                  (lift (ProtocolState.entry _ entry)) = false := by
                rw [origin.atCommit_lift]
                rfl
              obtain ⟨raw, rawSupported, middleEq⟩ :=
                (CommitRecoveryState.atPoint (lift (ProtocolState.entry _ entry))
                  excluded generation).step_noncommit_atPoint
                    (CommitRecoveryState.atPoint_blockFrontier _ _ _) notCommit joint middle
                      supported
              have kernel : ProtocolState.recoveryStep
                  (.reveal published owner name fresh selected unresolved suffix)
                  (ProtocolState.entry _ entry) excluded joint =
                  PMF.pure ((Sum.inr (ProtocolState.entry suffix kept) : ProtocolState _),
                    after) := rfl
              change raw ∈ (ProtocolState.recoveryStep setup.program
                (lift (ProtocolState.entry _ entry)) excluded joint).support at rawSupported
              rw [origin.recoveryStep_lift, kernel, PMF.pure_map,
                PMF.mem_support_pure_iff] at rawSupported
              have middleAtPoint : middle = CommitRecoveryState.atPoint
                  (lift (.inr (ProtocolState.entry suffix kept))) after generation := by
                rw [middleEq, rawSupported]
                rfl
              rw [middleAtPoint] at later
              obtain ⟨final, finalPoint, inherited⟩ := ih suffix prefixed
                (refs.cons (name := published) ⟨.inr (embedding.event ⟨0, by simp [eventCount]⟩),
                  reveal_head_layout embedding⟩)
                (embedding.tail suffix (by simp [eventCount]) (fun _ => rfl))
                (fun point => lift (.inr point))
                (origin.revealTail fresh selected unresolved suffix) kept after generation last
                  rest addresses later (by simpa only [List.length_cons, Nat.add_right_cancel_iff]
                    using length)
              refine ⟨final, finalPoint, ?_⟩
              intro cellName cellKind member privateCell
              obtain ⟨original, referenceEq, valueEq⟩ := inherited member privateCell
              cases original with
              | here => exact (privateCell (by trivial)).elim
              | there original =>
                  refine ⟨original, referenceEq, valueEq.trans ?_⟩
                  dsimp only [kept, result]
                  split_ifs <;> rfl

open Classical in
/-- A source prescription at nonterminal histories suffices for the literal
closed-fiber factorization. Terminal policy values never enter either the
finite run or its focal own-action product. -/
theorem prescribed_source_closed_products
    (scale sourceBad : Set.Icc (0 : ℝ) 1)
    (wellFormed : setup.WellFormed)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (prescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (who : Player) (canonical : setup.proposalRecoveryProtocol.History)
    (good : setup.proposalRecoveryForeignGood who canonical) :
    let factors : {state : setup.proposalRecoveryProtocol.State} →
        setup.proposalRecoveryProtocol.Trace state → ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ :=
      setup.proposalRecoveryForeignProducts values scale sourceBad scale who
    setup.proposalRecoveryClosedMass sourceProfile who canonical =
      ENNReal.ofReal canonical.trace.transitionMass *
        ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability (sourceProfile who)
          (setup.proposalRecoveryModel.ownPlay who canonical.trace)) *
            (factors canonical.trace).1 * (factors canonical.trace).2.1 ∧
    ∀ target, setup.proposalRecoveryClosedMass sourceProfile who canonical *
        setup.proposalRecoveryClosedLaw sourceProfile who canonical target =
      if setup.proposalRecoveryClosedKey who target =
          setup.proposalRecoveryClosedKey who canonical then
        setup.proposalRecoveryClosedMass sourceProfile who canonical * (factors target.trace).2.2
      else 0 := by
  classical
  intro factors
  let normalized := setup.proposalRecoveryNormalizedTrembledProfile
    scale.val scale.property.1 scale.property.2
    sourceBad.val sourceBad.property.1 sourceBad.property.2
    scale.val scale.property.1 scale.property.2 values
  have runs (fuel : Nat) :
      setup.proposalRecoveryModel.runBehavioral sourceProfile fuel =
        setup.proposalRecoveryModel.runBehavioral normalized fuel := by
    exact setup.proposalRecoveryModel.runBehavioralFrom_congr fuel
      setup.proposalRecoveryProtocol.initHistory
        (fun reached _ running owner => prescribed owner reached running)
  have own : ∀ {state : setup.proposalRecoveryProtocol.State}
      (trace : setup.proposalRecoveryProtocol.Trace state),
      setup.proposalRecoveryModel.playerReachProbability sourceProfile who trace =
        setup.proposalRecoveryModel.playerReachProbability normalized who trace := by
    intro state trace
    induction trace with
    | start => rfl
    | @extend before after prior joint legal reached ih =>
        rw [InformationModel.playerReachProbability,
          InformationModel.playerReachProbability, ih]
        unfold InformationModel.playerStepProb
        rw [prescribed who ⟨before, prior⟩ legal.1]
  have ownAt : setup.proposalRecoveryModel.ownPlayReachProbability (sourceProfile who)
      (setup.proposalRecoveryModel.ownPlay who canonical.trace) =
        setup.proposalRecoveryModel.ownPlayReachProbability (normalized who)
          (setup.proposalRecoveryModel.ownPlay who canonical.trace) := by
    simpa only [setup.proposalRecoveryModel.playerReachProbability_eq_ownPlayReachProbability]
      using own canonical.trace
  have mass : setup.proposalRecoveryClosedMass sourceProfile who canonical =
      setup.proposalRecoveryClosedMass normalized who canonical := by
    unfold Setup.proposalRecoveryClosedMass
    rw [runs]
  have law : setup.proposalRecoveryClosedLaw sourceProfile who canonical =
      setup.proposalRecoveryClosedLaw normalized who canonical := by
    unfold Setup.proposalRecoveryClosedLaw
    rw [runs]
  have products := setup.proposalRecoveryClosedMass_foreign_products values scale sourceBad
    scale wellFormed who canonical good
  change setup.proposalRecoveryClosedMass normalized who canonical =
      ENNReal.ofReal canonical.trace.transitionMass *
        ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability (normalized who)
          (setup.proposalRecoveryModel.ownPlay who canonical.trace)) *
            (factors canonical.trace).1 * (factors canonical.trace).2.1 ∧
    ∀ target, setup.proposalRecoveryClosedMass normalized who canonical *
        setup.proposalRecoveryClosedLaw normalized who canonical target =
      if setup.proposalRecoveryClosedKey who target =
          setup.proposalRecoveryClosedKey who canonical then
        setup.proposalRecoveryClosedMass normalized who canonical * (factors target.trace).2.2
      else 0 at products
  rw [mass, law, ownAt]
  exact products

end Vegas.PhaseProposalQualifiedBinding
