/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalCanonicalSourceKernel
import Vegas.Source.CommitRecoveryAttemptExtraction
import Vegas.Source.CommitRecoveryClear
import Vegas.Source.ProposalRecoveryOrdinaryCommit
import Vegas.Compile.EventGraphState
import Vegas.Compile.CommitPrefixReadStability

/-! # The ordinary source commitment telescope and its frozen graph potential -/

noncomputable section

namespace Vegas

open SourceProgram SourceProgram.Setup EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The ordinary owner-word profile at the actual residual source entry. -/
def ordinaryBlockProfile
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context)
      (outputLayout setup.program) (block.prepend suffix))
    (wholeViews : ∀ owner, ProtocolView owner (block.prepend suffix) →
      ProtocolView owner setup.program)
    (controls : Finset Player × Nat × Nat)
    (publicFrame : PhasePublicView (serviceGraph setup mode))
    (archive : Finset (ProposalRecoveryProposal L)) :
    SourceProgram.BehavioralProfile (block.prepend suffix) := by
  classical
  let keyAt := fun (owner : Player)
      (wholeView : SourceProgram.ProtocolView owner setup.program)
      (controls : Finset Player × Nat × Nat)
      (publicFrame : PhasePublicView (serviceGraph setup mode))
      (archive : Finset (ProposalRecoveryProposal L)) =>
    let rank := ProtocolView.position owner setup.program wholeView
    let addresses :=
      (publicFrame.sourcePublicAddressWord plan rank).reverse ++
        [(none, (∅, 0, 0))]
    let typed := ProtocolView.virtualBindings owner (setup.context.map Prod.fst).toFinset
      setup.program wholeView
    (setup.commitRecoveryErasedInformation owner
      (setup.commitRecoveryNoMissInformation owner
        (setup.commitRecoveryErasedRead owner typed controls addresses)), archive)
  let rec buildProfile
      {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
      (block : SourceProgram.CommitPrefix Γ O Δ P)
      (suffix : SourceProgram Player L Δ P)
      (embedding : OutputEmbedding (inputLayout setup.context)
        (outputLayout setup.program) (block.prepend suffix))
      (wholeViews : ∀ owner,
        SourceProgram.ProtocolView owner (block.prepend suffix) →
          SourceProgram.ProtocolView owner setup.program)
      (controls : Finset Player × Nat × Nat)
      (publicFrame : PhasePublicView (serviceGraph setup mode))
      (archive : Finset (ProposalRecoveryProposal L)) :
      SourceProgram.BehavioralProfile (block.prepend suffix) :=
    match Γ, O, Δ, P, block with
    | _, _, _, _, .nil => SourceProgram.failureProfile suffix
    | _, _, _, _,
        @SourceProgram.CommitPrefix.commit _ _ Γ O Δ P name owner valueType fresh guard rest =>
        fun observer => by
          refine ⟨?_, ?_⟩
          · intro owned observed
            subst observer
            let first : Fin (eventCount
                ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend
                  suffix)) :=
              ⟨0, by simp only [SourceProgram.CommitPrefix.prepend, eventCount]; omega⟩
            have shape : (serviceGraph setup mode).outputLayout
                (embedding.event first) = .binding owner valueType :=
              (embedding.layout_eq first).trans (by rfl)
            exact if owner ∈ controls.1 then PMF.pure .failure else
              (values owner
                (keyAt owner (wholeViews owner (Sum.inl observed)) controls
                  publicFrame archive)).map
                  fun sampled => PublicationResult.success
                    (phaseRecoveryDomainValue setup mode (embedding.event first) owner
                      valueType shape sampled.val.val)
          · let later := embedding.tail (rest.prepend suffix)
              (by simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
            exact buildProfile rest suffix later
              (fun owner laterView => wholeViews owner (Sum.inr laterView))
              controls publicFrame archive observer
  exact buildProfile block suffix embedding wholeViews controls publicFrame archive

omit [Fintype Player] in
/-- The structural block row reads the actual updated source query, including
its complete public address word and unchanged original proposal archive. -/
theorem ordinary_source_query_readback
    (setup : Setup (Player := Player) (L := L))
    (who : Player) (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (survives : who ∉ current.excluded)
    (ordinary : ProtocolState.BindingsHoldValues who setup.program current.point) :
    (setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryNoMissInformation who
        (setup.commitRecoveryErasedRead who
          (ProtocolView.virtualBindings who (setup.context.map Prod.fst).toFinset setup.program
            (ProtocolState.observe who setup.program current.point))
          (setup.commitRecoveryPublic (some current))
          ((setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace trace)).map
            (setup.commitRecoveryPublicAddress who)))),
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who trace)) =
        setup.proposalRecoveryQuery who (setup.proposalRecoveryModel.infoOf who trace) := by
  have read := setup.commitRecovery_erasedInformation_read who current
    (setup.proposalRecoveryEraseTrace trace) survives
  have erasedRead : setup.commitRecoveryErasedRead who
      (ProtocolView.eraseHistory who setup.program
        (ProtocolState.observe who setup.program current.point))
      (setup.commitRecoveryPublic (some current))
      ((setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace trace)).map
        (setup.commitRecoveryPublicAddress who)) =
      setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace trace)) := by
    simpa only [Setup.commitRecoveryErasedRead, ProtocolView.eraseHistory_idempotent,
      ProtocolView.publicPadding_eraseHistory] using read.symm
  rw [ProtocolState.virtualBindings_observe_eq who _ setup.program current.point ordinary,
    erasedRead]
  unfold Setup.proposalRecoveryQuery
  rw [setup.proposalRecoveryEraseInfo_observed]
  apply Prod.ext
  · rw [← setup.commitRecoveryNoMissInformation_erased,
      setup.commitRecoveryErasedInformation_idempotent]
  · rfl

/-- At an active source binding, the single structural block profile uses
exactly the ordinary value law at that trace's updated full query. -/
theorem ordinary_block_head_law
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (rest : SourceProgram.CommitPrefix ((name, .commitment owner payload) :: Γ)
      (insert name O) Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix))
    (wholeViews : ∀ who, ProtocolView who
      ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix) →
        ProtocolView who setup.program)
    (controls : Finset Player × Nat × Nat)
    (publicFrame : PhasePublicView (serviceGraph setup mode))
    (archive : Finset (ProposalRecoveryProposal L))
    (observed : DecisionView owner Γ)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (survives : owner ∉ current.excluded)
    (ordinary : ProtocolState.BindingsHoldValues owner setup.program current.point)
    (read : wholeViews owner (Sum.inl observed) =
      ProtocolState.observe owner setup.program current.point)
    (controlRead : setup.commitRecoveryPublic (some current) = controls)
    (addressRead : (setup.attemptPublicRecall owner
      (setup.proposalRecoveryEraseTrace trace)).map (setup.commitRecoveryPublicAddress owner) =
        (publicFrame.sourcePublicAddressWord plan
          (ProtocolView.position owner setup.program
            (ProtocolState.observe owner setup.program current.point))).reverse ++
              [(none, (∅, 0, 0))])
    (archiveRead : setup.proposalRecoveryArchive owner
      (setup.proposalRecoveryModel.infoOf owner trace) = archive) :
    let first : Fin (eventCount
      ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix)) :=
        ⟨0, by simp only [SourceProgram.CommitPrefix.prepend, eventCount]; omega⟩
    let shape : (serviceGraph setup mode).outputLayout (embedding.event first) =
      .binding owner payload := (embedding.layout_eq first).trans (by rfl)
    SourceProgram.commitKernel
      (ordinaryBlockProfile setup mode plan values
        (.commit name owner fresh guard rest) suffix embedding wholeViews
          controls publicFrame archive) observed =
      (values owner (setup.proposalRecoveryQuery owner
        (setup.proposalRecoveryModel.infoOf owner trace))).map (fun sampled =>
          PublicationResult.success (phaseRecoveryDomainValue setup mode
            (embedding.event first) owner payload shape sampled.val.val)) := by
  classical
  intro first shape
  have active : owner ∉ controls.1 := by
    rw [← controlRead]
    exact survives
  have queried := ordinary_source_query_readback setup owner current trace survives ordinary
  rw [controlRead, addressRead, archiveRead] at queried
  let drawAt := fun key : setup.ProposalRecoveryComponent owner =>
    (values owner key).map (fun sampled => PublicationResult.success
      (phaseRecoveryDomainValue setup mode (embedding.event first) owner payload shape
        sampled.val.val))
  change (if owner ∈ controls.1 then PMF.pure .failure else drawAt
    (setup.commitRecoveryErasedInformation owner
      (setup.commitRecoveryNoMissInformation owner
        (setup.commitRecoveryErasedRead owner
          (ProtocolView.virtualBindings owner (setup.context.map Prod.fst).toFinset
            setup.program (wholeViews owner (Sum.inl observed))) controls
          ((publicFrame.sourcePublicAddressWord plan
            (ProtocolView.position owner setup.program
              (wholeViews owner (Sum.inl observed)))).reverse ++ [(none, (∅, 0, 0))]))),
      archive)) = drawAt
        (setup.proposalRecoveryQuery owner (setup.proposalRecoveryModel.infoOf owner trace))
  rw [ite_eq_right active]
  apply congrArg drawAt
  rw [read]
  exact queried


omit [Fintype Player] in
/-- The graph may have computed inherited excluded fields ahead of the source
cursor. Every such field still lies in the unconsumed commitment telescope
and contains its literal failed binding. -/
def ExcludedCommitFieldsAhead
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (excluded : Finset Player) (offset count : Nat)
    (config : (serviceGraph setup mode).Config) : Prop :=
  ∀ event ∈ config.cut.completed, offset ≤ event.val →
    event.val < offset + count ∧
      ∃ (owner : Player) (payload : L.Ty)
        (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload),
        owner ∈ excluded ∧
          (⟨.inr event, binding⟩ : FieldRef (graphLayout setup.program)
            (.binding owner payload)).get? config.store = some .failure

omit [Fintype Player] in
/-- The source cursor keeps the actual enriched history and the ordinary
compiler dictionaries. Graph completion recall is deliberately separate from
the source's original own-action recall. -/
structure PhaseProposalOrdinarySourceCursor
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (anchor : (phaseApplication runtime leaks).Control)
    (phase : RuntimePhase (serviceGraph setup mode))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) where
  source : SourceProgram.Config Player L Γ
  current : CommitRecoveryState setup.program
  trace : setup.proposalRecoveryProtocol.Trace (some current)
  refs : ContextRefs (graphLayout setup.program) Γ
  revelations : Revelations Γ
  registry : Registry Γ
  embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
    (block.prepend suffix)
  before : ContextRefsBefore refs embedding
  offset : Nat
  compiled : CompiledSuffix setup.program (block.prepend suffix) refs revelations registry
    embedding before offset
  lift : ProtocolState (block.prepend suffix) → ProtocolState setup.program
  origin : ProtocolSuffix setup.program (block.prepend suffix) lift
  views : ProtocolViewSuffix setup.program (block.prepend suffix) refs embedding lift
  config : (serviceGraph setup mode).Config
  point : current.point = lift (ProtocolState.entry (block.prepend suffix) source)
  agrees : refs.Agrees source.state config.store
  excluded : current.excluded = anchor.execution.application.current.excluded
  entryExcluded : current.entryExcluded = anchor.execution.application.current.excluded
  savedCommit : 0 < block.length → ProtocolState.atCommit setup.program current.saved = true
  savedEnd : 0 < block.length → ProtocolState.commitEnd setup.program current.saved =
    instructionCount suffix
  live : ∀ who, who ∉ current.excluded → source.BindingsHoldValues who
  smaller : ∀ event : (serviceGraph setup mode).EventId, event.val < offset →
    event ∈ config.cut.completed
  ahead : ExcludedCommitFieldsAhead setup mode current.excluded offset block.length config
  interval : ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
    embedding.event index ∈ phase.events
  low : anchor.execution.application.attempt.phase ≤ offset
  controls : 0 < block.length → setup.commitRecoveryPublic (some current) =
    ((anchor.execution.application.publicView.retired.map fun record =>
      record.2.sourceFailureFootprint.2).foldr (fun first last => first ∪ last) ∅ ∪
        anchor.execution.application.current.native.publicView.sourceFailureFootprint.1
          anchor.execution.application.attempt.phase,
      anchor.execution.application.attempt.generation,
      anchor.execution.application.attempt.phase)
  addresses : 0 < block.length → ∀ who, (setup.attemptPublicRecall who
      (setup.proposalRecoveryEraseTrace trace)).map
        (setup.commitRecoveryPublicAddress who) =
    (anchor.execution.application.publicView.sourcePublicAddressWord plan offset).reverse ++
      [(none, (∅, 0, 0))]
  proposals : ∀ who, who ∉ current.excluded → setup.proposalRecoveryArchive who
      (setup.proposalRecoveryModel.infoOf who trace) =
    PhaseProposal.sourceArchive anchor.execution.network.inputs

omit [DecidableEq Player] [Fintype Player] in
theorem runPlan_retains_store
    {graph : Vegas.EventGraph Player L} (plan : graph.EventPlan) :
    ∀ fuel (config final : graph.Config), final ∈ (graph.runPlan plan fuel config).support →
      ∀ field value, config.store field = some value → final.store field = some value := by
  intro fuel
  induction fuel with
  | zero =>
      intro config final supported field value stored
      rw [runPlan, PMF.mem_support_pure_iff] at supported
      cases supported
      exact stored
  | succ fuel ih =>
      intro config final supported field value stored
      rw [runPlan] at supported
      split at supported
      · rw [PMF.mem_support_pure_iff] at supported
        cases supported
        exact stored
      · obtain ⟨choice, _chosen, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
        obtain ⟨middle, moved, continued⟩ := (PMF.mem_support_bind_iff _ _ _).mp rest
        exact ih middle final continued field value
          (config.step_store_of_some middle choice.1.1 choice.1.2 choice.2 moved field value
            stored)

omit [Fintype Player] in
/-- The canonical potential retains all source fields already present at the
cursor, even when its auxiliary continuation runs outside the commitment
interval. No policy restriction on those later events is needed. -/
theorem canonicalContinuation_retains_context
    {graph : Vegas.EventGraph Player L} (profile : graph.BehavioralProfile)
    {Γ : SourceCtx Player L} (refs : ContextRefs graph.layout Γ)
    (state : State L Γ) (config : graph.Config) (agree : refs.Agrees state config.store)
    (key : graph.SemanticKey) (supported : key ∈
      (graph.canonicalContinuation profile config).support) :
    refs.Agrees state key.2.1 := by
  obtain ⟨final, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  intro name cell source
  apply (refs.get source).get?_preserved config.store final.store
    (runPlan_retains_store _ _ config final reached)
  exact agree source

/-- The chronological graph cursor is ready whenever its head has not
already been computed. Smaller completed ranks discharge every actual direct
dependency; no eager excluded-owner drain is assumed. -/
theorem PhaseProposalOrdinarySourceCursor.head_ready
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (anchor : (phaseApplication runtime leaks).Control)
    (phase : RuntimePhase (serviceGraph setup mode))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst} {guard : SourceGuard L Γ owner name payload}
    {rest : SourceProgram.CommitPrefix
      ((name, .commitment owner payload) :: Γ) (insert name O) Δ P}
    (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
      (.commit name owner fresh guard rest) suffix)
    (unfinished : cursor.embedding.event ⟨0, by simp [CommitPrefix.prepend, eventCount]⟩ ∉
      cursor.config.cut.completed) :
    cursor.config.cut.Ready
      (cursor.embedding.event ⟨0, by simp [CommitPrefix.prepend, eventCount]⟩) := by
  refine ⟨unfinished, ?_⟩
  intro prior predecessor
  apply cursor.smaller
  have ordered := (serviceGraph setup mode).order.predecessor_lt predecessor
  have rank := cursor.compiled.rankEq ⟨0, by simp [CommitPrefix.prepend, eventCount]⟩
  simp only [Nat.add_zero] at rank
  omega

theorem PhaseProposalOrdinarySourceCursor.active_head_unfinished
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (anchor : (phaseApplication runtime leaks).Control)
    (phase : RuntimePhase (serviceGraph setup mode))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst} {guard : SourceGuard L Γ owner name payload}
    {rest : SourceProgram.CommitPrefix
      ((name, .commitment owner payload) :: Γ) (insert name O) Δ P}
    (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
      (.commit name owner fresh guard rest) suffix)
    (active : owner ∉ cursor.current.excluded) :
    cursor.embedding.event ⟨0, by simp [CommitPrefix.prepend, eventCount]⟩ ∉
      cursor.config.cut.completed := by
  intro done
  let head : Fin (eventCount
      ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix)) :=
    ⟨0, by simp [CommitPrefix.prepend, eventCount]⟩
  have rank : (cursor.embedding.event head).val = cursor.offset := by
    simpa only [head, Fin.val_zero, Nat.add_zero] using cursor.compiled.rankEq head
  obtain ⟨_inside, actor, kind, binding, excluded, _failed⟩ :=
    cursor.ahead (cursor.embedding.event head) done rank.ge
  have typed : (serviceGraph setup mode).outputLayout (cursor.embedding.event head) =
      .binding owner payload := by
    change outputLayout setup.program (cursor.embedding.event head) = .binding owner payload
    simpa only [head, CommitPrefix.prepend, outputLayout, Fin.mk_zero, Fin.cases_zero] using
      cursor.embedding.layout_eq head
  obtain ⟨same, _kind⟩ := EventField.binding.inj (binding.symm.trans typed)
  exact active (same ▸ excluded)

/-- The current getter uses the empty consumed prefix at each residual
cursor. The advanced references therefore decode this exact source history
uniformly over all consistent preceding assignments. -/
theorem PhaseProposalOrdinarySourceCursor.head_query
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (anchor : (phaseApplication runtime leaks).Control)
    (anchorTrace : ((phaseApplication runtime leaks).protocol initial horizon scheduler).Trace
      (some anchor))
    (phase : RuntimePhase (serviceGraph setup mode))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst} {guard : SourceGuard L Γ owner name payload}
    {rest : SourceProgram.CommitPrefix
      ((name, .commitment owner payload) :: Γ) (insert name O) Δ P}
    (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
      (.commit name owner fresh guard rest) suffix)
    (active : owner ∉ cursor.current.excluded) :
    phaseProposalQuery? setup mode runtime leaks plan owner
        (cursor.embedding.event ⟨0, by simp [CommitPrefix.prepend, eventCount]⟩)
        (anchor.execution.recall owner)
        (phaseProposalBindingGraphView setup mode runtime leaks anchor.execution owner
          ((serviceGraph setup mode).playerObserve owner cursor.config)) =
      some (setup.proposalRecoveryQuery owner
        (setup.proposalRecoveryModel.infoOf owner cursor.trace)) := by
  have positive : 0 < (SourceProgram.CommitPrefix.commit name owner fresh guard rest).length :=
    Nat.zero_lt_succ _
  have live : ProtocolState.BindingsHoldValues owner setup.program cursor.current.point := by
    rw [cursor.point, cursor.origin.bindingsHoldValues_lift,
      ProtocolState.bindingsHoldValues_entry]
    exact cursor.live owner active
  exact phaseProposalBindingGraphView_query_of_compiled_prefix setup mode runtime leaks plan
    initial horizon scheduler anchor anchorTrace (.nil (Γ := Γ) (O := O))
    ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix)
    cursor.refs cursor.embedding cursor.lift cursor.views cursor.config cursor.source cursor.agrees
    owner ⟨0, by simp [CommitPrefix.prepend, eventCount]⟩ rfl cursor.current cursor.trace
    cursor.point active live (cursor.controls positive)
    (by
      have rank := cursor.compiled.rankEq ⟨0, by simp [CommitPrefix.prepend, eventCount]⟩
      simpa only [Fin.val_zero, Nat.add_zero, rank] using cursor.addresses positive owner)
    (cursor.proposals owner active)

omit [Fintype Player] in
/-- The frozen graph encoder reads the same typed value selected by the
ordinary source commitment. Its total default branch is not used. -/
theorem phaseRecoveryDomainValue_of_compiled_commit
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    {Γ : SourceCtx Player L} {O : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard next))
    (lift : ProtocolState (.commit name owner fresh guard next) → ProtocolState setup.program)
    (views : ProtocolViewSuffix setup.program (.commit name owner fresh guard next)
      refs embedding lift)
    (binding : (serviceGraph setup mode).outputLayout
      (embedding.event ⟨0, by simp [eventCount]⟩) = .binding owner payload)
    (value : L.Val payload) :
    phaseRecoveryDomainValue setup mode (embedding.event ⟨0, by simp [eventCount]⟩)
        owner payload binding (some ⟨.commit owner name payload (.success value), false⟩) =
      value := by
  let head : Fin (eventCount (.commit name owner fresh guard next)) :=
    ⟨0, by simp [eventCount]⟩
  let action : EventField.Action (outputLayout setup.program (embedding.event head)) :=
    cast (congrArg EventField.Action binding.symm) (.success value)
  have returned : cast (congrArg EventField.Action (embedding.layout_eq head)) action =
      (.success value : PublicationResult (L.Val payload)) := by
    simp only [action, cast_cast, cast_eq]
  have decoded : decodeEventAction setup.program (embedding.event head) action =
      some (.commit owner name payload (.success value)) := by
    rw [views.actionEq head action, returned]
    rfl
  have encoded := encodeEventAction?_decodeEventAction_eq_some setup.program
    (embedding.event head) action (.commit owner name payload (.success value)) decoded
  unfold phaseRecoveryDomainValue phaseRecoveryBindingData
  simp only [Option.elim_some, Bool.false_eq_true, ↓reduceIte, Option.bind_some]
  rw [encoded]
  simp only [Option.map_some, Option.getD_some, action, cast_cast, cast_eq]

private theorem sourcePublicAddressWord_succ
    {graph : Vegas.EventGraph Player L} (plan : RuntimePhasePlan graph)
    (view : PhasePublicView graph) (offset : Nat) (afterLow : view.attempt.phase ≤ offset) :
    view.sourcePublicAddressWord plan (offset + 1) =
      view.sourcePublicAddressWord plan offset ++
        [(some (offset + 1),
          (view.retired.map fun record => record.2.sourceFailureFootprint.2).foldr
              (fun first last => first ∪ last) ∅ ∪
            view.native.sourceFailureFootprint.1 view.attempt.phase,
          view.attempt.generation, view.attempt.phase)] := by
  have difference : offset + 1 - view.attempt.phase = offset - view.attempt.phase + 1 := by
    omega
  have cursor : view.attempt.phase + (offset - view.attempt.phase) + 1 = offset + 1 := by
    omega
  simp only [PhasePublicView.sourcePublicAddressWord, difference, List.range_succ,
    List.map_append, List.map_singleton, cursor, List.append_assoc, List.map_map,
    Function.comp_def]

omit [Fintype Player] in
private def ordinarySourceChoices
    (setup : Setup (Player := Player) (L := L))
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (draws : ∀ who, setup.CommitRecoveryValueChoice who
      (setup.proposalRecoveryQuery who (setup.proposalRecoveryModel.infoOf who trace)).1) :
    ∀ who, setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who trace) := fun who =>
  (setup.proposalRecoveryComponentChoice who
    (setup.proposalRecoveryModel.infoOf who trace)).symm
      (setup.proposalRecoveryComponentLabelChoice who
        (setup.proposalRecoveryQuery who (setup.proposalRecoveryModel.infoOf who trace))
          false (draws who).val)

omit [Fintype Player] in
private theorem ordinarySourceChoices_semantic
    (setup : Setup (Player := Player) (L := L))
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (draws : ∀ who, setup.CommitRecoveryValueChoice who
      (setup.proposalRecoveryQuery who (setup.proposalRecoveryModel.infoOf who trace)).1) :
    proposalRecoveryJoint (fun who => (ordinarySourceChoices setup current trace draws who).val) =
      fun who => (draws who).val.val := by
  funext who
  change ((draws who).val.val.map (fun move => ProposalRecoveryMove.label move false)).map
      (·.semantic) = _
  simp only [Option.map_map, Function.comp_def, ProposalRecoveryMove.label_semantic]
  change Option.map id (draws who).val.val = (draws who).val.val
  exact congrFun Option.map_id _

omit [Fintype Player] in
private theorem ordinarySourceChoices_labelled
    (setup : Setup (Player := Player) (L := L))
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (draws : ∀ who, setup.CommitRecoveryValueChoice who
      (setup.proposalRecoveryQuery who (setup.proposalRecoveryModel.infoOf who trace)).1) :
    (fun who => (ordinarySourceChoices setup current trace draws who).val) =
      fun who => (draws who).val.val.map ProposalRecoveryMove.ordinary := by
  funext who
  change ((draws who).val.val.map (fun move => ProposalRecoveryMove.label move false)) = _
  simp only [ProposalRecoveryMove.label_false]

omit [Fintype Player] in
theorem ordinary_commit_close_metadata
    (setup : Setup (Player := Player) (L := L))
    (current : CommitRecoveryState setup.program)
    (ordinary : current.excluded = current.entryExcluded)
    (point : ProtocolState setup.program) :
    let installed := current.install (point, current.excluded) (Finset.Subset.refl _)
    installed.close.point = point ∧
      installed.close.excluded = current.excluded ∧
      installed.close.entryExcluded = current.excluded ∧
      installed.close.generation = current.generation := by
  intro installed
  have noFailure : ¬ installed.NewFailure := by
    simp only [CommitRecoveryState.NewFailure, installed, CommitRecoveryState.install, ordinary,
      Finset.sdiff_self, Finset.not_nonempty_empty, not_false_eq_true]
  refine ⟨installed.close_point_of_no_new_failure noFailure,
    installed.close_excluded, ?_, installed.close_generation_of_no_new_failure noFailure⟩
  unfold CommitRecoveryState.close
  split
  · rfl
  · split
    · exact ordinary.symm
    · rfl

omit [Fintype Player] in
private theorem ordinary_commit_close_saved
    (setup : Setup (Player := Player) (L := L))
    (current : CommitRecoveryState setup.program)
    (committing : ProtocolState.atCommit setup.program current.saved = true)
    (point : ProtocolState setup.program)
    (beforeEnd : ProtocolState.commitEnd setup.program current.saved <
      ProtocolState.remaining setup.program point) :
    (current.install (point, current.excluded) (Finset.Subset.refl _)).close =
      current.install (point, current.excluded) (Finset.Subset.refl _) := by
  exact CommitRecoveryState.close_eq_self_of_remaining_gt _ committing beforeEnd

omit [Fintype Player] in
theorem proposalRecovery_localStep_commit_attempt
    (setup : Setup (Player := Player) (L := L))
    {Γ : SourceCtx Player L} {O : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (tail : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (lift : ProtocolState (.commit name owner fresh guard tail) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (.commit name owner fresh guard tail) lift)
    (source : SourceProgram.Config Player L Γ)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (point : current.point = lift (.inl source))
    (choices : ∀ who, setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who trace))
    (next : setup.proposalRecoveryProtocol.History)
    (realized : next ∈ (setup.proposalRecoveryModel.localStep ⟨some current, trace⟩
      choices).support) :
    ∃ (finished : SourceProgram.Config Player L ((name, .commitment owner payload) :: Γ))
      (after : Finset Player)
      (attempt : (SourceProgram.CommitPrefix.commit (O := O)
        name owner fresh guard .nil).Attempt source current.excluded finished after)
      (monotone : current.excluded ⊆ after),
      attempt.joints = [proposalRecoveryJoint (fun who => (choices who).val)] ∧
      next.state = some ((current.install
        (lift (.inr (ProtocolState.entry tail finished)), after) monotone).close) ∧
      setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace next.trace) =
        attempt.joints.reverse ++
          setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace trace) ∧
      setup.proposalRecoveryJointRecall next.trace =
        (fun who => (choices who).val) :: setup.proposalRecoveryJointRecall trace := by
  have running : ¬ setup.proposalRecoveryProtocol.terminal (some current) := by
    intro stopped
    have zero := (ProtocolState.remaining_zero_iff_terminal setup.program current.point).mpr stopped
    rw [point, origin.remaining_lift] at zero
    change instructionCount tail + 1 = 0 at zero
    omega
  let joint := fun who => (choices who).val
  let legal : setup.proposalRecoveryProtocol.Legal (some current) joint :=
    setup.proposalRecoveryProtocol.legal_of_legalOption running fun who =>
      (setup.proposalRecoveryModel.menu_adequate who trace (choices who).val).mp
        (choices who).property
  rw [InformationModel.localStep, dite_eq_right running,
    PMF.mem_support_bindOnSupport_iff] at realized
  obtain ⟨actual, actualSupport, landed⟩ := realized
  rw [PMF.mem_support_pure_iff] at landed
  subst next
  change actual ∈ ((current.step (proposalRecoveryJoint joint)).map some).support at actualSupport
  obtain ⟨target, moved, same⟩ := (PMF.mem_support_map_iff _ _ _).mp actualSupport
  cases same
  obtain ⟨raw, rawSupport, closed⟩ := current.step_raw_result (proposalRecoveryJoint joint)
    target moved
  have semanticLegal : (SourceProgram.commitRecoveryProtocol setup.program
      (setup.initialConfig setup.initialLaw.support_nonempty.choose)).Legal current
        (proposalRecoveryJoint joint) := by
    change setup.commitRecoveryProtocol.Legal (some current) (proposalRecoveryJoint joint)
    exact setup.proposalRecovery_erase_legal joint legal
  obtain ⟨finished, after, attempt, word, rawEq⟩ := commitRecovery_commit_instruction_attempt
    (setup.initialConfig setup.initialLaw.support_nonempty.choose) guard tail origin source current
      point (proposalRecoveryJoint joint) semanticLegal raw.1 rawSupport
  have afterEq : raw.val.2 = after := congrArg Prod.snd rawEq
  have monotone : current.excluded ⊆ after := afterEq ▸ raw.2
  have rawSame : raw = ⟨(lift (.inr (ProtocolState.entry tail finished)), after), monotone⟩ :=
    Subtype.ext rawEq
  have closes : target = (current.install
      (lift (.inr (ProtocolState.entry tail finished)), after) monotone).close := by
    simpa only [rawSame] using closed
  refine ⟨finished, after, attempt, monotone, word,
    ?_, ?_, ?_⟩
  · exact congrArg some closes
  · rw [word]
    rfl
  · rfl

omit [Fintype Player] [IExpr.ResultTypes L] in
theorem proper_single_commit_attempt
    {Γ : SourceCtx Player L} {O : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst} {guard : SourceGuard L Γ owner name payload}
    {entry : SourceProgram.Config Player L Γ} {excluded : Finset Player}
    {finished : SourceProgram.Config Player L ((name, .commitment owner payload) :: Γ)}
    {after : Finset Player}
    (attempt : (SourceProgram.CommitPrefix.commit (O := O)
      name owner fresh guard .nil).Attempt entry excluded finished after)
    (joint : Player → Option (CommitRecoveryMove Player L)) (word : attempt.joints = [joint])
    (proper : ∀ who move, joint who = some move →
      move.missing = false ∧ ¬ move.action.IsFailure) :
    after = excluded ∧
      ((∀ who, who ∉ excluded → entry.BindingsHoldValues who) →
        ∀ who, who ∉ after → finished.BindingsHoldValues who) ∧
      (owner ∈ excluded → finished = automaticCommit name owner payload entry) ∧
      (owner ∉ excluded → ∃ value : L.Val payload,
        finished = commitSuccessor name guard entry (.success value) ∧
          joint owner = some ⟨.commit owner name payload (.success value), false⟩) := by
  cases attempt with
  | excluded inactive later =>
      cases later
      refine ⟨rfl, ?_, fun _ => rfl, fun active => (active inactive).elim⟩
      intro live who surviving readName readPayload cell
      cases cell with
      | here => exact (surviving inactive).elim
      | there cell => exact live who surviving cell
  | active active result missed missingFailure later =>
      cases later
      have selected : joint owner = some ⟨.commit owner name payload result, missed⟩ := by
        change [(fun who => if who = owner then
          some ⟨.commit owner name payload result, missed⟩ else none)] = [joint] at word
        have same := congrArg (fun moves => moves owner) (List.singleton_inj.mp word)
        simpa only [ite_true] using same.symm
      obtain ⟨notMissed, notFailed⟩ := proper owner _ selected
      change missed = false at notMissed
      subst missed
      cases result with
      | failure => exact (notFailed rfl).elim
      | success value =>
          refine ⟨rfl, ?_, fun inactive => (active inactive).elim, fun _ => ⟨value, rfl, selected⟩⟩
          intro live who surviving readName readPayload cell
          cases cell with
          | here => exact ⟨value, rfl⟩
          | there cell => exact live who surviving cell

omit [Fintype Player] in
private theorem ordinary_graph_cursor_complete
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (excluded : Finset Player) (offset count : Nat)
    (config : (serviceGraph setup mode).Config)
    (event : (serviceGraph setup mode).EventId) (rank : event.val = offset)
    (ready : config.cut.Ready event) (action : (serviceGraph setup mode).Action event)
    (value : ((serviceGraph setup mode).outputLayout event).Value)
    (smaller : ∀ query : (serviceGraph setup mode).EventId, query.val < offset →
      query ∈ config.cut.completed)
    (ahead : ExcludedCommitFieldsAhead setup mode excluded offset (count + 1) config) :
    let next := config.complete event ready action value
    (∀ query : (serviceGraph setup mode).EventId, query.val < offset + 1 →
      query ∈ next.cut.completed) ∧
      ExcludedCommitFieldsAhead setup mode excluded (offset + 1) count next := by
  intro next
  constructor
  · intro query before
    by_cases earlier : query.val < offset
    · exact Finset.mem_insert_of_mem (smaller query earlier)
    · have same : query = event := Fin.ext (by omega)
      subst query
      exact Finset.mem_insert_self _ _
  · intro query done later
    have different : query ≠ event := by
      intro same
      subst query
      omega
    have wasDone : query ∈ config.cut.completed :=
      (Finset.mem_insert.mp done).resolve_left different
    obtain ⟨inside, owner, payload, binding, inactive, failed⟩ := ahead query wasDone (by omega)
    refine ⟨by omega, owner, payload, binding, inactive, ?_⟩
    exact (⟨.inr query, binding⟩ : FieldRef (graphLayout setup.program)
      (.binding owner payload)).get?_preserved config.store next.store
        (config.complete_store_of_some event ready action value) .failure failed

omit [Fintype Player] in
private theorem ordinary_graph_cursor_stutter
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (excluded : Finset Player) (offset count : Nat)
    (config : (serviceGraph setup mode).Config)
    (event : (serviceGraph setup mode).EventId) (rank : event.val = offset)
    (done : event ∈ config.cut.completed)
    (smaller : ∀ query : (serviceGraph setup mode).EventId, query.val < offset →
      query ∈ config.cut.completed)
    (ahead : ExcludedCommitFieldsAhead setup mode excluded offset (count + 1) config) :
    (∀ query : (serviceGraph setup mode).EventId, query.val < offset + 1 →
      query ∈ config.cut.completed) ∧
      ExcludedCommitFieldsAhead setup mode excluded (offset + 1) count config := by
  constructor
  · intro query before
    by_cases earlier : query.val < offset
    · exact smaller query earlier
    · have same : query = event := Fin.ext (by omega)
      exact same ▸ done
  · intro query completed later
    obtain ⟨inside, owner, payload, binding, inactive, failed⟩ :=
      ahead query completed (by omega)
    exact ⟨by omega, owner, payload, binding, inactive, failed⟩

omit [Fintype Player] in
private def PhaseProposalOrdinarySourceCursor.advance
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (anchor : (phaseApplication runtime leaks).Control)
    (phase : RuntimePhase (serviceGraph setup mode))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (rest : SourceProgram.CommitPrefix
      ((name, .commitment owner payload) :: Γ) (insert name O) Δ P)
    (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
      (.commit name owner fresh guard rest) suffix)
    (nextSource : SourceProgram.Config Player L ((name, .commitment owner payload) :: Γ))
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some cursor.current) joint)
    (live : ∀ who, who ∉ cursor.current.excluded → nextSource.BindingsHoldValues who)
    (nextConfig : (serviceGraph setup mode).Config) :
    let head : Fin (eventCount
      ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix)) :=
      ⟨0, by simp [CommitPrefix.prepend, eventCount]⟩
    let field : FieldRef (graphLayout setup.program) (.binding owner payload) :=
      ⟨.inr (cursor.embedding.event head), by
        change outputLayout setup.program (cursor.embedding.event head) = .binding owner payload
        simpa only [head, CommitPrefix.prepend, outputLayout, Fin.mk_zero, Fin.cases_zero] using
          cursor.embedding.layout_eq head⟩
    let target := (cursor.current.install
      (cursor.lift (.inr (ProtocolState.entry (rest.prepend suffix) nextSource)),
        cursor.current.excluded) (Finset.Subset.refl _)).close
    ∀ supported : some target ∈ (setup.proposalRecoveryProtocol.step (some cursor.current)
      ⟨joint, legal⟩).support,
    (cursor.refs.cons (name := name) (cell := .commitment owner payload) field).Agrees
        nextSource.state nextConfig.store →
    (∀ event : (serviceGraph setup mode).EventId, event.val < cursor.offset + 1 →
      event ∈ nextConfig.cut.completed) →
    ExcludedCommitFieldsAhead setup mode cursor.current.excluded (cursor.offset + 1)
      rest.length nextConfig →
    PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase rest suffix := by
  intro head field target supported agreement smaller ahead
  let nextTrace := cursor.trace.extend joint legal supported
  have positive : 0 < (SourceProgram.CommitPrefix.commit name owner fresh guard rest).length :=
    Nat.zero_lt_succ _
  have ordinary : cursor.current.excluded = cursor.current.entryExcluded :=
    cursor.excluded.trans cursor.entryExcluded.symm
  have metadata := ordinary_commit_close_metadata setup cursor.current ordinary
    (cursor.lift (.inr (ProtocolState.entry (rest.prepend suffix) nextSource)))
  have unchanged (remaining : 0 < rest.length) : target = cursor.current.install
      (cursor.lift (.inr (ProtocolState.entry (rest.prepend suffix) nextSource)),
        cursor.current.excluded) (Finset.Subset.refl _) := by
    apply ordinary_commit_close_saved setup cursor.current (cursor.savedCommit positive)
    rw [cursor.origin.remaining_lift]
    change ProtocolState.commitEnd setup.program cursor.current.saved <
      ProtocolState.remaining (rest.prepend suffix)
        (ProtocolState.entry (rest.prepend suffix) nextSource)
    rw [ProtocolState.remaining_entry, rest.instructionCount_prepend,
      cursor.savedEnd positive]
    omega
  let tailEmbedding := cursor.embedding.tail (rest.prepend suffix)
    (by simp [CommitPrefix.prepend, eventCount]) (fun _ => rfl)
  let tailRefs := cursor.refs.cons (name := name) (cell := .commitment owner payload) field
  let tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
    intro readName cell source remaining
    cases source with
    | here =>
        change (cursor.embedding.event head).val <
          (cursor.embedding.event (Fin.succ remaining)).val
        apply cursor.embedding.strictMono
        exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
    | there source => exact cursor.before source (Fin.succ remaining)
  let obligation : Obligation ((name, .commitment owner payload) :: Γ) :=
    { owner := owner, subject := name, payload := payload, source := .here,
      guard := guard.weaken }
  refine
    { source := nextSource
      current := target
      trace := nextTrace
      refs := tailRefs
      revelations := Revelations.weaken cursor.revelations
      registry := obligation :: cursor.registry.weaken
      embedding := tailEmbedding
      before := tailBefore
      offset := cursor.offset + 1
      compiled := ?_
      lift := fun point => cursor.lift (.inr point)
      origin := ProtocolSuffix.commitTail fresh guard (rest.prepend suffix) cursor.origin
      views := ?_
      config := nextConfig
      point := metadata.1
      agrees := agreement
      excluded := metadata.2.1.trans cursor.excluded
      entryExcluded := metadata.2.2.1.trans cursor.excluded
      savedCommit := ?_
      savedEnd := ?_
      live := ?_
      smaller := smaller
      ahead := ?_
      interval := ?_
      low := by have lower := cursor.low; omega
      controls := ?_
      addresses := ?_
      proposals := ?_ }
  · exact cursor.compiled.commitTail setup.program fresh guard (rest.prepend suffix)
      cursor.refs cursor.revelations cursor.registry cursor.embedding cursor.before cursor.offset
  · exact ProtocolViewSuffix.commitTail setup.program fresh guard (rest.prepend suffix)
      cursor.refs cursor.embedding cursor.lift cursor.views
  · intro remaining
    rw [unchanged remaining]
    exact cursor.savedCommit positive
  · intro remaining
    rw [unchanged remaining]
    exact cursor.savedEnd positive
  · rw [metadata.2.1]
    exact live
  · rw [metadata.2.1]
    exact ahead
  · intro index inside
    exact cursor.interval (Fin.succ index) (by
      change index.val + 1 < rest.length + 1
      omega)
  · intro remaining
    rw [unchanged remaining]
    exact cursor.controls positive
  · intro remaining who
    have newControl : setup.commitRecoveryPublic (some target) =
        setup.commitRecoveryPublic (some cursor.current) := by
      rw [unchanged remaining]
      rfl
    have position : instructionCount setup.program -
        ProtocolState.remaining setup.program target.point = cursor.offset + 1 := by
      rw [metadata.1, cursor.origin.remaining_lift]
      simp only [CommitPrefix.prepend, ProtocolState.remaining, Sum.elim_inr,
        ProtocolState.remaining_entry]
      have count := cursor.compiled.countEq
      simp only [eventCount_eq_instructionCount, CommitPrefix.prepend, instructionCount] at count
      omega
    have address : target.publicAddress =
        (some (cursor.offset + 1), setup.commitRecoveryPublic (some cursor.current)) := by
      rw [← newControl]
      exact Prod.ext (congrArg some position) rfl
    have extended : (setup.attemptPublicRecall who
          (setup.proposalRecoveryEraseTrace nextTrace)).map
            (setup.commitRecoveryPublicAddress who) =
        target.publicAddress :: (setup.attemptPublicRecall who
          (setup.proposalRecoveryEraseTrace cursor.trace)).map
            (setup.commitRecoveryPublicAddress who) := by
      rw [setup.commitRecovery_publicRecall_addresses,
        setup.commitRecovery_publicRecall_addresses]
      simp only [nextTrace, Setup.proposalRecoveryEraseTrace,
        setup.recoveryAddressWord_extend, Option.elim_some, List.reverse_append,
        List.reverse_singleton, List.nil_append, List.cons_append]
    rw [extended, address, cursor.controls positive, cursor.addresses positive who,
      sourcePublicAddressWord_succ plan anchor.execution.application.publicView cursor.offset
        cursor.low]
    simp only [List.reverse_append, List.reverse_singleton, List.nil_append,
      List.cons_append]
    rfl
  · intro who surviving
    rw [setup.proposalRecoveryArchive_extend]
    have committing : ProtocolState.atCommit setup.program cursor.current.point = true := by
      rw [cursor.point, cursor.origin.atCommit_lift]
      rfl
    rw [setup.proposalRecoveryProposalOf_eq_none_of_atCommit cursor.current committing joint,
      Option.toList_none, List.toFinset_nil, Finset.union_empty]
    have sameExcluded : target.excluded = cursor.current.excluded := metadata.2.1
    exact cursor.proposals who (sameExcluded ▸ surviving)

omit [Fintype Player] in
private def OrdinaryCommitGraphSuccessor
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (excluded : Finset Player) (config : (serviceGraph setup mode).Config)
    (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (result : PublicationResult (L.Val payload)) (next : (serviceGraph setup mode).Config) : Prop :=
  (owner ∈ excluded ∧ event ∈ config.cut.completed ∧ next = config ∧
    (⟨.inr event, binding⟩ : FieldRef (graphLayout setup.program)
      (.binding owner payload)).get? config.store = some .failure) ∨
  ∃ ready : config.cut.Ready event,
    next = config.complete event ready
      (cast (congrArg EventField.Action binding.symm) result)
      (cast (congrArg EventField.Value binding.symm) result)

omit [DecidableEq Player] [Fintype Player] in
private theorem completed_binding_read
    {graph : Vegas.EventGraph Player L} (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (result : PublicationResult (L.Val payload)) :
    (⟨.inr event, binding⟩ : FieldRef graph.layout (.binding owner payload)).get?
      (config.complete event ready
        (cast (congrArg EventField.Action binding.symm) result)
        (cast (congrArg EventField.Value binding.symm) result)).store = some result := by
  rw [FieldRef.get?, EventGraph.store_complete]
  simp only [Function.update_self]
  change cast (congrArg (fun kind => Option kind.Value) binding)
    (some (cast (congrArg EventField.Value binding.symm) result)) = _
  have castSome {A B : Type} (same : A = B) (item : A) :
      cast (congrArg Option same) (some item) = some (cast same item) := by
    cases same
    rfl
  rw [castSome (congrArg EventField.Value binding)]
  simp only [cast_cast, cast_eq]

private theorem PhaseProposalOrdinarySourceCursor.row_coupling
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (anchor : (phaseApplication runtime leaks).Control)
    (anchorTrace : ((phaseApplication runtime leaks).protocol initial horizon scheduler).Trace
      (some anchor))
    (phase : RuntimePhase (serviceGraph setup mode))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (rest : SourceProgram.CommitPrefix
      ((name, .commitment owner payload) :: Γ) (insert name O) Δ P)
    (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
      (.commit name owner fresh guard rest) suffix) :
    let head : Fin (eventCount
      ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix)) :=
      ⟨0, by simp [CommitPrefix.prepend, eventCount]⟩
    let event := cursor.embedding.event head
    ∃ binding : (serviceGraph setup mode).outputLayout event = .binding owner payload,
    ∃ joint : PMF (setup.proposalRecoveryProtocol.History × (serviceGraph setup mode).Config),
      joint.map Prod.fst = setup.proposalRecoveryModel.runBehavioralFrom
        (setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
        1 ⟨some cursor.current, cursor.trace⟩ ∧
      joint.bind (fun pair => (serviceGraph setup mode).canonicalContinuation
        (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor.execution phase
          values) pair.2) =
        (serviceGraph setup mode).canonicalContinuation
          (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor.execution phase
            values) cursor.config ∧
      joint.map (fun pair =>
        (⟨.inr event, binding⟩ : FieldRef (graphLayout setup.program)
          (.binding owner payload)).get? pair.2.store) =
        (if owner ∈ cursor.current.excluded then PMF.pure .failure else
          (values owner (setup.proposalRecoveryQuery owner
            (setup.proposalRecoveryModel.infoOf owner cursor.trace))).map
              (fun choice => PublicationResult.success
                (phaseRecoveryDomainValue setup mode event owner payload binding
                  choice.val.val))).map some ∧
      ∀ pair ∈ joint.support,
        ∃ draws : ∀ who, setup.CommitRecoveryValueChoice who
          (setup.proposalRecoveryQuery who
            (setup.proposalRecoveryModel.infoOf who cursor.trace)).1,
          pair.1 ∈ (setup.proposalRecoveryModel.localStep ⟨some cursor.current, cursor.trace⟩
            (ordinarySourceChoices setup cursor.current cursor.trace draws)).support ∧
          OrdinaryCommitGraphSuccessor setup mode cursor.current.excluded cursor.config
            event owner payload binding
            (if owner ∈ cursor.current.excluded then .failure else
              .success (phaseRecoveryDomainValue setup mode event owner payload binding
                (draws owner).val.val)) pair.2 := by
  intro head event
  let graph := serviceGraph setup mode
  let profile := phaseProposalBindingPotentialProfile setup mode runtime leaks plan
    anchor.execution phase values
  let source := setup.proposalRecoveryNormalizedTrembledProfile
    0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
  let history : setup.proposalRecoveryProtocol.History := ⟨some cursor.current, cursor.trace⟩
  have binding : graph.outputLayout event = .binding owner payload := by
    change outputLayout setup.program (cursor.embedding.event head) = .binding owner payload
    simpa only [head, CommitPrefix.prepend, outputLayout, Fin.mk_zero, Fin.cases_zero] using
      cursor.embedding.layout_eq head
  have code : cast (congrArg (EventCode graph.layout) binding) (graph.nodes event) =
      .bind owner payload := by
    change cast (congrArg (EventCode (graphLayout setup.program)) binding)
      ((toEventGraph setup.program).nodes event) = .bind owner payload
    simpa only [event, head, CommitPrefix.prepend, compileRankedNodes, Fin.mk_zero,
      Fin.cases_zero] using cursor.compiled.nodeEq head
  have rank : event.val = cursor.offset := by
    simpa only [event, head, Fin.val_zero, Nat.add_zero] using cursor.compiled.rankEq head
  by_cases inactive : owner ∈ cursor.current.excluded
  · let next : graph.Config := if done : event ∈ cursor.config.cut.completed then cursor.config
      else cursor.config.complete event
        (cursor.head_ready setup mode runtime leaks plan anchor phase suffix done)
        (cast (congrArg EventField.Action binding.symm) .failure)
        (cast (congrArg EventField.Value binding.symm) .failure)
    have harmonic : graph.canonicalContinuation profile next =
        graph.canonicalContinuation profile cursor.config := by
      dsimp only [next]
      split
      · rfl
      · rename_i unfinished
        exact (phaseProposalBindingPotentialProfile_excluded_step setup mode runtime leaks plan
          anchor.execution phase values cursor.config event
          (cursor.head_ready setup mode runtime leaks plan anchor phase suffix unfinished)
          owner payload binding code (cursor.excluded ▸ inactive)).2
    let joint := (setup.proposalRecoveryModel.runBehavioralFrom source 1 history).map
      (fun nextHistory => (nextHistory, next))
    refine ⟨binding, joint, ?_, ?_, ?_, ?_⟩
    · rw [PMF.map_comp]
      change (setup.proposalRecoveryModel.runBehavioralFrom source 1 history).map id = _
      exact PMF.map_id _
    · rw [PMF.bind_map]
      change (setup.proposalRecoveryModel.runBehavioralFrom source 1 history).bind
        (fun _ => graph.canonicalContinuation profile next) = _
      rw [PMF.bind_const]
      exact harmonic
    · have stored : (⟨.inr event, binding⟩ : FieldRef (graphLayout setup.program)
          (.binding owner payload)).get? next.store = some .failure := by
        dsimp only [next]
        split
        · rename_i done
          obtain ⟨_inside, actor, kind, typed, _excluded, failed⟩ :=
            cursor.ahead event done rank.ge
          obtain ⟨sameOwner, sameKind⟩ := EventField.binding.inj (typed.symm.trans binding)
          subst actor
          subst kind
          exact failed
        · exact completed_binding_read cursor.config event _ owner payload binding .failure
      simp only [joint, PMF.map_comp, Function.comp_def, stored,
        inactive, ↓reduceIte, PMF.pure_map]
      exact PMF.map_const _ _
    · intro pair member
      obtain ⟨nextHistory, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      rw [setup.proposalRecovery_ordinary_run_succ values 0 history] at supported
      change nextHistory ∈ ((independentProduct (fun who => values who
        (setup.proposalRecoveryQuery who
          (setup.proposalRecoveryModel.infoOf who cursor.trace)))).bind
          (fun draws => (setup.proposalRecoveryModel.localStep history
            (ordinarySourceChoices setup cursor.current cursor.trace draws)).bind PMF.pure)).support
              at supported
      simp only [PMF.bind_pure] at supported
      obtain ⟨draws, _drawn, localSupport⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      refine ⟨draws, localSupport, ?_⟩
      by_cases done : event ∈ cursor.config.cut.completed
      · obtain ⟨_inside, actor, kind, typed, excluded, failed⟩ :=
          cursor.ahead event done rank.ge
        obtain ⟨sameOwner, sameKind⟩ := EventField.binding.inj (typed.symm.trans binding)
        subst actor
        subst kind
        refine Or.inl ⟨inactive, done, ?_, failed⟩
        simp only [next, dite_eq_left done]
      · refine Or.inr ⟨cursor.head_ready setup mode runtime leaks plan anchor phase suffix done,
          ?_⟩
        simp only [next, dite_eq_right done, inactive, ↓reduceIte]
  · have unfinished := cursor.active_head_unfinished setup mode runtime leaks plan anchor phase
      suffix inactive
    have ready := cursor.head_ready setup mode runtime leaks plan anchor phase suffix unfinished
    have queried := cursor.head_query setup mode runtime leaks plan initial horizon scheduler anchor
      anchorTrace phase suffix inactive
    obtain ⟨joint, first, second, supported⟩ :=
      phaseProposalBindingPotentialProfile_source_coupling setup mode runtime leaks plan
        anchor.execution phase values cursor.config event ready owner payload binding code
          (cursor.interval head (Nat.zero_lt_succ _)) (cursor.excluded ▸ inactive) cursor.current
          cursor.trace queried
    refine ⟨binding, joint, first, ?_, ?_, ?_⟩
    · change joint.bind ((graph.canonicalContinuation profile) ∘ Prod.snd) = _
      rw [← PMF.bind_map, second]
      exact phaseProposalBindingPotentialProfile_harmonic setup mode runtime leaks plan
        anchor.execution phase values cursor.config event ready
    · change joint.map ((fun config =>
          (⟨.inr event, binding⟩ : FieldRef (graphLayout setup.program)
            (.binding owner payload)).get? config.store) ∘ Prod.snd) = _
      rw [← PMF.map_comp, second,
        (phaseProposalBindingPotentialProfile_source_draw setup mode runtime leaks plan
          anchor.execution phase values cursor.config event ready owner payload binding code
            (cursor.interval head (Nat.zero_lt_succ _)) (cursor.excluded ▸ inactive)
              cursor.current cursor.trace queried).1]
      simp only [PMF.map_bind, commit_step cursor.config event ready binding code,
        PMF.pure_map, PMF.map_comp, Function.comp_def, inactive, ↓reduceIte]
      rw [← pmf_bind_pure_eq_map]
      apply congrArg (PMF.bind (values owner (setup.proposalRecoveryQuery owner
        (setup.proposalRecoveryModel.infoOf owner cursor.trace))))
      funext sampled
      apply congrArg PMF.pure
      exact completed_binding_read cursor.config event ready owner payload binding
        (.success (phaseRecoveryDomainValue setup mode event owner payload binding
          sampled.val.val))
    · intro pair member
      obtain ⟨draws, _drawn, localSupport, graphSupport⟩ := supported pair member
      refine ⟨draws, localSupport, Or.inr ⟨ready, ?_⟩⟩
      change pair.2 ∈ (cursor.config.step event ready
        (cast (congrArg EventField.Action binding.symm)
          (.success (phaseRecoveryDomainValue setup mode event owner payload binding
            (draws owner).val.val)))).support at graphSupport
      rw [commit_step cursor.config event ready binding code,
        PMF.mem_support_pure_iff] at graphSupport
      simpa only [inactive, ↓reduceIte] using graphSupport

/-- The supported relation retains the complete actual source history, its
typed ordinary attempt, every original joint and the final compiler dictionary
in the graph's complete semantic outcome. -/
def PhaseProposalOrdinarySourceBlockResult
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix))
    (lift : ProtocolState (block.prepend suffix) → ProtocolState setup.program)
    (source : SourceProgram.Config Player L Γ) (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (pair : setup.proposalRecoveryProtocol.History ×
      (serviceGraph setup mode).SemanticKey) : Prop :=
  ∃ (finished : SourceProgram.Config Player L Δ) (last : CommitRecoveryState setup.program)
    (lastTrace : setup.proposalRecoveryProtocol.Trace (some last))
    (attempt : block.Attempt source current.excluded finished last.excluded),
    pair.1 = ⟨some last, lastTrace⟩ ∧
      last.point = lift (block.liftPoint suffix (ProtocolState.entry suffix finished)) ∧
      last.excluded = current.excluded ∧
      last.generation = current.generation ∧
      (∀ who, who ∉ last.excluded → finished.BindingsHoldValues who) ∧
      (commitBlockRefs setup.program block suffix embedding refs).Agrees finished.state pair.2.2.1 ∧
      setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace lastTrace) =
        attempt.joints.reverse ++ setup.recoveryJointRecall
          (setup.proposalRecoveryEraseTrace trace) ∧
      setup.proposalRecoveryJointRecall lastTrace =
        attempt.joints.reverse.map
          (fun joint who => (joint who).map ProposalRecoveryMove.ordinary) ++
          setup.proposalRecoveryJointRecall trace

/-- Couple the actual finite ordinary enriched-source run and the existing
frozen graph continuation. Both inherited excluded-owner branches retain the
literal automatic source instruction, and the final source state includes its
real automatic close. The graph's own completion history is never substituted
for the original source history. -/
theorem phaseProposalBindingPotentialProfile_source_block_coupling
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (anchor : (phaseApplication runtime leaks).Control)
    (anchorTrace : ((phaseApplication runtime leaks).protocol initial horizon scheduler).Trace
      (some anchor))
    (phase : RuntimePhase (serviceGraph setup mode))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) :
    let controls : Finset Player × Nat × Nat :=
      ((anchor.execution.application.publicView.retired.map fun record =>
        record.2.sourceFailureFootprint.2).foldr (fun first last => first ∪ last) ∅ ∪
          anchor.execution.application.current.native.publicView.sourceFailureFootprint.1
            anchor.execution.application.attempt.phase,
        anchor.execution.application.attempt.generation,
        anchor.execution.application.attempt.phase)
    ∀ (suffix : SourceProgram Player L Δ P)
      (cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
        block suffix),
    ∃ joint : PMF (setup.proposalRecoveryProtocol.History ×
      (serviceGraph setup mode).SemanticKey),
      joint.map Prod.fst = setup.proposalRecoveryModel.runBehavioralFrom
        (setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
        block.length ⟨some cursor.current, cursor.trace⟩ ∧
      joint.map Prod.snd = (serviceGraph setup mode).canonicalContinuation
        (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor.execution phase
          values) cursor.config ∧
      (∀ pair ∈ joint.support, PhaseProposalOrdinarySourceBlockResult setup mode block suffix
        cursor.refs cursor.embedding cursor.lift cursor.source cursor.current cursor.trace
          pair) ∧
      ∀ (filler : SourceProgram.Config Player L Γ),
        (∀ who, who ∉ cursor.current.excluded → filler.view who = cursor.source.view who) →
        joint.map (fun pair => fillCommitPrefix setup.program block suffix cursor.embedding
          pair.2.2.1 filler) =
        block.prefixLaw suffix (ordinaryBlockProfile setup mode plan values block suffix
          cursor.embedding
            (fun who view => cursor.views.view who view) controls
            anchor.execution.application.publicView
            (PhaseProposal.sourceArchive anchor.execution.network.inputs)) filler := by
  intro controls
  classical
  let graph := serviceGraph setup mode
  let profile := phaseProposalBindingPotentialProfile setup mode runtime leaks plan
    anchor.execution phase values
  let source := setup.proposalRecoveryNormalizedTrembledProfile
    0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
  induction block with
  | nil =>
      intro suffix cursor
      let history : setup.proposalRecoveryProtocol.History := ⟨some cursor.current, cursor.trace⟩
      let joint := (graph.canonicalContinuation profile cursor.config).map
        (fun key => (history, key))
      refine ⟨joint, ?_, ?_, ?_, ?_⟩
      · rw [PMF.map_comp]
        change (graph.canonicalContinuation profile cursor.config).map
          (fun _ => history) = PMF.pure history
        exact PMF.map_const _ _
      · rw [PMF.map_comp]
        change (graph.canonicalContinuation profile cursor.config).map id = _
        exact PMF.map_id _
      · intro pair supported
        obtain ⟨key, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        refine ⟨cursor.source, cursor.current, cursor.trace, .nil _ _, rfl, cursor.point, rfl, rfl,
          cursor.live,
          canonicalContinuation_retains_context profile cursor.refs cursor.source.state
            cursor.config cursor.agrees key reached, rfl, rfl⟩
      · intro filler _same
        change joint.map (fun _ => filler) = PMF.pure filler
        exact PMF.map_const _ _
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      intro suffix cursor
      let head : Fin (eventCount
        ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix)) :=
        ⟨0, by simp [CommitPrefix.prepend, eventCount]⟩
      let event := cursor.embedding.event head
      let typed := ordinaryBlockProfile setup mode plan values
        (.commit name owner fresh guard rest) suffix cursor.embedding
          (fun who view => cursor.views.view who view) controls
          anchor.execution.application.publicView
          (PhaseProposal.sourceArchive anchor.execution.network.inputs)
      obtain ⟨binding, row, first, harmonic, rowRead, rowSupport⟩ :=
        cursor.row_coupling setup mode runtime
        leaks plan initial horizon scheduler anchor anchorTrace phase values fresh guard rest suffix
      let result := fun draws : ∀ who, setup.CommitRecoveryValueChoice who
          (setup.proposalRecoveryQuery who
            (setup.proposalRecoveryModel.infoOf who cursor.trace)).1 =>
        if owner ∈ cursor.current.excluded then PublicationResult.failure else
          .success (phaseRecoveryDomainValue setup mode event owner payload binding
            (draws owner).val.val)
      have branches (pair : setup.proposalRecoveryProtocol.History × graph.Config)
          (member : pair ∈ row.support) :
          ∃ joint : PMF (setup.proposalRecoveryProtocol.History × graph.SemanticKey),
            joint.map Prod.fst = setup.proposalRecoveryModel.runBehavioralFrom source
              rest.length pair.1 ∧
            joint.map Prod.snd = graph.canonicalContinuation profile pair.2 ∧
            (∀ final ∈ joint.support,
              PhaseProposalOrdinarySourceBlockResult setup mode
                (.commit name owner fresh guard rest) suffix cursor.refs cursor.embedding
                  cursor.lift cursor.source cursor.current cursor.trace final) ∧
            ∀ (filler : SourceProgram.Config Player L Γ),
              (∀ who, who ∉ cursor.current.excluded →
                filler.view who = cursor.source.view who) →
              joint.map (fun final => fillCommitPrefix setup.program
                (.commit name owner fresh guard rest) suffix cursor.embedding
                  final.2.2.1 filler) =
              rest.prefixLaw suffix (afterCommit typed)
                (commitSuccessor name guard filler
                  (((⟨.inr event, binding⟩ : FieldRef (graphLayout setup.program)
                    (.binding owner payload)).get? pair.2.store).getD .failure)) := by
        obtain ⟨draws, localSupport, graphStep⟩ := rowSupport pair member
        obtain ⟨middleSource, after, headAttempt, monotone, headWord, middleState, middleWord,
            _middleLabels⟩ :=
          proposalRecovery_localStep_commit_attempt setup fresh guard (rest.prepend suffix)
            cursor.lift cursor.origin cursor.source cursor.current cursor.trace cursor.point
              (ordinarySourceChoices setup cursor.current cursor.trace draws) pair.1 localSupport
        rw [ordinarySourceChoices_semantic] at headWord
        obtain ⟨afterEq, middleLive, automatic, value⟩ := proper_single_commit_attempt headAttempt
          _ headWord (fun who move selected => (draws who).property move selected)
        have middleLive := middleLive cursor.live
        cases afterEq
        let field : FieldRef (graphLayout setup.program) (.binding owner payload) :=
          ⟨.inr event, binding⟩
        have sourceResult : middleSource.state.get HasVar.here = result draws := by
          by_cases inactive : owner ∈ cursor.current.excluded
          · rw [automatic inactive]
            simp only [result, inactive, ↓reduceIte, automaticCommit]
            rfl
          · obtain ⟨actualValue, middleEq, selected⟩ := value inactive
            rw [middleEq]
            simp only [result, inactive, ↓reduceIte, selected]
            rw [phaseRecoveryDomainValue_of_compiled_commit setup mode fresh guard
              (rest.prepend suffix) cursor.refs cursor.embedding cursor.lift cursor.views
                binding actualValue]
            rfl
        have nextData :
            (cursor.refs.cons (name := name) (cell := .commitment owner payload) field).Agrees
              middleSource.state pair.2.store ∧
            (∀ query : graph.EventId, query.val < cursor.offset + 1 →
              query ∈ pair.2.cut.completed) ∧
            ExcludedCommitFieldsAhead setup mode cursor.current.excluded (cursor.offset + 1)
              rest.length pair.2 := by
          have rank : event.val = cursor.offset := by
            simpa only [event, head, Fin.val_zero, Nat.add_zero] using cursor.compiled.rankEq head
          rcases graphStep with ⟨inactive, graphDone, same, failed⟩ | ⟨ready, same⟩
          · rw [same]
            have geometry := ordinary_graph_cursor_stutter setup mode cursor.current.excluded
              cursor.offset rest.length cursor.config event rank graphDone cursor.smaller
                cursor.ahead
            refine ⟨?_, geometry⟩
            rw [automatic inactive]
            apply ContextRefs.Agrees.cons cursor.refs cursor.source.state cursor.config.store
              cursor.agrees (name := name) (cell := .commitment owner payload) field .failure
            exact failed
          · rw [same]
            let action := cast (congrArg EventField.Action binding.symm) (result draws)
            let stored := cast (congrArg EventField.Value binding.symm) (result draws)
            let nextConfig := cursor.config.complete event ready action stored
            have oldRefs : cursor.refs.Agrees cursor.source.state nextConfig.store :=
              ContextRefs.Agrees.complete ready action stored cursor.refs cursor.source.state
                cursor.agrees (fun selected => cursor.before selected head)
            have headStored : field.get? nextConfig.store = some (result draws) := by
              rw [FieldRef.get?, EventGraph.store_complete]
              simp only [field, Function.update_self]
              change cast (congrArg (fun kind => Option kind.Value) binding)
                (some (cast (congrArg EventField.Value binding.symm) (result draws))) = _
              have castSome {A B : Type} (same : A = B) (item : A) :
                  cast (congrArg Option same) (some item) = some (cast same item) := by
                cases same
                rfl
              rw [castSome (congrArg EventField.Value binding)]
              simp only [cast_cast, cast_eq]
            have sourceState : middleSource.state =
                Env.cons (x := name) (result draws) cursor.source.state := by
              by_cases inactive : owner ∈ cursor.current.excluded
              · rw [automatic inactive]
                simp only [result, inactive, ↓reduceIte]
                rfl
              · obtain ⟨actualValue, same, _selected⟩ := value inactive
                rw [same]
                rw [same] at sourceResult
                change PublicationResult.success actualValue = result draws at sourceResult
                exact congrArg (fun item => Env.cons (x := name) item cursor.source.state)
                  sourceResult
            have geometry := ordinary_graph_cursor_complete setup mode cursor.current.excluded
              cursor.offset rest.length cursor.config event rank ready action stored cursor.smaller
                cursor.ahead
            refine ⟨?_, geometry⟩
            rw [sourceState]
            exact ContextRefs.Agrees.cons cursor.refs cursor.source.state nextConfig.store oldRefs
              (name := name) (cell := .commitment owner payload) field (result draws) headStored
        have running : ¬ setup.proposalRecoveryProtocol.terminal (some cursor.current) := by
          intro stopped
          have zero := (ProtocolState.remaining_zero_iff_terminal setup.program
            cursor.current.point).mpr stopped
          rw [cursor.point, cursor.origin.remaining_lift] at zero
          change instructionCount (rest.prepend suffix) + 1 = 0 at zero
          omega
        let choices := ordinarySourceChoices setup cursor.current cursor.trace draws
        let sourceJoint := fun who => (choices who).val
        let legal := setup.proposalRecoveryProtocol.legal_of_legalOption running fun who =>
          (setup.proposalRecoveryModel.menu_adequate who cursor.trace (choices who).val).mp
            (choices who).property
        rcases pair with ⟨middleHistory, nextConfig⟩
        rw [InformationModel.localStep, dite_eq_right running,
          PMF.mem_support_bindOnSupport_iff] at localSupport
        obtain ⟨actual, actualSupport, landed⟩ := localSupport
        rw [PMF.mem_support_pure_iff] at landed
        cases landed
        cases middleState
        let nextCursor := cursor.advance setup mode runtime leaks plan anchor phase fresh guard rest
          suffix middleSource sourceJoint legal middleLive nextConfig actualSupport nextData.1
            nextData.2.1 nextData.2.2
        obtain ⟨joint, left, right, related, tailMarginal⟩ := ih suffix nextCursor
        refine ⟨joint, left, right, ?_, ?_⟩
        · intro final reached
          obtain ⟨finished, last, lastTrace, tailAttempt, historyEq, lastPoint, lastExcluded,
            lastGeneration, lastLive, agreement, lastWord, lastLabelledWord⟩ :=
              related final reached
          have nextExcluded : nextCursor.current.excluded = cursor.current.excluded := by
            exact ordinary_commit_close_metadata setup cursor.current
              (cursor.excluded.trans cursor.entryExcluded.symm) _ |>.2.1
          let tailTyped : rest.Attempt middleSource cursor.current.excluded finished
              last.excluded :=
            nextExcluded ▸ tailAttempt
          let attempt := headAttempt.prepend tailTyped
          have nextGeneration : nextCursor.current.generation = cursor.current.generation := by
            exact ordinary_commit_close_metadata setup cursor.current
              (cursor.excluded.trans cursor.entryExcluded.symm) _ |>.2.2.2
          have tailWord : tailTyped.joints = tailAttempt.joints := by
            have transport {first second : Finset Player} (same : first = second)
                (attempt : rest.Attempt middleSource first finished last.excluded) :
                (same ▸ attempt).joints = attempt.joints := by cases same; rfl
            exact transport nextExcluded tailAttempt
          refine ⟨finished, last, lastTrace, attempt, historyEq, lastPoint,
            lastExcluded.trans nextExcluded, lastGeneration.trans nextGeneration, lastLive,
            agreement, ?_, ?_⟩
          · have nextWord : setup.recoveryJointRecall
                (setup.proposalRecoveryEraseTrace nextCursor.trace) = headAttempt.joints.reverse ++
                  setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace cursor.trace) :=
              middleWord
            rw [lastWord, nextWord]
            rw [CommitPrefix.Attempt.prepend_joints, List.reverse_append, tailWord]
            exact (List.append_assoc _ _ _).symm
          · have nextWord : setup.proposalRecoveryJointRecall nextCursor.trace =
                headAttempt.joints.reverse.map
                  (fun joint who => (joint who).map ProposalRecoveryMove.ordinary) ++
                    setup.proposalRecoveryJointRecall cursor.trace := by
              change sourceJoint :: setup.proposalRecoveryJointRecall cursor.trace = _
              rw [headWord]
              simp only [List.reverse_singleton, List.map_singleton, List.singleton_append]
              exact congrArg (List.cons · (setup.proposalRecoveryJointRecall cursor.trace))
                (ordinarySourceChoices_labelled setup cursor.current cursor.trace draws)
            rw [lastLabelledWord, nextWord]
            rw [CommitPrefix.Attempt.prepend_joints, List.reverse_append, List.map_append, tailWord]
            exact (List.append_assoc _ _ _).symm
        · intro filler sameViews
          have nextExcluded : nextCursor.current.excluded = cursor.current.excluded :=
            (ordinary_commit_close_metadata setup cursor.current
              (cursor.excluded.trans cursor.entryExcluded.symm) _).2.1
          have headStored : field.get? nextConfig.store = some (result draws) := by
            have stored := nextData.1 HasVar.here
            change field.get? nextConfig.store = some (middleSource.state.get HasVar.here)
              at stored
            exact stored.trans (congrArg some sourceResult)
          let nextFiller := commitSuccessor name guard filler (result draws)
          have nextViews : ∀ who, who ∉ nextCursor.current.excluded →
              nextFiller.view who = nextCursor.source.view who := by
            intro who active
            rw [nextExcluded] at active
            change nextFiller.view who = middleSource.view who
            by_cases inactive : owner ∈ cursor.current.excluded
            · have foreign : owner ≠ who := fun same => active (same ▸ inactive)
              rw [automatic inactive]
              exact (Config.view_commit_congr name guard filler cursor.source
                (sameViews who active) (result draws) .failure
                  (fun same => (foreign same).elim)).trans
                    (Config.automaticCommit_view_eq_failure who owner foreign
                      name guard cursor.source).symm
            · obtain ⟨actualValue, same, _selected⟩ := value inactive
              have chosen : result draws = .success actualValue := by
                rw [same] at sourceResult
                exact sourceResult.symm
              rw [same]
              exact Config.view_commit_congr name guard filler cursor.source
                (sameViews who active) (result draws) (.success actualValue)
                  (fun _ => chosen)
          have tailLaw := tailMarginal nextFiller nextViews
          have readEq : joint.map (fun final => fillCommitPrefix setup.program
                (.commit name owner fresh guard rest) suffix cursor.embedding
                  final.2.2.1 filler) =
              joint.map (fun final => fillCommitPrefix setup.program rest suffix
                nextCursor.embedding final.2.2.1 nextFiller) := by
            apply map_congr_on_support joint
            intro final supported
            have graphSupport : final.2 ∈
                (graph.canonicalContinuation profile nextConfig).support := by
              have mapped : joint.map Prod.snd =
                  graph.canonicalContinuation profile nextConfig := right
              rw [← mapped]
              exact (PMF.mem_support_map_iff ..).mpr ⟨final, supported, rfl⟩
            have kept : (cursor.refs.cons
                (name := name) (cell := .commitment owner payload) field).Agrees
                  middleSource.state final.2.2.1 :=
              canonicalContinuation_retains_context profile
                (cursor.refs.cons (name := name) (cell := .commitment owner payload) field)
                middleSource.state nextConfig nextData.1 final.2 graphSupport
            have stored : field.get? final.2.2.1 = some (result draws) := by
              have read := kept HasVar.here
              change field.get? final.2.2.1 = some (middleSource.state.get HasVar.here) at read
              exact read.trans (congrArg some sourceResult)
            change fillCommitPrefix setup.program rest suffix nextCursor.embedding
              final.2.2.1
                (commitSuccessor name guard filler ((field.get? final.2.2.1).getD .failure)) = _
            rw [stored]
            rfl
          rw [readEq, tailLaw]
          change rest.prefixLaw suffix (afterCommit typed) nextFiller = _
          rw [headStored]
          rfl
      let branch := fun pair member => (branches pair member).choose
      refine ⟨row.bindOnSupport branch, ?_, ?_, ?_, ?_⟩
      · rw [map_bindOnSupport]
        rw [show (SourceProgram.CommitPrefix.commit name owner fresh guard rest).length =
          1 + rest.length by simp only [CommitPrefix.length]; omega]
        rw [setup.proposalRecoveryModel.runBehavioralFrom_add source 1 rest.length,
          ← first, PMF.bind_map]
        apply bindOnSupport_eq_bind_of_eq_on_support
        intro pair member
        exact (branches pair member).choose_spec.1
      · rw [map_bindOnSupport, ← harmonic]
        apply bindOnSupport_eq_bind_of_eq_on_support
        intro pair member
        exact (branches pair member).choose_spec.2.1
      · intro final supported
        obtain ⟨pair, member, reached⟩ :=
          Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ supported)
        exact (branches pair member).choose_spec.2.2.1 final reached
      · intro filler sameViews
        rw [map_bindOnSupport]
        have mixed : (row.bindOnSupport fun pair member =>
            (branch pair member).map (fun final => fillCommitPrefix setup.program
              (.commit name owner fresh guard rest) suffix cursor.embedding
                final.2.2.1 filler)) =
            row.bind (fun pair => rest.prefixLaw suffix (afterCommit typed)
              (commitSuccessor name guard filler
                (((⟨.inr event, binding⟩ : FieldRef (graphLayout setup.program)
                  (.binding owner payload)).get? pair.2.store).getD .failure))) := by
          apply bindOnSupport_eq_bind_of_eq_on_support
          intro pair member
          exact (branches pair member).choose_spec.2.2.2 filler sameViews
        rw [mixed]
        change row.bind ((fun result => rest.prefixLaw suffix (afterCommit typed)
          (commitSuccessor name guard filler (result.getD .failure))) ∘
            (fun pair => (⟨.inr event, binding⟩ : FieldRef (graphLayout setup.program)
              (.binding owner payload)).get? pair.2.store)) = _
        rw [← PMF.bind_map, rowRead, PMF.bind_map]
        change (if owner ∈ cursor.current.excluded then PMF.pure .failure else
          (values owner (setup.proposalRecoveryQuery owner
            (setup.proposalRecoveryModel.infoOf owner cursor.trace))).map
              (fun choice => PublicationResult.success
                (phaseRecoveryDomainValue setup mode event owner payload binding
                  choice.val.val))).bind
                    (fun result => rest.prefixLaw suffix (afterCommit typed)
                      (commitSuccessor name guard filler result)) = _
        change _ = (commitKernel typed (filler.view owner)).bind (fun result =>
          rest.prefixLaw suffix (afterCommit typed) (commitSuccessor name guard filler result))
        apply congrArg (fun law : PMF (PublicationResult (L.Val payload)) =>
          law.bind (fun result =>
          rest.prefixLaw suffix (afterCommit typed) (commitSuccessor name guard filler result)))
        have positive : 0 < (CommitPrefix.commit name owner fresh guard rest).length :=
          Nat.zero_lt_succ _
        have controlsEq := cursor.controls positive
        have excludedEq : controls.1 = cursor.current.excluded :=
          (congrArg Prod.fst controlsEq).symm
        by_cases inactive : owner ∈ cursor.current.excluded
        · simp only [typed, ordinaryBlockProfile, ordinaryBlockProfile.buildProfile,
            commitKernel, excludedEq, inactive,
            ↓reduceIte]
        · rw [ite_eq_right inactive]
          have live : ProtocolState.BindingsHoldValues owner setup.program
              cursor.current.point := by
            rw [cursor.point, cursor.origin.bindingsHoldValues_lift,
              ProtocolState.bindingsHoldValues_entry]
            exact cursor.live owner inactive
          have observed : cursor.views.view owner (Sum.inl (filler.view owner)) =
              ProtocolState.observe owner setup.program cursor.current.point := by
            rw [sameViews owner inactive, cursor.point, cursor.views.observe]
            rfl
          have rank : ProtocolView.position owner setup.program
              (ProtocolState.observe owner setup.program cursor.current.point) =
                cursor.offset := by
            have position := ProtocolView.position_add_remaining owner setup.program
              cursor.current.point
            have remaining : ProtocolState.remaining setup.program cursor.current.point =
                instructionCount
                  ((CommitPrefix.commit name owner fresh guard rest).prepend suffix) := by
              rw [cursor.point, cursor.origin.remaining_lift, ProtocolState.remaining_entry]
            rw [remaining] at position
            have count := cursor.compiled.countEq
            simp only [eventCount_eq_instructionCount] at count
            omega
          exact (ordinary_block_head_law setup mode plan values fresh guard rest suffix
            cursor.embedding (fun who view => cursor.views.view who view) controls
              anchor.execution.application.publicView
              (PhaseProposal.sourceArchive anchor.execution.network.inputs) (filler.view owner)
              cursor.current cursor.trace inactive live observed controlsEq
              (by rw [rank]; exact cursor.addresses positive owner)
              (cursor.proposals owner inactive)).symm

/-- Ordinary source play completes the literal commitment prefix without new
exclusions. Its actual joint word contains only proper preparations, even when
an older stored binding has failed. -/
theorem proposalRecovery_ordinary_commit_block_support
    (setup : Setup (Player := Player) (L := L))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (lift : ProtocolState (block.prepend suffix) → ProtocolState setup.program)
      (_origin : ProtocolSuffix setup.program (block.prepend suffix) lift)
      (source : SourceProgram.Config Player L Γ)
      (current : CommitRecoveryState setup.program)
      (trace : setup.proposalRecoveryProtocol.Trace (some current))
      (_point : current.point = lift (ProtocolState.entry (block.prepend suffix) source))
      (_ordinary : current.excluded = current.entryExcluded)
      (final : setup.proposalRecoveryProtocol.History),
      final ∈ (setup.proposalRecoveryModel.runBehavioralFrom
        (setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
        block.length ⟨some current, trace⟩).support →
      ∃ (finished : SourceProgram.Config Player L Δ)
        (last : CommitRecoveryState setup.program)
        (lastTrace : setup.proposalRecoveryProtocol.Trace (some last))
        (attempt : block.Attempt source current.excluded finished last.excluded),
        final = ⟨some last, lastTrace⟩ ∧
        last.point = lift (block.liftPoint suffix (ProtocolState.entry suffix finished)) ∧
        last.excluded = current.excluded ∧ last.entryExcluded = current.excluded ∧
        last.generation = current.generation ∧
        setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace lastTrace) =
          attempt.joints.reverse ++ setup.recoveryJointRecall
            (setup.proposalRecoveryEraseTrace trace) ∧
        setup.proposalRecoveryJointRecall lastTrace =
          attempt.joints.reverse.map
              (fun joint who => (joint who).map ProposalRecoveryMove.ordinary)
            ++ setup.proposalRecoveryJointRecall trace ∧
        (∀ joint ∈ attempt.joints, ∀ who move, joint who = some move →
          move.missing = false ∧ ¬ move.action.IsFailure) := by
  classical
  induction block with
  | nil =>
      intro suffix lift origin source current trace point ordinary final supported
      have same : final = ⟨some current, trace⟩ := (PMF.mem_support_pure_iff ..).mp supported
      subst final
      refine ⟨source, current, trace, .nil _ _, rfl, point, rfl, ordinary.symm, rfl, ?_, ?_, ?_⟩
      · rfl
      · rfl
      · intro joint member
        cases member
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      intro suffix lift origin source current trace point ordinary final supported
      rw [show (SourceProgram.CommitPrefix.commit name owner fresh guard rest).length =
        rest.length + 1 from rfl,
        setup.proposalRecovery_ordinary_run_succ values] at supported
      obtain ⟨draws, _drawSupport, restSupport⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      obtain ⟨middle, localSupport, finalSupport⟩ := (PMF.mem_support_bind_iff _ _ _).mp restSupport
      obtain ⟨middleSource, after, headAttempt, monotone, headWord, middleState, middleWord,
          middleLabels⟩ :=
        proposalRecovery_localStep_commit_attempt setup fresh guard (rest.prepend suffix)
          lift origin source current trace point
            (ordinarySourceChoices setup current trace draws) middle localSupport
      rw [ordinarySourceChoices_semantic] at headWord
      have proper : ∀ who move, (draws who).val.val = some move →
          move.missing = false ∧ ¬ move.action.IsFailure :=
        fun who move selected => (draws who).property move selected
      obtain ⟨afterEq, _live, _automatic, _value⟩ :=
        proper_single_commit_attempt headAttempt _ headWord proper
      cases afterEq
      let next := (current.install
        (lift (.inr (ProtocolState.entry (rest.prepend suffix) middleSource)), current.excluded)
          (Finset.Subset.refl _)).close
      have metadata := ordinary_commit_close_metadata setup current ordinary
        (lift (.inr (ProtocolState.entry (rest.prepend suffix) middleSource)))
      rcases middle with ⟨middleState', middleTrace⟩
      change middleState' = some next at middleState
      subst middleState'
      obtain ⟨finished, last, lastTrace, tailAttempt, finalEq, lastPoint, lastExcluded,
          lastEntry, lastGeneration, lastWord, lastLabels, tailProper⟩ :=
        ih suffix (fun point => lift (.inr point))
          (ProtocolSuffix.commitTail fresh guard (rest.prepend suffix) origin)
          middleSource next middleTrace metadata.1
          (metadata.2.1.trans metadata.2.2.1.symm) final finalSupport
      let tailTyped : rest.Attempt middleSource current.excluded finished last.excluded :=
        metadata.2.1 ▸ tailAttempt
      have tailWord : tailTyped.joints = tailAttempt.joints := by
        have transport {first second : Finset Player} (same : first = second)
            (attempt : rest.Attempt middleSource first finished last.excluded) :
            (same ▸ attempt).joints = attempt.joints := by cases same; rfl
        exact transport metadata.2.1 tailAttempt
      refine ⟨finished, last, lastTrace, headAttempt.prepend tailTyped, finalEq, lastPoint,
        lastExcluded.trans metadata.2.1, lastEntry.trans metadata.2.1,
        lastGeneration.trans metadata.2.2.2, ?_, ?_, ?_⟩
      · rw [lastWord, middleWord, CommitPrefix.Attempt.prepend_joints,
          List.reverse_append, tailWord]
        exact (List.append_assoc _ _ _).symm
      · have headLabels : setup.proposalRecoveryJointRecall middleTrace =
            headAttempt.joints.reverse.map
              (fun joint who => (joint who).map ProposalRecoveryMove.ordinary) ++
                setup.proposalRecoveryJointRecall trace := by
          rw [middleLabels, headWord]
          simp only [List.reverse_singleton, List.map_singleton, List.singleton_append]
          exact congrArg (List.cons · (setup.proposalRecoveryJointRecall trace))
            (ordinarySourceChoices_labelled setup current trace draws)
        rw [lastLabels, headLabels, CommitPrefix.Attempt.prepend_joints,
          List.reverse_append, List.map_append, tailWord]
        exact (List.append_assoc _ _ _).symm
      · intro joint member who move selected
        rw [CommitPrefix.Attempt.prepend_joints, tailWord] at member
        rcases List.mem_append.mp member with head | tail
        · rw [headWord, List.mem_singleton] at head
          subst joint
          exact proper who move selected
        · exact tailProper joint tail who move selected

end Vegas
