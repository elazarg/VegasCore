/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalObservableDebt
import Vegas.Game.PhaseProposalSourceWordReadout
import Vegas.Compile.CommitPrefixCompletionSnoc
import Vegas.Game.RecoveryFixedCommitSelector
import Vegas.Source.CommitRecoveryAttemptDebt
import Vegas.Source.CommitRecoveryAttemptSuccess

/-! # Actual unresolved failed cells at surviving binding callbacks -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem failuresCovered_of_observe_eq (who : Player)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (excluded : Finset Player) (first second : ProtocolState program)
    (same : ProtocolState.observe who program first = ProtocolState.observe who program second)
    (covered : ProtocolState.FailuresCovered program excluded first) :
    ProtocolState.FailuresCovered program excluded second := by
  induction program with
  | ret => trivial
  | sample name fresh law next ih =>
      cases first <;> cases second
      · trivial
      · cases same
      · cases same
      · exact ih _ _ (Sum.inr.inj same) covered
  | commit name owner fresh guard next ih =>
      cases first <;> cases second
      · trivial
      · cases same
      · cases same
      · exact ih _ _ (Sum.inr.inj same) covered
  | reveal published owner name fresh selected unresolved next ih =>
      cases first with
      | inl =>
          cases second
          · trivial
          · cases same
      | inr first =>
          cases second with
          | inl => cases same
          | inr second =>
              have views := Sum.inr.inj same
              have published := sourceObserve_publication_eq
                (ProtocolState.sourceObserve_base_eq_of_observe_eq who next first second views)
                  .here
              exact ⟨fun failed => covered.1 (published.trans failed),
                ih _ _ views covered.2⟩

private theorem suffix_origin_cast
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO}
    {first second : SourceProgram Player L Γ O} (same : first = second)
    (lift : ProtocolState second → ProtocolState whole)
    (origin : ProtocolSuffix whole second lift) :
    ProtocolSuffix whole first (fun point => lift (cast (congrArg ProtocolState same) point)) := by
  cases same
  exact origin

private theorem embedding_rank_cast
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO}
    {first second : SourceProgram Player L Γ O} (same : first = second)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) second)
    (offset : Nat) (ranked : ∀ index, (embedding.event index).val = offset + index.val) :
    ∀ index, ((cast (congrArg (fun program => OutputEmbedding (inputLayout wholeΓ)
      (outputLayout whole) program) same.symm) embedding).event index).val =
        offset + index.val := by
  cases same
  exact ranked

private theorem failedBinding_reflect_of_covered
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) (who : Player) (excluded : Finset Player)
    (active : who ∉ excluded) :
    ∀ point, ProtocolState.FailuresCovered whole excluded (lift point) →
      ProtocolState.FailedBinding who whole (lift point) →
        ProtocolState.FailuresCovered program excluded point ∧
          ProtocolState.FailedBinding who program point := by
  induction origin with
  | initial => exact fun _ covered failed => ⟨covered, failed⟩
  | sampleTail fresh law next previous ih =>
      exact fun point covered failed => ih (.inr point) covered failed
  | commitTail fresh guard next previous ih =>
      exact fun point covered failed => ih (.inr point) covered failed
  | revealTail fresh selected unresolved next previous ih =>
      intro point covered failed
      obtain ⟨priorCoverage, priorFailure⟩ := ih (.inr point) covered failed
      refine ⟨priorCoverage.2, ?_⟩
      rcases priorFailure with ⟨own, published⟩ | pending
      · exact (active (own ▸ priorCoverage.1 published)).elim
      · exact pending

private theorem failedBinding_commit_entry_reflect
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (finished : SourceProgram.Config Player L Δ)
    (who : Player)
    (failed : ProtocolState.FailedBinding who (block.prepend suffix)
      (block.liftPoint suffix (ProtocolState.entry suffix finished))) :
    finished.FailedBinding who P := by
  induction block with
  | nil => cases suffix <;> exact failed
  | commit name owner fresh guard rest ih => exact ih suffix finished failed

private theorem failedBinding_of_active_erased_view
    (setup : Setup (Player := Player) (L := L)) (who : Player)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (active : who ∉ current.excluded)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (lift : ProtocolState (block.prepend suffix) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (block.prepend suffix) lift)
    (finished : SourceProgram.Config Player L Δ)
    (same : ProtocolView.eraseHistory who setup.program
        (ProtocolState.observe who setup.program current.point) =
      ProtocolView.eraseHistory who setup.program (ProtocolState.observe who setup.program
        (lift (block.liftPoint suffix (ProtocolState.entry suffix finished)))))
    (failed : ProtocolState.FailedBinding who setup.program current.point) :
    finished.FailedBinding who P := by
  let point := lift (block.liftPoint suffix (ProtocolState.entry suffix finished))
  have views : ProtocolState.observe who setup.program
      (ProtocolState.withHistory setup.program current.point (fun _ => [])) =
      ProtocolState.observe who setup.program
        (ProtocolState.withHistory setup.program point (fun _ => [])) := by
    simpa only [ProtocolView.eraseHistory_observe] using same
  have covered := (setup.commitRecovery_failuresCovered trace current rfl).2
  have erasedCoverage := (ProtocolState.failuresCovered_withHistory setup.program
    current.excluded current.point (fun _ => [])).mpr covered
  have pointCoverage := failuresCovered_of_observe_eq who setup.program current.excluded _ _
    views erasedCoverage
  have pointFailure := (ProtocolState.failedBinding_iff_of_observe_eq who setup.program _ _
    views).mp ((ProtocolState.failedBinding_withHistory who setup.program current.point
      (fun _ => [])).mpr failed)
  have reflected := failedBinding_reflect_of_covered origin who current.excluded active _
    ((ProtocolState.failuresCovered_withHistory setup.program current.excluded point
      (fun _ => [])).mp pointCoverage)
    ((ProtocolState.failedBinding_withHistory who setup.program point (fun _ => [])).mp
      pointFailure)
  exact failedBinding_commit_entry_reflect block suffix finished who reflected.2

private theorem commit_attempt_prefix_agreement
    {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId} (earlier : SourceProgram.CommitPrefix Γ O Δ P) :
    ∀ {Ξ : SourceCtx Player L} {Q : Finset VarId} (later : SourceProgram.CommitPrefix Δ P Ξ Q)
      (suffix : SourceProgram Player L Ξ Q)
      (full : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
        ((earlier.append later).prepend suffix))
      (prefixEmbedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
        (earlier.prepend (later.prepend suffix)))
      (_same : ∀ first second, first.val = second.val →
        full.event first = prefixEmbedding.event second)
      (refs : ContextRefs (graphLayout whole) Γ) (store : Store (graphLayout whole))
      (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player)
      (finished : SourceProgram.Config Player L Ξ) (after : Finset Player)
      (_attempt : (earlier.append later).Attempt entry excluded finished after),
      (commitBlockRefs whole (earlier.append later) suffix full refs).Agrees finished.state store →
      ∃ (middle : SourceProgram.Config Player L Δ) (owners : Finset Player),
        Nonempty (earlier.Attempt entry excluded middle owners) ∧
          Nonempty (later.Attempt middle owners finished after) ∧
            (commitBlockRefs whole earlier (later.prepend suffix) prefixEmbedding refs).Agrees
              middle.state store := by
  induction earlier with
  | nil =>
      intro Ξ Q later suffix full prefixEmbedding same refs store entry excluded finished after
        attempt agreement
      exact ⟨entry, excluded, ⟨.nil entry excluded⟩, ⟨attempt⟩,
        commitBlockRefs_agrees_entry whole later suffix full refs store entry excluded finished
          after attempt agreement⟩
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      intro Ξ Q later suffix full prefixEmbedding same refs store entry excluded finished after
        attempt agreement
      let fullZero : Fin (eventCount
          (((SourceProgram.CommitPrefix.commit name owner fresh guard rest).append later).prepend
            suffix)) :=
        ⟨0, by
          simp only [SourceProgram.CommitPrefix.append, SourceProgram.CommitPrefix.prepend,
            eventCount]
          omega⟩
      let prefixZero : Fin (eventCount
          ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend
            (later.prepend suffix))) :=
        ⟨0, by simp only [SourceProgram.CommitPrefix.prepend, eventCount]; omega⟩
      let fullField : FieldRef (graphLayout whole) (.binding owner payload) :=
        ⟨.inr (full.event fullZero), full.layout_eq _⟩
      let prefixField : FieldRef (graphLayout whole) (.binding owner payload) :=
        ⟨.inr (prefixEmbedding.event prefixZero), prefixEmbedding.layout_eq _⟩
      have headEq : fullField = prefixField := by
        have coordinate : fullField.field = prefixField.field :=
          congrArg Sum.inr (same fullZero prefixZero rfl)
        rcases fullField with ⟨first, firstEq⟩
        rcases prefixField with ⟨second, secondEq⟩
        dsimp only at coordinate
        subst second
        rfl
      let fullTail := full.tail ((rest.append later).prepend suffix)
        (by simp only [SourceProgram.CommitPrefix.append, SourceProgram.CommitPrefix.prepend,
          eventCount]) (fun _ => rfl)
      let prefixTail := prefixEmbedding.tail (rest.prepend (later.prepend suffix))
        (by simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      let nextRefs := refs.cons (name := name) (cell := .commitment owner payload) fullField
      have tailSame : ∀ first second, first.val = second.val →
          fullTail.event first = prefixTail.event second := by
        intro first second equal
        exact same (Fin.succ first) (Fin.succ second) (congrArg Nat.succ equal)
      cases attempt with
      | active active choice missed valid remaining =>
          obtain ⟨middle, owners, ⟨first⟩, ⟨second⟩, reads⟩ :=
            ih later suffix fullTail prefixTail tailSame nextRefs store _ _ finished after
              remaining agreement
          refine ⟨middle, owners, ⟨.active active choice missed valid first⟩, ⟨second⟩, ?_⟩
          change (commitBlockRefs whole rest (later.prepend suffix) prefixTail
            (refs.cons (name := name) (cell := .commitment owner payload) prefixField)).Agrees
              middle.state store
          rw [← headEq]
          exact reads
      | excluded inactive remaining =>
          obtain ⟨middle, owners, ⟨first⟩, ⟨second⟩, reads⟩ :=
            ih later suffix fullTail prefixTail tailSame nextRefs store _ _ finished after
              remaining agreement
          refine ⟨middle, owners, ⟨.excluded inactive first⟩, ⟨second⟩, ?_⟩
          change (commitBlockRefs whole rest (later.prepend suffix) prefixTail
            (refs.cons (name := name) (cell := .commitment owner payload) prefixField)).Agrees
              middle.state store
          rw [← headEq]
          exact reads

/-- Every completed original typed attempt retains an earlier failed owned
cell read from the ready callback. The actual closing-store extension and
compiler references discharge the middle observation; no view equality or
usability premise is supplied. A subsequent restore is a separate branch. -/
theorem failed_binding_retained_in_completed_attempt
    {wholeΓ Γ Δ Ξ : SourceCtx Player L} {wholeO O P Q : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO)
    (earlier : SourceProgram.CommitPrefix Γ O Δ P) (later : SourceProgram.CommitPrefix Δ P Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (full : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      ((earlier.append later).prepend suffix))
    (prefixEmbedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (earlier.prepend (later.prepend suffix)))
    (same : ∀ first second, first.val = second.val →
      full.event first = prefixEmbedding.event second)
    (refs : ContextRefs (graphLayout whole) Γ)
    (current closing : Store (graphLayout whole))
    (preserved : ∀ field value, current field = some value → closing field = some value)
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (finished : SourceProgram.Config Player L Ξ) (after : Finset Player)
    (attempt : (earlier.append later).Attempt entry excluded finished after)
    (agree : (commitBlockRefs whole (earlier.append later) suffix full refs).Agrees
      finished.state closing)
    (who : Player)
    (available : ∀ index : Fin (eventCount (earlier.prepend (later.prepend suffix))),
      index.val < earlier.length →
      eventOwner? (earlier.prepend (later.prepend suffix)) index = some who →
        ((prefixEmbedding.ref index).get? current).isSome = true)
    (failed : (fillCommitPrefix whole earlier (later.prepend suffix) prefixEmbedding current
      entry).FailedBinding who P) : finished.FailedBinding who Q := by
  obtain ⟨middle, owners, ⟨first⟩, ⟨second⟩, prefixAgree⟩ :=
    commit_attempt_prefix_agreement whole earlier later suffix full prefixEmbedding same refs
      closing entry excluded finished after attempt agree
  have oldAgree : refs.Agrees entry.state closing :=
    commitBlockRefs_agrees_entry whole earlier (later.prepend suffix)
      prefixEmbedding refs closing entry excluded middle owners first prefixAgree
  have closingAvailable : ∀ index : Fin (eventCount (earlier.prepend (later.prepend suffix))),
      index.val < earlier.length →
      eventOwner? (earlier.prepend (later.prepend suffix)) index = some who →
        ((prefixEmbedding.ref index).get? closing).isSome = true := by
    intro index inside acting
    obtain ⟨value, present⟩ := Option.isSome_iff_exists.mp (available index inside acting)
    rw [(prefixEmbedding.ref index).get?_preserved current closing preserved value present]
    rfl
  have filledRead := fillCommitPrefix_observation whole earlier (later.prepend suffix)
    prefixEmbedding refs closing entry who (decodeObservation?_eq_some refs who entry.state
      closing oldAgree) closingAvailable
  have actualRead := decodeObservation?_eq_some
    (commitBlockRefs whole earlier (later.prepend suffix) prefixEmbedding refs)
      who middle.state closing prefixAgree
  have sameClosing := Option.some.inj (filledRead.symm.trans actualRead)
  have extension := fillCommitPrefix_view_of_extension whole earlier (later.prepend suffix)
    prefixEmbedding current closing entry who preserved available
  have sameCells := (congrArg Prod.fst extension).trans sameClosing
  exact second.preserves_failedBinding who
    (Config.FailedBinding.of_sourceObserve_eq sameCells failed)

/-- The observable current failure is a concrete unresolved failed cell of
the SAME filled compiler prefix. Genuine source failure coverage rules out an
old failed publication of the surviving owner; it is not inverted away. -/
theorem RecoverySourceCheckpoint.current_binding_failure_cell [Finite Player]
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    {Δ : SourceCtx Player L} {P : Finset VarId} {name : VarId}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ who name payload)
    (next : SourceProgram Player L ((name, .commitment who payload) :: Δ) (insert name P))
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name who fresh guard next) = checkpoint.residual.tail)
    (selected : Fin (eventCount checkpoint.residual.tail))
    (atEnd : selected.val = earlier.length) (named : checkpoint.embedding.event selected = event)
    (failed : phaseProposalCurrentBindingFailure setup mode runtime leaks who event
      (control.execution.observe (phaseApplication runtime leaks) who)) :
    let embedding := cast (congrArg
      (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) reconstruct.symm) checkpoint.embedding
    (fillCommitPrefix setup.program earlier (.commit name who fresh guard next) embedding
      control.execution.application.current.native.config.store checkpoint.source).FailedBinding
        who P := by
  intro embedding
  let suffix := SourceProgram.commit name who fresh guard next
  let filled := fillCommitPrefix setup.program earlier suffix embedding
    control.execution.application.current.native.config.store checkpoint.source
  let lift : ProtocolState (earlier.prepend suffix) → ProtocolState setup.program :=
    fun point => checkpoint.residual.lift
      (cast (congrArg ProtocolState reconstruct) point)
  have origin : ProtocolSuffix setup.program (earlier.prepend suffix) lift :=
    suffix_origin_cast reconstruct checkpoint.residual.lift checkpoint.origin
  let inputs := setup.initialLaw.map encodeInputs
  have actualTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler
    actualTrace
  obtain ⟨current, sourceTrace, excluded, _generation, _control, _acting, _played, decoded⟩ :=
    phaseSurvivingSourceView?_of_ready_binding setup mode runtime leaks plan maximal horizon
      scheduler trace who event payload binding request
  have coverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
    actualTrace
  have active : who ∉ current.excluded := by
    rw [excluded]
    exact fun member => request.2.2.2.2 (coverage.inherited member)
  have currentFailure := (phaseProposalCurrentBindingFailure_iff_of_readback setup mode runtime
    leaks who event _ current.point decoded).mp failed
  rw [phaseSurvivingSourceView?_observed_of_history setup mode runtime leaks plan inputs horizon
    scheduler actualTrace who event] at decoded
  have filledRead := checkpoint.filled_prefix_view fresh guard next earlier reconstruct stored
    selected atEnd (named.symm ▸ request.2.2.1) (named.symm ▸ request.2.2.2.1)
      (by rw [named, binding]; exact id) (filled.history who) rfl
  rw [named] at filledRead
  have erasedCurrent := congrArg (Option.map (ProtocolView.eraseHistory who setup.program)) decoded
  have erasedFilled := congrArg (Option.map (ProtocolView.eraseHistory who setup.program))
    filledRead
  rw [← decodeEventView?_eraseHistory] at erasedCurrent erasedFilled
  have same := Option.some.inj (erasedCurrent.symm.trans erasedFilled)
  exact failedBinding_of_active_erased_view setup who current sourceTrace active earlier suffix
    lift origin filled same currentFailure

/-- The actual current classifier persists in the completed original binding
image. The typed attempt and compiler agreement are the existing completed
phase readback; later source choices, including unusable values, stay literal. -/
theorem RecoverySourceCheckpoint.current_binding_failure_retained [Finite Player]
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    {Δ Ξ : SourceCtx Player L} {P Q : Finset VarId} {name : VarId}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ who name payload)
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (later : SourceProgram.CommitPrefix ((name, .commitment who payload) :: Δ) (insert name P) Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (reconstruct : earlier.prepend (.commit name who fresh guard (later.prepend suffix)) =
      checkpoint.residual.tail)
    (selected : Fin (eventCount checkpoint.residual.tail))
    (atEnd : selected.val = earlier.length) (named : checkpoint.embedding.event selected = event)
    (failed : phaseProposalCurrentBindingFailure setup mode runtime leaks who event
      (control.execution.observe (phaseApplication runtime leaks) who))
    (full : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      ((earlier.append (.commit name who fresh guard later)).prepend suffix))
    (closing : Store (graphLayout setup.program))
    (preserved : ∀ field value,
      control.execution.application.current.native.config.store field = some value →
        closing field = some value)
    (finished : SourceProgram.Config Player L Ξ) (after : Finset Player)
    (attempt : (earlier.append (.commit name who fresh guard later)).Attempt checkpoint.source
      control.execution.application.entry.excluded finished after)
    (agree : (commitBlockRefs setup.program (earlier.append (.commit name who fresh guard later))
      suffix full checkpoint.refs).Agrees finished.state closing) :
    let embedding := cast (congrArg
      (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) reconstruct.symm) checkpoint.embedding
    (∀ first second, first.val = second.val → full.event first = embedding.event second) →
      finished.FailedBinding who Q := by
  intro embedding aligned
  let next := later.prepend suffix
  have currentFailure := checkpoint.current_binding_failure_cell setup mode runtime leaks plan
    maximal horizon scheduler trace who event payload binding request fresh guard next earlier
      reconstruct selected atEnd named failed
  let prefixIndex : Fin (eventCount (earlier.prepend (.commit name who fresh guard next))) :=
    ⟨earlier.length, by rw [reconstruct]; simpa only [← atEnd] using selected.isLt⟩
  have addressed : embedding.event prefixIndex = event := by
    have same := OutputEmbedding.event_cast setup.program reconstruct.symm checkpoint.embedding
      selected prefixIndex (by exact atEnd)
    exact same.symm.trans named
  have available := commitPrefix_owned_fields_of_ready setup mode earlier
    (.commit name who fresh guard next) embedding
    control.execution.application.current.native.config
    who prefixIndex rfl (addressed.symm ▸ request.2.2.1)
      (addressed.symm ▸ request.2.2.2.1) (by rw [addressed, binding]; exact id)
  exact failed_binding_retained_in_completed_attempt setup.program earlier
    (.commit name who fresh guard later) suffix full embedding aligned checkpoint.refs _ closing
      preserved checkpoint.source control.execution.application.entry.excluded finished after
        attempt agree who available currentFailure

/-- A failed cell in the actual decoded whole binding attempt is a failed
binding of its original whole-program source result. The original suffix
embedding is retained through the compiler's exact maximal-block split. -/
theorem RecoverySourceCheckpoint.commitResultPoint_failedBinding
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (image : RecoveryState (serviceGraph setup mode)) (who : Player)
    (failed : match commitPhase checkpoint.residual.tail with
      | ⟨_, names, suffix, block, reconstruct, _⟩ =>
        let embedding := cast (congrArg (fun program => OutputEmbedding
          (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
            checkpoint.embedding
        (decodeCommitAttempt setup.program mode block suffix embedding image.native
          checkpoint.source state.entry.excluded).1.FailedBinding who names) :
    ProtocolState.FailedBinding who setup.program (checkpoint.commitResultPoint image) := by
  unfold RecoverySourceCheckpoint.commitResultPoint
  generalize decomposition : commitPhase checkpoint.residual.tail = segment at failed ⊢
  rcases segment with ⟨Δ, names, suffix, block, reconstruct, boundary⟩
  dsimp only at failed ⊢
  let lift : ProtocolState (block.prepend suffix) → ProtocolState setup.program :=
    fun point => checkpoint.residual.lift (cast (congrArg ProtocolState reconstruct) point)
  have origin : ProtocolSuffix setup.program (block.prepend suffix) lift :=
    suffix_origin_cast reconstruct checkpoint.residual.lift checkpoint.origin
  exact origin.failedBinding_lift who _
    (block.failedBinding_liftPoint suffix who _ (ProtocolState.failedBinding_entry _ _ failed))

/-- The actual ready callback's failed-cell classifier survives the same
completed original binding image. The only closing inputs are physical
binding provenance, receipt order, completed phase events and immutable-store
extension. All typed source splits and decoded-cell agreements are derived. -/
theorem RecoverySourceCheckpoint.current_binding_failure_in_result [Finite Player]
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : control.execution.application.phases = phase :: remaining)
    (kind : phase.kind = .commitment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (failed : phaseProposalCurrentBindingFailure setup mode runtime leaks who event
      (control.execution.observe (phaseApplication runtime leaks) who))
    (closing : RecoveryState (serviceGraph setup mode))
    (valid : closing.native.BindingInvariant)
    (receipts : BindingReceiptOrder control.execution.application.attempt.phase
      control.execution.application.entry.excluded closing.native.accepted)
    (completed : ∀ selected ∈ phase.events, selected ∈ closing.native.config.cut.completed)
    (preserved : ∀ field value,
      control.execution.application.current.native.config.store field = some value →
        closing.native.config.store field = some value) :
    ProtocolState.FailedBinding who setup.program (checkpoint.commitResultPoint closing) := by
  let inputs := setup.initialLaw.map encodeInputs
  have actualTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler
    actualTrace
  have frontier := (phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler
    actualTrace).frontier
  have chain := (phasePlanGeometry_history runtime leaks plan maximal inputs horizon scheduler
    actualTrace).2.2
  have inside : event ∈ phase.events := by
    obtain ⟨selected, member, inside⟩ := request.2.1
    have same : selected = phase := by
      exact (show phase = selected by
        simpa only [installed, List.head?_cons, Option.mem_some_iff] using member).symm
    exact same ▸ inside
  have geometry := checkpoint.commit_phase_geometry phase remaining installed kind frontier chain
  apply checkpoint.commitResultPoint_failedBinding closing who
  generalize decomposition : commitPhase checkpoint.residual.tail = segment at geometry ⊢
  rcases segment with ⟨Δ, names, suffix, block, reconstruct, boundary⟩
  dsimp only at geometry ⊢
  have high : phase.high = phase.low + block.length := by
    have low := phase.nonempty
    omega
  obtain ⟨selected, named, Ξ, Q, name, fresh, guard, earlier, later, size, sameBlock,
    predecessor⟩ := checkpoint.fixed_binding_prefix block suffix reconstruct frontier phase
      remaining installed high event inside request.2.2.1 who payload binding
  cases sameBlock
  let full := cast (congrArg (fun program => OutputEmbedding
    (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
      checkpoint.embedding
  have ranked : ∀ index, (full.event index).val =
      control.execution.application.attempt.phase + index.val :=
    embedding_rank_cast reconstruct checkpoint.embedding _ checkpoint.compiled.rankEq
  have entryAgree : checkpoint.refs.Agrees checkpoint.source.state
      closing.native.config.store := by
    intro name cell source
    exact (checkpoint.refs.get source).get?_preserved _ _ preserved _
      (checkpoint.current_agrees stored source)
  let decoded := decodeCommitAttempt setup.program mode
    (earlier.append (.commit name who fresh guard later)) suffix full closing.native
      checkpoint.source control.execution.application.entry.excluded
  have agreement : (commitBlockRefs setup.program
      (earlier.append (.commit name who fresh guard later)) suffix full checkpoint.refs).Agrees
        decoded.1.state closing.native.config.store :=
    decodeCommitAttempt_state_agrees setup.program mode
      (earlier.append (.commit name who fresh guard later)) suffix full checkpoint.refs
      closing.native checkpoint.source control.execution.application.entry.excluded
        control.execution.application.attempt.phase ranked valid receipts entryAgree
          (fun index bound => completed _ (geometry.2 index bound))
  have retained := checkpoint.current_binding_failure_retained setup mode runtime leaks plan
    maximal horizon scheduler trace who event payload binding request fresh guard earlier later
      suffix predecessor selected size.symm named failed full closing.native.config.store
        preserved decoded.1 decoded.2.1 decoded.2.2 agreement
  apply retained
  intro first second same
  apply Fin.ext
  rw [ranked]
  have prefixRank : ((cast (congrArg (fun program => OutputEmbedding
        (inputLayout setup.context) (outputLayout setup.program) program) predecessor.symm)
      checkpoint.embedding).event second).val =
      control.execution.application.attempt.phase + second.val := by
    exact embedding_rank_cast predecessor checkpoint.embedding _ checkpoint.compiled.rankEq second
  rw [prefixRank, same]

end Vegas
