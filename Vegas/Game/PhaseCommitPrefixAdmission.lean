/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCompletedBindingAdmission
import Vegas.Compile.CommitPrefixCompletionSnoc
import Interaction.ReactiveHistory

/-! # Admission of all actual owned cells in a surviving commitment prefix -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] [Fintype Player] in
/-- At a clear endpoint, a physically completed owned binding has an accepted
handle, including when its hidden declared typed result is unusable. -/
private theorem completed_binding_accepted_of_clear
    {graph : Vegas.EventGraph Player L} (state : RecoveryState graph)
    (coverage : state.FailureCoverage) (clear : state.excluded = ∅)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (completed : event ∈ state.native.config.cut.completed) :
    ∃ candidate, state.native.accepted (.inr event) = some candidate := by
  cases installed : state.native.accepted (.inr event) with
  | some candidate => exact ⟨candidate, rfl⟩
  | none =>
      have missed := (state.native.publicView_missedBinding event owner payload binding).mpr
        ⟨completed, installed⟩
      have excluded := coverage.covered event owner
        (EventGraph.actor?_of_outputLayout_binding graph binding) (Or.inl missed)
      rw [clear] at excluded
      exact (Finset.notMem_empty owner excluded).elim

omit [DecidableEq Player] [Fintype Player] in
private theorem output_completed_of_available
    {graph : Vegas.EventGraph Player L} (config : graph.Config) (event : graph.EventId)
    {kind : EventField Player L} (ref : FieldRef graph.layout kind)
    (field : ref.field = .inr event) (available : (ref.get? config.store).isSome = true) :
    event ∈ config.cut.completed := by
  have present : (config.store ref.field).isSome = true := by
    cases ref with
    | mk field layout =>
        cases layout
        exact available
  rw [field, EventGraph.Config.store_output] at present
  exact (config.output_available event).mp present

omit [Fintype Player] in
private theorem binding_at_prefix_end
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P))
    (block : SourceProgram.CommitPrefix Γ O Δ P) :
    ∀ selected : Fin (eventCount (block.prepend (.commit name owner fresh guard next))),
      selected.val = block.length →
      outputLayout (block.prepend (.commit name owner fresh guard next)) selected =
        .binding owner payload := by
  induction block with
  | nil =>
      intro selected
      refine Fin.cases ?_ ?_ selected
      · intro _atEnd
        rfl
      · intro index impossible
        change index.val + 1 = 0 at impossible
        omega
  | commit prior author priorFresh priorGuard rest ih =>
      intro selected
      refine Fin.cases ?_ ?_ selected
      · intro impossible
        change 0 = rest.length + 1 at impossible
        omega
      · intro index atEnd
        apply ih fresh guard next index
        change index.val + 1 = rest.length + 1 at atEnd
        omega

omit [Fintype Player] in
private theorem eventOwner_eq_of_program_eq
    {Γ : SourceCtx Player L} {O : Finset VarId}
    {first second : SourceProgram Player L Γ O} (same : first = second)
    (left : Fin (eventCount first)) (right : Fin (eventCount second))
    (coordinate : left.val = right.val) : eventOwner? first left = eventOwner? second right := by
  cases same
  congr 1
  exact Fin.ext coordinate

/-- Every available owned binding in one surviving actual prefix is admitted.
The proof descends on the static source prefix at authentic earlier callbacks;
no prior admission or intended current-view witness is supplied. -/
private theorem phase_commitPrefix_admitted_bounded
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source
      assessment.strategy)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) :
    ∀ (depth : Nat) {control : (phaseApplication runtime leaks).Control}
    (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (_clear : control.execution.application.current.excluded = ∅)
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    {Δ : SourceCtx Player L} {P : Finset VarId}
    (block : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (suffix : SourceProgram Player L Δ P)
    (reconstruct : block.prepend suffix = checkpoint.residual.tail)
    (who : Player)
    (_consistent : (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      who).Consistent (control.execution.recall who))
    (_savedIntended : ProtocolState.Intended setup.program
      (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source)))
    (image : RecoveryState (serviceGraph setup mode))
    (_imageFacts : image.excluded = ∅ ∧ image.FailureCoverage ∧ image.native.BindingInvariant ∧
      (∀ handle payload, image.native.bindingResult handle payload =
        control.execution.application.current.native.bindingResult handle payload) ∧
      BindingStamp (fun owner => (phaseApplication runtime leaks).outputs
        (control.execution.recall owner)) control.execution.application.attempt image.native ∧
      KeepsStore control.execution.application.current.native image.native)
    (_shortEnough : block.length ≤ depth)
    (_available :
      let embedding := cast (congrArg
        (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
          program) reconstruct.symm) checkpoint.embedding
      ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
        eventOwner? (block.prepend suffix) index = some who →
          embedding.event index ∈
            image.native.config.cut.completed),
    let embedding := cast (congrArg
      (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) reconstruct.symm) checkpoint.embedding
    (fillCommitPrefix setup.program block suffix embedding
      image.native.config.store checkpoint.source).IntendedFor
        who P := by
  classical
  intro depth
  induction depth using Nat.strong_induction_on with
  | h depth ih =>
    intro control trace clear checkpoint Δ P block suffix reconstruct who consistent savedIntended
      image imageFacts shortEnough available
    classical
    rcases imageFacts with
      ⟨imageClear, imageCoverage, imageBindings, results, stamped, preservedImage⟩
    let fixed := checkpoint
    rcases checkpoint with
      ⟨⟨Γ, O, program, lift⟩, sourceEntry, refs, registry, embedding, beforeCut,
      compiled, terminalAlignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
      endpoints, automatic, sourceHistories, memories, steps, menus, readout, initializedSource,
      views, savedHistory, origin⟩
    dsimp only at *
    change SourceProgram.Config Player L Γ at sourceEntry
    change SourceProgram.CommitPrefix Γ O Δ P at block
    change OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program
      at embedding
    change block.prepend suffix = program at reconstruct
    subst program
    by_cases empty : block.length = 0
    · cases block with
      | nil =>
          have localIntended := origin.intended_reflect _ savedIntended
          change ProtocolState.Intended suffix (ProtocolState.entry suffix sourceEntry)
            at localIntended
          cases suffix with
          | ret => exact localIntended.intendedFor who
          | sample => exact localIntended.1.intendedFor who
          | commit => exact localIntended.1.intendedFor who
          | reveal => exact localIntended.1.intendedFor who
      | commit _ _ _ _ rest => simp only [SourceProgram.CommitPrefix.length] at empty; omega
    · obtain ⟨Ξ, Q, name, owner, payload, fresh, guard, earlier, contextEq, pendingEq, same⟩ :=
        block.exists_snoc (Nat.pos_of_ne_zero empty)
      cases contextEq
      cases pendingEq
      have blockEq := eq_of_heq same
      subst block
      have smaller : earlier.length < depth := by
        rw [SourceProgram.CommitPrefix.length_snoc] at shortEnough
        omega
      let app := phaseApplication runtime leaks
      let menu := PhaseCount.onePacketMenu runtime leaks bounds
      let initial := inputs.map (PhaseRuntimeState.initial plan)
      let next := suffix
      let prefixEmbedding := cast (congrArg (fun program =>
        OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
          (earlier.prepend_snoc name owner fresh guard next)) embedding
      let selected : Fin (eventCount ((earlier.snoc name owner fresh guard).prepend next)) :=
        ⟨earlier.length, by
          have count := (earlier.snoc name owner fresh guard).eventCount_prepend next
          rw [SourceProgram.CommitPrefix.length_snoc] at count
          omega⟩
      let shorter : Fin (eventCount (earlier.prepend (.commit name owner fresh guard next))) :=
        ⟨earlier.length, by
          have count := earlier.eventCount_prepend (.commit name owner fresh guard next)
          simp only [eventCount] at count
          omega⟩
      have coordinate : embedding.event selected = prefixEmbedding.event shorter :=
        OutputEmbedding.event_cast setup.program
          (earlier.prepend_snoc name owner fresh guard next) embedding selected shorter rfl
      have localBinding := binding_at_prefix_end fresh guard next earlier shorter rfl
      have binding : (serviceGraph setup mode).outputLayout (embedding.event selected) =
          .binding owner payload := by
        rw [coordinate]
        exact (prefixEmbedding.layout_eq shorter).trans localBinding
      have localOwner : eventOwner? ((earlier.snoc name owner fresh guard).prepend next) selected =
          some owner := by
        have fullBinding := (embedding.layout_eq selected).symm.trans binding
        exact (eventOwner?_eq_actor _ selected).trans
          (EventGraph.actor?_of_outputLayout_binding (toEventGraph _) fullBinding)
      let field : FieldRef (serviceGraph setup mode).layout (.binding owner payload) :=
        ⟨.inr (embedding.event selected), binding⟩
      have named : field.field = .inr (prefixEmbedding.event shorter) := congrArg Sum.inr coordinate
      have earlierReconstruct : earlier.prepend (.commit name owner fresh guard next) =
          fixed.residual.tail := (earlier.prepend_snoc name owner fresh guard next).symm
      change (fillCommitPrefix setup.program (earlier.snoc name owner fresh guard) next embedding
        image.native.config.store sourceEntry).IntendedFor
          who (insert name Q)
      change ∀ index : Fin (eventCount ((earlier.snoc name owner fresh guard).prepend next)),
        index.val < (earlier.snoc name owner fresh guard).length →
        eventOwner? ((earlier.snoc name owner fresh guard).prepend next) index = some who →
        embedding.event index ∈ image.native.config.cut.completed
          at available
      by_cases own : owner = who
      · subst owner
        have completed := available selected (by
          simp only [selected, SourceProgram.CommitPrefix.length_snoc]
          omega) localOwner
        obtain ⟨candidate, accepted⟩ := completed_binding_accepted_of_clear image imageCoverage
          imageClear (embedding.event selected) who payload binding completed
        have lower : control.execution.application.attempt.phase ≤
            (embedding.event selected).val := by
          have ranked := fixed.compiled.rankEq selected
          change (embedding.event selected).val =
            control.execution.application.attempt.phase + selected.val at ranked
          omega
        obtain ⟨value, _result, read, _predicts, admitted⟩ := phase_stamped_binding_admitted
          setup mode runtime leaks bounds wellFormed source assessment copies plan maximal inputs
            horizon scheduler trace clear fixed fresh guard next earlier earlierReconstruct selected
              rfl binding image.native imageBindings results stamped preservedImage candidate
                accepted lower consistent savedIntended (by
                intro before prior retainedTrace sameAttempt ready
                have initialized : ∀ state ∈ initial.support, state.Ordered := by
                  intro state positive
                  obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ positive
                  exact PhaseRuntimeState.initial_ordered plan draw
                have rawBefore := menu.toRawTrace initial horizon scheduler prior
                have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon
                  scheduler initialized rawBefore
                have sameEntry := phase_entry_of_same_attempt_prefix runtime leaks menu initial
                  initialized horizon scheduler before control prior trace retainedTrace ordered
                    sameAttempt
                let author := fixed.transfer sameEntry
                  (congrArg CommitAttemptId.generation sameAttempt)
                  (congrArg CommitAttemptId.phase sameAttempt)
                have beforeClear := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial
                  horizon scheduler before control prior trace retainedTrace clear).1
                have recallPrefix := (app).reaches_recall_prefix initial horizon scheduler
                  (menu.reaches_raw initial horizon scheduler retainedTrace.reachesWithin)
                    before control rfl rfl who
                obtain ⟨tail, sameRecall⟩ := recallPrefix
                have authorConsistent : (phaseSourcePolicy setup mode runtime leaks bounds
                    wellFormed assessment who).Consistent (before.execution.recall who) := by
                  apply ReactiveApplication.Policy.Consistent.of_append (after := tail)
                  rw [sameRecall]
                  exact consistent
                apply ih earlier.length smaller prior beforeClear
                    author
                    earlier (.commit name who fresh guard next) earlierReconstruct who
                      authorConsistent savedIntended before.execution.application.current
                        ⟨beforeClear, (phaseFailureCoverage_history runtime leaks plan inputs
                          horizon scheduler rawBefore).active,
                        (phaseBindingRecord_history runtime leaks plan inputs horizon scheduler
                          rawBefore).active,
                        (fun _ _ => rfl),
                        (phaseLiveBindingStamp_history runtime leaks plan inputs horizon scheduler
                          rawBefore), (fun _ _ present => present)⟩ (Nat.le_refl _)
                intro index earlierIndex owned
                have fields := commitPrefix_owned_fields_of_ready setup mode earlier
                    (.commit name who fresh guard next) prefixEmbedding
                      before.execution.application.current.native.config who shorter rfl
                      (by rw [← coordinate]; exact ready)
                      (by rw [← coordinate]; exact
                        EventGraph.actor?_of_outputLayout_binding (serviceGraph setup mode) binding)
                      (by rw [← coordinate, binding]; simp only [EventField.IsPublication,
                        not_false_eq_true])
                have availableField := fields index earlierIndex owned
                let actualField : FieldRef (serviceGraph setup mode).layout
                    (outputLayout (earlier.prepend (.commit name who fresh guard next)) index) :=
                  prefixEmbedding.ref index
                exact output_completed_of_available
                  before.execution.application.current.native.config (prefixEmbedding.event index)
                    actualField rfl availableField)
        rw [fillCommitPrefix_snoc setup.program earlier name who fresh guard next embedding
          image.native.config.store sourceEntry field shorter rfl
            named, read, Option.getD_some]
        exact admitted
      · have earlierAvailable :
            ∀ index : Fin (eventCount (earlier.prepend (.commit name owner fresh guard next))),
            index.val < earlier.length →
            eventOwner? (earlier.prepend (.commit name owner fresh guard next)) index = some who →
            prefixEmbedding.event index ∈
              image.native.config.cut.completed := by
          intro index earlierIndex owned
          let fullIndex : Fin (eventCount ((earlier.snoc name owner fresh guard).prepend next)) :=
            ⟨index.val, by
              rw [congrArg eventCount (earlier.prepend_snoc name owner fresh guard next)]
              exact index.isLt⟩
          have sameEvent := OutputEmbedding.event_cast setup.program
            (earlier.prepend_snoc name owner fresh guard next) embedding fullIndex index rfl
          rw [← sameEvent]
          apply available fullIndex (by
            simp only [fullIndex, SourceProgram.CommitPrefix.length_snoc]
            omega)
          exact (eventOwner_eq_of_program_eq
            (earlier.prepend_snoc name owner fresh guard next) fullIndex index rfl).trans owned
        have admitted := ih earlier.length smaller trace clear fixed earlier
            (.commit name owner fresh guard next) earlierReconstruct who consistent savedIntended
              image
              ⟨imageClear, imageCoverage, imageBindings, results, stamped, preservedImage⟩
              (Nat.le_refl _) earlierAvailable
        rw [fillCommitPrefix_snoc setup.program earlier name owner fresh guard next embedding
          image.native.config.store sourceEntry field shorter rfl
            named]
        exact admitted.commit_other fresh guard own _

/-- An actual raw completion image is admitted at the same saved checkpoint.
The image is linked by physical stamps and immutable reads to real callbacks;
it is not required to be an initialized normalized trace endpoint. -/
theorem phase_commitPrefix_image_admitted
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source
      assessment.strategy)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    {Δ : SourceCtx Player L} {P : Finset VarId}
    (block : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (suffix : SourceProgram Player L Δ P)
    (reconstruct : block.prepend suffix = checkpoint.residual.tail)
    (who : Player)
    (consistent : (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      who).Consistent (control.execution.recall who))
    (savedIntended : ProtocolState.Intended setup.program
      (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source)))
    (image : RecoveryState (serviceGraph setup mode))
    (imageClear : image.excluded = ∅) (imageCoverage : image.FailureCoverage)
    (imageBindings : image.native.BindingInvariant)
    (results : ∀ handle payload, image.native.bindingResult handle payload =
      control.execution.application.current.native.bindingResult handle payload)
    (stamped : BindingStamp (fun owner => (phaseApplication runtime leaks).outputs
      (control.execution.recall owner)) control.execution.application.attempt image.native)
    (preservedImage : KeepsStore control.execution.application.current.native image.native)
    (available :
      let embedding := cast (congrArg
        (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
          program) reconstruct.symm) checkpoint.embedding
      ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
        eventOwner? (block.prepend suffix) index = some who →
          embedding.event index ∈
            image.native.config.cut.completed) :
    let embedding := cast (congrArg
      (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) reconstruct.symm) checkpoint.embedding
    (fillCommitPrefix setup.program block suffix embedding
      image.native.config.store checkpoint.source).IntendedFor
        who P := by
  exact phase_commitPrefix_admitted_bounded setup mode runtime leaks bounds wellFormed source
    assessment copies plan maximal inputs horizon scheduler block.length trace clear checkpoint
      block suffix
      reconstruct who consistent savedIntended image
        ⟨imageClear, imageCoverage, imageBindings, results, stamped, preservedImage⟩
          (Nat.le_refl _) available

/-- Every available owned binding in one surviving actual prefix is admitted.
The proof descends on the static source prefix at authentic earlier callbacks;
no prior admission or intended current-view witness is supplied. -/
theorem phase_commitPrefix_admitted
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source
      assessment.strategy)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    {Δ : SourceCtx Player L} {P : Finset VarId}
    (block : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (suffix : SourceProgram Player L Δ P)
    (reconstruct : block.prepend suffix = checkpoint.residual.tail)
    (who : Player)
    (consistent : (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      who).Consistent (control.execution.recall who))
    (savedIntended : ProtocolState.Intended setup.program
      (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source)))
    (available :
      let embedding := cast (congrArg
        (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
          program) reconstruct.symm) checkpoint.embedding
      ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
        eventOwner? (block.prepend suffix) index = some who →
          embedding.event index ∈
            control.execution.application.current.native.config.cut.completed) :
    let embedding := cast (congrArg
      (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) reconstruct.symm) checkpoint.embedding
    (fillCommitPrefix setup.program block suffix embedding
      control.execution.application.current.native.config.store checkpoint.source).IntendedFor
        who P := by
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  exact phase_commitPrefix_admitted_bounded setup mode runtime leaks bounds wellFormed source
    assessment copies plan maximal inputs horizon scheduler block.length trace clear checkpoint
      block suffix
      reconstruct who consistent savedIntended control.execution.application.current
        ⟨clear, (phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
          raw).active,
        (phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw).active,
        (fun _ _ => rfl),
        (phaseLiveBindingStamp_history runtime leaks plan inputs horizon scheduler raw),
        (fun _ _ present => present)⟩ (Nat.le_refl _) available

end Vegas
