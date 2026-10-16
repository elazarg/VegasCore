/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixPolicyReadout
import Vegas.Source.CommitPrefixWord
import Vegas.Source.ProtocolSuffixPolicy
import Vegas.Game.CommitRecoveryNonmissingSource
import Vegas.Game.RecoveryReadyCommitWitness
import Vegas.Game.RecoveryReadyCommitInformation
import Vegas.Game.RecoveryCommitPrefixSupport
import Vegas.Game.PhaseBindingSourceReference

/-! # Complete-word prediction at actual partially completed binding callbacks

The saved entry and actual completed own word determine a supported source
conditioning view. Future foreign and repeated-owner choices remain in the
complete block draw. This does not identify the entire native observation law.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

theorem protocolAction_cast {Γ : SourceCtx Player L} {O : Finset VarId}
    (first second : SourceProgram Player L Γ O) (equal : first = second)
    (profile : SourceProgram.BehavioralProfile second) (who : Player) (point :
      ProtocolState first) :
    ((cast (congrArg SourceProgram.BehavioralProfile equal.symm) profile) who).protocolAction first
        (ProtocolState.observe who first point) =
      (profile who).protocolAction second
        (ProtocolState.observe who second (cast (congrArg ProtocolState equal) point)) := by
  cases equal
  rfl

/-- The actual clear callback's source kernel is predicted from a complete
current-block word, conditional on its actual filled owned view. Source
support is derived from the original fully mixed auxiliary assessment. -/
theorem RecoverySourceCheckpoint.binding_word_prediction_of_ready
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (execution : (phaseApplication runtime leaks).Execution)
    (checkpoint : RecoverySourceCheckpoint setup mode execution.application)
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    {Δ Ξ : SourceCtx Player L} {P Q : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (later : SourceProgram.CommitPrefix ((name, .commitment owner payload) :: Δ)
      (insert name P) Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard (later.prepend suffix)) =
      checkpoint.residual.tail)
    (clear : execution.application.entry.excluded = ∅)
    (stored : execution.application.StoredCheckpoint)
    (selected : Fin (eventCount checkpoint.residual.tail))
    (atEnd : selected.val = earlier.length)
    (ready : execution.application.current.native.config.cut.Ready
      (checkpoint.embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (checkpoint.embedding.event selected) = some owner)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (checkpoint.embedding.event selected)).IsPublication)
    (valid : execution.application.current.native.BindingInvariant) {inputs}
    (reachable : execution.application.current.native.config.Reachable inputs)
    (retained : execution.application.HistoryCheckpoint)
    (saved : execution.application.entry.native.config.cut.IsPrefix
      execution.application.attempt.phase) :
    ∃ residual : SourceProgram.BehavioralProfile checkpoint.residual.tail,
      let typed := cast (congrArg SourceProgram.BehavioralProfile reconstruct.symm) residual
      let embedding := cast (congrArg
        (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
          program) reconstruct.symm) checkpoint.embedding
      let filled := fillCommitPrefix setup.program earlier
        (.commit name owner fresh guard (later.prepend suffix)) embedding
        execution.application.current.native.config.store checkpoint.source
      let current := earlier.tailProfile
        (.commit name owner fresh guard (later.prepend suffix)) typed
      let before := earlier.prefixLaw
        (.commit name owner fresh guard (later.prepend suffix)) typed checkpoint.source
      let complete := before.bind (fun config =>
        ((SourceProgram.CommitPrefix.commit name owner fresh guard later).prefixLaw suffix
          current config))
      let read := fun config : SourceProgram.Config Player L Ξ =>
        let view := later.entryView owner (config.view owner)
        (view.back true, (view.1.cells name (.commitment owner payload) .here).getD .failure)
      (filled.view owner ∈ (before.map (SourceProgram.Config.view owner)).support) ∧
        (fiberPosterior complete (fun config => (read config).1) (filled.view owner)).map
          (fun config => some (OwnAction.commit owner name payload (read config).2)) =
        (setup.commitRecoveryNonmissingProfile assessment.strategy owner
          (setup.commitRecoveryClearInformation wellFormed owner
            (phaseSourceView? setup mode runtime leaks owner (checkpoint.embedding.event selected)
              (execution.observe (phaseApplication runtime leaks) owner)))).map
                (fun choice => CommitRecoveryMove.underlying choice.1) := by
  obtain ⟨residual, same⟩ := checkpoint.origin.exists_behavioralProfile
    (setup.commitRecoveryNonmissingSourceProfile wellFormed assessment.strategy)
  have raw : ∀ owner point,
      (residual owner).protocolAction checkpoint.residual.tail
          (ProtocolState.observe owner checkpoint.residual.tail point) =
        (setup.commitRecoveryNonmissingProfile assessment.strategy owner
          (setup.commitRecoveryClearInformation wellFormed owner
            (some (ProtocolState.observe owner setup.program
              (checkpoint.residual.lift point))))).map
                (fun choice => CommitRecoveryMove.underlying choice.1) := by
    intro owner point
    exact (same owner point).trans
      (setup.commitRecovery_nonmissingSource_raw wellFormed assessment.strategy owner _)
  refine ⟨residual, ?_⟩
  intro typed embedding filled current before complete read
  have attempt := fillCommitPrefix_attempt setup.program earlier
    (.commit name owner fresh guard (later.prepend suffix)) embedding
      execution.application.current.native.config.store checkpoint.source
  have supported := checkpoint.attempt_mem_prefixLaw clear wellFormed assessment mixed residual
    raw earlier (.commit name owner fresh guard (later.prepend suffix)) reconstruct filled attempt
  have present : filled.view owner ∈ (before.map (SourceProgram.Config.view owner)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨filled, supported, rfl⟩
  refine ⟨present, ?_⟩
  have nextLaw := earlier.prefixLaw_binding_conditional fresh guard later suffix typed
    checkpoint.source (filled.view owner) present
  change (fiberPosterior complete (fun config => (read config).1) (filled.view owner)).map
      (fun config => (read config).2) = commitKernel current (filled.view owner) at nextLaw
  have encoded := congrArg (fun law : PMF (PublicationResult (L.Val payload)) =>
    law.map (fun result => some (OwnAction.commit owner name payload result))) nextLaw
  rw [PMF.map_comp] at encoded
  have localLaw := earlier.binding_kernel_protocolAction fresh guard (later.prepend suffix)
    typed filled
  let point := cast (congrArg ProtocolState reconstruct)
    (earlier.liftPoint (.commit name owner fresh guard (later.prepend suffix))
      (ProtocolState.entry (.commit name owner fresh guard (later.prepend suffix)) filled))
  have castLaw := protocolAction_cast _ _ reconstruct residual owner
    (earlier.liftPoint (.commit name owner fresh guard (later.prepend suffix))
      (ProtocolState.entry (.commit name owner fresh guard (later.prepend suffix)) filled))
  have aligned := checkpoint.filled_prefix_history_of_ready fresh guard (later.prepend suffix)
    earlier reconstruct clear selected atEnd ready acting valid reachable retained saved
  have decoded := checkpoint.filled_prefix_view fresh guard (later.prepend suffix) earlier
    reconstruct stored selected atEnd ready acting notPublication _ aligned
  have actualDecoded : phaseSourceView? setup mode runtime leaks owner
      (checkpoint.embedding.event selected)
        (execution.observe (phaseApplication runtime leaks) owner) = some
      (ProtocolState.observe owner setup.program (checkpoint.residual.lift point)) :=
    (phaseSourceView?_observed setup mode runtime leaks execution owner
      (checkpoint.embedding.event selected)).trans decoded
  calc
    _ = (commitKernel current (filled.view owner)).map
        (fun result => some (OwnAction.commit owner name payload result)) := encoded
    _ = (typed owner).protocolAction _ _ := localLaw
    _ = (residual owner).protocolAction checkpoint.residual.tail
        (ProtocolState.observe owner checkpoint.residual.tail point) := castLaw
    _ = _ := by rw [raw, actualDecoded]

/-- The actual filled owned view predicts the next draw of the ORIGINAL complete block word. -/
theorem RecoverySourceCheckpoint.binding_owned_word_prediction_of_ready
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (execution : (phaseApplication runtime leaks).Execution)
    (checkpoint : RecoverySourceCheckpoint setup mode execution.application)
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    {Δ Ξ : SourceCtx Player L} {P Q : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (later : SourceProgram.CommitPrefix ((name, .commitment owner payload) :: Δ)
      (insert name P) Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard (later.prepend suffix)) =
      checkpoint.residual.tail)
    (clear : execution.application.entry.excluded = ∅)
    (stored : execution.application.StoredCheckpoint)
    (selected : Fin (eventCount checkpoint.residual.tail))
    (atEnd : selected.val = earlier.length)
    (ready : execution.application.current.native.config.cut.Ready
      (checkpoint.embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (checkpoint.embedding.event selected) = some owner)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (checkpoint.embedding.event selected)).IsPublication)
    (valid : execution.application.current.native.BindingInvariant) {inputs}
    (reachable : execution.application.current.native.config.Reachable inputs)
    (retained : execution.application.HistoryCheckpoint)
    (saved : execution.application.entry.native.config.cut.IsPrefix
      execution.application.attempt.phase) :
    ∃ residual : SourceProgram.BehavioralProfile checkpoint.residual.tail,
      let typed := cast (congrArg SourceProgram.BehavioralProfile reconstruct.symm) residual
      let embedding := cast (congrArg
        (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
          program) reconstruct.symm) checkpoint.embedding
      let filled := fillCommitPrefix setup.program earlier
        (.commit name owner fresh guard (later.prepend suffix)) embedding
        execution.application.current.native.config.store checkpoint.source
      let current := earlier.tailProfile
        (.commit name owner fresh guard (later.prepend suffix)) typed
      let before := earlier.prefixLaw
        (.commit name owner fresh guard (later.prepend suffix)) typed checkpoint.source
      let complete := before.bind (fun config =>
        ((SourceProgram.CommitPrefix.commit name owner fresh guard later).prefixLaw suffix
          current config))
      let beforeView := fun view : DecisionView owner Ξ =>
        (later.entryView owner view).back true
      let wordAction := (earlier.append (.commit name owner fresh guard later)).wordAction
        owner earlier.length
      (filled.view owner ∈ (before.map (SourceProgram.Config.view owner)).support) ∧
        (fiberPosterior (complete.map (SourceProgram.Config.view owner)) beforeView
          (filled.view owner)).map wordAction =
        (setup.commitRecoveryNonmissingProfile assessment.strategy owner
          (setup.commitRecoveryClearInformation wellFormed owner
            (phaseSourceView? setup mode runtime leaks owner (checkpoint.embedding.event selected)
              (execution.observe (phaseApplication runtime leaks) owner)))).map
                (fun choice => CommitRecoveryMove.underlying choice.1) := by
  obtain ⟨residual, predicted⟩ := checkpoint.binding_word_prediction_of_ready runtime leaks
    execution wellFormed assessment mixed fresh guard later suffix earlier reconstruct clear
    stored selected atEnd ready acting notPublication valid reachable retained saved
  refine ⟨residual, ?_⟩
  intro typed embedding filled current before complete beforeView wordAction
  obtain ⟨present, predicts⟩ := predicted
  have oldNext := earlier.prefixLaw_binding_conditional fresh guard later suffix typed
    checkpoint.source (filled.view owner) present
  have encodedOld := congrArg (fun law : PMF (PublicationResult (L.Val payload)) =>
    law.map fun result => some (OwnAction.commit owner name payload result)) oldNext
  rw [PMF.map_comp] at encodedOld
  have next := earlier.prefixLaw_owned_word_conditional fresh guard later suffix typed
    checkpoint.source (filled.view owner) present
  exact ⟨present, next.trans (encodedOld.symm.trans predicts)⟩

variable [Fintype Player]

/-- Actual canonical and fresh-slot callback outcomes use precisely the
conditional next draw of a complete source block word. Raw uniform noise
remains outside this reference law. -/
theorem RecoverySourceCheckpoint.binding_word_native_reference_of_ready
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
        horizon scheduler).Trace (some control))
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    {Δ Ξ : SourceCtx Player L} {P Q : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (later : SourceProgram.CommitPrefix ((name, .commitment owner payload) :: Δ)
      (insert name P) Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard (later.prepend suffix)) =
      checkpoint.residual.tail)
    (clear : control.execution.application.entry.excluded = ∅)
    (stored : control.execution.application.StoredCheckpoint)
    (selected : Fin (eventCount checkpoint.residual.tail))
    (atEnd : selected.val = earlier.length)
    (ready : control.execution.application.current.native.config.cut.Ready
      (checkpoint.embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (checkpoint.embedding.event selected) = some owner)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (checkpoint.embedding.event selected)).IsPublication)
    (valid : control.execution.application.current.native.BindingInvariant) {inputs}
    (reachable : control.execution.application.current.native.config.Reachable inputs)
    (retained : control.execution.application.HistoryCheckpoint)
    (saved : control.execution.application.entry.native.config.cut.IsPrefix
      control.execution.application.attempt.phase)
    (binding : (serviceGraph setup mode).outputLayout (checkpoint.embedding.event selected) =
      .binding owner payload)
    (actingControl : control.actor = some owner)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, checkpoint.embedding.event selected⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall owner),
      PhaseCount.event? message.payload ≠
        some ⟨control.execution.application.attempt, checkpoint.embedding.event selected⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1) :
    let initial := setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan
      (encodeInputs draw)
    let model := (PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
      scheduler
    let input := some (control.execution.recall owner,
      control.execution.observe (phaseApplication runtime leaks) owner)
    let law := mix slotWeight slotNonnegative slotBounded
      (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler owner input)
      (phaseSourceStrategy setup mode runtime leaks bounds wellFormed assessment initial horizon
        scheduler owner input)
    let outcome := fun choice : model.Choice owner input =>
      phaseBindingResponseOutcome setup mode runtime leaks control.execution owner payload
        (choice.1.getD ⟨none⟩)
    ∃ residual : SourceProgram.BehavioralProfile checkpoint.residual.tail,
      let typed := cast (congrArg SourceProgram.BehavioralProfile reconstruct.symm) residual
      let embedding := cast (congrArg
        (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
          program) reconstruct.symm) checkpoint.embedding
      let filled := fillCommitPrefix setup.program earlier
        (.commit name owner fresh guard (later.prepend suffix)) embedding
        control.execution.application.current.native.config.store checkpoint.source
      let current := earlier.tailProfile
        (.commit name owner fresh guard (later.prepend suffix)) typed
      let before := earlier.prefixLaw
        (.commit name owner fresh guard (later.prepend suffix)) typed checkpoint.source
      let complete := before.bind (fun config =>
        ((SourceProgram.CommitPrefix.commit name owner fresh guard later).prefixLaw suffix
          current config))
      let read := fun config : SourceProgram.Config Player L Ξ =>
        let view := later.entryView owner (config.view owner)
        (view.back true, (view.1.cells name (.commitment owner payload) .here).getD .failure)
      (filled.view owner ∈ (before.map (SourceProgram.Config.view owner)).support) ∧
        (fiberPosterior complete (fun config => (read config).1) (filled.view owner)).map
          (fun config => some (OwnAction.commit owner name payload (read config).2)) =
        (fiberPosterior (law.map outcome) Prod.snd false).map
          (fun data => decodeEventAction setup.program (checkpoint.embedding.event selected)
            (cast (congrArg EventField.Action binding.symm) data.1)) := by
  intro initial model input law outcome
  obtain ⟨residual, prediction⟩ := checkpoint.binding_word_prediction_of_ready runtime leaks
    control.execution wellFormed assessment mixed fresh guard later suffix earlier reconstruct
      clear stored selected atEnd ready acting notPublication valid reachable retained saved
  refine ⟨residual, ?_⟩
  intro typed embedding filled current before complete read
  dsimp only at prediction
  refine ⟨prediction.1, prediction.2.trans ?_⟩
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  have physicalTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  obtain ⟨view, decoded, actual⟩ := phaseSourceMixture_source_reference_of_history setup mode
    runtime leaks bounds wellFormed assessment owner (checkpoint.embedding.event selected)
      payload binding (PhaseCount.onePacketMenu runtime leaks bounds) plan inputs horizon scheduler
        capacity control physicalTrace actingControl request unsent values initial slotWeight
          slotNonnegative slotBounded
  rw [setup.commitRecovery_nonmissingSource_raw] at actual
  rw [decoded]
  exact actual.symm

end Vegas
