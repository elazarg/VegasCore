/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryBindingWordRealization
import Vegas.Game.PhaseSourceTimingPolicy

/-! # Actual timing responses from complete source commitment words -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

open Classical in
/-- The independent slot tier and selected timing option use the SAME latent
word result. A timing WAIT is silence and leaves the original omission flag
semantically distinct. Every serial is guarded by the actual universal menu. -/
def phaseBindingTimingWordResponse (who : Player) (event : (serviceGraph setup mode).EventId)
    (payload : L.Ty) (missing : PMF Bool) (option : LateOption bounds.candidateCount)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (result : PublicationResult (L.Val payload))
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    PMF (phaseApplication runtime leaks).Action :=
  mix slotWeight slotNonnegative slotBounded
    (PhaseCount.phaseBindingWordResponse runtime leaks bounds who event payload missing 0
      1 (by norm_num) le_rfl result past view)
    (match option with
    | none => PMF.pure ⟨none⟩
    | some serial =>
        if serial.val ∈ PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
            past view then
          PhaseCount.phaseBindingWordResponse runtime leaks bounds who event payload missing
            serial.val 0 le_rfl (by norm_num) result past view
        else PMF.pure ⟨none⟩)

/-- Every hidden-word member is globally legal in the actual one-packet menu,
including WAIT, unavailable serials and typed failure results. -/
theorem phaseBindingTimingWordResponse_covered (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (missing : PMF Bool) (option : LateOption bounds.candidateCount)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (result : PublicationResult (L.Val payload))
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (phaseBindingTimingWordResponse setup mode runtime leaks bounds who
      event payload missing option slotWeight slotNonnegative slotBounded result past
        view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  classical
  unfold phaseBindingTimingWordResponse at supported
  rcases support_mix_subset _ _ _ _ _ supported with slots | selected
  · rw [PhaseCount.phaseBindingWordResponse, PMF.support_bind] at slots
    obtain ⟨omitted, _possible, responseAt⟩ := Set.mem_iUnion₂.mp slots
    cases omitted with
    | true =>
        cases (PMF.mem_support_pure_iff ..).mp responseAt
        exact PhaseCount.silence_onePacket runtime leaks bounds who past view
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, mix_one] at responseAt
        exact PhaseCount.phaseBindingSlotPolicy_covered runtime leaks bounds who event payload
          (fun _ _ => PMF.pure result) past view response responseAt
  · cases option with
    | none =>
        cases (PMF.mem_support_pure_iff ..).mp selected
        exact PhaseCount.silence_onePacket runtime leaks bounds who past view
    | some serial =>
        by_cases eligible : serial.val ∈ PhaseCount.phaseBindingSlots runtime leaks bounds who
            event payload past view
        · simp only [eligible, ↓reduceIte] at selected
          rw [PhaseCount.phaseBindingWordResponse, PMF.support_bind] at selected
          obtain ⟨omitted, _possible, responseAt⟩ := Set.mem_iUnion₂.mp selected
          cases omitted with
          | true =>
              cases (PMF.mem_support_pure_iff ..).mp responseAt
              exact PhaseCount.silence_onePacket runtime leaks bounds who past view
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, mix_zero] at responseAt
              cases (PMF.mem_support_pure_iff ..).mp responseAt
              exact (Finset.mem_filter.mp eligible).2.2 result
        · simp only [eligible, ↓reduceIte] at selected
          cases (PMF.mem_support_pure_iff ..).mp selected
          exact PhaseCount.silence_onePacket runtime leaks bounds who past view

/-- A nonsilent reply identifies the actual typed result for every timing
option; WAIT itself cannot create a transmission. -/
theorem phaseBindingTimingWordResponse_nonsilent (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (missing : PMF Bool) (option : LateOption bounds.candidateCount)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (result : PublicationResult (L.Val payload))
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (phaseBindingTimingWordResponse setup mode runtime leaks bounds who
      event payload missing option slotWeight slotNonnegative slotBounded result past view).support)
    (sending : response ≠ ⟨none⟩) :
    ∃ serial, response = phaseBindingResponse runtime leaks who event payload result serial := by
  classical
  unfold phaseBindingTimingWordResponse at supported
  rcases support_mix_subset _ _ _ _ _ supported with slots | selected
  · exact PhaseCount.phaseBindingWordResponse_nonsilent runtime leaks bounds who event payload
      missing 0 1 (by norm_num) le_rfl result past view response slots sending
  · cases option with
    | none => exact (sending ((PMF.mem_support_pure_iff ..).mp selected)).elim
    | some serial =>
        by_cases eligible : serial.val ∈ PhaseCount.phaseBindingSlots runtime leaks bounds who
            event payload past view
        · simp only [eligible, ↓reduceIte] at selected
          exact PhaseCount.phaseBindingWordResponse_nonsilent runtime leaks bounds who event
            payload missing serial.val 0 le_rfl (by norm_num) result past view response
              selected sending
        · simp only [eligible, ↓reduceIte] at selected
          exact (sending ((PMF.mem_support_pure_iff ..).mp selected)).elim

/-- Silence has the same likelihood under every latent typed word result.
A timing WAIT remains distinct from an original omission. -/
theorem phaseBindingTimingWordResponse_silence_congr (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (missing : PMF Bool) (option : LateOption bounds.candidateCount)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (first second : PublicationResult (L.Val payload))
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    phaseBindingTimingWordResponse setup mode runtime leaks bounds who event payload missing
        option slotWeight slotNonnegative slotBounded first past view ⟨none⟩ =
      phaseBindingTimingWordResponse setup mode runtime leaks bounds who event payload missing
        option slotWeight slotNonnegative slotBounded second past view ⟨none⟩ := by
  classical
  simp only [phaseBindingTimingWordResponse, mix_apply]
  rw [PhaseCount.phaseBindingWordResponse_silence_congr runtime leaks bounds who event payload
    missing 0 1 (by norm_num) le_rfl first second past view]
  cases option with
  | none => rfl
  | some serial =>
      by_cases eligible : serial.val ∈ PhaseCount.phaseBindingSlots runtime leaks bounds who
          event payload past view
      · simp only [eligible, ↓reduceIte]
        rw [PhaseCount.phaseBindingWordResponse_silence_congr runtime leaks bounds who event payload
          missing serial.val 0 le_rfl (by norm_num) first second past view]
      · simp only [eligible, ↓reduceIte]

/-- On common support, all timing-member reply atoms have identical mass
across hidden source results. This supplies the original-word filter theorem
for arbitrary timing plans, with the RAW perturbation tier kept separate. -/
theorem phaseBindingTimingWordResponse_apply_eq_of_support (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (missing : PMF Bool) (option : LateOption bounds.candidateCount)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (first second : PublicationResult (L.Val payload))
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (left : response ∈ (phaseBindingTimingWordResponse setup mode runtime leaks bounds who event
      payload missing option slotWeight slotNonnegative slotBounded first past view).support)
    (right : response ∈ (phaseBindingTimingWordResponse setup mode runtime leaks bounds who event
      payload missing option slotWeight slotNonnegative slotBounded second past view).support) :
    phaseBindingTimingWordResponse setup mode runtime leaks bounds who event payload missing
        option slotWeight slotNonnegative slotBounded first past view response =
      phaseBindingTimingWordResponse setup mode runtime leaks bounds who event payload missing
        option slotWeight slotNonnegative slotBounded second past view response := by
  by_cases silent : response = ⟨none⟩
  · rw [silent]
    exact phaseBindingTimingWordResponse_silence_congr setup mode runtime leaks bounds who event
      payload missing option slotWeight slotNonnegative slotBounded first second past view
  · obtain ⟨firstSlot, firstAt⟩ := phaseBindingTimingWordResponse_nonsilent setup mode runtime leaks
      bounds who event payload missing option slotWeight slotNonnegative slotBounded first past
        view response left silent
    obtain ⟨secondSlot, secondAt⟩ := phaseBindingTimingWordResponse_nonsilent setup mode runtime
      leaks bounds who event payload missing option slotWeight slotNonnegative slotBounded second
        past view response right silent
    have same := ((phaseBindingResponse_eq_iff runtime leaks who event payload first
      second firstSlot secondSlot).mp (firstAt.symm.trans secondAt)).2
    cases same
    rfl

private theorem timingPolicy_unavailable (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (serial : Fin bounds.candidateCount)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (unavailable : serial.val ∉ PhaseCount.phaseBindingSlots runtime leaks bounds who event
      payload past view) :
    phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed assessment who event
      payload binding (some serial) past view = PMF.pure ⟨none⟩ := by
  classical
  rw [phaseRecoveryTimingPolicy, phaseRecoveryTimingTaggedLaw, PMF.map_comp]
  have constant (choice : Option (CommitRecoveryMove Player L)) :
      phaseBindingTimingResponse setup mode runtime leaks bounds who event payload (some serial)
        past view (phaseRecoveryBindingData setup mode event who payload binding choice) =
          ⟨none⟩ := by
    unfold phaseBindingTimingResponse
    split <;> simp only [unavailable, ↓reduceIte]
  simp only [Function.comp_def, constant]
  exact PMF.map_const _ _

/-- The complete original nonmissing word law and original omission marginal
realize EVERY operational option with the same prior, including WAIT. -/
theorem phaseBindingTimingWordResponse_law {Word : Type}
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (prior : PMF Word) (read : Word → Option (OwnAction Player L))
    (predicts : prior.map read =
      (setup.commitRecoveryNonmissingProfile assessment.strategy who
        (setup.commitRecoveryClearInformation wellFormed who
          (phaseSourceView? setup mode runtime leaks who event view))).map
            (fun choice => CommitRecoveryMove.underlying choice.1))
    (option : LateOption bounds.candidateCount) :
    let missing := (assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
      (phaseSourceView? setup mode runtime leaks who event view))).map
        (fun choice => CommitRecoveryMove.missed choice.1)
    mix slotWeight slotNonnegative slotBounded
      (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed assessment who event
        payload binding past view)
      (phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed assessment who event
        payload binding option past view) =
      prior.bind (fun word => phaseBindingTimingWordResponse setup mode runtime leaks bounds
        who event payload missing option slotWeight slotNonnegative slotBounded
        (phaseRecoveryBindingData setup mode event who payload binding
          (CommitRecoveryMove.lift (read word))).1 past view) := by
  classical
  intro missing
  have slots := word_response_law setup mode runtime leaks bounds wellFormed assessment who
    event payload binding 0 past view 1 (by norm_num) le_rfl prior read predicts
  simp only [mix_one] at slots
  cases option with
  | none =>
      rw [phaseRecoveryTimingPolicy_wait, slots]
      have constant : prior.bind (fun _ => PMF.pure (⟨none⟩ :
          (phaseApplication runtime leaks).Action)) = PMF.pure ⟨none⟩ := PMF.bind_const _ _
      rw [← constant, ← bind_mix_kernel]
      rfl
  | some serial =>
      by_cases eligible : serial.val ∈ PhaseCount.phaseBindingSlots runtime leaks bounds who
          event payload past view
      · have fixed := word_response_law setup mode runtime leaks bounds wellFormed assessment who
          event payload binding serial.val past view 0 le_rfl (by norm_num) prior read predicts
        simp only [mix_zero] at fixed
        rw [phaseRecoveryTimingPolicy_send setup mode runtime leaks bounds wellFormed assessment
          who event payload binding serial past view eligible]
        change mix slotWeight slotNonnegative slotBounded _
          (phaseRecoveryBindingLaw setup mode runtime leaks wellFormed assessment who event
            payload binding serial.val
              (phaseSourceView? setup mode runtime leaks who event view)) = _
        rw [slots, fixed, ← bind_mix_kernel]
        apply bind_congr_on_support
        intro word _
        simp only [phaseBindingTimingWordResponse, eligible, ↓reduceIte]
        rfl
      · rw [timingPolicy_unavailable setup mode runtime leaks bounds wellFormed assessment who
          event payload binding serial past view eligible, slots]
        have constant : prior.bind (fun _ => PMF.pure (⟨none⟩ :
            (phaseApplication runtime leaks).Action)) = PMF.pure ⟨none⟩ := PMF.bind_const _ _
        rw [← constant, ← bind_mix_kernel]
        apply bind_congr_on_support
        intro word _
        simp only [phaseBindingTimingWordResponse, eligible, ↓reduceIte]
        rfl

/-- One actual clear callback derives ONE complete original word prior for ALL
operational timing options. No predicted result or source-view equality is a
premise, and accepted typed failure remains among the original draws. -/
theorem RecoverySourceCheckpoint.binding_timing_word_response_of_ready
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
      execution.application.attempt.phase)
    (bounds : MessageBounds (serviceGraph setup mode))
    (binding : (serviceGraph setup mode).outputLayout (checkpoint.embedding.event selected) =
      .binding owner payload)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight)
    (slotBounded : slotWeight ≤ 1) :
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
        ∀ option : LateOption bounds.candidateCount,
          mix slotWeight slotNonnegative slotBounded
            (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed assessment owner
              (checkpoint.embedding.event selected) payload binding (execution.recall owner)
              (execution.observe (phaseApplication runtime leaks) owner))
            (phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed assessment owner
              (checkpoint.embedding.event selected) payload binding option (execution.recall owner)
              (execution.observe (phaseApplication runtime leaks) owner)) =
          (fiberPosterior (complete.map (SourceProgram.Config.view owner)) beforeView
            (filled.view owner)).bind
            (fun word => phaseBindingTimingWordResponse setup mode runtime leaks bounds owner
              (checkpoint.embedding.event selected) payload
              ((assessment.strategy owner (setup.commitRecoveryClearInformation wellFormed owner
                (phaseSourceView? setup mode runtime leaks owner
                  (checkpoint.embedding.event selected)
                  (execution.observe (phaseApplication runtime leaks) owner)))).map
                    (fun choice => CommitRecoveryMove.missed choice.1)) option slotWeight
              slotNonnegative slotBounded
              (phaseRecoveryBindingData setup mode (checkpoint.embedding.event selected) owner
                payload binding (CommitRecoveryMove.lift (wordAction word))).1
              (execution.recall owner)
              (execution.observe (phaseApplication runtime leaks) owner)) := by
  obtain ⟨residual, prediction⟩ := checkpoint.binding_owned_word_prediction_of_ready runtime leaks
    execution wellFormed assessment mixed fresh guard later suffix earlier reconstruct clear
    stored selected atEnd ready acting notPublication valid reachable retained saved
  refine ⟨residual, ?_⟩
  intro typed embedding filled current before complete beforeView wordAction
  obtain ⟨present, predicts⟩ := prediction
  refine ⟨present, ?_⟩
  intro option
  exact phaseBindingTimingWordResponse_law setup mode runtime leaks bounds wellFormed assessment
    owner (checkpoint.embedding.event selected) payload binding (execution.recall owner)
      (execution.observe (phaseApplication runtime leaks) owner) slotWeight slotNonnegative
      slotBounded (fiberPosterior (complete.map (SourceProgram.Config.view owner)) beforeView
        (filled.view owner)) wordAction predicts option

/-- Decoding the actual finite timing component retains its independent RAW
tier and both complete physical source tiers, at every full input. -/
theorem phaseSourceTimingComponent_decoded (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (option : LateOption bounds.candidateCount) :
    (phaseSourceTimingComponent setup mode runtime leaks bounds initial horizon scheduler
      wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
        slotBounded who (some (past, view)) option).map
          (fun choice => choice.1.getD ⟨none⟩) =
      mix noise noiseNonnegative noiseBounded
        (((PhaseCount.onePacketMenu runtime leaks bounds).uniformPolicy initial horizon
          scheduler who (some (past, view))).map (fun choice => choice.1.getD ⟨none⟩))
        (mix slotWeight slotNonnegative slotBounded
          (phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed assessment who
            past view)
          (phaseSourceTimingPolicy setup mode runtime leaks bounds wellFormed assessment option
            who past view)) := by
  let extract : Option (phaseApplication runtime leaks).Action →
      (phaseApplication runtime leaks).Action := fun response => response.getD ⟨none⟩
  have slotMap := congrArg (PMF.map extract)
    (phaseSourceSlotStrategy_map_val setup mode runtime leaks bounds wellFormed assessment
      initial horizon scheduler who past view)
  simp only [PMF.map_comp, Function.comp_def] at slotMap
  change _ = (phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed assessment who
    past view).map id at slotMap
  rw [PMF.map_id] at slotMap
  have timingMap := congrArg (PMF.map extract)
    (phaseSourceTimingStrategy_map_val setup mode runtime leaks bounds wellFormed assessment
      initial horizon scheduler option who past view)
  simp only [PMF.map_comp, Function.comp_def] at timingMap
  change _ = (phaseSourceTimingPolicy setup mode runtime leaks bounds wellFormed assessment
    option who past view).map id at timingMap
  rw [PMF.map_id] at timingMap
  dsimp only [extract] at slotMap timingMap
  rw [phaseSourceTimingComponent, mix_map, mix_map, slotMap, timingMap]

end Vegas
