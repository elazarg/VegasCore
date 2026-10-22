/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.QualifiedBinding.ReplayCoverage

/-! # Original annotation sums and qualified mass normalization -/

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

local notation "nativeModel" => ReactiveApplication.ResponseMenu.information
  nativeMenu nativeInitial implementation.horizon implementation.scheduler

open Classical in
/-- The deleted qualification mass is the exact complement inside the
original information mass, including foreign-bad and false-admission fibers. -/
theorem qualified_prefix_complement
    (profile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (who : Player) (site : (nativeModel).InformationSite who)
    (event : (serviceGraph setup .concurrent).EventId)
    (finite : (nativeModel).informationMass profile who site ≠ ⊤) :
    (nativeModel).informationMass profile who site -
        qualifiedPrefixMass setup implementation profile who site event =
      ∑' history : (nativeModel).InformationHistory who site.1,
        (nativeModel).historyReachWeight profile history.val *
          (if (∀ owner, owner ≠ who →
              ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
                implementation.leaks implementation.bounds nativeInitial implementation.horizon
                implementation.scheduler owner history.val) ∧
              history.val.state.elim True (fun control =>
                who ∉ control.execution.application.current.excluded) then
            ∑' tape : ReservedEpoch.Tape Player implementation.tapeLength,
              prefixTapeLaw setup implementation history.val tape *
                if bindingAdmissionBit setup implementation who event history.val tape
                  then 0 else 1
          else 1) := by
  classical
  let good := fun history : (nativeModel).InformationHistory who site.1 =>
    (∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
        history.val) ∧ history.val.state.elim True (fun control =>
          who ∉ control.execution.application.current.excluded)
  let success := fun history : (nativeModel).InformationHistory who site.1 =>
    if good history then
      ∑' tape : ReservedEpoch.Tape Player implementation.tapeLength,
        prefixTapeLaw setup implementation history.val tape *
          if bindingAdmissionBit setup implementation who event history.val tape then 1 else 0
    else 0
  let failure := fun history : (nativeModel).InformationHistory who site.1 =>
    if good history then
      ∑' tape : ReservedEpoch.Tape Player implementation.tapeLength,
        prefixTapeLaw setup implementation history.val tape *
          if bindingAdmissionBit setup implementation who event history.val tape then 0 else 1
    else 1
  have partition (history : (nativeModel).InformationHistory who site.1) :
      failure history + success history = 1 := by
    by_cases qualified : good history
    · simp only [failure, success, qualified, ↓reduceIte]
      rw [← ENNReal.tsum_add]
      calc
        _ = ∑' tape : ReservedEpoch.Tape Player implementation.tapeLength,
            prefixTapeLaw setup implementation history.val tape := by
          apply tsum_congr
          intro tape
          cases bindingAdmissionBit setup implementation who event history.val tape <;> simp
        _ = 1 := (prefixTapeLaw setup implementation history.val).tsum_coe
    · simp only [failure, success, qualified, ↓reduceIte, add_zero]
  have total :
      (∑' history : (nativeModel).InformationHistory who site.1,
        (nativeModel).historyReachWeight profile history.val * failure history) +
          qualifiedPrefixMass setup implementation profile who site event =
        (nativeModel).informationMass profile who site := by
    change (∑' history : (nativeModel).InformationHistory who site.1,
      (nativeModel).historyReachWeight profile history.val * failure history) +
        (∑' history : (nativeModel).InformationHistory who site.1,
          (nativeModel).historyReachWeight profile history.val * success history) =
        ∑' history : (nativeModel).InformationHistory who site.1,
          (nativeModel).historyReachWeight profile history.val
    rw [← ENNReal.tsum_add]
    apply tsum_congr
    intro history
    rw [← mul_add, partition, mul_one]
  have bounded : qualifiedPrefixMass setup implementation profile who site event ≤
      (nativeModel).informationMass profile who site := by
    rw [← total]
    exact le_add_self
  have admittedFinite : qualifiedPrefixMass setup implementation profile who site event ≠ ⊤ :=
    ne_top_of_le_ne_top finite bounded
  exact (ENNReal.eq_sub_of_add_eq admittedFinite total).symm

open Classical in
private theorem mechanical_index_sum
    (who : Player) (history : (nativeProtocol).History)
    (weight : ReservedEpoch.Tape Player implementation.tapeLength → ℝ≥0∞) :
    (∑' index : MechanicalIndex setup implementation who,
      if mechanicalWord setup implementation who history.trace = index.1.val
        then weight index.2 else 0) = ∑' tape, weight tape := by
  classical
  erw [ENNReal.tsum_prod']
  let selected : Set.range (fun history : (nativeProtocol).History =>
      mechanicalWord setup implementation who history.trace) :=
    ⟨mechanicalWord setup implementation who history.trace, history, rfl⟩
  rw [tsum_eq_single selected]
  · simp only [selected, ↓reduceIte]
  · intro other different
    have mismatch : mechanicalWord setup implementation who history.trace ≠ other.val := by
      intro equal
      exact different (Subtype.ext equal.symm)
    simp only [mismatch, ↓reduceIte, tsum_zero]

/-- Tonelli expansion of the actual annotation keeps qualification inside
the original history and tape sum. No source or native likelihood is changed. -/
theorem annotated_continuation_sum
    (operational : implementation.Operational)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (who : Player) (site : (nativeModel).InformationSite who)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (value : L.Val payload)
    (reward : setup.proposalRecoveryProtocol.History →
      setup.proposalRecoveryProtocol.History → ℝ≥0∞) :
    (∑' index : MechanicalIndex setup implementation who,
      ∑' cut : setup.proposalRecoveryProtocol.History,
        ∑' completed : setup.proposalRecoveryProtocol.History,
          annotatedForcedBlockWeight setup values implementation operational sourceProfile
            nativeProfile who site index event payload value cut completed *
              reward cut completed) =
      ∑' history : (nativeModel).InformationHistory who site.1,
        ∑' tape : ReservedEpoch.Tape Player implementation.tapeLength,
          ∑' cut : setup.proposalRecoveryProtocol.History,
            ∑' completed : setup.proposalRecoveryProtocol.History,
              ∑' entry : setup.proposalRecoveryProtocol.History,
                ∑' word : SourceProgram.History Player L,
                  annotatedPrefixWeight setup values implementation operational sourceProfile
                    nativeProfile who history.val tape entry word *
                    (if bindingAdmissionBit setup implementation who event history.val tape
                      then 1 else 0) *
                    sourceForcedBlockJoint setup values implementation who history.val event
                      payload entry word value (cut, completed) * reward cut completed := by
  classical
  let weight := fun (history : (nativeModel).InformationHistory who site.1)
      (tape : ReservedEpoch.Tape Player implementation.tapeLength)
      (cut completed : setup.proposalRecoveryProtocol.History) =>
    ∑' entry : setup.proposalRecoveryProtocol.History,
      ∑' word : SourceProgram.History Player L,
        annotatedPrefixWeight setup values implementation operational sourceProfile nativeProfile
          who history.val tape entry word *
          (if bindingAdmissionBit setup implementation who event history.val tape then 1 else 0) *
          sourceForcedBlockJoint setup values implementation who history.val event payload entry
            word value (cut, completed) * reward cut completed
  let term := fun (history : (nativeModel).InformationHistory who site.1)
      (index : MechanicalIndex setup implementation who)
      (cut completed : setup.proposalRecoveryProtocol.History) =>
    if mechanicalWord setup implementation who history.val.trace = index.1.val
      then weight history index.2 cut completed else 0
  have expanded :
      (∑' index : MechanicalIndex setup implementation who,
        ∑' cut : setup.proposalRecoveryProtocol.History,
          ∑' completed : setup.proposalRecoveryProtocol.History,
            annotatedForcedBlockWeight setup values implementation operational sourceProfile
              nativeProfile who site index event payload value cut completed *
                reward cut completed) =
      ∑' index : MechanicalIndex setup implementation who,
        ∑' cut : setup.proposalRecoveryProtocol.History,
          ∑' completed : setup.proposalRecoveryProtocol.History,
            ∑' history : (nativeModel).InformationHistory who site.1,
              term history index cut completed := by
    apply tsum_congr
    intro index
    apply tsum_congr
    intro cut
    apply tsum_congr
    intro completed
    rw [annotatedForcedBlockWeight, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro history
    by_cases same : mechanicalWord setup implementation who history.val.trace = index.1.val
    · simp only [term, same, ↓reduceIte]
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro entry
      rw [← ENNReal.tsum_mul_right]
    · simp only [term, same, ↓reduceIte, zero_mul]
  rw [expanded]
  calc
    _ = ∑' index : MechanicalIndex setup implementation who,
        ∑' cut : setup.proposalRecoveryProtocol.History,
          ∑' history : (nativeModel).InformationHistory who site.1,
            ∑' completed : setup.proposalRecoveryProtocol.History,
              term history index cut completed := by
      apply tsum_congr
      intro index
      apply tsum_congr
      intro cut
      exact ENNReal.tsum_comm
    _ = ∑' index : MechanicalIndex setup implementation who,
        ∑' history : (nativeModel).InformationHistory who site.1,
          ∑' cut : setup.proposalRecoveryProtocol.History,
            ∑' completed : setup.proposalRecoveryProtocol.History,
              term history index cut completed := by
      apply tsum_congr
      intro index
      exact ENNReal.tsum_comm
    _ = ∑' history : (nativeModel).InformationHistory who site.1,
        ∑' index : MechanicalIndex setup implementation who,
          ∑' cut : setup.proposalRecoveryProtocol.History,
            ∑' completed : setup.proposalRecoveryProtocol.History,
              term history index cut completed := ENNReal.tsum_comm
    _ = ∑' history : (nativeModel).InformationHistory who site.1,
        ∑' index : MechanicalIndex setup implementation who,
          if mechanicalWord setup implementation who history.val.trace = index.1.val then
            ∑' cut : setup.proposalRecoveryProtocol.History,
              ∑' completed : setup.proposalRecoveryProtocol.History,
                weight history index.2 cut completed
          else 0 := by
      apply tsum_congr
      intro history
      apply tsum_congr
      intro index
      by_cases same : mechanicalWord setup implementation who history.val.trace = index.1.val
      · simp only [term, same, ↓reduceIte]
      · simp only [term, same, ↓reduceIte, tsum_zero]
    _ = _ := by
      apply tsum_congr
      intro history
      exact mechanical_index_sum setup implementation who history.val
        (fun tape => ∑' cut, ∑' completed, weight history tape cut completed)

private theorem native_binding_site_history
    (who : Player) (site : (nativeModel).InformationSite who)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (siteEq : site.1 = some (past, view))
    (history : (nativeModel).InformationHistory who site.1) :
    ∃ (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control)),
      history.val = ⟨some control, trace⟩ ∧ control.actor = some who ∧
      control.execution.recall who = past ∧
      control.execution.observe nativeApplication who = view := by
  have observed : (nativeModel).infoOf who history.val.trace = some (past, view) :=
    history.property.trans siteEq
  rcases history with ⟨⟨state, trace⟩, _historyInfo⟩
  cases state with
  | none =>
    have nativeInfo := (nativeMenu).info nativeInitial implementation.horizon
      implementation.scheduler who trace
    simp only [ReactiveApplication.observe] at nativeInfo
    change ((nativeMenu).signals nativeInitial implementation.horizon
      implementation.scheduler).infoOf who trace = some (past, view) at observed
    rw [nativeInfo] at observed
    cases observed
  | some control =>
    have active : control.actor = some who := by
      by_contra inactive
      have nativeInfo := (nativeMenu).info nativeInitial implementation.horizon
        implementation.scheduler who trace
      simp only [ReactiveApplication.observe, inactive, ↓reduceIte] at nativeInfo
      change ((nativeMenu).signals nativeInitial implementation.horizon
        implementation.scheduler).infoOf who trace = some (past, view) at observed
      rw [nativeInfo] at observed
      cases observed
    have actualInfo : (nativeModel).infoOf who trace =
        some (control.execution.recall who, control.execution.observe nativeApplication who) := by
      change ((nativeMenu).signals nativeInitial implementation.horizon
        implementation.scheduler).infoOf who trace = _
      have nativeInfo := (nativeMenu).info nativeInitial implementation.horizon
        implementation.scheduler who trace
      simpa only [ReactiveApplication.observe, active, ↓reduceIte] using nativeInfo
    have views := Option.some.inj (actualInfo.symm.trans observed)
    exact ⟨control, trace, rfl, active, congrArg Prod.fst views, congrArg Prod.snd views⟩

open Classical in
/-- Actual cursors of one selected residual with common entry and completion
have the same structural replay history. -/
private theorem ordinary_cursor_structural_history_eq
    (first second : ResidualProgram setup.program) (sameResidual : first = second)
    (leftControl rightControl : (nativeApplication).Control)
    (leftPhase rightPhase : RuntimePhase (serviceGraph setup .concurrent))
    (left : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
      implementation.leaks implementation.plan leftControl leftPhase
        (SourceProgram.commitPhase first.tail).block (SourceProgram.commitPhase first.tail).suffix)
    (right : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
      implementation.leaks implementation.plan rightControl rightPhase
        (SourceProgram.commitPhase second.tail).block
        (SourceProgram.commitPhase second.tail).suffix)
    (leftLift : ∀ point, left.lift point = first.lift
      (cast (congrArg ProtocolState (SourceProgram.commitPhase first.tail).reconstruct) point))
    (rightLift : ∀ point, right.lift point = second.lift
      (cast (congrArg ProtocolState (SourceProgram.commitPhase second.tail).reconstruct) point))
    (leftResult : SourceProgram.Config Player L (SourceProgram.commitPhase first.tail).context)
    (rightResult : SourceProgram.Config Player L (SourceProgram.commitPhase second.tail).context)
    (leftLast rightLast : CommitRecoveryState setup.program)
    (leftTrace : setup.proposalRecoveryProtocol.Trace (some leftLast))
    (rightTrace : setup.proposalRecoveryProtocol.Trace (some rightLast))
    (leftAttempt : (SourceProgram.commitPhase first.tail).block.Attempt left.source
      left.current.excluded leftResult leftLast.excluded)
    (rightAttempt : (SourceProgram.commitPhase second.tail).block.Attempt right.source
      right.current.excluded rightResult rightLast.excluded)
    (sameEntry : (⟨some left.current, left.trace⟩ : setup.proposalRecoveryProtocol.History) =
      ⟨some right.current, right.trace⟩)
    (sameFinished : (⟨some leftLast, leftTrace⟩ : setup.proposalRecoveryProtocol.History) =
      ⟨some rightLast, rightTrace⟩)
    (leftRows : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace leftTrace) =
      leftAttempt.joints.reverse ++ setup.recoveryJointRecall
        (setup.proposalRecoveryEraseTrace left.trace))
    (rightRows : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace rightTrace) =
      rightAttempt.joints.reverse ++ setup.recoveryJointRecall
        (setup.proposalRecoveryEraseTrace right.trace)) :
    (leftAttempt.withoutMisses ∅ left.source).history =
      (rightAttempt.withoutMisses ∅ right.source).history := by
  classical
  cases sameResidual
  have sameCurrent := Option.some.inj (congrArg History.state sameEntry)
  have sameSource : left.source = right.source := by
    apply ProtocolState.entry_injective ((SourceProgram.commitPhase first.tail).block.prepend
      (SourceProgram.commitPhase first.tail).suffix)
    apply sourceReplaySuffixInjective setup left.origin
    calc
      _ = left.current.point := left.point.symm
      _ = right.current.point := congrArg CommitRecoveryState.point sameCurrent
      _ = right.lift _ := right.point
      _ = _ := by rw [leftLift, rightLift]
  have prior := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
    setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace history.trace)) sameEntry
  have completed := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
    setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace history.trace)) sameFinished
  have rows := leftRows.symm.trans (completed.trans rightRows)
  rw [prior] at rows
  have joints := List.reverse_injective (List.append_cancel_right rows)
  have replay : ∀ (entry other : SourceProgram.Config Player L first.context)
      (excluded otherExcluded : Finset Player)
      (firstResult secondResult : SourceProgram.Config Player L
        (SourceProgram.commitPhase first.tail).context)
      (firstAfter secondAfter : Finset Player)
      (firstAttempt : (SourceProgram.commitPhase first.tail).block.Attempt entry excluded
        firstResult firstAfter)
      (secondAttempt : (SourceProgram.commitPhase first.tail).block.Attempt other otherExcluded
        secondResult secondAfter),
      entry = other → excluded = otherExcluded → firstAttempt.joints = secondAttempt.joints →
      (firstAttempt.withoutMisses ∅ entry).history =
        (secondAttempt.withoutMisses ∅ other).history := by
    intro entry other excluded otherExcluded firstResult secondResult firstAfter secondAfter
      firstAttempt secondAttempt sourceEq masks word
    subst other
    subst otherExcluded
    exact congrArg SourceProgram.Config.history (structural_replay_eq_of_joints
      (SourceProgram.commitPhase first.tail).block entry excluded firstResult secondResult
        firstAfter secondAfter firstAttempt secondAttempt word entry)
  exact replay left.source right.source left.current.excluded right.current.excluded
    leftResult rightResult leftLast.excluded rightLast.excluded leftAttempt rightAttempt
      sameSource (congrArg CommitRecoveryState.excluded sameCurrent) joints

open Classical in
/-- Positive original annotations at the same native information and source cut
retain the same literal closed source entry across native histories. -/
theorem positive_original_annotated_entry_eq
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (who : Player) (site : (nativeModel).InformationSite who)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (siteEq : site.1 = some (past, view))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who past view event payload)
    (value : L.Val payload)
    (histories : Bool → (nativeModel).InformationHistory who site.1)
    (tapes : Bool → ReservedEpoch.Tape Player implementation.tapeLength)
    (targets : Bool → setup.proposalRecoveryProtocol.History)
    (words : Bool → SourceProgram.History Player L)
    (cut finished : setup.proposalRecoveryProtocol.History)
    (canonicalSupported : ∀ side, setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational (histories side).val) ≠ 0)
    (positive : ∀ side, annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who (histories side).val (tapes side) (targets side) (words side) *
        (if bindingAdmissionBit setup implementation who event (histories side).val (tapes side)
          then 1 else 0) *
        sourceForcedBlockJoint setup values implementation who (histories side).val event payload
          (targets side) (words side) value (cut, finished) ≠ 0) :
    targets false = targets true := by
  classical
  have geometric (side : Bool) : TracePrefix (targets side).trace cut.trace ∧
      cut.trace.length = (targets side).trace.length +
        (event.val - view.application.2.attempt.phase) := by
    obtain ⟨control, trace, historyEq, active, pastEq, viewEq⟩ :=
      native_binding_site_history setup implementation who site past view siteEq (histories side)
    have actualClean : CleanUnsentBinding setup implementation who
        (control.execution.recall who) (control.execution.observe nativeApplication who)
          event payload := by
      rw [pastEq, viewEq]
      exact clean
    have supported := canonicalSupported side
    have atom := positive side
    have information := (histories side).property.trans siteEq
    rw [historyEq] at supported atom information
    have pair := positive_original_annotated_pair setup values implementation operational
      fullValues sourceProfile nativeProfile who control trace (tapes side) (targets side)
        cut finished (words side) supported past view information event payload clean value atom
    have geometry := positive_original_annotated_geometry setup values implementation operational
      fullValues sourceProfile nativeProfile who control trace active (tapes side) (targets side)
        cut finished (words side) supported event payload actualClean value atom
    have phase : control.execution.application.attempt.phase =
        view.application.2.attempt.phase :=
      congrArg (fun observed : (nativeApplication).PlayerView =>
        observed.application.2.attempt.phase) viewEq
    exact ⟨pair.2.2.2.2.1, by simpa only [phase] using geometry.2.2.2.1⟩
  have left := geometric false
  have right := geometric true
  exact left.1.eq_of_same_length right.1 (by omega)

open Classical in
/-- At one actual source pair, positive original annotations retain one structural
foreign word across native histories at the same native information. -/
theorem positive_original_annotated_word_eq
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (who : Player) (site : (nativeModel).InformationSite who)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (siteEq : site.1 = some (past, view))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who past view event payload)
    (value : L.Val payload)
    (histories : Bool → (nativeModel).InformationHistory who site.1)
    (tapes : Bool → ReservedEpoch.Tape Player implementation.tapeLength)
    (targets : Bool → setup.proposalRecoveryProtocol.History)
    (words : Bool → SourceProgram.History Player L)
    (cut finished : setup.proposalRecoveryProtocol.History)
    (canonicalSupported : ∀ side, setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational (histories side).val) ≠ 0)
    (positive : ∀ side, annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who (histories side).val (tapes side) (targets side) (words side) *
        (if bindingAdmissionBit setup implementation who event (histories side).val (tapes side)
          then 1 else 0) *
        sourceForcedBlockJoint setup values implementation who (histories side).val event payload
          (targets side) (words side) value (cut, finished) ≠ 0) :
    words false = words true := by
  classical
  choose control trace historyEq _active _pastEq viewEq using fun side =>
    native_binding_site_history setup implementation who site past view siteEq (histories side)
  have actualSupported (side : Bool) : setup.proposalRecoveryModel.historyReachWeight
      sourceProfile (canonicalSource setup implementation operational
        ⟨some (control side), trace side⟩) ≠ 0 := by
    rw [← historyEq side]
    exact canonicalSupported side
  have information (side : Bool) : (nativeModel).infoOf who (trace side) =
      some (past, view) := by
    have observed := (histories side).property.trans siteEq
    rw [historyEq side] at observed
    exact observed
  have actualPair (side : Bool) := positive_original_annotated_pair setup values implementation
    operational fullValues sourceProfile nativeProfile who (control side) (trace side) (tapes side)
      (targets side) cut finished (words side) (actualSupported side) past view (information side)
        event payload clean value (by simpa only [historyEq side] using positive side)
  have sameTarget := positive_original_annotated_entry_eq setup values implementation operational
    fullValues sourceProfile nativeProfile who site past view siteEq event payload clean value
      histories tapes targets words cut finished canonicalSupported positive
  obtain ⟨_leftRead, _leftReadEq, _leftUnique, leftPhase, left, leftResult, leftLast, leftTrace,
      leftAttempt, leftStart, leftLift, leftFinish, leftWord, leftRows, _leftLabels⟩ :=
    (actualPair false).2.2.2.2.2.2
  obtain ⟨_rightRead, _rightReadEq, _rightUnique, rightPhase, right, rightResult, rightLast,
      rightTrace, rightAttempt, rightStart, rightLift, rightFinish, rightWord, rightRows,
      _rightLabels⟩ := (actualPair true).2.2.2.2.2.2
  let checkpoint (side : Bool) :=
    (checkpointSelection setup implementation operational (trace side)).val.checkpoint
  have phase (side : Bool) : (control side).execution.application.attempt.phase =
      view.application.2.attempt.phase :=
    congrArg (fun observed : (nativeApplication).PlayerView =>
      observed.application.2.attempt.phase) (viewEq side)
  have residual := (checkpoint false).residual_eq_of_phase_eq (checkpoint true)
    ((phase false).trans (phase true).symm)
  have replay := ordinary_cursor_structural_history_eq setup implementation
    (checkpoint false).residual (checkpoint true).residual residual (control false) (control true)
      leftPhase rightPhase left right leftLift rightLift leftResult rightResult leftLast rightLast
        leftTrace rightTrace leftAttempt rightAttempt
          (leftStart.symm.trans (sameTarget.trans rightStart))
          (leftFinish.symm.trans rightFinish) leftRows rightRows
  rw [leftWord, rightWord]
  exact congrArg (fun history : SourceProgram.History Player L =>
    fun owner => if owner = who then [] else history owner) replay

open Classical in
/-- The original annotation has zero mass whenever its actual qualified source
term vanishes, including offsite, foreign-bad and unsupported encoded cuts. -/
theorem annotated_forced_block_zero_of_source_zero
    (operational : implementation.Operational)
    (scale sourceBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (sourceBadPositive : 0 < sourceBad.val) (sourceBadBelow : sourceBad.val < 1)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (who : Player) (site : (nativeModel).InformationSite who)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (siteEq : site.1 = some (past, view))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who past view event payload)
    (source : QualifiedBindingSource setup values implementation sourceProfile who site
      past view event payload clean.binding)
    (index : MechanicalIndex setup implementation who) (value : L.Val payload)
    (cut finished : setup.proposalRecoveryProtocol.History)
    (zero : (if same : setup.proposalRecoveryModel.infoOf who cut.trace = source.site.1 then
        if setup.proposalRecoveryForeignGood who cut then
          setup.proposalRecoveryModel.historyReachWeight sourceProfile cut *
            sourceForcedBlock setup values who cut (same.symm ▸ source.encode value) finished
        else 0
      else 0) = 0) :
    annotatedForcedBlockWeight setup values implementation operational sourceProfile nativeProfile
      who site index event payload value cut finished = 0 := by
  classical
  unfold annotatedForcedBlockWeight
  apply ENNReal.tsum_eq_zero.mpr
  intro history
  by_cases mechanical : mechanicalWord setup implementation who history.val.trace = index.1.val
  · rw [ite_eq_left mechanical]
    apply ENNReal.tsum_eq_zero.mpr
    intro target
    apply ENNReal.tsum_eq_zero.mpr
    intro word
    by_contra positive
    obtain ⟨control, trace, historyEq, active, pastEq, viewEq⟩ :=
      native_binding_site_history setup implementation who site past view siteEq history
    have historyInfo : (nativeModel).infoOf who trace = site.1 :=
      (congrArg (fun history : (nativeProtocol).History =>
        (nativeModel).infoOf who history.trace) historyEq).symm.trans history.property
    rw [historyEq] at positive
    subst past
    subst view
    obtain ⟨same, _key, _entryGood, cutGood, _finishedGood, reach,
        _past, _future, _cutDepth, _finishedDepth, supported, _wordSupport, _unique⟩ :=
      positive_original_annotated_coverage setup values implementation operational scale sourceBad
        scalePositive scaleBelow sourceBadPositive sourceBadBelow fullValues sourceProfile
          nativeProfile sourcePrescribed who site control trace active historyInfo index.2
            target cut finished word event payload clean source value positive
    rw [dite_eq_left same, ite_eq_left cutGood] at zero
    exact (ENNReal.mul_pos reach.ne' supported.ne').ne' zero
  · exact ite_eq_right mechanical

open Classical in
/-- The actual qualified source package supplies positive finite source mass
and representative-independent own and foreign-class factors. -/
private theorem qualified_source_factors
    (wellFormed : setup.WellFormed)
    (scale sourceBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (sourceBadBelow : sourceBad.val < 1)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (who : Player) (site : (nativeModel).InformationSite who)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload)
    (source : QualifiedBindingSource setup values implementation sourceProfile who site
      past view event payload binding) :
    let own := ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
      (sourceProfile who) (setup.proposalRecoveryModel.ownPlay who source.anchor.trace))
    let classes := (setup.proposalRecoveryForeignProducts values scale sourceBad scale
      who source.anchor.trace).1
    let mass := ∑' history : setup.proposalRecoveryModel.InformationHistory who source.site.1,
      if setup.proposalRecoveryForeignGood who history.val then
        setup.proposalRecoveryModel.historyReachWeight sourceProfile history.val else 0
    0 < own ∧ own ≠ ⊤ ∧ 0 < classes ∧ classes ≠ ⊤ ∧ 0 < mass ∧ mass ≠ ⊤ ∧
      ∀ history : setup.proposalRecoveryProtocol.History,
        setup.proposalRecoveryForeignGood who history →
        setup.proposalRecoveryModel.infoOf who history.trace = source.site.1 →
        own = ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
          (sourceProfile who) (setup.proposalRecoveryModel.ownPlay who history.trace)) ∧
        classes = (setup.proposalRecoveryForeignProducts values scale sourceBad scale
          who history.trace).1 := by
  classical
  intro own classes mass
  have reachFinite := setup.proposalRecoveryModel.historyReachWeight_ne_top sourceProfile
    source.anchor
  have realReach := ENNReal.toReal_pos source.anchorReach.ne' reachFinite
  rw [setup.proposalRecoveryModel.historyReachProbability_eq_player_mul_counterfactual
    sourceProfile who source.anchor.trace,
    setup.proposalRecoveryModel.playerReachProbability_eq_ownPlayReachProbability] at realReach
  have ownPositive : 0 < own := by
    apply ENNReal.ofReal_pos.mpr
    apply lt_of_not_ge
    intro nonpositive
    exact (not_le_of_gt realReach) (mul_nonpos_of_nonpos_of_nonneg nonpositive
      (setup.proposalRecoveryModel.counterfactualReachProbability_nonneg sourceProfile who
        source.anchor.trace))
  have classesPositive : 0 < classes :=
    setup.proposalRecovery_foreign_class_pos_of_good values scale sourceBad scale scalePositive
      scaleBelow sourceBadBelow scalePositive scaleBelow wellFormed who source.anchor.trace
        source.anchorGood
  have classesFinite : classes ≠ ⊤ :=
    (setup.proposalRecoveryForeignProducts_finite values scale sourceBad scale who
      source.anchor.trace).1
  have anchorTerm := ENNReal.le_tsum
    (f := fun history : setup.proposalRecoveryModel.InformationHistory who source.site.1 =>
      if setup.proposalRecoveryForeignGood who history.val then
        setup.proposalRecoveryModel.historyReachWeight sourceProfile history.val else 0)
      ⟨source.anchor, source.anchorInfo⟩
  have massPositive : 0 < mass := source.anchorReach.trans_le (by
    simpa only [ite_eq_left source.anchorGood] using anchorTerm)
  have massBound : mass ≤ setup.proposalRecoveryModel.informationMass sourceProfile who
      source.site := by
    apply ENNReal.tsum_le_tsum
    intro history
    split
    · exact le_rfl
    · exact bot_le
  have massFinite : mass ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (massBound.trans (setup.proposalRecoveryModel.informationMass_le_one sourceProfile who
      source.site (setup.proposalRecoveryModel_decisionAntichain who source.site)))
  refine ⟨ownPositive, ENNReal.ofReal_ne_top, classesPositive, classesFinite, massPositive,
    massFinite, ?_⟩
  intro history good information
  have common := source.anchorInfo.trans information.symm
  have record := setup.proposalRecoveryModel_perfectRecall who source.anchor.trace history.trace
    common
  exact ⟨congrArg (fun record => ENNReal.ofReal
    (setup.proposalRecoveryModel.ownPlayReachProbability (sourceProfile who) record)) record,
    setup.proposalRecovery_foreign_class_eq_of_information values scale sourceBad scale
      scalePositive scaleBelow sourceBadBelow scalePositive scaleBelow wellFormed who
        source.anchor.trace history.trace common source.anchorGood good⟩

open Classical in
/-- A positive complete issued-and-selected source cylinder implies the
foreign ledger cylinder is positive before any annotation is normalized. -/
theorem closed_entry_foreign_positive
    (operational : implementation.Operational)
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload)
    (entry : NativeBindingEntry setup implementation operational control trace who event)
    (saved : control.execution.application.current.excluded =
      control.execution.application.entry.excluded)
    (value : L.Val payload) (current : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some current))
    (erased : setup.proposalRecoveryErasedHistory ⟨some entry.cursor.current, entry.cursor.trace⟩ =
      setup.proposalRecoveryErasedHistory ⟨some current, targetTrace⟩)
    (present : true ∈ ((setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values)
      (SourceProgram.commitPhase
        (checkpointSelection setup implementation operational
          trace).val.checkpoint.residual.tail).block.length
      ⟨some current, targetTrace⟩).map
      (bindingCompletedObservation setup implementation
        (checkpointSelection setup implementation operational trace).val.checkpoint control who
          event
          payload binding value)).support) :
    true ∈ ((ordinaryForeignJoint setup values implementation operational who ⟨some control, trace⟩
      ⟨some current, targetTrace⟩).map Prod.snd).support := by
  classical
  let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
  let block := SourceProgram.commitPhase checkpoint.residual.tail
  obtain ⟨cursor, canonical, _offset, _source, _refs, embedding, lift, views, _config, size⟩ :=
    selected_binding_cursor setup implementation operational who control trace event entry
      true
  have same : setup.proposalRecoveryErasedHistory ⟨some cursor.current, cursor.trace⟩ =
      setup.proposalRecoveryErasedHistory ⟨some current, targetTrace⟩ :=
    (congrArg setup.proposalRecoveryErasedHistory
      (canonical.trans entry.canonicalHistory.symm)).trans erased
  let selected := PhaseProposalOrdinarySourceCursor.of_erasedHistory setup .concurrent
    implementation.runtime implementation.leaks implementation.plan control entry.phase
      block.block block.suffix cursor current targetTrace same
  have positive : 0 < block.block.length := by
    have nonempty := entry.phase.nonempty
    rw [size]
    omega
  let observed := fun history : setup.proposalRecoveryProtocol.History =>
    match history.state.bind (fun last => residualEntry? block.suffix
        (fun point => selected.lift (block.block.liftPoint block.suffix point)) last.point) with
    | none => false
    | some finished => decide (∀ owner, issuedLedger setup implementation block.block
        control.execution.application.attempt.phase control
        (control.execution.application.attempt.phase + block.block.length) owner
        (finished.view owner))
  have ledgerPresent : true ∈ ((setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) block.block.length
      ⟨some selected.current, selected.trace⟩).map observed).support := by
    obtain ⟨history, supported, observedTrue⟩ := (PMF.mem_support_map_iff ..).mp present
    refine (PMF.mem_support_map_iff ..).mpr ⟨history, supported, ?_⟩
    have sameLift : (fun point => selected.lift (block.block.liftPoint block.suffix point)) =
        (fun point => checkpoint.residual.lift
          (cast (congrArg ProtocolState block.reconstruct)
            (block.block.liftPoint block.suffix point))) := by
      funext point
      exact lift _
    unfold bindingCompletedObservation at observedTrue
    unfold residualBindingObservation at observedTrue
    dsimp only [observed]
    rw [sameLift]
    simp only [checkpoint, block] at observedTrue ⊢
    cases pulled : history.state.bind (fun last => residualEntry? block.suffix
        (fun point => checkpoint.residual.lift
          (cast (congrArg ProtocolState block.reconstruct)
            (block.block.liftPoint block.suffix point))) last.point) with
    | none =>
        simp only [checkpoint, block] at pulled
        simp only [pulled] at observedTrue
        cases observedTrue
    | some finished =>
        simp only [checkpoint, block] at pulled
        simp only [pulled] at observedTrue ⊢
        apply decide_eq_true
        exact (decide_eq_true_eq.mp observedTrue).1
  have actual := ordinaryForeignJoint_positive_of_source_ledger setup values implementation
    operational
    who control trace entry.phase saved selected positive embedding lift views ledgerPresent
  simpa only [selected, PhaseProposalOrdinarySourceCursor.of_erasedHistory] using actual

open Classical in
/-- At an actual clean qualified native history, the complete source
annotation has exactly its original native-reach and whole-tape prefix mass. -/
private theorem annotated_prefix_mass
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (who : Player) (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control)) (active : control.actor = some who)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational ⟨some control, trace⟩) ≠ 0)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨some control, trace⟩)
    (value : L.Val payload) (tape : ReservedEpoch.Tape Player implementation.tapeLength) :
    (∑' target : setup.proposalRecoveryProtocol.History, ∑' word : SourceProgram.History Player L,
      annotatedPrefixWeight setup values implementation operational sourceProfile nativeProfile
        who ⟨some control, trace⟩ tape target word) =
      (nativeModel).historyReachWeight nativeProfile ⟨some control, trace⟩ *
        prefixTapeLaw setup implementation ⟨some control, trace⟩ tape := by
  classical
  let history : (nativeProtocol).History := ⟨some control, trace⟩
  let canonical := canonicalSource setup implementation operational history
  let closed := setup.proposalRecoveryClosedLaw sourceProfile who canonical
  let posterior := fun target => ((fiberPosterior
    (ordinaryForeignJoint setup values implementation operational who history target) Prod.snd
      true).map Prod.fst)
  let weight := (nativeModel).historyReachWeight nativeProfile history *
    prefixTapeLaw setup implementation history tape
  let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
  let block := SourceProgram.commitPhase checkpoint.residual.tail
  obtain ⟨entry⟩ := qualified_binding_entry setup implementation operational control trace who
    event payload clean foreign
  obtain ⟨saved, _represented⟩ := entry.selected
  have currentSaved : control.execution.application.current.excluded =
      control.execution.application.entry.excluded :=
    entry.excluded.trans (entry.entryExcluded.symm.trans (congrArg RecoveryState.excluded saved))
  have alive : who ∉ control.execution.application.current.excluded := clean.request.2.2.2.2
  have guarded : (∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          history) ∧ history.state.elim True (fun current =>
            who ∉ current.execution.application.current.excluded) := ⟨foreign, alive⟩
  have mass : setup.proposalRecoveryClosedMass sourceProfile who canonical ≠ 0 := by
    apply (PMF.mem_support_iff ..).mp
    exact (PMF.mem_support_map_iff ..).mpr
      ⟨canonical, (PMF.mem_support_iff ..).mpr canonicalSupported, rfl⟩
  obtain ⟨_ready, graphPresent, _posterior, _graphMass⟩ :=
    binding_value_frontier_posterior setup values
    implementation operational fullValues control trace who active event payload clean foreign
      entry value
  have length := (selected_binding_observation setup implementation operational control trace
    who event payload clean.binding entry value).1
  change block.block.length = entry.block.length at length
  have foreignPositive (target : setup.proposalRecoveryProtocol.History)
      (supported : target ∈ closed.support) :
      true ∈ ((ordinaryForeignJoint setup values implementation operational who history target).map
        Prod.snd).support := by
    have key := ((setup.proposalRecoveryClosedLaw_support sourceProfile who canonical target
      mass).mp supported).1
    obtain ⟨current, targetTrace, targetEq, _good, erased⟩ := closed_key_entry_erased_history
      setup implementation operational who control trace event entry target foreign key
    obtain ⟨sourcePresent, _words, _support⟩ := closed_entry_binding_word setup values
      implementation operational control trace who event payload clean.binding
        (currentSaved ▸ alive) entry value current targetTrace erased graphPresent
    have present : true ∈ ((setup.proposalRecoveryModel.runBehavioralFrom
        (sourceUnflaggedStrategy setup values) block.block.length ⟨some current, targetTrace⟩).map
        (bindingCompletedObservation setup implementation
          (checkpointSelection setup implementation operational trace).val.checkpoint control who
            event payload clean.binding value)).support := by
      rwa [length]
    have actual := closed_entry_foreign_positive setup values implementation operational control
      trace who event payload clean.binding entry currentSaved value current targetTrace erased
        present
    exact targetEq.symm ▸ actual
  have perEntry (target : setup.proposalRecoveryProtocol.History) :
      (∑' word : SourceProgram.History Player L,
        annotatedPrefixWeight setup values implementation operational sourceProfile nativeProfile
          who history tape target word) = weight * closed target := by
    by_cases supported : target ∈ closed.support
    · have present := (PMF.mem_support_iff ..).mp (foreignPositive target supported)
      unfold annotatedPrefixWeight
      dsimp only
      simp_rw [ite_eq_left guarded, ite_eq_right present]
      change (∑' word, weight * (closed target * posterior target word)) = weight * closed target
      simp only [ENNReal.tsum_mul_left, (posterior target).tsum_coe, mul_one]
    · have absent : closed target = 0 := by
        by_contra nonzero
        exact supported ((PMF.mem_support_iff ..).mpr nonzero)
      have atomZero (word : SourceProgram.History Player L) :
          annotatedPrefixWeight setup values implementation operational sourceProfile nativeProfile
            who history tape target word = 0 := by
        unfold annotatedPrefixWeight
        dsimp only
        rw [ite_eq_left guarded]
        change weight * (closed target * _) = 0
        rw [absent, zero_mul, mul_zero]
      simp only [atomZero, tsum_zero, absent, mul_zero]
  change (∑' target, ∑' word, annotatedPrefixWeight setup values implementation operational
    sourceProfile nativeProfile who history tape target word) = weight
  simp_rw [perEntry]
  rw [ENNReal.tsum_mul_left, closed.tsum_coe, mul_one]

theorem tsum_interchange_blocks {A B C D : Type}
    (term : A → B → C → D → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, term a b c d) =
      ∑' c, ∑' d, ∑' a, ∑' b, term a b c d := by
  calc
    _ = ∑' a, ∑' c, ∑' d, ∑' b, term a b c d := by
      apply tsum_congr
      intro a
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro c
      exact ENNReal.tsum_comm
    _ = ∑' c, ∑' a, ∑' d, ∑' b, term a b c d := ENNReal.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro c
      exact ENNReal.tsum_comm

open Classical in
/-- Summing the actual original annotation over its mechanical index and both
source coordinates recovers exactly the original qualification mass. -/
private theorem annotated_forced_block_mass
    (operational : implementation.Operational)
    (scale sourceBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (sourceBadPositive : 0 < sourceBad.val) (sourceBadBelow : sourceBad.val < 1)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (who : Player) (site : (nativeModel).InformationSite who)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (siteEq : site.1 = some (past, view))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who past view event payload)
    (value : L.Val payload) :
    (∑' index : MechanicalIndex setup implementation who,
      ∑' cut : setup.proposalRecoveryProtocol.History,
        ∑' finished : setup.proposalRecoveryProtocol.History,
          annotatedForcedBlockWeight setup values implementation operational sourceProfile
            nativeProfile who site index event payload value cut finished) =
      qualifiedPrefixMass setup implementation nativeProfile who site event := by
  classical
  have jointMass (history : (nativeProtocol).History)
      (target : setup.proposalRecoveryProtocol.History) (word : SourceProgram.History Player L) :
      (∑' cut : setup.proposalRecoveryProtocol.History,
        ∑' finished : setup.proposalRecoveryProtocol.History,
          sourceForcedBlockJoint setup values implementation who history event payload target word
            value (cut, finished)) = 1 := by
    rw [← ENNReal.tsum_prod']
    exact (sourceForcedBlockJoint setup values implementation who history event payload target word
      value).tsum_coe
  have rows (history : (nativeProtocol).History)
      (tape : ReservedEpoch.Tape Player implementation.tapeLength) :
      (∑' cut : setup.proposalRecoveryProtocol.History,
        ∑' finished : setup.proposalRecoveryProtocol.History,
          ∑' target : setup.proposalRecoveryProtocol.History,
            ∑' word : SourceProgram.History Player L,
              annotatedPrefixWeight setup values implementation operational sourceProfile
                nativeProfile who history tape target word *
              (if bindingAdmissionBit setup implementation who event history tape then 1 else 0) *
              sourceForcedBlockJoint setup values implementation who history event payload target
                word value (cut, finished)) =
      (∑' target : setup.proposalRecoveryProtocol.History,
        ∑' word : SourceProgram.History Player L,
          annotatedPrefixWeight setup values implementation operational sourceProfile nativeProfile
            who history tape target word) *
        (if bindingAdmissionBit setup implementation who event history tape then 1 else 0) := by
    rw [tsum_interchange_blocks]
    calc
      _ = ∑' target : setup.proposalRecoveryProtocol.History,
          ∑' word : SourceProgram.History Player L,
            (annotatedPrefixWeight setup values implementation operational sourceProfile
              nativeProfile who history tape target word *
              (if bindingAdmissionBit setup implementation who event history tape then 1 else 0)) *
              (∑' cut : setup.proposalRecoveryProtocol.History,
                ∑' finished : setup.proposalRecoveryProtocol.History,
                  sourceForcedBlockJoint setup values implementation who history event payload
                    target word value (cut, finished)) := by
        apply tsum_congr
        intro target
        apply tsum_congr
        intro word
        simp only [ENNReal.tsum_mul_left]
      _ = ∑' target : setup.proposalRecoveryProtocol.History,
          ∑' word : SourceProgram.History Player L,
            annotatedPrefixWeight setup values implementation operational sourceProfile
              nativeProfile who history tape target word *
              (if bindingAdmissionBit setup implementation who event history tape then 1 else 0) :=
        tsum_congr fun target => tsum_congr fun word => by rw [jointMass history target word,
          mul_one]
      _ = _ := by simp only [ENNReal.tsum_mul_right]
  have expanded := annotated_continuation_sum setup values implementation operational sourceProfile
    nativeProfile who site event payload value (fun _ _ => 1)
  simp only [mul_one] at expanded
  rw [expanded]
  simp_rw [rows]
  unfold qualifiedPrefixMass
  apply tsum_congr
  intro history
  obtain ⟨control, trace, historyEq, active, pastEq, viewEq⟩ :=
    native_binding_site_history setup implementation who site past view siteEq history
  rw [historyEq]
  subst past
  subst view
  by_cases foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨some control, trace⟩
  · have alive : who ∉ control.execution.application.current.excluded := clean.request.2.2.2.2
    have guarded : (∀ owner, owner ≠ who →
        ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
          implementation.leaks implementation.bounds nativeInitial implementation.horizon
            implementation.scheduler owner ⟨some control, trace⟩) ∧
        who ∉ control.execution.application.current.excluded := ⟨foreign, alive⟩
    simp only [Option.elim_some, ite_eq_left guarded]
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro tape
    have canonicalSupported := ne_of_gt (prescribed_source_history_positive setup values scale
      sourceBad scalePositive scaleBelow sourceBadPositive sourceBadBelow fullValues sourceProfile
        sourcePrescribed (canonicalSource setup implementation operational ⟨some control, trace⟩))
    rw [annotated_prefix_mass setup values implementation operational fullValues sourceProfile
      nativeProfile who control trace active canonicalSupported event payload clean foreign value
        tape]
    exact mul_assoc _ _ _
  · simp only [Option.elim_some, foreign, false_and, ↓reduceIte, mul_zero]
    apply ENNReal.tsum_eq_zero.mpr
    intro tape
    simp only [annotatedPrefixWeight, foreign, false_and, ↓reduceIte, mul_zero,
      tsum_zero, zero_mul]

open Classical in
/-- The actual package's forced source kernel sums to its good source mass,
with offsite source histories contributing literally zero. -/
private theorem qualified_source_forced_mass
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (who : Player) (site : (nativeModel).InformationSite who)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload)
    (source : QualifiedBindingSource setup values implementation sourceProfile who site
      past view event payload binding)
    (value : L.Val payload) :
    (∑' cut : setup.proposalRecoveryProtocol.History,
      ∑' finished : setup.proposalRecoveryProtocol.History,
        if same : setup.proposalRecoveryModel.infoOf who cut.trace = source.site.1 then
          if setup.proposalRecoveryForeignGood who cut then
            setup.proposalRecoveryModel.historyReachWeight sourceProfile cut *
              sourceForcedBlock setup values who cut (same.symm ▸ source.encode value) finished
          else 0
        else 0) =
      ∑' history : setup.proposalRecoveryModel.InformationHistory who source.site.1,
        if setup.proposalRecoveryForeignGood who history.val then
          setup.proposalRecoveryModel.historyReachWeight sourceProfile history.val else 0 := by
  classical
  let term := fun cut : setup.proposalRecoveryProtocol.History =>
    if setup.proposalRecoveryModel.infoOf who cut.trace = source.site.1 then
      if setup.proposalRecoveryForeignGood who cut then
        setup.proposalRecoveryModel.historyReachWeight sourceProfile cut else 0
    else 0
  have perCut (cut : setup.proposalRecoveryProtocol.History) :
      (∑' finished : setup.proposalRecoveryProtocol.History,
        if same : setup.proposalRecoveryModel.infoOf who cut.trace = source.site.1 then
          if setup.proposalRecoveryForeignGood who cut then
            setup.proposalRecoveryModel.historyReachWeight sourceProfile cut *
              sourceForcedBlock setup values who cut (same.symm ▸ source.encode value) finished
          else 0
        else 0) = term cut := by
    by_cases same : setup.proposalRecoveryModel.infoOf who cut.trace = source.site.1
    · by_cases good : setup.proposalRecoveryForeignGood who cut
      · simp only [term, dite_eq_left same, ite_eq_left same, ite_eq_left good]
        rw [ENNReal.tsum_mul_left,
          (sourceForcedBlock setup values who cut (same.symm ▸ source.encode value)).tsum_coe,
          mul_one]
      · simp only [term, dite_eq_left same, ite_eq_left same, ite_eq_right good, tsum_zero]
    · simp only [term, dite_eq_right same, ite_eq_right same, tsum_zero]
  simp_rw [perCut]
  have supported : Function.support term ⊆
      {cut | setup.proposalRecoveryModel.infoOf who cut.trace = source.site.1} := by
    intro cut nonzero
    by_contra absent
    change ¬ setup.proposalRecoveryModel.infoOf who cut.trace = source.site.1 at absent
    exact nonzero (by simp only [term, ite_eq_right absent])
  rw [← tsum_subtype_eq_of_support_subset supported]
  apply tsum_congr
  intro history
  have same : setup.proposalRecoveryModel.infoOf who history.val.trace = source.site.1 :=
    history.property
  simp only [term, ite_eq_left same]

open Classical in
/-- The exact rectangle identity for the actual original annotation forces
positive finite mechanical coefficient mass and its source normalization. -/
theorem qualified_annotation_normalization
    (operational : implementation.Operational)
    (scale sourceBad nativeBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (sourceBadPositive : 0 < sourceBad.val) (sourceBadBelow : sourceBad.val < 1)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (who : Player) (site : (nativeModel).InformationSite who)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (siteEq : site.1 = some (past, view))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who past view event payload)
    (qualified : 0 < qualifiedPrefixMass setup implementation nativeProfile who site event)
    (source : QualifiedBindingSource setup values implementation sourceProfile who site
      past view event payload clean.binding) :
    let own := ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
      (sourceProfile who) (setup.proposalRecoveryModel.ownPlay who source.anchor.trace))
    let classes := (setup.proposalRecoveryForeignProducts values scale sourceBad scale
      who source.anchor.trace).1
    let coefficient := mechanicalCoefficient setup implementation
      ⟨nativeBad, scale, scale, scale⟩ nativeProfile who site event
    let mass := ∑' history : setup.proposalRecoveryModel.InformationHistory who source.site.1,
      if setup.proposalRecoveryForeignGood who history.val then
        setup.proposalRecoveryModel.historyReachWeight sourceProfile history.val else 0
    (∀ (index : MechanicalIndex setup implementation who) (value : L.Val payload)
      (cut finished : setup.proposalRecoveryProtocol.History),
      own * classes * annotatedForcedBlockWeight setup values implementation operational
        sourceProfile nativeProfile who site index event payload value cut finished =
      coefficient index *
        (if same : setup.proposalRecoveryModel.infoOf who cut.trace = source.site.1 then
          if setup.proposalRecoveryForeignGood who cut then
            setup.proposalRecoveryModel.historyReachWeight sourceProfile cut *
              sourceForcedBlock setup values who cut (same.symm ▸ source.encode value) finished
          else 0
        else 0)) →
    0 < own ∧ own ≠ ⊤ ∧ 0 < classes ∧ classes ≠ ⊤ ∧ 0 < mass ∧ mass ≠ ⊤ ∧
      0 < ∑' index, coefficient index ∧ (∑' index, coefficient index) ≠ ⊤ ∧
      (∀ history : setup.proposalRecoveryProtocol.History,
        setup.proposalRecoveryForeignGood who history →
        setup.proposalRecoveryModel.infoOf who history.trace = source.site.1 →
        own = ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
          (sourceProfile who) (setup.proposalRecoveryModel.ownPlay who history.trace)) ∧
        classes = (setup.proposalRecoveryForeignProducts values scale sourceBad scale
          who history.trace).1) ∧
      (∑' index, coefficient index) * mass =
        own * classes * qualifiedPrefixMass setup implementation nativeProfile who site event := by
  classical
  intro own classes coefficient mass rectangle
  obtain ⟨ownPositive, ownFinite, classesPositive, classesFinite, massPositive, massFinite,
      constant⟩ := qualified_source_factors setup values implementation operational.wellFormed
    scale sourceBad scalePositive scaleBelow sourceBadBelow sourceProfile who site past view event
      payload clean.binding source
  let value := L.someValue payload
  let annotation := fun index cut finished => annotatedForcedBlockWeight setup values implementation
    operational sourceProfile nativeProfile who site index event payload value cut finished
  let sourceTerm := fun cut finished : setup.proposalRecoveryProtocol.History =>
    if same : setup.proposalRecoveryModel.infoOf who cut.trace = source.site.1 then
      if setup.proposalRecoveryForeignGood who cut then
        setup.proposalRecoveryModel.historyReachWeight sourceProfile cut *
          sourceForcedBlock setup values who cut (same.symm ▸ source.encode value) finished
      else 0
    else 0
  have sourceTotal : (∑' cut, ∑' finished, sourceTerm cut finished) = mass :=
    qualified_source_forced_mass setup values implementation sourceProfile who site past view event
      payload clean.binding source value
  have annotationTotal : (∑' index, ∑' cut, ∑' finished, annotation index cut finished) =
      qualifiedPrefixMass setup implementation nativeProfile who site event :=
    annotated_forced_block_mass setup values implementation operational scale sourceBad
      scalePositive scaleBelow sourceBadPositive sourceBadBelow fullValues sourceProfile
        nativeProfile sourcePrescribed who site past view siteEq event payload clean value
  have pointwise (index : MechanicalIndex setup implementation who)
      (cut finished : setup.proposalRecoveryProtocol.History) :
      own * classes * annotation index cut finished = coefficient index * sourceTerm cut finished :=
    rectangle index value cut finished
  have summed : own * classes * qualifiedPrefixMass setup implementation nativeProfile who site
      event = (∑' index, coefficient index) * mass := by
    calc
      _ = own * classes * (∑' index, ∑' cut, ∑' finished, annotation index cut finished) := by
        rw [annotationTotal]
      _ = ∑' index, ∑' cut, ∑' finished, own * classes * annotation index cut finished := by
        simp only [ENNReal.tsum_mul_left]
      _ = ∑' index, ∑' cut, ∑' finished, coefficient index * sourceTerm cut finished :=
        tsum_congr fun index => tsum_congr fun cut => tsum_congr fun finished =>
          pointwise index cut finished
      _ = ∑' index, coefficient index * (∑' cut, ∑' finished, sourceTerm cut finished) := by
        apply tsum_congr
        intro index
        simp only [ENNReal.tsum_mul_left]
      _ = _ := by rw [sourceTotal, ENNReal.tsum_mul_right]
  have qualifiedBound : qualifiedPrefixMass setup implementation nativeProfile who site event ≤
      (nativeModel).informationMass nativeProfile who site := by
    unfold qualifiedPrefixMass
    apply ENNReal.tsum_le_tsum
    intro history
    split
    · calc
        _ ≤ (nativeModel).historyReachWeight nativeProfile history.val *
            (∑' tape : ReservedEpoch.Tape Player implementation.tapeLength,
              prefixTapeLaw setup implementation history.val tape) := by
          apply mul_le_mul_right
          apply ENNReal.tsum_le_tsum
          intro tape
          cases bindingAdmissionBit setup implementation who event history.val tape <;> simp
        _ = _ := by rw [(prefixTapeLaw setup implementation history.val).tsum_coe, mul_one]
    · simp only [mul_zero]
      exact bot_le
  have qualifiedFinite : qualifiedPrefixMass setup implementation nativeProfile who site event ≠
      ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (qualifiedBound.trans
        ((nativeModel).informationMass_le_one nativeProfile who site
          ((nativeMenu).decisionInformationAntichain nativeInitial implementation.horizon
            implementation.scheduler who site)))
  have numeratorPositive : 0 < own * classes *
      qualifiedPrefixMass setup implementation nativeProfile who site event :=
    ENNReal.mul_pos (mul_ne_zero ownPositive.ne' classesPositive.ne') qualified.ne'
  have numeratorFinite : own * classes *
      qualifiedPrefixMass setup implementation nativeProfile who site event ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ownFinite classesFinite) qualifiedFinite
  have normalized : own * classes *
      qualifiedPrefixMass setup implementation nativeProfile who site event * mass⁻¹ =
        ∑' index, coefficient index := by
    calc
      _ = ((∑' index, coefficient index) * mass) * mass⁻¹ :=
        congrArg (fun total : ℝ≥0∞ => total * mass⁻¹) summed
      _ = _ := by rw [mul_assoc, ENNReal.mul_inv_cancel massPositive.ne' massFinite, mul_one]
  have coefficientPositive : 0 < ∑' index, coefficient index := by
    rw [← normalized]
    exact ENNReal.mul_pos numeratorPositive.ne' (ENNReal.inv_ne_zero.mpr massFinite)
  have coefficientFinite : (∑' index, coefficient index) ≠ ⊤ := by
    rw [← normalized]
    exact ENNReal.mul_ne_top numeratorFinite (ENNReal.inv_ne_top.mpr massPositive.ne')
  exact ⟨ownPositive, ownFinite, classesPositive, classesFinite, massPositive, massFinite,
    coefficientPositive, coefficientFinite, constant, summed.symm⟩

open Classical in
/-- Summing the literal native atom balance gives the original weighted
rectangle. The replay law remains normalized when either displayed source
or mechanical factor is zero; this calculation uses no cancellation. -/
theorem qualified_annotation_rectangle_of_native_atoms
    (operational : implementation.Operational)
    (scale sourceBad nativeBad : Set.Icc (0 : ℝ) 1)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner, (nativeModel).BehavioralPolicy owner)
    (who : Player) (site : (nativeModel).InformationSite who)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload)
    (source : QualifiedBindingSource setup values implementation sourceProfile who site past view
      event payload binding)
    (index : MechanicalIndex setup implementation who) (value : L.Val payload)
    (cut completed : setup.proposalRecoveryProtocol.History)
    (law : PMF ((nativeModel).InformationHistory who site.1)) :
    let own := ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability
      (sourceProfile who) (setup.proposalRecoveryModel.ownPlay who source.anchor.trace))
    let classes := (setup.proposalRecoveryForeignProducts values scale sourceBad scale
      who source.anchor.trace).1
    let coefficient := mechanicalCoefficient setup implementation
      ⟨nativeBad, scale, scale, scale⟩ nativeProfile who site event
    let density :=
      if same : setup.proposalRecoveryModel.infoOf who cut.trace = source.site.1 then
        if setup.proposalRecoveryForeignGood who cut then
          setup.proposalRecoveryModel.historyReachWeight sourceProfile cut *
            sourceForcedBlock setup values who cut (same.symm ▸ source.encode value) completed
        else 0
      else 0
    (∀ history : (nativeModel).InformationHistory who site.1,
      own * classes *
        (if mechanicalWord setup implementation who history.val.trace = index.1.val then
          ∑' entry : setup.proposalRecoveryProtocol.History,
            ∑' word : SourceProgram.History Player L,
              annotatedPrefixWeight setup values implementation operational sourceProfile
                  nativeProfile who history.val index.2 entry word *
                (if bindingAdmissionBit setup implementation who event history.val index.2
                  then 1 else 0) *
                sourceForcedBlockJoint setup values implementation who history.val event payload
                  entry word value (cut, completed)
        else 0) = coefficient index * density * law history) →
      own * classes * annotatedForcedBlockWeight setup values implementation operational
        sourceProfile nativeProfile who site index event payload value cut completed =
          coefficient index * density := by
  intro own classes coefficient density balanced
  rw [annotatedForcedBlockWeight, ← ENNReal.tsum_mul_left]
  calc
    _ = ∑' history : (nativeModel).InformationHistory who site.1,
        coefficient index * density * law history := tsum_congr balanced
    _ = coefficient index * density := by
      rw [ENNReal.tsum_mul_left, law.tsum_coe, mul_one]

end Vegas.PhaseProposalQualifiedBinding
