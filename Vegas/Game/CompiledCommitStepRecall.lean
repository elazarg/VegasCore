/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledAttemptObservation
import Vegas.Game.CompiledCommitMemory
import Vegas.Game.CompiledCommitSuccessor
import Vegas.Game.CompiledCommitHead
import Vegas.Game.RecoverySourceBoundary
import Vegas.Source.CommitRecoveryObservedClosure
import Vegas.Source.CommitRecoverySurvivingInformation
import Vegas.Source.ProtocolSuffix

/-! # Equal remembered source signals for actual physical commitment instructions -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem suffix_observe_congr
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) (who : Player) :
    ∀ first second, ProtocolState.observe who program first =
        ProtocolState.observe who program second →
      ProtocolState.observe who whole (lift first) =
        ProtocolState.observe who whole (lift second) := by
  induction origin with
  | initial => intro first second same; exact same
  | sampleTail fresh law next previous ih =>
      intro first second same
      exact ih (.inr first) (.inr second) (congrArg Sum.inr same)
  | commitTail fresh guard next previous ih =>
      intro first second same
      exact ih (.inr first) (.inr second) (congrArg Sum.inr same)
  | revealTail fresh selected unresolved next previous ih =>
      intro first second same
      exact ih (.inr first) (.inr second) (congrArg Sum.inr same)

/-- A real decoded commitment instruction preserves the full observed source
state across closure in two physical histories with equal public and focal
observations. The source entries and saved views are genuine prior induction
data; hidden foreign accepted values and original missing flags are retained. -/
private theorem decoded_commit_close_full_observed_eq
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    {Γ : SourceCtx Player L} {O : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (tail : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard tail))
    (lift : ProtocolState (.commit name owner fresh guard tail) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (.commit name owner fresh guard tail) lift)
    (first second : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (firstValid : first.BindingInvariant) (secondValid : second.BindingInvariant)
    (firstEntry secondEntry : SourceProgram.Config Player L Γ)
    (left right : CommitRecoveryState setup.program) (who : Player)
    (entry : firstEntry.view who = secondEntry.view who)
    (publicView : first.publicView = second.publicView)
    (observed : ((toEventGraph setup.program).withMode mode).playerObserve who first.config =
      ((toEventGraph setup.program).withMode mode).playerObserve who second.config)
    (firstCompleted : embedding.event ⟨0, by simp only [eventCount]; omega⟩ ∈
      first.config.cut.completed)
    (secondCompleted : embedding.event ⟨0, by simp only [eventCount]; omega⟩ ∈
      second.config.cut.completed)
    (saved : ProtocolState.observe who setup.program left.saved =
      ProtocolState.observe who setup.program right.saved)
    (excluded : left.excluded = right.excluded)
    (entryExcluded : left.entryExcluded = right.entryExcluded)
    (generation : left.generation = right.generation) :
    let block : SourceProgram.CommitPrefix Γ O
        ((name, .commitment owner payload) :: Γ) (insert name O) :=
      .commit name owner fresh guard .nil
    let leftDecoded := decodeCommitAttempt setup.program mode block tail embedding first
      firstEntry left.excluded
    let rightDecoded := decodeCommitAttempt setup.program mode block tail embedding second
      secondEntry right.excluded
    let leftRaw := left.install
      (lift (Sum.inr (ProtocolState.entry tail leftDecoded.1)), leftDecoded.2.1)
      (fun _ member => leftDecoded.2.2.excluded_subset member)
    let rightRaw := right.install
      (lift (Sum.inr (ProtocolState.entry tail rightDecoded.1)), rightDecoded.2.1)
      (fun _ member => rightDecoded.2.2.excluded_subset member)
    (ProtocolState.observe who setup.program leftRaw.close.point,
        ProtocolState.observe who setup.program leftRaw.close.saved, leftRaw.close.excluded,
        leftRaw.close.entryExcluded, leftRaw.close.generation) =
      (ProtocolState.observe who setup.program rightRaw.close.point,
        ProtocolState.observe who setup.program rightRaw.close.saved, rightRaw.close.excluded,
        rightRaw.close.entryExcluded, rightRaw.close.generation) := by
  intro block leftDecoded rightDecoded leftRaw rightRaw
  have firstAll : ∀ index : Fin (eventCount (block.prepend tail)), index.val < block.length →
      embedding.event index ∈ first.config.cut.completed := by
    intro index before
    have zero : index = ⟨0, by change 0 < eventCount tail + 1; omega⟩ := by
      apply Fin.ext
      change index.val = 0
      change index.val < 1 at before
      omega
    rw [zero]
    exact firstCompleted
  have secondAll : ∀ index : Fin (eventCount (block.prepend tail)), index.val < block.length →
      embedding.event index ∈ second.config.cut.completed := by
    intro index before
    have zero : index = ⟨0, by change 0 < eventCount tail + 1; omega⟩ := by
      apply Fin.ext
      change index.val = 0
      change index.val < 1 at before
      omega
    rw [zero]
    exact secondCompleted
  have decoded := decodeCommitAttempt_view_eq setup.program mode block tail embedding first second
    firstValid secondValid who firstEntry secondEntry left.excluded entry publicView observed
    firstAll secondAll
  have rawPoint : ProtocolState.observe who setup.program leftRaw.point =
      ProtocolState.observe who setup.program rightRaw.point := by
    apply suffix_observe_congr origin who
    change Sum.inr (ProtocolState.observe who tail (ProtocolState.entry tail leftDecoded.1)) =
      Sum.inr (ProtocolState.observe who tail (ProtocolState.entry tail rightDecoded.1))
    have localView : leftDecoded.1.view who = rightDecoded.1.view who := by
      exact decoded.1.trans (congrArg (fun owners =>
        (decodeCommitAttempt setup.program mode block tail embedding second secondEntry
          owners).1.view who) excluded)
    exact congrArg Sum.inr
      (ProtocolState.observe_entry_congr who tail _ _ localView)
  apply CommitRecoveryState.close_observed_congr who leftRaw rightRaw rawPoint saved
  · change leftDecoded.2.1 = rightDecoded.2.1
    exact decoded.2.trans (congrArg (fun owners =>
      (decodeCommitAttempt setup.program mode block tail embedding second secondEntry owners).2.1)
        excluded)
  · exact entryExcluded
  · exact generation

/-- Equal current typed cells suffice for the actual closed semantic observations.
Both old private words remain arbitrary, and the original retry dispatcher is used. -/
private theorem decoded_commit_close_semantic_observed_eq
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    {Γ : SourceCtx Player L} {O : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (tail : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard tail))
    (lift : ProtocolState (.commit name owner fresh guard tail) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (.commit name owner fresh guard tail) lift)
    (first second : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (firstValid : first.BindingInvariant) (secondValid : second.BindingInvariant)
    (firstEntry secondEntry : SourceProgram.Config Player L Γ)
    (left right : CommitRecoveryState setup.program) (who : Player)
    (entry : (firstEntry.view who).1 = (secondEntry.view who).1)
    (publicView : first.publicView = second.publicView)
    (observed : ((toEventGraph setup.program).withMode mode).playerObserve who first.config =
      ((toEventGraph setup.program).withMode mode).playerObserve who second.config)
    (firstCompleted : embedding.event ⟨0, by simp only [eventCount]; omega⟩ ∈
      first.config.cut.completed)
    (secondCompleted : embedding.event ⟨0, by simp only [eventCount]; omega⟩ ∈
      second.config.cut.completed)
    (saved : ProtocolView.eraseHistory who setup.program
        (ProtocolState.observe who setup.program left.saved) =
      ProtocolView.eraseHistory who setup.program
        (ProtocolState.observe who setup.program right.saved))
    (excluded : left.excluded = right.excluded)
    (entryExcluded : left.entryExcluded = right.entryExcluded)
    (generation : left.generation = right.generation) :
    let block : SourceProgram.CommitPrefix Γ O
        ((name, .commitment owner payload) :: Γ) (insert name O) :=
      .commit name owner fresh guard .nil
    let leftDecoded := decodeCommitAttempt setup.program mode block tail embedding first
      firstEntry left.excluded
    let rightDecoded := decodeCommitAttempt setup.program mode block tail embedding second
      secondEntry right.excluded
    let leftRaw := left.install
      (lift (Sum.inr (ProtocolState.entry tail leftDecoded.1)), leftDecoded.2.1)
      (fun _ member => leftDecoded.2.2.excluded_subset member)
    let rightRaw := right.install
      (lift (Sum.inr (ProtocolState.entry tail rightDecoded.1)), rightDecoded.2.1)
      (fun _ member => rightDecoded.2.2.excluded_subset member)
    (ProtocolView.eraseHistory who setup.program
        (ProtocolState.observe who setup.program leftRaw.close.point),
        ProtocolView.eraseHistory who setup.program
          (ProtocolState.observe who setup.program leftRaw.close.saved), leftRaw.close.excluded,
        leftRaw.close.entryExcluded, leftRaw.close.generation) =
      (ProtocolView.eraseHistory who setup.program
        (ProtocolState.observe who setup.program rightRaw.close.point),
        ProtocolView.eraseHistory who setup.program
          (ProtocolState.observe who setup.program rightRaw.close.saved), rightRaw.close.excluded,
        rightRaw.close.entryExcluded, rightRaw.close.generation) := by
  intro block leftDecoded rightDecoded leftRaw rightRaw
  let firstClean := {firstEntry with history := fun _ => []}
  let secondClean := {secondEntry with history := fun _ => []}
  have entryClean : firstClean.view who = secondClean.view who := Prod.ext entry rfl
  have savedClean : ProtocolState.observe who setup.program left.eraseHistory.saved =
      ProtocolState.observe who setup.program right.eraseHistory.saved := by
    simpa only [CommitRecoveryState.eraseHistory, ProtocolView.eraseHistory_observe] using saved
  have closed := decoded_commit_close_full_observed_eq setup mode fresh guard tail embedding lift
    origin first second firstValid secondValid firstClean secondClean left.eraseHistory
    right.eraseHistory who entryClean publicView observed firstCompleted secondCompleted
    savedClean excluded entryExcluded generation
  have firstMemory := decodeCommitAttempt_install_eraseHistory setup.program mode block tail
    embedding origin first firstEntry left
  have secondMemory := decodeCommitAttempt_install_eraseHistory setup.program mode block tail
    embedding origin second secondEntry right
  change leftRaw.close.eraseHistory = _ at firstMemory
  change rightRaw.close.eraseHistory = _ at secondMemory
  let observation := fun state : CommitRecoveryState setup.program =>
    (ProtocolState.observe who setup.program state.point,
      ProtocolState.observe who setup.program state.saved, state.excluded,
      state.entryExcluded, state.generation)
  have reduced := congrArg (fun item =>
    (ProtocolView.eraseHistory who setup.program item.1,
      ProtocolView.eraseHistory who setup.program item.2.1, item.2.2.1,
      item.2.2.2.1, item.2.2.2.2)) closed
  have same : observation leftRaw.close.eraseHistory =
      observation rightRaw.close.eraseHistory := by
    rw [firstMemory, secondMemory]
    simpa only [observation, CommitRecoveryState.eraseHistory,
      ProtocolView.eraseHistory_observe, block, CommitPrefix.liftPoint,
      firstClean, secondClean] using reduced
  simpa only [observation, CommitRecoveryState.eraseHistory,
    ProtocolView.eraseHistory_observe] using same

/-- The actual closed decoder compares either full remembered views or the
same current typed fields with old remembered words erased. -/
theorem decoded_commit_close_observed_eq
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    {Γ : SourceCtx Player L} {O : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (tail : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard tail))
    (lift : ProtocolState (.commit name owner fresh guard tail) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (.commit name owner fresh guard tail) lift)
    (first second : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (firstValid : first.BindingInvariant) (secondValid : second.BindingInvariant)
    (firstEntry secondEntry : SourceProgram.Config Player L Γ)
    (left right : CommitRecoveryState setup.program) (who : Player)
    (remember : Bool)
    (entry : DecisionView.historyProjection remember (firstEntry.view who) =
      DecisionView.historyProjection remember (secondEntry.view who))
    (publicView : first.publicView = second.publicView)
    (observed : ((toEventGraph setup.program).withMode mode).playerObserve who first.config =
      ((toEventGraph setup.program).withMode mode).playerObserve who second.config)
    (firstCompleted : embedding.event ⟨0, by simp only [eventCount]; omega⟩ ∈
      first.config.cut.completed)
    (secondCompleted : embedding.event ⟨0, by simp only [eventCount]; omega⟩ ∈
      second.config.cut.completed)
    (saved : ProtocolView.historyProjection who setup.program remember
        (ProtocolState.observe who setup.program left.saved) =
      ProtocolView.historyProjection who setup.program remember
        (ProtocolState.observe who setup.program right.saved))
    (excluded : left.excluded = right.excluded)
    (entryExcluded : left.entryExcluded = right.entryExcluded)
    (generation : left.generation = right.generation) :
    let block : SourceProgram.CommitPrefix Γ O
        ((name, .commitment owner payload) :: Γ) (insert name O) :=
      .commit name owner fresh guard .nil
    let leftDecoded := decodeCommitAttempt setup.program mode block tail embedding first
      firstEntry left.excluded
    let rightDecoded := decodeCommitAttempt setup.program mode block tail embedding second
      secondEntry right.excluded
    let leftRaw := left.install
      (lift (Sum.inr (ProtocolState.entry tail leftDecoded.1)), leftDecoded.2.1)
      (fun _ member => leftDecoded.2.2.excluded_subset member)
    let rightRaw := right.install
      (lift (Sum.inr (ProtocolState.entry tail rightDecoded.1)), rightDecoded.2.1)
      (fun _ member => rightDecoded.2.2.excluded_subset member)
    (ProtocolView.historyProjection who setup.program remember
          (ProtocolState.observe who setup.program leftRaw.close.point),
        ProtocolView.historyProjection who setup.program remember
          (ProtocolState.observe who setup.program leftRaw.close.saved), leftRaw.close.excluded,
        leftRaw.close.entryExcluded, leftRaw.close.generation) =
      (ProtocolView.historyProjection who setup.program remember
          (ProtocolState.observe who setup.program rightRaw.close.point),
        ProtocolView.historyProjection who setup.program remember
          (ProtocolState.observe who setup.program rightRaw.close.saved), rightRaw.close.excluded,
        rightRaw.close.entryExcluded, rightRaw.close.generation) := by
  cases remember with
  | true =>
      exact decoded_commit_close_full_observed_eq setup mode fresh guard tail embedding
        lift origin first second firstValid secondValid firstEntry secondEntry left right who
        entry publicView observed firstCompleted secondCompleted saved excluded entryExcluded
        generation
  | false =>
      have cells := congrArg (fun view : DecisionView who Γ => view.1) entry
      exact decoded_commit_close_semantic_observed_eq setup mode fresh guard tail embedding
        lift origin first second firstValid secondValid firstEntry secondEntry left right who
        cells publicView observed firstCompleted secondCompleted saved
        excluded entryExcluded generation

/-- Two actual physical binding decoders extend their genuine initialized
source histories with equal newly produced signals under any observation of prior recall.
The unchanged current typed observations are retained separately. This constructs
the legal source steps and compares their actual closed images; no next source
information equality or counterpart trace is supplied. -/
theorem decoded_commit_source_traces
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    {Γ : SourceCtx Player L} {O : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (tail : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard tail))
    (lift : ProtocolState (.commit name owner fresh guard tail) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (.commit name owner fresh guard tail) lift)
    (first second : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (firstValid : first.BindingInvariant) (secondValid : second.BindingInvariant)
    (firstEntry secondEntry : SourceProgram.Config Player L Γ)
    (left right : CommitRecoveryState setup.program) (who : Player)
    (remember : Bool)
    {Observation : Type*}
    (observe : setup.ProtocolView who × (Finset Player × Nat × Nat) → Observation)
    (entry : DecisionView.historyProjection remember (firstEntry.view who) =
      DecisionView.historyProjection remember (secondEntry.view who))
    (publicView : first.publicView = second.publicView)
    (observed : ((toEventGraph setup.program).withMode mode).playerObserve who first.config =
      ((toEventGraph setup.program).withMode mode).playerObserve who second.config)
    (firstCompleted : embedding.event ⟨0, by simp only [eventCount]; omega⟩ ∈
      first.config.cut.completed)
    (secondCompleted : embedding.event ⟨0, by simp only [eventCount]; omega⟩ ∈
      second.config.cut.completed)
    (saved : ProtocolView.historyProjection who setup.program remember
        (ProtocolState.observe who setup.program left.saved) =
      ProtocolView.historyProjection who setup.program remember
        (ProtocolState.observe who setup.program right.saved))
    (excluded : left.excluded = right.excluded)
    (entryExcluded : left.entryExcluded = right.entryExcluded)
    (generation : left.generation = right.generation)
    (firstAtEntry : left.point = lift (Sum.inl firstEntry))
    (secondAtEntry : right.point = lift (Sum.inl secondEntry))
    (ranks : ∀ point, ProtocolState.remaining setup.program (lift point) =
      ProtocolState.remaining (.commit name owner fresh guard tail) point)
    (actors : ∀ point, ProtocolState.actor setup.program (lift point) =
      ProtocolState.actor (.commit name owner fresh guard tail) point)
    (menus : ∀ point player, ProtocolView.recoveryAvailable player setup.program
      (ProtocolState.observe player setup.program (lift point)) =
      ProtocolView.recoveryAvailable player (.commit name owner fresh guard tail)
        (ProtocolState.observe player (.commit name owner fresh guard tail) point))
    (steps : ∀ point owners joint, ProtocolState.recoveryStep setup.program (lift point) owners
        joint =
      (ProtocolState.recoveryStep (.commit name owner fresh guard tail) point owners joint).map
        (fun result => (lift result.1, result.2)))
    (firstTrace : setup.commitRecoveryProtocol.Trace (some left))
    (secondTrace : setup.commitRecoveryProtocol.Trace (some right))
    (prior : setup.commitRecoveryProjectedRecall who remember observe
        (setup.commitRecoverySignals.infoOf who firstTrace) =
      setup.commitRecoveryProjectedRecall who remember observe
        (setup.commitRecoverySignals.infoOf who secondTrace)) :
    let block : SourceProgram.CommitPrefix Γ O
        ((name, .commitment owner payload) :: Γ) (insert name O) :=
      .commit name owner fresh guard .nil
    let leftDecoded := decodeCommitAttempt setup.program mode block tail embedding first
      firstEntry left.excluded
    let rightDecoded := decodeCommitAttempt setup.program mode block tail embedding second
      secondEntry right.excluded
    let leftRaw := left.install
      (lift (Sum.inr (ProtocolState.entry tail leftDecoded.1)), leftDecoded.2.1)
      (fun _ member => leftDecoded.2.2.excluded_subset member)
    let rightRaw := right.install
      (lift (Sum.inr (ProtocolState.entry tail rightDecoded.1)), rightDecoded.2.1)
      (fun _ member => rightDecoded.2.2.excluded_subset member)
    ∃ (leftTrace : setup.commitRecoveryProtocol.Trace (some leftRaw.close))
      (rightTrace : setup.commitRecoveryProtocol.Trace (some rightRaw.close)),
      ∃ (leftFuel rightFuel : Nat),
      setup.commitRecoveryProtocol.ReachesWithin leftFuel
        ⟨some left, firstTrace⟩ ⟨some leftRaw.close, leftTrace⟩ ∧
      setup.commitRecoveryProtocol.ReachesWithin rightFuel
        ⟨some right, secondTrace⟩ ⟨some rightRaw.close, rightTrace⟩ ∧
      setup.commitRecoveryHistorySignal who remember
          (setup.commitRecoverySignals.infoOf who leftTrace).1 =
        setup.commitRecoveryHistorySignal who remember
          (setup.commitRecoverySignals.infoOf who rightTrace).1 ∧
      setup.commitRecoveryProjectedRecall who remember observe
          (setup.commitRecoverySignals.infoOf who leftTrace) =
        setup.commitRecoveryProjectedRecall who remember observe
          (setup.commitRecoverySignals.infoOf who rightTrace) ∧
      setup.recoveryJointRecall leftTrace = leftDecoded.2.2.joints.reverse ++
        setup.recoveryJointRecall firstTrace ∧
      setup.recoveryJointRecall rightTrace = rightDecoded.2.2.joints.reverse ++
        setup.recoveryJointRecall secondTrace := by
  intro block leftDecoded rightDecoded leftRaw rightRaw
  let initial := setup.initialConfig setup.initialLaw.support_nonempty.choose
  obtain ⟨firstJoint, firstLegal, firstReached, firstJointExact⟩ :=
    decoded_commit_successor setup.program initial
    mode fresh guard tail embedding first firstEntry left lift firstAtEntry ranks actors menus
    steps
  obtain ⟨secondJoint, secondLegal, secondReached, secondJointExact⟩ :=
    decoded_commit_successor setup.program initial
    mode fresh guard tail embedding second secondEntry right lift secondAtEntry ranks actors menus
    steps
  let leftTrace : setup.commitRecoveryProtocol.Trace (some leftRaw.close) :=
    firstTrace.extend firstJoint firstLegal
      ((PMF.mem_support_map_iff _ _ _).mpr ⟨leftRaw.close, firstReached, rfl⟩)
  let rightTrace : setup.commitRecoveryProtocol.Trace (some rightRaw.close) :=
    secondTrace.extend secondJoint secondLegal
      ((PMF.mem_support_map_iff _ _ _).mpr ⟨rightRaw.close, secondReached, rfl⟩)
  have closed := decoded_commit_close_observed_eq setup mode fresh guard tail embedding lift origin
    first second firstValid secondValid firstEntry secondEntry left right who remember entry
    publicView
    observed firstCompleted secondCompleted saved excluded entryExcluded generation
  have pointEq := congrArg Prod.fst closed
  have savedEq := congrArg (fun item => item.2.1) closed
  have excludedEq := congrArg (fun item => item.2.2.1) closed
  have generationEq := congrArg (fun item => item.2.2.2.2) closed
  change ProtocolView.historyProjection who setup.program remember
      (ProtocolState.observe who setup.program leftRaw.close.point) =
    ProtocolView.historyProjection who setup.program remember
      (ProtocolState.observe who setup.program rightRaw.close.point) at pointEq
  change ProtocolView.historyProjection who setup.program remember
      (ProtocolState.observe who setup.program leftRaw.close.saved) =
    ProtocolView.historyProjection who setup.program remember
      (ProtocolState.observe who setup.program rightRaw.close.saved) at savedEq
  change leftRaw.close.excluded = rightRaw.close.excluded at excludedEq
  change leftRaw.close.generation = rightRaw.close.generation at generationEq
  have firstCount := ProtocolView.position_add_remaining who setup.program leftRaw.close.saved
  have secondCount := ProtocolView.position_add_remaining who setup.program rightRaw.close.saved
  have positions := congrArg (ProtocolView.position who setup.program) savedEq
  simp only [ProtocolView.position_historyProjection] at positions
  have remainingEq : ProtocolState.remaining setup.program leftRaw.close.saved =
      ProtocolState.remaining setup.program rightRaw.close.saved := by omega
  have privateEq := congrArg some pointEq
  have publicEq : setup.commitRecoveryPublic (some leftRaw.close) =
      setup.commitRecoveryPublic (some rightRaw.close) := by
    change (leftRaw.close.excluded, leftRaw.close.generation,
      instructionCount setup.program - ProtocolState.remaining setup.program leftRaw.close.saved) =
      (rightRaw.close.excluded, rightRaw.close.generation,
        instructionCount setup.program -
          ProtocolState.remaining setup.program rightRaw.close.saved)
    rw [excludedEq, generationEq, remainingEq]
  have current : setup.commitRecoveryHistorySignal who remember
      (setup.commitRecoveryPrivate who (some leftRaw.close),
        setup.commitRecoveryPublic (some leftRaw.close)) =
    setup.commitRecoveryHistorySignal who remember
      (setup.commitRecoveryPrivate who (some rightRaw.close),
        setup.commitRecoveryPublic (some rightRaw.close)) := Prod.ext privateEq publicEq
  refine ⟨leftTrace, rightTrace, 1, 1,
    .step firstJoint firstLegal _ (.refl 0 _),
    .step secondJoint secondLegal _ (.refl 0 _), current, ?_, ?_, ?_⟩
  · let observation := observe ∘ setup.commitRecoveryHistorySignal who remember
    change (observation (setup.commitRecoveryPrivate who (some leftRaw.close),
        setup.commitRecoveryPublic (some leftRaw.close)),
          observation (setup.commitRecoverySignals.infoOf who firstTrace).1 ::
            (setup.commitRecoverySignals.infoOf who firstTrace).2.map observation) =
      (observation (setup.commitRecoveryPrivate who (some rightRaw.close),
        setup.commitRecoveryPublic (some rightRaw.close)),
          observation (setup.commitRecoverySignals.infoOf who secondTrace).1 ::
            (setup.commitRecoverySignals.infoOf who secondTrace).2.map observation)
    exact Prod.ext (congrArg observe current)
      (congrArg₂ List.cons (congrArg Prod.fst prior) (congrArg Prod.snd prior))
  · have word := decodeCommitAttempt_head_joints setup.program mode fresh guard tail embedding
      first firstEntry left
    change firstJoint :: setup.recoveryJointRecall firstTrace = _
    rw [word, List.reverse_singleton, List.singleton_append, firstJointExact]
  · have word := decodeCommitAttempt_head_joints setup.program mode fresh guard tail embedding
      second secondEntry right
    change secondJoint :: setup.recoveryJointRecall secondTrace = _
    rw [word, List.reverse_singleton, List.singleton_append, secondJointExact]

end Vegas
