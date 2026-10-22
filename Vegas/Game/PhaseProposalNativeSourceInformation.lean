/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryPublicClassConstancy
import Vegas.Game.PhaseProposalSourceFiber
import Vegas.Game.ProposalRecoveryArchivePublicHistory
import Vegas.Game.PhaseProposalInstalledSourceBlock
import Vegas.Compile.CommitPrefixReadStability
import Vegas.Source.CommitAttemptRanks
import Vegas.Source.ProposalRecoveryDisclosure
import Vegas.Source.ProposalRecoveryVirtualLift
import Vegas.Source.CommitPrefixPointAppend
import Vegas.Compile.CommitPrefixCompletionSnoc
import Vegas.Game.PhaseSurvivingSourceView
import Vegas.Game.RecoveryFixedCommitSelector
import Vegas.Game.PhaseCountServiceForeignWord
import Vegas.Source.CommitRecoveryNoMissQuery
import Vegas.Source.ProposalRecoveryCommitWindow
import Vegas.Source.CommitRecoveryPublicObservation
import Vegas.Game.PhaseCommitmentProposalArchive
import Vegas.Source.CommitRecoveryInitialInputs
import Vegas.Pending.PhaseValueSwap
import Vegas.Pending.ValueSwapPairs
import Vegas.Pending.PhaseArchiveOrder
import Vegas.Game.ConcurrentRawSequentialPreservation
import Vegas.Game.PhaseProposalHistory
import Vegas.Game.ReservedEpochBindingAliases
import Vegas.Game.PhaseBindingRecallWord
import Vegas.Source.CommitPrefixWordHistory
import Vegas.Source.CommitPrefixProduct
import Vegas.Game.PhaseCommitWordSourceView
import Interaction.ReactiveEmissionOrder
import Vegas.Pending.PhaseProposalPacketLaw
import Vegas.Game.PhaseProposalGeneratedPreparation
import Vegas.Game.PhaseProposalGenuineReference
import Vegas.Pending.PhaseProposalLostRecallReplay
import Vegas.Source.CommitRecoveryAttemptExit
import Interaction.ReactiveReceiptBoundary
import Vegas.Source.IntendedPrefixSwap
import Vegas.Pending.PhaseProposalLostBindingClosure
import Vegas.Game.ServiceWithheldForfeit
import Vegas.Source.ProposalRecoveryPrefixLift
import Vegas.Game.PhaseProposalSourceUsability
import GameTheoryExtensions.Protocol.OwnPlayPrefix
import Vegas.Game.PhaseProposalCommitWord
import Vegas.Source.ProposalRecoveryPreparationMenuInverse
import Vegas.Game.RecoverySameAttemptWitness
import Vegas.Game.PhaseProposalOrdinaryBindingCheckpoint
import Vegas.Game.PhaseProposalOwnBindingFailure
import Vegas.Game.PhaseProposalBindingPhaseLaw
import Vegas.Game.PhaseProposalBindingKernel
import Vegas.Game.PhaseProposalQueryDomain
import Vegas.Game.PhaseProposalSavedBindingValues

/-! # Complete source information under foreign disclosure refinements

The source histories remain genuine histories of the original protocol.
Foreign publication causes can differ while their public results and locked
proposal deltas agree. The observer's literal labeled choices are retained.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

end Vegas.SourceProgram.Setup

namespace Vegas

open SourceProgram SourceProgram.Setup EventGraph EventGraphRuntime Interaction
  GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
theorem fillCommitPrefix_eq_withoutMisses
    {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId} (block : SourceProgram.CommitPrefix Γ O Δ P) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
        (block.prepend suffix)) (refs : ContextRefs (graphLayout whole) Γ)
      (store : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ)
      (excluded : Finset Player) (finished : SourceProgram.Config Player L Δ)
      (after : Finset Player) (attempt : block.Attempt entry excluded finished after)
      (replacement : SourceProgram.Config Player L Γ),
      (commitBlockRefs whole block suffix embedding refs).Agrees finished.state store →
      fillCommitPrefix whole block suffix embedding store replacement =
        attempt.withoutMisses ∅ replacement := by
  induction block with
  | nil =>
      intro suffix embedding refs store entry excluded finished after attempt replacement _agree
      cases attempt
      rfl
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      intro suffix embedding refs store entry excluded finished after attempt replacement agree
      let zero : Fin (eventCount
          ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix)) :=
        ⟨0, by simp only [SourceProgram.CommitPrefix.prepend, eventCount]; omega⟩
      let field : FieldRef (graphLayout whole) (.binding owner payload) := by
        simpa only [zero, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
          Fin.cases_zero]
          using embedding.ref zero
      let laterEmbedding := embedding.tail (rest.prepend suffix)
        (by simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      let laterRefs := refs.cons (name := name) (cell := .commitment owner payload) field
      cases attempt with
      | active _active choice _missed _valid later =>
          have middle : laterRefs.Agrees
              (commitSuccessor name guard entry choice).state store :=
            commitBlockRefs_agrees_entry whole rest suffix laterEmbedding laterRefs
              store (commitSuccessor name guard entry choice) _ finished after later agree
          have stored := middle (.here (x := name) (τ := CellTy.commitment owner payload))
          change field.get? store = some choice at stored
          change fillCommitPrefix whole rest suffix laterEmbedding store
              (commitSuccessor name guard replacement ((field.get? store).getD .failure)) =
            later.withoutMisses ∅ (commitSuccessor name guard replacement choice)
          rw [stored, Option.getD_some]
          exact ih suffix laterEmbedding laterRefs store _ _ finished after later _ agree
      | excluded _inactive later =>
          have middle : laterRefs.Agrees
              (automaticCommit name owner payload entry).state store :=
            commitBlockRefs_agrees_entry whole rest suffix laterEmbedding laterRefs
              store (automaticCommit name owner payload entry) _ finished after later agree
          have stored := middle (.here (x := name) (τ := CellTy.commitment owner payload))
          change field.get? store = some .failure at stored
          simp only [SourceProgram.CommitPrefix.Attempt.withoutMisses, Finset.notMem_empty,
            ↓reduceIte]
          change fillCommitPrefix whole rest suffix laterEmbedding store
              (commitSuccessor name guard replacement ((field.get? store).getD .failure)) =
            later.withoutMisses ∅ (commitSuccessor name guard replacement .failure)
          rw [stored, Option.getD_some]
          exact ih suffix laterEmbedding laterRefs store _ _ finished after later _ agree

omit [Fintype Player] in
theorem fillCommitPrefix_view_of_attempt_agrees
    {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId} (block : SourceProgram.CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (refs : ContextRefs (graphLayout whole) Γ)
    (store : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ)
    (excluded : Finset Player) (finished : SourceProgram.Config Player L Δ)
    (after : Finset Player) (attempt : block.Attempt entry excluded finished after)
    (agree : (commitBlockRefs whole block suffix embedding refs).Agrees finished.state store)
    (who : Player) (survives : who ∉ after) :
    finished.view who = (fillCommitPrefix whole block suffix embedding store entry).view who := by
  have view := attempt.withoutMisses_surviving_view ∅ entry who rfl survives
  rw [← fillCommitPrefix_eq_withoutMisses whole block suffix embedding refs store entry excluded
    finished after attempt entry agree] at view
  exact view

omit [Fintype Player] in
private theorem commitPrefix_observe_lift_of_view
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (who : Player) (left right : SourceProgram.Config Player L Δ)
    (same : left.view who = right.view who) :
    SourceProgram.ProtocolState.observe who (block.prepend suffix)
        (block.liftPoint suffix (SourceProgram.ProtocolState.entry suffix left)) =
      SourceProgram.ProtocolState.observe who (block.prepend suffix)
        (block.liftPoint suffix (SourceProgram.ProtocolState.entry suffix right)) := by
  induction block with
  | nil => exact SourceProgram.ProtocolState.observe_entry_congr who suffix left right same
  | commit _ _ _ _ _ ih => exact congrArg Sum.inr (ih suffix left right same)

omit [Fintype Player] in
private theorem fillCommitPrefix_rank_of_events
    {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO)
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (earlier : SourceProgram.CommitPrefix Γ O Δ P)
    (later : SourceProgram.CommitPrefix Δ P Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (full : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      ((earlier.append later).prepend suffix))
    (prefixEmbedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (earlier.prepend (later.prepend suffix)))
    (same : ∀ left right, left.val = right.val → full.event left = prefixEmbedding.event right)
    (store : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ)
    (who : Player) :
    ProtocolView.atRank who (earlier.prepend (later.prepend suffix)) earlier.length
        (SourceProgram.ProtocolState.observe who (earlier.prepend (later.prepend suffix))
          (earlier.liftPoint (later.prepend suffix)
            (later.liftPoint suffix (SourceProgram.ProtocolState.entry suffix
              (fillCommitPrefix whole (earlier.append later) suffix full store entry))))) =
      some (SourceProgram.ProtocolState.observe who (earlier.prepend (later.prepend suffix))
        (earlier.liftPoint (later.prepend suffix)
          (SourceProgram.ProtocolState.entry (later.prepend suffix)
            (fillCommitPrefix whole earlier (later.prepend suffix) prefixEmbedding store
              entry)))) := by
  induction earlier with
  | nil =>
      exact ProtocolView.atRank_zero_of_entryView who (later.prepend suffix) _ entry
        ((fillCommitPrefix_attempt whole later suffix full store entry).entryView suffix who
          (Finset.notMem_empty who))
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      let fullZero : Fin (eventCount
          (((SourceProgram.CommitPrefix.commit name owner fresh guard rest).append later).prepend
            suffix)) := ⟨0, by
        simp only [SourceProgram.CommitPrefix.append, SourceProgram.CommitPrefix.prepend,
          eventCount]; omega⟩
      let prefixZero : Fin (eventCount
          ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend
            (later.prepend suffix))) := ⟨0, by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]; omega⟩
      let fullField : FieldRef (graphLayout whole) (.binding owner payload) :=
        ⟨.inr (full.event fullZero), full.layout_eq _⟩
      let prefixField : FieldRef (graphLayout whole) (.binding owner payload) :=
        ⟨.inr (prefixEmbedding.event prefixZero), prefixEmbedding.layout_eq _⟩
      have sameField : fullField = prefixField := by
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
      have tailSame : ∀ left right, left.val = right.val →
          fullTail.event left = prefixTail.event right := by
        intro left right coordinate
        exact same (Fin.succ left) (Fin.succ right) (congrArg Nat.succ coordinate)
      have lower := ih later fullTail prefixTail tailSame
        (commitSuccessor name guard entry ((prefixField.get? store).getD .failure))
      change (ProtocolView.atRank who (rest.prepend (later.prepend suffix)) rest.length
        (SourceProgram.ProtocolState.observe who (rest.prepend (later.prepend suffix))
          (rest.liftPoint (later.prepend suffix)
            (later.liftPoint suffix (SourceProgram.ProtocolState.entry suffix
              (fillCommitPrefix whole (rest.append later) suffix fullTail store
                (commitSuccessor name guard entry
                  ((fullField.get? store).getD .failure)))))))).map Sum.inr = _
      rw [sameField, lower]
      rfl

omit [Fintype Player] in
private theorem source_rank_lift_cast
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {whole : SourceProgram Player L Γ O} {first second : SourceProgram Player L Δ P}
    (same : first = second)
    (lift : SourceProgram.ProtocolState first → SourceProgram.ProtocolState whole)
    (origin : ProtocolSuffix whole first lift) (who : Player)
    (before later : SourceProgram.ProtocolState second) (rank : Nat)
    (read : ProtocolView.atRank who second rank
        (SourceProgram.ProtocolState.observe who second later) =
      some (SourceProgram.ProtocolState.observe who second before)) :
    ProtocolView.atRank who whole
        (instructionCount whole - instructionCount second + rank)
        (SourceProgram.ProtocolState.observe who whole
          (lift (cast (congrArg SourceProgram.ProtocolState same.symm) later))) =
      some (SourceProgram.ProtocolState.observe who whole
        (lift (cast (congrArg SourceProgram.ProtocolState same.symm) before))) := by
  cases same
  exact origin.atRank_lift who before later rank read

omit [Fintype Player] in
private theorem filled_prefix_decode_cast
    {wholeΓ Γ Δ : SourceCtx Player L} {wholeO O P : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO)
    (program : SourceProgram Player L Γ O)
    (earlier : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (same : program = earlier.prepend suffix)
    (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
    (lift : SourceProgram.ProtocolState program → SourceProgram.ProtocolState whole)
    (views : ProtocolViewSuffix whole program refs embedding lift)
    (store : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ)
    (who : Player) (selected : Fin (eventCount (earlier.prepend suffix)))
    (atEnd : selected.val = earlier.length)
    (agree : refs.Agrees entry.state store)
    (available : ∀ index : Fin (eventCount (earlier.prepend suffix)),
      index.val < earlier.length → eventOwner? (earlier.prepend suffix) index = some who →
        (((cast (congrArg (OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)) same)
          embedding).ref index).get? store).isSome = true) :
    let prefixEmbedding := cast
      (congrArg (OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)) same) embedding
    let filled := fillCommitPrefix whole earlier suffix prefixEmbedding store entry
    decodeEventView? whole (ContextRefs.initial wholeΓ (outputLayout whole))
        (outputEmbedding whole).ref who (prefixEmbedding.event selected)
        ((toEventGraph whole).playerStore who store) (filled.history who) =
      some (SourceProgram.ProtocolState.observe who whole
        (lift (cast (congrArg SourceProgram.ProtocolState same.symm)
          (earlier.liftPoint suffix (SourceProgram.ProtocolState.entry suffix filled))))) := by
  subst program
  dsimp only [cast_eq]
  have observation := fillCommitPrefix_observation whole earlier suffix embedding refs store entry
    who (decodeObservation?_eq_some refs who entry.state store agree) available
  have masked := (decodeObservation?_playerStore (graph := toEventGraph whole) who
    (commitBlockRefs whole earlier suffix embedding refs) store).trans observation
  have localView := decodeEventView?_commitPrefix_entry whole earlier suffix embedding refs
    ((toEventGraph whole).playerStore who store) _ who selected atEnd masked
  rw [views.decode, localView, Option.map_some]
  exact congrArg some (views.observe who _).symm

omit [Fintype Player] in
private theorem filled_prefix_rank_readback
    {wholeΓ Γ Δ Ξ : SourceCtx Player L} {wholeO O P Q : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO)
    (block : SourceProgram.CommitPrefix Γ O Ξ Q)
    (earlier : SourceProgram.CommitPrefix Γ O Δ P)
    (later : SourceProgram.CommitPrefix Δ P Ξ Q)
    (split : earlier.append later = block) (suffix : SourceProgram Player L Ξ Q)
    (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix))
    (lift : SourceProgram.ProtocolState (block.prepend suffix) →
      SourceProgram.ProtocolState whole)
    (origin : ProtocolSuffix whole (block.prepend suffix) lift)
    (views : ProtocolViewSuffix whole (block.prepend suffix) refs embedding lift)
    (store completedStore : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ)
    (who : Player) (event : Fin (eventCount whole))
    (current : SourceProgram.ProtocolState whole)
    (agree : refs.Agrees entry.state store)
    (preserved : ∀ field value, store field = some value → completedStore field = some value)
    (rank : ProtocolView.atRank who whole event.val
      (SourceProgram.ProtocolState.observe who whole
        (lift (block.liftPoint suffix (SourceProgram.ProtocolState.entry suffix
          (fillCommitPrefix whole block suffix embedding completedStore entry))))) =
      some (SourceProgram.ProtocolState.observe who whole current)) :
    let association := (congrArg (fun block => block.prepend suffix) split).symm.trans
      (earlier.prepend_append later suffix)
    let prefixEmbedding := cast
      (congrArg (OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)) association) embedding
    ∀ (selected : Fin (eventCount (earlier.prepend (later.prepend suffix)))),
      selected.val = earlier.length → prefixEmbedding.event selected = event →
      event.val = instructionCount whole - instructionCount (earlier.prepend
        (later.prepend suffix)) + earlier.length →
      (∀ index : Fin (eventCount (earlier.prepend (later.prepend suffix))),
        index.val < earlier.length →
        eventOwner? (earlier.prepend (later.prepend suffix)) index = some who →
        ((prefixEmbedding.ref index).get? store).isSome = true) →
      decodeEventView? whole (ContextRefs.initial wholeΓ (outputLayout whole))
          (outputEmbedding whole).ref who event ((toEventGraph whole).playerStore who store)
          (SourceProgram.Config.history
            (fillCommitPrefix whole earlier (later.prepend suffix) prefixEmbedding store
              entry) who) =
        some (SourceProgram.ProtocolState.observe who whole current) := by
  cases split
  intro association prefixEmbedding selected atEnd selectedEq coordinate available
  have sourceRank := fillCommitPrefix_rank_of_events whole earlier later suffix embedding
    prefixEmbedding (fun left right same => OutputEmbedding.event_cast whole association embedding
      left right same) completedStore entry who
  have extension := fillCommitPrefix_view_of_extension whole earlier (later.prepend suffix)
    prefixEmbedding store completedStore entry who preserved available
  have pointView := commitPrefix_observe_lift_of_view earlier (later.prepend suffix) who _ _
    extension
  rw [← pointView] at sourceRank
  rw [← earlier.liftPoint_append later suffix] at sourceRank
  have wholeRank := source_rank_lift_cast association lift origin who _ _ earlier.length sourceRank
  simp only [cast_cast, cast_eq] at wholeRank
  rw [← coordinate, rank] at wholeRank
  have decoded := filled_prefix_decode_cast whole ((earlier.append later).prepend suffix)
    earlier (later.prepend suffix) association refs embedding lift views store entry who selected
    atEnd agree available
  dsimp only at decoded
  rw [selectedEq] at decoded
  exact decoded.trans wholeRank.symm

omit [Fintype Player] in
theorem source_binding_prefix_addresses
    (setup : Setup (Player := Player) (L := L)) (who : Player)
    (point : SourceProgram.ProtocolState setup.program) (excluded : Finset Player)
    (generation : Nat)
    (prior : setup.commitRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint point excluded generation)))
    (committing : SourceProgram.ProtocolState.atCommit setup.program point = true)
    (survives : who ∉ excluded)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) (kept : TracePrefix prior trace)
    (inside : trace.length + SourceProgram.ProtocolState.commitEnd setup.program point <
      prior.length + SourceProgram.ProtocolState.remaining setup.program point)
    (unchanged : (setup.commitRecoveryPublic state).1 = excluded) :
    setup.recoveryAddressWord trace = setup.recoveryAddressWord prior ++
      (List.range (trace.length - prior.length)).map (fun index =>
        (some (instructionCount setup.program -
          SourceProgram.ProtocolState.remaining setup.program point + index + 1),
          excluded, generation, instructionCount setup.program -
            SourceProgram.ProtocolState.remaining setup.program point)) := by
  induction kept with
  | refl => simp only [Nat.sub_self, List.range_zero, List.map_nil, List.append_nil]
  | @extend source target earlier retained joint legal supported ih =>
      have previousInside : earlier.length +
          SourceProgram.ProtocolState.commitEnd setup.program point < prior.length +
            SourceProgram.ProtocolState.remaining setup.program point := by
        simp only [Trace.length] at inside
        omega
      have lower := setup.commitRecovery_public_excluded_of_reaches retained.reachesWithin
      have upper := setup.commitRecovery_step_excluded_subset joint legal supported
      have previousUnchanged : (setup.commitRecoveryPublic source).1 = excluded := by
        apply Finset.Subset.antisymm
        · intro owner member
          exact unchanged ▸ upper member
        · exact lower
      have surviving : who ∉ (setup.commitRecoveryPublic target).1 := fun member =>
        survives (unchanged ▸ member)
      obtain ⟨current, _replay, endpoint, saved, _entryExcluded, currentGeneration, _rest⟩ :=
        setup.commitRecovery_noMiss_prefix_information who point excluded generation prior
          committing (earlier.extend joint legal supported) (.extend retained joint legal supported)
            inside surviving
      obtain ⟨rankCurrent, rankEndpoint, _currentCommit, _end, remaining⟩ :=
        setup.commitRecovery_prefix_inside_commit _ prior committing
          (earlier.extend joint legal supported) (.extend retained joint legal supported) inside
      have currentEq : rankCurrent = current := Option.some.inj (rankEndpoint.symm.trans endpoint)
      subst rankCurrent
      change (earlier.extend joint legal supported).length +
        SourceProgram.ProtocolState.remaining setup.program current.point =
        prior.length + SourceProgram.ProtocolState.remaining setup.program point at remaining
      have excludedEq : current.excluded = excluded := by
        simpa only [endpoint, Setup.commitRecoveryPublic] using unchanged
      have address : target.elim (none, (∅, 0, 0)) CommitRecoveryState.publicAddress =
          (some (instructionCount setup.program -
            SourceProgram.ProtocolState.remaining setup.program point +
              ((earlier.extend joint legal supported).length - prior.length)),
            excluded, generation, instructionCount setup.program -
              SourceProgram.ProtocolState.remaining setup.program point) := by
        conv_lhs => rw [endpoint]
        dsimp only [Option.elim, CommitRecoveryState.publicAddress]
        rw [saved, currentGeneration, excludedEq]
        congr 2
        have bounded := SourceProgram.ProtocolState.remaining_le_instructionCount setup.program
          point
        have length := retained.length_le
        simp only [Trace.length] at remaining ⊢
        omega
      have count : (earlier.extend joint legal supported).length - prior.length =
          (earlier.length - prior.length) + 1 := by
        have length := retained.length_le
        simp only [Trace.length]
        omega
      rw [setup.recoveryAddressWord_extend, ih previousInside previousUnchanged, address, count,
        List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
      simp only [Nat.add_assoc]

omit [Fintype Player] in
private theorem checkpoint_history_cast
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {first second : PhaseRuntimeState (serviceGraph setup mode)} (same : first = second)
    (checkpoint : RecoverySourceCheckpoint setup mode first) :
    (⟨_, (cast (congrArg (RecoverySourceCheckpoint setup mode) same) checkpoint).trace⟩ :
      setup.commitRecoveryProtocol.History) = ⟨_, checkpoint.trace⟩ := by
  cases same
  rfl

omit [Fintype Player] in
theorem initialized_checkpoint_history
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (theta : State L setup.context) (supported : theta ∈ setup.initialLaw.support) :
    (⟨_, (RecoverySourceCheckpoint.initialized setup mode plan theta supported).trace⟩ :
      setup.commitRecoveryProtocol.History) =
      ⟨_, (RecoverySourceCheckpoint.initial setup mode plan theta supported).trace⟩ :=
  checkpoint_history_cast (phaseInitial_eq_raw plan (encodeInputs theta)).symm _

omit [Fintype Player] in
private theorem initialized_lift_info_eq
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (plan : RuntimePhasePlan (serviceGraph setup mode)) (who : Player)
    (left right : State L setup.context)
    (leftSupported : left ∈ setup.initialLaw.support)
    (rightSupported : right ∈ setup.initialLaw.support)
    (leftLabels rightLabels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    (observed : sourceObserve who left = sourceObserve who right) :
    setup.proposalRecoveryModel.infoOf who (setup.proposalRecoveryLiftTrace leftLabels
        (RecoverySourceCheckpoint.initialized setup mode plan left leftSupported).trace) =
      setup.proposalRecoveryModel.infoOf who (setup.proposalRecoveryLiftTrace rightLabels
        (RecoverySourceCheckpoint.initialized setup mode plan right rightSupported).trace) := by
  have leftRaw := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    setup.proposalRecoveryModel.infoOf who (setup.proposalRecoveryLiftTrace leftLabels
      history.trace)) (initialized_checkpoint_history setup mode plan left leftSupported)
  have rightRaw := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    setup.proposalRecoveryModel.infoOf who (setup.proposalRecoveryLiftTrace rightLabels
      history.trace)) (initialized_checkpoint_history setup mode plan right rightSupported)
  rw [leftRaw, rightRaw]
  dsimp only [RecoverySourceCheckpoint.initial, Setup.proposalRecoveryLiftTrace,
    Setup.proposalRecoveryLiftJoint, Setup.proposalRecoveryModel, Setup.proposalRecoverySignals,
    InfoSignals.withOwnPlayRecall, InfoSignals.infoOf, Setup.proposalRecoveryPublic,
    Setup.proposalRecoveryProposalOf, Setup.commitRecoveryPrivate, Setup.commitRecoveryPublic,
    CommitRecoveryState.atPoint]
  simp only [Option.map_none, Option.map_some, id_eq,
    SourceProgram.ProtocolState.remaining_entry]
  have initialState : setup.commitRecoveryProtocol.init = none := rfl
  simp only [initialState, Option.bind_none]
  have entries := SourceProgram.ProtocolState.observe_entry_congr who setup.program
    (setup.initialConfig left) (setup.initialConfig right) (Prod.ext observed rfl)
  change (((some (SourceProgram.ProtocolState.observe who setup.program
        (SourceProgram.ProtocolState.entry setup.program (setup.initialConfig left))),
      (((∅ : Finset Player), 0,
        instructionCount setup.program - instructionCount setup.program), none)),
      [(none, (((∅ : Finset Player), 0, 0), none))]), []) =
    (((some (SourceProgram.ProtocolState.observe who setup.program
        (SourceProgram.ProtocolState.entry setup.program (setup.initialConfig right))),
      (((∅ : Finset Player), 0,
        instructionCount setup.program - instructionCount setup.program), none)),
      [(none, (((∅ : Finset Player), 0, 0), none))]), [])
  rw [entries]

/-- Actual initialized compiler and source-block witnesses for a canonical
source cut before an ordinary native binding. The completion key belongs
only to the current generation. Older canceled declarations remain in the
checkpoint's literal source past. All value, trace and frontier conditions
are support obligations of the native augmentation, not Bayes assumptions. -/
structure PhaseProposalCanonicalBindingCut
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (nativeTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) where
  active : control.actor = some who
  request : control.execution.application.SeedRequest who
    ⟨control.execution.application.attempt, event⟩
  unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
    PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩
  payload : L.Ty
  binding : (serviceGraph setup mode).outputLayout event = .binding who payload
  phase : RuntimePhase (serviceGraph setup mode)
  installed : control.execution.application.phases.head? = some phase
  commitment : phase.kind = .commitment
  inside : event ∈ phase.events
  entry : (phaseApplication runtime leaks).Control
  entryTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
    horizon scheduler).Trace (some entry)
  nativeRetained : TracePrefix entryTrace nativeTrace
  sameAttempt : entry.execution.application.attempt = control.execution.application.attempt
  entryInstalled : entry.execution.application.phases.head? = some phase
  entryIdle : entry.actor = none
  entryExcluded : entry.execution.application.entry.excluded =
    entry.execution.application.current.excluded
  fresh : ∀ owner, ∀ record ∈ entry.execution.recall owner,
    record.beforeView.application.2.attempt ≠ entry.execution.application.attempt
  witness : RecoverySourceWitness setup mode plan entry.execution.application
  archived : witness.checkpoint.ArchivedProposals entry.execution.network.inputs
  targetContext : SourceCtx Player L
  targetNames : Finset VarId
  block : SourceProgram.CommitPrefix witness.checkpoint.residual.context
    witness.checkpoint.residual.names targetContext targetNames
  suffix : SourceProgram Player L targetContext targetNames
  cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan entry phase block suffix
  size : block.length = phase.high - phase.low
  offset : cursor.offset = phase.low
  source : cursor.source = witness.checkpoint.source
  config : cursor.config = entry.execution.application.current.native.config
  cursorHistory : (⟨some cursor.current, cursor.trace⟩ : setup.proposalRecoveryProtocol.History) =
    ⟨_, setup.proposalRecoveryLiftTrace
      (nativeArchiveLabels setup (PhaseProposal.sourceArchive entry.execution.network.inputs))
      witness.checkpoint.trace⟩
  refs : cursor.refs = witness.checkpoint.refs
  reconstruct : block.prepend suffix = witness.checkpoint.residual.tail
  embedding : cursor.embedding = cast (congrArg (fun program => OutputEmbedding
    (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
      witness.checkpoint.embedding
  lift : ∀ point, cursor.lift point = witness.checkpoint.residual.lift
    (cast (congrArg SourceProgram.ProtocolState reconstruct) point)
  theta : State L setup.context
  thetaSupported : theta ∈ setup.initialLaw.support
  originalInputs : control.execution.application.current.native.config.inputs = encodeInputs theta
  initializer : CommitRecoveryState setup.program
  initializerTrace : setup.proposalRecoveryProtocol.Trace (some initializer)
  initialized : (⟨some initializer, initializerTrace⟩ : setup.proposalRecoveryProtocol.History) =
    ⟨_, setup.proposalRecoveryLiftTrace
      (nativeArchiveLabels setup (PhaseProposal.sourceArchive entry.execution.network.inputs))
      (RecoverySourceCheckpoint.initialized setup mode plan theta thetaSupported).trace⟩
  sourceRetained : TracePrefix initializerTrace cursor.trace
  completed : setup.proposalRecoveryProtocol.History
  key : (serviceGraph setup mode).SemanticKey
  blockResult : PhaseProposalOrdinarySourceBlockResult setup mode block suffix cursor.refs
    cursor.embedding cursor.lift cursor.source cursor.current cursor.trace (completed, key)
  sourceSupported : completed ∈ (setup.proposalRecoveryModel.runBehavioralFrom
    (setup.proposalRecoveryNormalizedTrembledProfile
      0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
    block.length ⟨some cursor.current, cursor.trace⟩).support
  graphSupported : key ∈ ((serviceGraph setup mode).canonicalContinuation
    (phaseProposalBindingPotentialProfile setup mode runtime leaks plan entry.execution phase
      values)
    cursor.config).support
  lockedStore : ∀ field value,
    control.execution.application.current.native.config.store field = some value →
      key.2.1 field = some value
  lockedEmissions : ∀ owner, owner ∉ cursor.current.excluded →
    ∀ record ∈ control.execution.recall owner,
      record.beforeView.application.2.attempt = control.execution.application.attempt →
      ∀ message, record.emitted = some message →
      ∀ (declared : (serviceGraph setup mode).EventId) (domain : L.Ty)
        (output : (serviceGraph setup mode).outputLayout declared = .binding owner domain)
        (value : L.Val domain),
      PhaseCount.event? message.payload =
        some ⟨control.execution.application.attempt, declared⟩ →
      record.action.transmission.bind PhaseProposal.bindingPreparation = some ⟨domain, value⟩ →
      (⟨.inr declared, output⟩ : FieldRef (graphLayout setup.program)
        (.binding owner domain)).get? key.2.1 = some (.success value)
  current : CommitRecoveryState setup.program
  trace : setup.proposalRecoveryProtocol.Trace (some current)
  past : TracePrefix cursor.trace trace
  future : TracePrefix trace completed.trace
  clock : trace.length = cursor.trace.length + (event.val - phase.low)
  rank : instructionCount setup.program -
      SourceProgram.ProtocolState.remaining setup.program current.point =
    event.val
  actor : SourceProgram.ProtocolState.actor setup.program current.point = some who
  atCommit : SourceProgram.ProtocolState.atCommit setup.program current.point = true
  survives : who ∉ current.excluded

namespace PhaseProposalCanonicalBindingCut

variable {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
  {runtime : EventGraphRuntime (serviceGraph setup mode)}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode))}
  {bounds : MessageBounds (serviceGraph setup mode)}
  {plan : RuntimePhasePlan (serviceGraph setup mode)}
  {values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
    PMF (setup.CommitRecoveryValueChoice owner key.1)}
  {horizon : Nat} {scheduler : (phaseApplication runtime leaks).Scheduler}
  {control : (phaseApplication runtime leaks).Control}
  {nativeTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
    horizon scheduler).Trace (some control)}
  {who : Player} {event : (serviceGraph setup mode).EventId}

/-- The arbitrary supplied interior source cut is read at its rank from the
SAME completed source history and typed Attempt. This does not select another
source path from an equal terminal store. -/
theorem final_view_rank
    (cut : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler control nativeTrace who event) :
    ∃ (finished : SourceProgram.Config Player L cut.targetContext)
      (last : CommitRecoveryState setup.program)
      (lastTrace : setup.proposalRecoveryProtocol.Trace (some last))
      (_attempt : cut.block.Attempt cut.cursor.source cut.cursor.current.excluded
        finished last.excluded),
      cut.completed = ⟨some last, lastTrace⟩ ∧
      last.point = cut.cursor.lift
        (cut.block.liftPoint cut.suffix (SourceProgram.ProtocolState.entry cut.suffix finished)) ∧
      (commitBlockRefs setup.program cut.block cut.suffix cut.cursor.embedding
        cut.cursor.refs).Agrees finished.state cut.key.2.1 ∧
      last.excluded = cut.cursor.current.excluded ∧
      ProtocolView.atRank who setup.program event.val
        (SourceProgram.ProtocolState.observe who setup.program last.point) =
          some (SourceProgram.ProtocolState.observe who setup.program cut.current.point) := by
  obtain ⟨finished, last, lastTrace, attempt, completed, point, excluded, _generation,
    _live, agrees, _semanticWord, _labeledWord⟩ := cut.blockResult
  have endpoint : cut.completed.state = some last :=
    congrArg (fun history : setup.proposalRecoveryProtocol.History => history.state) completed
  have earlier := setup.proposalRecoveryEraseTrace_prefix cut.past
  have later := setup.proposalRecoveryEraseTrace_prefix cut.future
  have lower := setup.commitRecovery_public_excluded_of_reaches earlier.reachesWithin
  have upper := setup.commitRecovery_public_excluded_of_reaches later.reachesWithin
  change cut.cursor.current.excluded ⊆ cut.current.excluded at lower
  change cut.current.excluded ⊆ (setup.commitRecoveryPublic cut.completed.state).1 at upper
  rw [endpoint] at upper
  change cut.current.excluded ⊆ last.excluded at upper
  have currentExcluded : cut.current.excluded = cut.cursor.current.excluded :=
    Finset.Subset.antisymm (by simpa only [excluded] using upper) lower
  have cursorEntry : cut.cursor.current.entryExcluded = cut.cursor.current.excluded :=
    cut.cursor.entryExcluded.trans cut.cursor.excluded.symm
  have currentEntry := (setup.commitRecovery_clean_rank_of_reaches who earlier.reachesWithin
    cut.cursor.current cut.current rfl rfl cursorEntry currentExcluded cut.survives).1
  have lastExcluded : last.excluded = cut.current.excluded :=
    excluded.trans currentExcluded.symm
  have lastSurvives : who ∉ last.excluded := fun member =>
    cut.survives (lastExcluded ▸ member)
  have rankRead := (setup.commitRecovery_clean_rank_of_reaches who later.reachesWithin
    cut.current last rfl endpoint currentEntry lastExcluded lastSurvives).2
  have position : ProtocolView.position who setup.program
      (SourceProgram.ProtocolState.observe who setup.program cut.current.point) = event.val := by
    have positional := ProtocolView.position_add_remaining who setup.program cut.current.point
    have exactRank := cut.rank
    omega
  have read := rankRead event.val (by rw [position])
  rw [← position, ProtocolView.atRank_position] at read
  exact ⟨finished, last, lastTrace, attempt, completed, point, agrees, excluded, by
    simpa only [position] using read⟩

/-- The supplied cut is the original rank projection of the completed
locked store, with the surviving owner's entire source action history.
The equality uses the SAME completed typed attempt and source suffix. -/
theorem filled_rank
    (cut : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler control nativeTrace who event) :
    ProtocolView.atRank who setup.program event.val
        (SourceProgram.ProtocolState.observe who setup.program
          (cut.cursor.lift (cut.block.liftPoint cut.suffix
            (SourceProgram.ProtocolState.entry cut.suffix
              (fillCommitPrefix setup.program cut.block cut.suffix cut.cursor.embedding
                cut.key.2.1 cut.cursor.source))))) =
      some (SourceProgram.ProtocolState.observe who setup.program cut.current.point) := by
  obtain ⟨finished, last, _lastTrace, attempt, _completed, point, agrees, excluded, rank⟩ :=
    cut.final_view_rank
  have earlier := setup.commitRecovery_public_excluded_of_reaches
    (setup.proposalRecoveryEraseTrace_prefix cut.past).reachesWithin
  change cut.cursor.current.excluded ⊆ cut.current.excluded at earlier
  have surviving : who ∉ last.excluded := fun member =>
    cut.survives (earlier (excluded ▸ member))
  have configView := fillCommitPrefix_view_of_attempt_agrees setup.program cut.block cut.suffix
    cut.cursor.embedding cut.cursor.refs cut.key.2.1 cut.cursor.source
    cut.cursor.current.excluded finished last.excluded attempt agrees who surviving
  have localView := commitPrefix_observe_lift_of_view cut.block cut.suffix who _ _ configView
  have fullView := (cut.cursor.views.observe who _).trans
    ((congrArg (cut.cursor.views.view who) localView).trans
      (cut.cursor.views.observe who _).symm)
  rw [point, fullView] at rank
  exact rank

/-- Every supported completion and its supplied interior cut have the full
source view read from this actual native callback. The retained source past
supplies all archived owned actions, including accepted canceled bindings. -/
theorem source_view
    (cut : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler control nativeTrace who event) :
    phaseSurvivingSourceView? setup mode runtime leaks who event
        (control.execution.observe (phaseApplication runtime leaks) who) =
      some (SourceProgram.ProtocolState.observe who setup.program cut.current.point) := by
  let inputs := setup.initialLaw.map encodeInputs
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let raw := menu.toRawTrace initial horizon scheduler nativeTrace
  let entryRaw := menu.toRawTrace initial horizon scheduler cut.entryTrace
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized entryRaw
  have saved := ((phase_attempt_progress_of_prefix runtime leaks menu initial initialized
    horizon scheduler cut.entry control cut.entryTrace nativeTrace cut.nativeRetained
      ordered).2.2 cut.sameAttempt).symm
  have controls := phase_attempt_metadata_of_prefix runtime leaks menu initial initialized horizon
    scheduler cut.entry control cut.entryTrace nativeTrace cut.nativeRetained ordered
      cut.sameAttempt
  have retired : control.execution.application.retired =
      cut.entry.execution.application.retired := congrArg Prod.snd controls.symm
  let cp := cut.witness.checkpoint.transfer saved
    (congrArg CommitAttemptId.generation cut.sameAttempt).symm
    (congrArg CommitAttemptId.phase cut.sameAttempt).symm
  have aligned : cp.ArchivedRecall := by
    intro owner survives
    change cut.witness.checkpoint.source.history owner = _
    rw [saved, retired]
    rw [saved] at survives
    exact cut.witness.aligned owner survives
  have exclusion := phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler raw
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler raw
  have bindingRecord := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw
  have remembered := phaseHistoryCheckpoint_history runtime leaks plan inputs horizon scheduler raw
  have archives := PhaseRuntimeState.archivesBefore_history runtime leaks plan inputs horizon
    scheduler raw
  obtain ⟨_draw, native⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler raw
  obtain ⟨remaining, installed⟩ := List.head?_eq_some_iff.mp cut.installed
  obtain ⟨selected, selectedEq, Ξ, Q, name, fresh, guard, earlier, later, size, split,
      reconstruct⟩ := cp.fixed_binding_prefix cut.block cut.suffix cut.reconstruct
    exclusion.frontier cut.phase remaining installed (by
      have size := cut.size
      have interval := (cut.phase.mem_events event).mp cut.inside
      omega)
    event cut.inside cut.request.2.2.1 who cut.payload cut.binding
  let next := SourceProgram.commit name who fresh guard (later.prepend cut.suffix)
  let prefixEmbedding := cast (congrArg (fun program => OutputEmbedding
    (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm) cp.embedding
  let chosen : Fin (eventCount (earlier.prepend next)) :=
    ⟨selected.val, by
      have counts := congrArg eventCount reconstruct
      have bounded := selected.isLt
      dsimp only [next] at *
      omega⟩
  have chosenVal : chosen.val = selected.val := rfl
  have chosenEvent : prefixEmbedding.event chosen = event := by
    have same := OutputEmbedding.event_cast setup.program reconstruct.symm cp.embedding selected
      chosen chosenVal.symm
    exact same.symm.trans selectedEq
  have acting := cut.request.2.2.2.1
  have plain : ¬ ((serviceGraph setup mode).outputLayout event).IsPublication := by
    rw [cut.binding]
    exact id
  have available := commitPrefix_owned_fields_of_ready setup mode earlier next prefixEmbedding
    control.execution.application.current.native.config who chosen (chosenVal.trans size.symm)
      (chosenEvent.symm ▸ cut.request.2.2.1) (chosenEvent.symm ▸ acting)
      (chosenEvent.symm ▸ plain)
  have positioned := exclusion.frontier.positioned
  rw [installed] at positioned
  have savedPrefix : control.execution.application.entry.native.config.cut.IsPrefix
      control.execution.application.attempt.phase := by
    simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some] using positioned.1
  have survives : who ∉ control.execution.application.entry.excluded := by
    intro member
    exact cut.request.2.2.2.2
      ((phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler raw).inherited
        member)
  have owned := cp.filled_prefix_archived_history_of_ready aligned archives fresh guard
    (later.prepend cut.suffix) earlier reconstruct survives selected size.symm
      (selectedEq.symm ▸ cut.request.2.2.1) (selectedEq.symm ▸ acting) bindingRecord.active
        native.active.reachable remembered savedPrefix
  have agreement : cut.cursor.refs.Agrees cut.cursor.source.state
      control.execution.application.current.native.config.store := by
    rw [cut.refs, cut.source]
    intro name cell member
    exact (cp.refs.get member).get?_preserved _ _ stored _ (cp.agrees member)
  have coordinate : event.val = instructionCount setup.program -
      instructionCount (earlier.prepend next) + earlier.length := by
    have offset := cp.saved_position
    rw [cp.remaining, SourceProgram.ProtocolState.remaining_entry] at offset
    have rank := cp.compiled.rankEq selected
    rw [selectedEq] at rank
    rw [reconstruct]
    omega
  have embeddingEq :
      cast (congrArg (OutputEmbedding (inputLayout setup.context) (outputLayout setup.program))
        ((congrArg (fun block => block.prepend cut.suffix) split).symm.trans
          (earlier.prepend_append (.commit name who fresh guard later) cut.suffix)))
          cut.cursor.embedding = prefixEmbedding := by
    rw [cut.embedding]
    simp only [cast_cast]
    rfl
  have decoded := filled_prefix_rank_readback setup.program cut.block earlier
    (.commit name who fresh guard later) split cut.suffix cut.cursor.refs cut.cursor.embedding
      cut.cursor.lift cut.cursor.origin cut.cursor.views
      control.execution.application.current.native.config.store cut.key.2.1 cut.cursor.source
      who event cut.current.point agreement cut.lockedStore cut.filled_rank
  dsimp only at decoded
  rw [embeddingEq, cut.source] at decoded
  have read := decoded chosen (chosenVal.trans size.symm) chosenEvent coordinate available
  change (fillCommitPrefix setup.program earlier next prefixEmbedding
    control.execution.application.current.native.config.store cut.witness.checkpoint.source).history
      who = _ at owned
  change decodeEventView? setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program).ref who event
    ((toEventGraph setup.program).playerStore who
      control.execution.application.current.native.config.store)
    ((fillCommitPrefix setup.program earlier next prefixEmbedding
      control.execution.application.current.native.config.store
      cut.witness.checkpoint.source).history who) = _ at read
  rw [owned] at read
  rw [phaseSurvivingSourceView?_observed_of_history setup mode runtime leaks plan inputs horizon
    scheduler raw who event]
  exact read

/-- The original supported source prefix retains the actual saved source
controls and the complete chronological address suffix. This applies to the
supplied interior cut rather than an independently chosen replay. -/
theorem source_control_word
    (cut : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler control nativeTrace who event) :
    cut.current.saved = cut.witness.checkpoint.residual.lift
        (SourceProgram.ProtocolState.entry cut.witness.checkpoint.residual.tail
          cut.witness.checkpoint.source) ∧
      cut.current.entryExcluded = cut.entry.execution.application.entry.excluded ∧
      cut.current.excluded = cut.entry.execution.application.entry.excluded ∧
      cut.current.generation = cut.entry.execution.application.generation ∧
      setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace cut.trace) =
        setup.recoveryAddressWord cut.witness.checkpoint.trace ++
          (List.range (event.val - cut.phase.low)).map (fun index =>
            (some (cut.entry.execution.application.attempt.phase + index + 1),
              cut.entry.execution.application.entry.excluded,
              cut.entry.execution.application.generation,
              cut.entry.execution.application.attempt.phase)) ∧
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who cut.trace) =
        PhaseProposal.sourceArchive cut.entry.execution.network.inputs := by
  let cp := cut.witness.checkpoint
  let firstPoint := cp.residual.lift
    (SourceProgram.ProtocolState.entry cp.residual.tail cp.source)
  let first := CommitRecoveryState.atPoint firstPoint
    cut.entry.execution.application.entry.excluded cut.entry.execution.application.generation
  have sourceStart : (⟨some cut.cursor.current,
        setup.proposalRecoveryEraseTrace cut.cursor.trace⟩ : setup.commitRecoveryProtocol.History) =
      ⟨some first, cp.trace⟩ := by
    have same := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
      (⟨history.state, setup.proposalRecoveryEraseTrace history.trace⟩ :
        setup.commitRecoveryProtocol.History)) cut.cursorHistory
    simpa only [setup.proposalRecoveryEraseTrace_lift] using same
  have firstEq : cut.cursor.current = first :=
    Option.some.inj (congrArg (fun history : setup.commitRecoveryProtocol.History => history.state)
      sourceStart)
  have firstPointEq : cut.cursor.current.point = firstPoint :=
    congrArg CommitRecoveryState.point firstEq
  have firstClock := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    history.trace.length) sourceStart
  simp only [setup.proposalRecoveryEraseTrace_length] at firstClock
  have path := (setup.proposalRecoveryEraseTrace_prefix cut.past).reachesWithin
  change setup.commitRecoveryProtocol.ReachesWithin _
    ⟨some cut.cursor.current, setup.proposalRecoveryEraseTrace cut.cursor.trace⟩
    ⟨some cut.current, setup.proposalRecoveryEraseTrace cut.trace⟩ at path
  rw [sourceStart] at path
  have kept := path.tracePrefix
  have interval := (cut.phase.mem_events event).mp cut.inside
  have beforeEnd : event.val - cut.phase.low < cut.block.length := by
    have size := cut.size
    omega
  have positive : 0 < cut.block.length := by omega
  have committing : SourceProgram.ProtocolState.atCommit setup.program firstPoint = true := by
    have commit := cut.cursor.savedCommit positive
    rw [firstEq] at commit
    exact commit
  have window : cut.block.length + SourceProgram.ProtocolState.commitEnd setup.program firstPoint ≤
      SourceProgram.ProtocolState.remaining setup.program firstPoint := by
    rw [← firstPointEq, cut.cursor.point, cut.cursor.origin.commitEnd_lift,
      cut.cursor.origin.remaining_lift]
    exact cut.block.length_le_commit_window cut.suffix cut.cursor.source
  have inside : (setup.proposalRecoveryEraseTrace cut.trace).length +
      SourceProgram.ProtocolState.commitEnd setup.program firstPoint <
        cp.trace.length + SourceProgram.ProtocolState.remaining setup.program firstPoint := by
    have clock := cut.clock
    rw [setup.proposalRecoveryEraseTrace_length]
    omega
  obtain ⟨_finished, last, _lastTrace, _attempt, completed, _point, _agrees, lastExcluded,
      _rank⟩ := cut.final_view_rank
  have endpoint : cut.completed.state = some last :=
    congrArg (fun history : setup.proposalRecoveryProtocol.History => history.state) completed
  have upper := setup.commitRecovery_public_excluded_of_reaches
    (setup.proposalRecoveryEraseTrace_prefix cut.future).reachesWithin
  change cut.current.excluded ⊆ (setup.commitRecoveryPublic cut.completed.state).1 at upper
  rw [endpoint] at upper
  change cut.current.excluded ⊆ last.excluded at upper
  have lower := setup.commitRecovery_public_excluded_of_reaches
    (setup.proposalRecoveryEraseTrace_prefix cut.past).reachesWithin
  change cut.cursor.current.excluded ⊆ cut.current.excluded at lower
  have excluded : cut.current.excluded = cut.entry.execution.application.entry.excluded := by
    have same : cut.current.excluded = cut.cursor.current.excluded :=
      Finset.Subset.antisymm (fun owner member => lastExcluded ▸ upper member) lower
    exact same.trans (cut.cursor.excluded.trans cut.entryExcluded.symm)
  have surviving : who ∉ cut.entry.execution.application.entry.excluded := fun member =>
    cut.survives (excluded.symm ▸ member)
  obtain ⟨current, _replay, currentEq, saved, entryExcluded, generation, _rest⟩ :=
    setup.commitRecovery_noMiss_prefix_information who firstPoint
      cut.entry.execution.application.entry.excluded cut.entry.execution.application.generation
      cp.trace committing (setup.proposalRecoveryEraseTrace cut.trace) kept inside
        (show who ∉ (setup.commitRecoveryPublic (some cut.current)).1 from cut.survives)
  have sameCurrent : current = cut.current := (Option.some.inj currentEq).symm
  subst current
  have addresses := source_binding_prefix_addresses setup who firstPoint
    cut.entry.execution.application.entry.excluded cut.entry.execution.application.generation
      cp.trace committing surviving (setup.proposalRecoveryEraseTrace cut.trace) kept inside
        excluded
  have position := cp.saved_position
  have clock : (setup.proposalRecoveryEraseTrace cut.trace).length - cp.trace.length =
      event.val - cut.phase.low := by
    have count := cut.clock
    rw [setup.proposalRecoveryEraseTrace_length]
    omega
  rw [clock, position] at addresses
  have sourceArchive := setup.proposalRecoveryArchive_eq_of_commit_window who cut.cursor.current
    cut.cursor.trace (by simpa only [firstEq, first, CommitRecoveryState.atPoint] using committing)
    cut.trace cut.past (by
      rw [firstPointEq]
      rw [setup.proposalRecoveryEraseTrace_length] at inside
      omega)
  rw [cut.cursor.proposals who (by rw [firstEq]; exact surviving)] at sourceArchive
  exact ⟨saved, entryExcluded, excluded, generation, addresses, sourceArchive⟩

/-- Full source controls, numeric public recall and proposal archive are read
from the actual native callback. Physical in-phase failures do not enter the
saved source exclusion set or its preceding public chronology. -/
theorem native_readback
    (cut : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler control nativeTrace who event) :
    setup.commitRecoveryPublic (some cut.current) =
        (control.execution.application.entry.excluded,
          control.execution.application.generation, control.execution.application.attempt.phase) ∧
      (setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace cut.trace)).map
          (setup.commitRecoveryPublicAddress who) =
        (control.execution.application.sourcePublicAddressWord plan event.val).reverse ++
          [(none, (∅, 0, 0))] ∧
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who cut.trace) =
        PhaseProposal.sourceArchive control.execution.network.inputs := by
  let inputs := setup.initialLaw.map encodeInputs
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let raw := menu.toRawTrace initial horizon scheduler nativeTrace
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized (menu.toRawTrace initial horizon scheduler cut.entryTrace)
  have saved := ((phase_attempt_progress_of_prefix runtime leaks menu initial initialized
    horizon scheduler cut.entry control cut.entryTrace nativeTrace cut.nativeRetained
      ordered).2.2 cut.sameAttempt).symm
  have metadata := phase_attempt_metadata_of_prefix runtime leaks menu initial initialized horizon
    scheduler cut.entry control cut.entryTrace nativeTrace cut.nativeRetained ordered
      cut.sameAttempt
  obtain ⟨sourceSaved, _sourceEntry, sourceExcluded, sourceGeneration, numeric, archive⟩ :=
    cut.source_control_word
  have sameGeneration : cut.entry.execution.application.generation =
      control.execution.application.generation :=
    congrArg CommitAttemptId.generation cut.sameAttempt
  have sourceControl : setup.commitRecoveryPublic (some cut.current) =
      (control.execution.application.entry.excluded, control.execution.application.generation,
        control.execution.application.attempt.phase) := by
    change (cut.current.excluded, cut.current.generation, instructionCount setup.program -
      SourceProgram.ProtocolState.remaining setup.program cut.current.saved) = _
    rw [sourceSaved, sourceExcluded, sourceGeneration, cut.witness.checkpoint.saved_position,
      saved, sameGeneration,
      ← congrArg CommitAttemptId.phase cut.sameAttempt]
  obtain ⟨entryRest, entryInstalled⟩ := List.head?_eq_some_iff.mp cut.entryInstalled
  have entryLow : cut.entry.execution.application.attempt.phase = cut.phase.low := by
    simp only [PhaseRuntimeState.attempt, entryInstalled, List.head?_cons, Option.map_some,
      Option.getD_some]
  have savedE := PhaseRuntimeState.saved_excluded_eq_public_failures cut.witness.exclusions
    cut.witness.failures cut.witness.receipts.exclusion.frontier cut.phase entryRest entryInstalled
  have records := PhaseRuntimeState.sourceRecordFailures_sourceControlRecords
    cut.entry.execution.application.retired
  unfold RuntimePhasePlan.sourceRecordFailures at records
  have nativeNumeric : setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace cut.trace) =
      cut.entry.execution.application.sourcePublicAddressWord plan event.val := by
    rw [numeric, cut.witness.chronology.addresses,
      PhaseRuntimeState.sourcePublicAddressWord_saved]
    dsimp only [PhaseRuntimeState.sourcePublicAddressWord, State.sourceFailureFootprint]
    rw [records, ← savedE, entryLow]
    rfl
  have positioned := cut.witness.receipts.exclusion.frontier.positioned
  rw [entryInstalled] at positioned
  have completed : ∀ prior : (serviceGraph setup mode).EventId,
      prior.val < cut.entry.execution.application.attempt.phase →
        prior ∈ cut.entry.execution.application.entry.native.config.cut.completed := by
    intro prior earlier
    exact (positioned.1.2 prior).mpr (entryLow ▸ earlier)
  have currentFrame := phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon
    scheduler raw
  change control.execution.application.entry.native.PublicFailureExtension
    control.execution.application.current.native at currentFrame
  rw [saved] at currentFrame
  have sameFailures : ∀ rank ≤ cut.entry.execution.application.attempt.phase,
      cut.entry.execution.application.current.native.failureOwnersBefore rank =
        control.execution.application.current.native.failureOwnersBefore rank := by
    intro rank bounded
    exact (cut.witness.failures.failureOwnersBefore_eq_below _ completed rank bounded).symm.trans
      (currentFrame.failureOwnersBefore_eq_below _ completed rank bounded)
  have publicNumeric := PhaseRuntimeState.sourcePublicAddressWord_eq_of_prefix plan
    cut.sameAttempt (congrArg Prod.snd metadata) sameFailures event.val
  have recalled := setup.commitRecovery_publicRecall_addresses who
    (setup.proposalRecoveryEraseTrace cut.trace)
  rw [nativeNumeric, publicNumeric] at recalled
  have scope : ∀ (middle : (phaseApplication runtime leaks).Control)
      (prior : (menu.protocol initial horizon scheduler).Trace (some middle)),
      TracePrefix cut.entryTrace prior → TracePrefix prior nativeTrace →
      prior.length < nativeTrace.length →
        middle.execution.application.attempt = cut.entry.execution.application.attempt := by
    intro middle prior afterEntry beforeCurrent _shorter
    have middleOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
      scheduler initialized (menu.toRawTrace initial horizon scheduler prior)
    obtain ⟨lowerGen, lowerPhase, _⟩ := phase_attempt_progress_of_prefix runtime leaks menu initial
      initialized horizon scheduler cut.entry middle cut.entryTrace prior afterEntry ordered
    obtain ⟨upperGen, upperPhase, _⟩ := phase_attempt_progress_of_prefix runtime leaks menu initial
      initialized horizon scheduler middle control prior nativeTrace beforeCurrent middleOrdered
    have generation := congrArg CommitAttemptId.generation cut.sameAttempt
    have phase := congrArg CommitAttemptId.phase cut.sameAttempt
    cases first : cut.entry.execution.application.attempt with
    | mk firstPhase firstGeneration =>
      cases second : middle.execution.application.attempt with
      | mk secondPhase secondGeneration =>
        cases third : control.execution.application.attempt with
        | mk thirdPhase thirdGeneration =>
          simp only [first, second, third] at lowerGen lowerPhase upperGen upperPhase
          simp only [first, third] at generation phase ⊢
          congr 1 <;> omega
  obtain ⟨ending, endpoint, archiveEq⟩ := PhaseProposal.phase_commitment_prefix_sourceArchive
    runtime leaks bounds plan (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon
      scheduler cut.entry cut.entryTrace cut.phase (Option.mem_def.mpr cut.entryInstalled)
        cut.commitment nativeTrace cut.nativeRetained scope
  cases Option.some.inj endpoint
  exact ⟨sourceControl, recalled, archive.trans archiveEq.symm⟩

/-- The supplied initializer is the original single setup draw, with its
literal trace length. This identifies that witness without choosing another
initial source history from the same typed endpoint. -/
theorem initializer_facts
    (cut : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler control nativeTrace who event) :
    cut.initializer = CommitRecoveryState.atPoint
        (SourceProgram.ProtocolState.entry setup.program (setup.initialConfig cut.theta)) ∅ 0 ∧
      cut.initializerTrace.length = 1 := by
  have raw := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    (⟨history.state, setup.proposalRecoveryLiftTrace
      (nativeArchiveLabels setup (PhaseProposal.sourceArchive cut.entry.execution.network.inputs))
      history.trace⟩ : setup.proposalRecoveryProtocol.History))
        (initialized_checkpoint_history setup mode plan cut.theta cut.thetaSupported)
  have initial := cut.initialized.trans raw
  have state := congrArg (fun history : setup.proposalRecoveryProtocol.History => history.state)
    initial
  have length := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
    history.trace.length) initial
  exact ⟨Option.some.inj state, length⟩

/-- All original input cells of the arbitrary supplied source prefix come
from its literal supported setup draw, even after previous canceled attempts. -/
theorem base_eq_theta
    (cut : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler control nativeTrace who event) :
    SourceProgram.ProtocolState.base setup.program cut.current.point = cut.theta := by
  have initial := cut.initializer_facts.1
  obtain ⟨current, endpoint, cells, _saved⟩ := setup.commitRecovery_base_of_prefix cut.initializer
    (setup.proposalRecoveryEraseTrace cut.initializerTrace) (by rw [initial]; rfl)
    (setup.proposalRecoveryEraseTrace cut.trace)
    (setup.proposalRecoveryEraseTrace_prefix (cut.sourceRetained.trans cut.past))
  have same : current = cut.current := (Option.some.inj endpoint).symm
  subst current
  rw [initial, CommitRecoveryState.atPoint, SourceProgram.ProtocolState.base_entry] at cells
  exact cells

end PhaseProposalCanonicalBindingCut

/-- Equal complete native information identifies the actual static binding
coordinate. The two requests are quantified separately and compared through
their genuine public request projections and owning-event uniqueness. -/
theorem PhaseProposalCanonicalBindingCut.event_eq_of_information
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {runtime : EventGraphRuntime (serviceGraph setup mode)}
    {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode))}
    {bounds : MessageBounds (serviceGraph setup mode)}
    {plan : RuntimePhasePlan (serviceGraph setup mode)}
    {values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1)}
    {horizon : Nat} {scheduler : (phaseApplication runtime leaks).Scheduler}
    {leftControl rightControl : (phaseApplication runtime leaks).Control}
    {leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some leftControl)}
    {rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some rightControl)}
    {who : Player} {leftEvent rightEvent : (serviceGraph setup mode).EventId}
    (left : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler leftControl leftTrace who leftEvent)
    (right : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler rightControl rightTrace who rightEvent)
    (same : ((PhaseCount.onePacketMenu runtime leaks bounds).information
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon scheduler).infoOf who leftTrace =
      ((PhaseCount.onePacketMenu runtime leaks bounds).information
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon scheduler).infoOf who rightTrace) : leftEvent = rightEvent := by
  let initial := (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  change (menu.signals initial horizon scheduler).infoOf who leftTrace =
    (menu.signals initial horizon scheduler).infoOf who rightTrace at same
  rw [menu.info initial horizon scheduler who leftTrace,
    menu.info initial horizon scheduler who rightTrace] at same
  simp only [ReactiveApplication.observe, left.active, right.active, ↓reduceIte] at same
  have observed := congrArg Prod.snd (Option.some.inj same)
  have publicViewEq : leftControl.execution.application.publicView =
      rightControl.execution.application.publicView :=
    congrArg (fun view => view.application.2) observed
  obtain ⟨_leftInputs, leftValid⟩ := phaseNativeInvariant_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon scheduler
    (menu.toRawTrace initial horizon scheduler leftTrace)
  obtain ⟨_rightInputs, rightValid⟩ := phaseNativeInvariant_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon scheduler
    (menu.toRawTrace initial horizon scheduler rightTrace)
  have publicRequest := (PhaseRuntimeState.requests_publicView _ leftValid who _).mpr left.request
  rw [publicViewEq] at publicRequest
  have transported := (PhaseRuntimeState.requests_publicView _ rightValid who _).mp publicRequest
  exact ((serviceGraph_revealRelaxedOrdered setup mode).ready_actor_unique
    rightControl.execution.application.current.native.config.cut transported.2.2.1
    right.request.2.2.1 transported.2.2.2.1 right.request.2.2.2.1).symm

/- Complete native information determines the entire canonical source information. -/
theorem PhaseProposalCanonicalBindingCut.info_eq_of_information
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {runtime : EventGraphRuntime (serviceGraph setup mode)}
    {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode))}
    {bounds : MessageBounds (serviceGraph setup mode)}
    {plan : RuntimePhasePlan (serviceGraph setup mode)}
    {values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1)}
    {horizon : Nat} {scheduler : (phaseApplication runtime leaks).Scheduler}
    {leftControl rightControl : (phaseApplication runtime leaks).Control}
    {leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some leftControl)}
    {rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some rightControl)}
    {who : Player} {leftEvent rightEvent : (serviceGraph setup mode).EventId}
    (left : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler leftControl leftTrace who leftEvent)
    (right : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
      horizon scheduler rightControl rightTrace who rightEvent)
    (complete : leaks = MessageNetwork.completePendingObservation)
    (same : ((PhaseCount.onePacketMenu runtime leaks bounds).information
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon scheduler).infoOf who leftTrace =
      ((PhaseCount.onePacketMenu runtime leaks bounds).information
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon scheduler).infoOf who rightTrace) :
    setup.proposalRecoveryModel.infoOf who left.trace =
      setup.proposalRecoveryModel.infoOf who right.trace := by
  have events := left.event_eq_of_information right same
  cases events
  let inputs := setup.initialLaw.map encodeInputs
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let leftRaw := menu.toRawTrace initial horizon scheduler leftTrace
  let rightRaw := menu.toRawTrace initial horizon scheduler rightTrace
  have nativeInfo := same
  change (menu.signals initial horizon scheduler).infoOf who leftTrace =
    (menu.signals initial horizon scheduler).infoOf who rightTrace at nativeInfo
  rw [menu.info initial horizon scheduler who leftTrace,
    menu.info initial horizon scheduler who rightTrace] at nativeInfo
  simp only [ReactiveApplication.observe, left.active, right.active, ↓reduceIte] at nativeInfo
  have native := Option.some.inj nativeInfo
  have observed := congrArg Prod.snd native
  have publicViewEq : leftControl.execution.application.publicView =
      rightControl.execution.application.publicView :=
    congrArg (fun view => view.application.2) observed
  have views : SourceProgram.ProtocolState.observe who setup.program left.current.point =
      SourceProgram.ProtocolState.observe who setup.program right.current.point := by
    have decoded := congrArg (phaseSurvivingSourceView? setup mode runtime leaks who leftEvent)
      observed
    rw [left.source_view, right.source_view] at decoded
    exact Option.some.inj decoded
  have savedExclusions := phase_saved_excluded_eq_of_publicView_eq runtime leaks plan inputs
    horizon scheduler leftRaw rightRaw (by
      intro empty
      have installed := left.installed
      rw [empty] at installed
      cases installed) (by
      intro empty
      have installed := right.installed
      rw [empty] at installed
      cases installed) publicViewEq
  have sameGeneration : leftControl.execution.application.generation =
      rightControl.execution.application.generation :=
    congrArg (fun view => view.attempt.generation) publicViewEq
  have samePhase : leftControl.execution.application.attempt.phase =
      rightControl.execution.application.attempt.phase :=
    congrArg (fun view => view.attempt.phase) publicViewEq
  have leftRead := left.native_readback
  have rightRead := right.native_readback
  have controls : setup.commitRecoveryPublic (some left.current) =
      setup.commitRecoveryPublic (some right.current) := by
    rw [leftRead.1, rightRead.1, savedExclusions, sameGeneration, samePhase]
  have numbers : (setup.attemptPublicRecall who
        (setup.proposalRecoveryEraseTrace left.trace)).map
        (setup.commitRecoveryPublicAddress who) =
      (setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace right.trace)).map
        (setup.commitRecoveryPublicAddress who) := by
    rw [leftRead.2.1, rightRead.2.1,
      PhaseRuntimeState.sourcePublicAddressWord_congr plan publicViewEq]
  have erased : setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace left.trace)) =
      setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace right.trace)) := by
    rw [setup.commitRecovery_erasedInformation_read who left.current
        (setup.proposalRecoveryEraseTrace left.trace) left.survives,
      setup.commitRecovery_erasedInformation_read who right.current
        (setup.proposalRecoveryEraseTrace right.trace) right.survives,
      views, controls, numbers]
  have proposals : setup.proposalRecoveryArchive who
        (setup.proposalRecoveryModel.infoOf who left.trace) =
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who right.trace) := by
    rw [leftRead.2.2, rightRead.2.2]
    exact PhaseProposal.sourceArchive_eq_of_completeInput runtime leaks complete initial horizon
      scheduler scheduler leftControl rightControl leftRaw rightRaw who left.active right.active
        (congrArg Prod.fst native) observed
  have original := SourceProgram.ProtocolState.sourceObserve_base_eq_of_observe_eq who
    setup.program left.current.point right.current.point views
  rw [left.base_eq_theta, right.base_eq_theta] at original
  have initialViews := SourceProgram.ProtocolState.observe_entry_congr who setup.program
    (setup.initialConfig left.theta) (setup.initialConfig right.theta) (Prod.ext original rfl)
  have initialObserved :
      (SourceProgram.ProtocolState.observe who setup.program left.initializer.point,
        SourceProgram.ProtocolState.observe who setup.program left.initializer.saved,
        left.initializer.excluded, left.initializer.entryExcluded, left.initializer.generation) =
      (SourceProgram.ProtocolState.observe who setup.program right.initializer.point,
        SourceProgram.ProtocolState.observe who setup.program right.initializer.saved,
        right.initializer.excluded, right.initializer.entryExcluded,
          right.initializer.generation) := by
    rw [left.initializer_facts.1, right.initializer_facts.1]
    dsimp only [CommitRecoveryState.atPoint]
    rw [initialViews]
  have initialInformation : setup.proposalRecoveryModel.infoOf who left.initializerTrace =
      setup.proposalRecoveryModel.infoOf who right.initializerTrace := by
    have leftInitial := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
      setup.proposalRecoveryModel.infoOf who history.trace) left.initialized
    have rightInitial := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
      setup.proposalRecoveryModel.infoOf who history.trace) right.initialized
    exact leftInitial.trans ((initialized_lift_info_eq setup mode plan who left.theta right.theta
      left.thetaSupported right.thetaSupported _ _ original).trans rightInitial.symm)
  have owned := SourceProgram.ProtocolState.history_eq_of_observe who setup.program
    left.current.point right.current.point views
  exact setup.proposalRecovery_info_eq_of_erased_archive_and_own_history who left.initializer
    right.initializer left.initializerTrace right.initializerTrace
    (by rw [left.initializer_facts.2, right.initializer_facts.2]) initialObserved initialInformation
    left.trace right.trace (left.sourceRetained.trans left.past)
    (right.sourceRetained.trans right.past) left.survives right.survives erased proposals
    (congrArg some owned)

/-- Every allowed latent source preimage retains a canonical current-block
support witness and its genuine foreign-cause refinement. This relation does
not assume full information equality, source reach proportionality or
two-sided coverage of source fibers. -/
structure PhaseProposalNativeSourceMatch
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (nativeTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (history : setup.proposalRecoveryProtocol.History) where
  canonical : PhaseProposalCanonicalBindingCut setup mode runtime leaks bounds plan values
    horizon scheduler control nativeTrace who event
  refined : setup.ProposalRecoveryForeignRefinement who canonical.initializer
    canonical.initializerTrace ⟨some canonical.current, canonical.trace⟩ history

namespace PhaseProposalNativeSourceMatch

variable {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
  {runtime : EventGraphRuntime (serviceGraph setup mode)}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode))}
  {bounds : MessageBounds (serviceGraph setup mode)}
  {plan : RuntimePhasePlan (serviceGraph setup mode)}
  {values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
    PMF (setup.CommitRecoveryValueChoice owner key.1)}
  {horizon : Nat} {scheduler : (phaseApplication runtime leaks).Scheduler}
  {control : (phaseApplication runtime leaks).Control}
  {nativeTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
    horizon scheduler).Trace (some control)}
  {who : Player} {event : (serviceGraph setup mode).EventId}
  {history : setup.proposalRecoveryProtocol.History}

/-- Every permitted latent preimage is an actual surviving binding decision
at the same static event. Foreign publication refinements retain this fact
through the full observer comparison; no canonical Boolean identity is used. -/
theorem decision
    (matched : PhaseProposalNativeSourceMatch setup mode runtime leaks bounds plan values
      horizon scheduler control nativeTrace who event history) :
    ∃ current : CommitRecoveryState setup.program,
      history.state = some current ∧
      SourceProgram.ProtocolState.actor setup.program current.point = some who ∧
      who ∉ current.excluded ∧
      SourceProgram.ProtocolState.atCommit setup.program current.point = true ∧
      instructionCount setup.program -
          SourceProgram.ProtocolState.remaining setup.program current.point =
        event.val ∧
      setup.proposalRecoveryModel.IsDecisionInfo who
        (setup.proposalRecoveryModel.infoOf who history.trace) := by
  let cut := matched.canonical
  obtain ⟨current, endpoint⟩ := setup.state_some_of_prefix cut.initializer
    (setup.proposalRecoveryEraseTrace cut.initializerTrace)
    (setup.proposalRecoveryEraseTrace history.trace)
    (setup.proposalRecoveryEraseTrace_prefix matched.refined.retained.2)
  have same := matched.refined.info_eq
  have privateRead := congrArg (fun information => information.1.1.1) same
  have semantic := congrArg (setup.proposalRecoveryEraseInfo who) same
  rw [setup.proposalRecoveryEraseInfo_observed, setup.proposalRecoveryEraseInfo_observed]
    at semantic
  have controls := congrArg (fun information => information.1.1.2) semantic
  have currentPrivate : (setup.proposalRecoveryModel.infoOf who history.trace).1.1.1 =
      setup.commitRecoveryPrivate who history.state := by
    change (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who history.trace).1.1.1 = _
    rw [InfoSignals.withOwnPlayRecall_infoOf]
    exact congrArg Prod.fst (setup.proposalRecoverySignals_control who history.trace)
  have cutPrivate : (setup.proposalRecoveryModel.infoOf who cut.trace).1.1.1 =
      some (SourceProgram.ProtocolState.observe who setup.program cut.current.point) := by
    change (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who cut.trace).1.1.1 = _
    rw [InfoSignals.withOwnPlayRecall_infoOf]
    exact congrArg Prod.fst (setup.proposalRecoverySignals_control who cut.trace)
  have currentPublic : (setup.commitRecoveryModel.infoOf who
      (setup.proposalRecoveryEraseTrace history.trace)).1.1.2 =
      setup.commitRecoveryPublic history.state := by
    change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who
      (setup.proposalRecoveryEraseTrace history.trace)).1.1.2 = _
    rw [InfoSignals.withOwnPlayRecall_infoOf]
    exact congrArg Prod.snd (setup.commitRecoverySignals_current who _)
  have cutPublic : (setup.commitRecoveryModel.infoOf who
      (setup.proposalRecoveryEraseTrace cut.trace)).1.1.2 =
      setup.commitRecoveryPublic (some cut.current) := by
    change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who
      (setup.proposalRecoveryEraseTrace cut.trace)).1.1.2 = _
    rw [InfoSignals.withOwnPlayRecall_infoOf]
    exact congrArg Prod.snd (setup.commitRecoverySignals_current who _)
  rw [cutPrivate, currentPrivate, endpoint] at privateRead
  have observed := Option.some.inj privateRead
  dsimp only at observed
  rw [cutPublic, currentPublic, endpoint] at controls
  have excludes : cut.current.excluded = current.excluded := congrArg Prod.fst controls
  have actor := congrArg (ProtocolView.actor who setup.program) observed
  simp only [SourceProgram.ProtocolState.actor_observe_eq] at actor
  have committing := congrArg (ProtocolView.atCommit who setup.program) observed
  simp only [SourceProgram.ProtocolState.atCommit_observe] at committing
  have positions := congrArg (ProtocolView.position who setup.program) observed
  have leftPosition := ProtocolView.position_add_remaining who setup.program cut.current.point
  have rightPosition := ProtocolView.position_add_remaining who setup.program current.point
  have currentRank : instructionCount setup.program -
      SourceProgram.ProtocolState.remaining setup.program current.point = event.val := by
    have cutRank := cut.rank
    omega
  have currentDecision := setup.proposalRecovery_isDecisionInfo_of_surviving_actor cut.current
    cut.trace who cut.survives cut.actor
  rw [same] at currentDecision
  exact ⟨current, endpoint, actor.symm.trans cut.actor,
    fun member => cut.survives (excludes.symm ▸ member),
    committing.symm.trans cut.atCommit, currentRank, currentDecision⟩

end PhaseProposalNativeSourceMatch

/-- Every permitted latent preimage of the same complete native information
has the same ENTIRE labeled source information. Original setup draws and
foreign failure-cause refinements remain literal quantified witnesses. -/
theorem PhaseProposalNativeSourceMatch.info_eq_of_information
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {runtime : EventGraphRuntime (serviceGraph setup mode)}
    {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode))}
    {bounds : MessageBounds (serviceGraph setup mode)}
    {plan : RuntimePhasePlan (serviceGraph setup mode)}
    {values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1)}
    {horizon : Nat} {scheduler : (phaseApplication runtime leaks).Scheduler}
    {leftControl rightControl : (phaseApplication runtime leaks).Control}
    {leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some leftControl)}
    {rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some rightControl)}
    {who : Player} {leftEvent rightEvent : (serviceGraph setup mode).EventId}
    {leftHistory rightHistory : setup.proposalRecoveryProtocol.History}
    (left : PhaseProposalNativeSourceMatch setup mode runtime leaks bounds plan values
      horizon scheduler leftControl leftTrace who leftEvent leftHistory)
    (right : PhaseProposalNativeSourceMatch setup mode runtime leaks bounds plan values
      horizon scheduler rightControl rightTrace who rightEvent rightHistory)
    (complete : leaks = MessageNetwork.completePendingObservation)
    (same : ((PhaseCount.onePacketMenu runtime leaks bounds).information
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon scheduler).infoOf who leftTrace =
      ((PhaseCount.onePacketMenu runtime leaks bounds).information
        ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
        horizon scheduler).infoOf who rightTrace) :
    setup.proposalRecoveryModel.infoOf who leftHistory.trace =
      setup.proposalRecoveryModel.infoOf who rightHistory.trace := by
  exact left.refined.info_eq.symm.trans
    ((left.canonical.info_eq_of_information right.canonical complete same).trans
      right.refined.info_eq)

section CurrentBindingProperness

variable (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "initial" => PMF.map (PhaseRuntimeState.initial plan) inputs

omit [Fintype Player] in
theorem filled_failed_binding_field
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (block.prepend suffix))
      (store : Store (graphLayout setup.program)) (entry : SourceProgram.Config Player L Γ),
      (Γ.map Prod.fst).Nodup →
      ∀ (who : Player) (payload : L.Ty)
        (index : Fin (eventCount (block.prepend suffix))), index.val < block.length →
        outputLayout (block.prepend suffix) index = .binding who payload →
        ∀ field : FieldRef (graphLayout setup.program) (.binding who payload),
          field.field = .inr (embedding.event index) → field.get? store = some .failure →
            (fillCommitPrefix setup.program block suffix embedding store entry).FailedBinding
              who P := by
  induction block with
  | nil =>
      intro suffix embedding store entry unique who payload index inside
      simp only [SourceProgram.CommitPrefix.length] at inside
      omega
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      intro suffix embedding store entry unique who ty index
      refine Fin.cases ?_ ?_ index
      · intro inside typed field named failed
        change EventField.binding owner payload = .binding who ty at typed
        cases typed
        let zero : Fin (eventCount
            ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix)) :=
          ⟨0, by simp only [SourceProgram.CommitPrefix.prepend, eventCount]; omega⟩
        let head : FieldRef (graphLayout setup.program) (.binding owner payload) :=
          ⟨.inr (embedding.event zero), embedding.layout_eq zero⟩
        have fields : head = field := by
          rcases field with ⟨actual, layout⟩
          change actual = .inr (embedding.event zero) at named
          subst actual; rfl
        let later := embedding.tail (rest.prepend suffix)
          (by simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
        have choice : (head.get? store).getD .failure = .failure := by
          rw [fields, failed]; rfl
        have debt := (fillCommitPrefix_attempt setup.program rest suffix later store
          (commitSuccessor name guard entry .failure)).preserves_failedBinding owner
            (SourceProgram.Config.failedBinding_commit entry unique fresh guard O)
        change (fillCommitPrefix setup.program rest suffix later store
          (commitSuccessor name guard entry ((head.get? store).getD .failure))).FailedBinding
            owner P
        rw [choice]
        exact debt
      · intro index inside typed field named failed
        dsimp only [fillCommitPrefix]
        exact ih suffix _ store _ (List.nodup_cons.mpr ⟨fresh, unique⟩) who ty index
          (by change index.val + 1 < rest.length + 1 at inside; omega) typed field named failed

theorem current_prefix_no_failed_binding
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (who : Player) (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (noCurrent : ¬ phaseProposalCurrentBindingFailure setup mode runtime leaks who event
      (control.execution.observe app who))
    {Δ : SourceCtx Player L} {P : Finset VarId} {name : VarId}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ who name payload)
    (next : SourceProgram Player L ((name, .commitment who payload) :: Δ) (insert name P))
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names
      Δ P)
    (reconstruct : earlier.prepend (.commit name who fresh guard next) = checkpoint.residual.tail)
    (selected : Fin (eventCount checkpoint.residual.tail))
    (atEnd : selected.val = earlier.length) (named : checkpoint.embedding.event selected = event) :
    let embedding := cast (congrArg (fun program => OutputEmbedding
      (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
        checkpoint.embedding
    ¬ (fillCommitPrefix setup.program earlier (.commit name who fresh guard next) embedding
      control.execution.application.current.native.config.store checkpoint.source).FailedBinding
        who P := by
  intro embedding failed
  let suffix := SourceProgram.commit name who fresh guard next
  let filled := fillCommitPrefix setup.program earlier suffix embedding
    control.execution.application.current.native.config.store checkpoint.source
  have raw := (menu).toRawTrace initial horizon scheduler trace
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler raw
  have filledRead := checkpoint.filled_prefix_view fresh guard next earlier reconstruct stored
    selected atEnd (named.symm ▸ request.2.2.1) (named.symm ▸ request.2.2.2.1)
      (by rw [named, binding]; exact id) (filled.history who) rfl
  rw [named] at filledRead
  have initialEq : initial = setup.initialLaw.map
      (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) := PMF.map_comp _ _ _
  obtain ⟨current, sourceTrace, _excluded, _generation, _control, _acting, _played, decoded⟩ :=
    phaseSurvivingSourceView?_of_ready_binding setup mode runtime leaks plan maximal horizon
      scheduler (initialEq ▸ raw) who event payload binding request
  have originalRead := decoded
  rw [phaseSurvivingSourceView?_observed_of_history setup mode runtime leaks plan inputs horizon
    scheduler raw who event] at decoded
  have currentErased := congrArg (Option.map (ProtocolView.eraseHistory who setup.program)) decoded
  have filledErased := congrArg (Option.map (ProtocolView.eraseHistory who setup.program))
    filledRead
  rw [← decodeEventView?_eraseHistory] at currentErased filledErased
  have views := Option.some.inj (currentErased.symm.trans filledErased)
  let point := checkpoint.residual.lift (cast (congrArg SourceProgram.ProtocolState reconstruct)
    (earlier.liftPoint suffix (ProtocolState.entry suffix filled)))
  have transport {first second : SourceProgram Player L checkpoint.residual.context
      checkpoint.residual.names} (eq : first = second)
      (lift : ProtocolState second → ProtocolState setup.program)
      (origin : ProtocolSuffix setup.program second lift) :
      ProtocolSuffix setup.program first (fun p => lift (cast (congrArg
        SourceProgram.ProtocolState eq) p)) := by
    cases eq; exact origin
  have pointFailed : ProtocolState.FailedBinding who setup.program point :=
    (transport reconstruct checkpoint.residual.lift checkpoint.origin).failedBinding_lift who _
      (earlier.failedBinding_liftPoint suffix who _
        (ProtocolState.failedBinding_entry suffix filled failed))
  have erasedViews : ProtocolState.observe who setup.program
      (ProtocolState.withHistory setup.program current.point (fun _ => [])) =
      ProtocolState.observe who setup.program
        (ProtocolState.withHistory setup.program point (fun _ => [])) := by
    simpa only [ProtocolView.eraseHistory_observe] using views
  have currentFailed := (ProtocolState.failedBinding_withHistory who setup.program current.point
    (fun _ => [])).mp
      ((ProtocolState.failedBinding_iff_of_observe_eq who setup.program _ _ erasedViews).mpr
        ((ProtocolState.failedBinding_withHistory who setup.program point (fun _ => [])).mpr
          pointFailed))
  exact noCurrent ((phaseProposalCurrentBindingFailure_iff_of_readback setup mode runtime leaks
    who event _ current.point originalRead).mpr currentFailed)

/-- Every focal preparation in the current visit is proper before a clean
unsent callback. Earlier canceled visits are not restricted. -/
theorem phaseProposal_recalled_current_binding_preparation_value
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (witness : RecoverySourceWitness setup mode plan control.execution.application)
    (phase : RuntimePhase (graph)) (rest : List (RuntimePhase (graph)))
    (installed : control.execution.application.phases = phase :: rest)
    (kind : phase.kind = .commitment)
    (focal : Player) (current : (graph).EventId) (currentPayload : L.Ty)
    (currentBinding : (graph).outputLayout current = .binding focal currentPayload)
    (request : control.execution.application.SeedRequest focal
      ⟨control.execution.application.attempt, current⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall focal),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, current⟩)
    (noCurrent : ¬ phaseProposalCurrentBindingFailure setup mode runtime leaks focal current
      (control.execution.observe app focal))
    (event : (graph).EventId) (inside : event ∈ phase.events) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding focal payload)
    (serial : Nat) (opening : Option (Raw L)) (evidence : EvidenceRequest (graph))
    (record : (app).PlayerEntry) (recorded : record ∈ control.execution.recall focal)
    (declared : record.action =
      ⟨some ⟨⟨.commitment event (focal, .prepared serial), opening⟩, evidence⟩⟩)
    (sameAttempt : record.beforeView.application.2.attempt =
      control.execution.application.attempt) :
    ∃ value : L.Val payload, opening.bind (fun raw => raw.as? payload) = some value := by
  classical
  have frontier := witness.order.frontier
  have geometry := witness.checkpoint.commit_phase_geometry phase rest installed kind frontier
    (maximal.suffix witness.suffix)
  have lower : control.execution.application.attempt.phase ≤ event.val := by
    simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some] using ((phase.mem_events event).mp inside).1
  have earlier := phase_recorded_binding_rank_lt_of_unsent_request runtime leaks bounds plan
    inputs horizon (serviceGraph_revealRelaxedOrdered setup mode) scheduler trace focal record
      recorded ⟨⟨.commitment event (focal, .prepared serial), opening⟩, evidence⟩
        (by rw [declared]) event (focal, .prepared serial) rfl sameAttempt current request unsent
  have dependency := (serviceGraph_revealRelaxedOrdered setup mode).keeps
    (barrierOrder_same_owner (graph).outputLayout earlier
      (by rw [binding, currentBinding]; rfl))
    (Or.inl (by simp only [binding, EventField.IsPublication, not_false_eq_true]))
  have completed := request.2.2.1.2 dependency
  have originalRead := phaseProposal_completed_binding_material runtime leaks bounds plan
    inputs horizon scheduler control trace focal event payload binding lower completed
      request.2.2.2.2 serial opening evidence record recorded declared sameAttempt
  cases decoded : opening.bind (fun value => value.as? payload) with
  | some value => exact ⟨value, rfl⟩
  | none =>
    have failedRead : (⟨.inr event, binding⟩ :
        FieldRef (graph).layout (.binding focal payload)).get?
          control.execution.application.current.native.config.store = some .failure := by
      simpa only [decoded, Option.elim_none] using originalRead
    generalize decomposition :
      commitPhase witness.checkpoint.residual.tail = segment at geometry
    rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
    dsimp only at geometry
    have high : phase.high = phase.low + block.length := by
      have positive := phase.nonempty
      omega
    have currentInside : current ∈ phase.events := by
      obtain ⟨selected, member, present⟩ := request.2.1
      have selectedEq : selected = phase :=
        (by simpa only [installed, List.head?_cons, Option.mem_some_iff]
          using member : phase = selected).symm
      exact selectedEq ▸ present
    obtain ⟨selected, named, Ξ, Q, name, fresh, guard, keptRecall, later, size,
      _sameBlock, prefixEq⟩ := witness.checkpoint.fixed_binding_prefix block suffix reconstruct
        frontier phase rest installed high current currentInside request.2.2.1 focal
          currentPayload currentBinding
    have notFailed := current_prefix_no_failed_binding setup mode runtime leaks bounds plan
      maximal horizon scheduler control trace witness.checkpoint focal current currentPayload
        currentBinding request noCurrent fresh guard (later.prepend suffix) keptRecall prefixEq
          selected size.symm named
    let embedding := cast (congrArg (fun program => OutputEmbedding
      (inputLayout setup.context) (outputLayout setup.program) program) prefixEq.symm)
        witness.checkpoint.embedding
    have rankTransport {first second : SourceProgram Player L
        witness.checkpoint.residual.context witness.checkpoint.residual.names}
        (eq : first = second) (e : OutputEmbedding (inputLayout setup.context)
          (outputLayout setup.program) second)
        (r : ∀ i, (e.event i).val = control.execution.application.attempt.phase + i.val) :
        ∀ i, ((cast (congrArg (fun p => OutputEmbedding (inputLayout setup.context)
          (outputLayout setup.program) p) eq.symm) e).event i).val =
            control.execution.application.attempt.phase + i.val := by cases eq; exact r
    have ranks := rankTransport prefixEq witness.checkpoint.embedding
      witness.checkpoint.compiled.rankEq
    have currentRank := witness.checkpoint.compiled.rankEq selected
    rw [named, ← size] at currentRank
    let index : Fin (eventCount (keptRecall.prepend
        (.commit name focal fresh guard (later.prepend suffix)))) :=
      ⟨event.val - control.execution.application.attempt.phase, by
        have bound := keptRecall.eventCount_prepend
          (.commit name focal fresh guard (later.prepend suffix))
        omega⟩
    have indexed : embedding.event index = event := Fin.ext (by
      change (embedding.event index).val = event.val
      rw [ranks]
      dsimp only [index]
      omega)
    have typed : outputLayout
        (keptRecall.prepend (.commit name focal fresh guard (later.prepend suffix))) index =
          .binding focal payload :=
      (embedding.layout_eq index).symm.trans (indexed.symm ▸ binding)
    exact (notFailed (filled_failed_binding_field setup keptRecall
      (.commit name focal fresh guard (later.prepend suffix)) embedding
        control.execution.application.current.native.config.store witness.checkpoint.source
          witness.checkpoint.unique focal payload index (by dsimp only [index]; omega) typed
            ⟨.inr event, binding⟩ (congrArg Sum.inr indexed.symm) failedRead)).elim

end CurrentBindingProperness

end Vegas

namespace Vegas.PhaseProposalQualifiedBinding

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

section EmissionConditioning

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

variable (values : ∀ who (key : setup.ProposalRecoveryComponent who),
  PMF (setup.CommitRecoveryValueChoice who key.1))

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds

/-- At one fixed original entry, conditioning on the just-emitted immutable
binding gives its actual updated continuation. This normalization occurs
inside the entry fiber, before any source annotation is integrated. -/
private theorem binding_potential_emitted_posterior
    (anchor : (app).Execution) (phase : RuntimePhase (serviceGraph setup mode))
    (config : (serviceGraph setup mode).Config)
    (event : (serviceGraph setup mode).EventId) (ready : config.cut.Ready event)
    (who : Player) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (code : cast (congrArg (EventCode (serviceGraph setup mode).layout) binding)
      ((serviceGraph setup mode).nodes event) = .bind who payload)
    (inside : event ∈ phase.events) (active : who ∉ anchor.application.current.excluded)
    (result : PublicationResult (L.Val payload)) :
    let profile := phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase
      values
    let prior := phaseProposalBindingResults setup mode runtime leaks plan values
      PhaseProposalRates.zero who event payload binding (anchor.recall who)
        (phaseProposalBindingGraphView setup mode runtime leaks anchor who
          ((serviceGraph setup mode).playerObserve who config))
    let completed := fun chosen : PublicationResult (L.Val payload) => config.complete event ready
      (cast (congrArg EventField.Action binding.symm) chosen)
      (cast (congrArg EventField.Value binding.symm) chosen)
    let field : FieldRef (serviceGraph setup mode).layout (.binding who payload) :=
      ⟨.inr event, binding⟩
    result ∈ prior.support →
      some result ∈ (((serviceGraph setup mode).canonicalContinuation profile config).map
        (fun key => field.get? key.2.1)).support ∧
      fiberPosterior ((serviceGraph setup mode).canonicalContinuation profile config)
        (fun key => field.get? key.2.1) (some result) =
      (serviceGraph setup mode).canonicalContinuation profile (completed result) ∧
      (((serviceGraph setup mode).canonicalContinuation profile config).map
        (fun key => field.get? key.2.1)) (some result) = prior result := by
  classical
  intro profile prior completed field supported
  let graph := serviceGraph setup mode
  have actor : graph.actor? event = some who := graph.actor?_of_outputLayout_binding binding
  have draw : graph.normalizePolicy who (profile who) event actor
      (graph.playerObserve who config) =
        prior.map (cast (congrArg EventField.Action binding.symm)) := by
    rw [phaseProposalBindingPotentialProfile_normalize]
    simp only [phaseProposalBindingPotentialProfile, nodeView_eq_bind binding code]
    rw [dite_eq_left True.intro, ite_eq_left ⟨inside, active⟩]
  have step : graph.normalizedPolicyStep profile config event ready = prior.bind
      (fun chosen => PMF.pure (completed chosen)) := by
    unfold normalizedPolicyStep
    split
    · rename_i owner selected
      have ownerEq : owner = who := Option.some.inj (selected.symm.trans actor)
      subst owner
      rw [draw, PMF.bind_map]
      apply congrArg (PMF.bind prior)
      funext chosen
      exact commit_step config event ready binding code chosen
    · rename_i absent
      rw [absent] at actor
      cases actor
  let kernel := fun chosen => graph.canonicalContinuation profile (completed chosen)
  have harmonic : prior.bind kernel = graph.canonicalContinuation profile config := by
    have equation := phaseProposalBindingPotentialProfile_harmonic setup mode runtime leaks plan
      anchor phase values config event ready
    rw [normalizedThenCanonical, step, PMF.bind_bind] at equation
    simpa only [PMF.pure_bind, kernel] using equation
  have recovers : ∀ chosen ∈ prior.support, ∀ key ∈ (kernel chosen).support,
      field.get? key.2.1 = some chosen := by
    intro chosen _chosenSupport key reached
    obtain ⟨final, member, rfl⟩ := (PMF.mem_support_map_iff ..).mp reached
    have initialRead : field.get? (completed chosen).store = some chosen := by
      have cancel {First Second : Type} (equal : First = Second) (value : Second) :
          cast (congrArg Option equal) (some (cast equal.symm value)) = some value := by
        cases equal
        rfl
      simpa only [field, FieldRef.get?, completed, Config.store_output,
        Config.complete_output_same] using cancel (congrArg EventField.Value binding) chosen
    exact field.get?_preserved (completed chosen).store final.store
      (runPlan_retains_store _ _ (completed chosen) final member) chosen initialRead
  have present : some result ∈ (prior.map some).support :=
    (PMF.mem_support_map_iff ..).mpr ⟨result, supported, rfl⟩
  have posterior : fiberPosterior prior some (some result) = PMF.pure result := by
    apply pmf_eq_pure_of_support_subset_singleton
    intro chosen reached
    exact Option.some.inj (mem_support_fiberPosterior present reached).1
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨key, reached⟩ := (kernel result).support_nonempty
    apply (PMF.mem_support_map_iff ..).mpr
    refine ⟨key, ?_, recovers result supported key reached⟩
    rw [← harmonic]
    exact (PMF.mem_support_bind_iff ..).mpr ⟨result, supported, reached⟩
  · rw [← harmonic, fiberPosterior_bind_of_observation prior kernel some
      (fun key => field.get? key.2.1) recovers (some result) present, posterior, PMF.pure_bind]
  · have marginal :
        ((graph.canonicalContinuation profile config).map
          (fun key => field.get? key.2.1)) = prior.map some := by
      rw [← harmonic, PMF.map_bind, ← PMF.bind_pure_comp]
      apply bind_congr_on_support prior
      intro chosen member
      apply pmf_eq_pure_of_support_subset_singleton
      intro observed reached
      obtain ⟨key, keySupport, rfl⟩ := (PMF.mem_support_map_iff ..).mp reached
      exact recovers chosen member key keySupport
    rw [marginal]
    exact pmf_map_apply_of_injective prior (Option.some_injective _) result

/-- A proper value at the actual callback has positive conditional mass at
its emitted frontier. Both query agreement and inherited automatic closure
come from the original callback frame, including pending foreign emissions. -/
theorem binding_frontier_proper_posterior
    (complete : leaks = MessageNetwork.completePendingObservation)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (fullValues : ∀ who key, FullSupport (values who key))
    (fuel : Nat) (serviceScheduler : (app).Scheduler) (remaining : Nat) (who : Player)
    (execution anchor : (app).Execution)
    (trace : ((menu).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      fuel serviceScheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : RuntimePhase (serviceGraph setup mode)) (commitment : phase.kind = .commitment)
    (frontier : (serviceGraph setup mode).Config)
    (frame : PhaseProposalBindingCallbackFrame setup mode runtime leaks anchor phase
      execution frontier (some who))
    (attempt : execution.application.attempt = anchor.application.attempt)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (code : cast (congrArg (EventCode (serviceGraph setup mode).layout) binding)
      ((serviceGraph setup mode).nodes event) = .bind who payload)
    (inside : event ∈ phase.events) (active : who ∉ anchor.application.current.excluded)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩)
    (value : L.Val payload) :
    ∃ ready : frontier.cut.Ready event,
      let profile := phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase
        values
      let field : FieldRef (serviceGraph setup mode).layout (.binding who payload) :=
        ⟨.inr event, binding⟩
      let filled := frontier.complete event ready
        (cast (congrArg EventField.Action binding.symm) (.success value))
        (cast (congrArg EventField.Value binding.symm) (.success value))
      some (PublicationResult.success value) ∈
        (((serviceGraph setup mode).canonicalContinuation profile frontier).map
          (fun key => field.get? key.2.1)).support ∧
      fiberPosterior ((serviceGraph setup mode).canonicalContinuation profile frontier)
          (fun key => field.get? key.2.1) (some (.success value)) =
        (serviceGraph setup mode).canonicalContinuation profile
          (phaseProposalBindingFrontierDrain setup mode runtime leaks anchor phase filled) ∧
      (((serviceGraph setup mode).canonicalContinuation profile frontier).map
        (fun key => field.get? key.2.1)) (some (.success value)) =
        phaseProposalBindingResults setup mode runtime leaks plan values
          PhaseProposalRates.zero who event payload binding (execution.recall who)
            (execution.observe (app) who) (.success value) := by
  classical
  let graph := serviceGraph setup mode
  have actor : graph.actor? event = some who := graph.actor?_of_outputLayout_binding binding
  have surviving : who ∉ execution.application.current.excluded := by
    simpa only [frame.excluded] using active
  obtain ⟨ready, hidden⟩ := phaseProposalBindingPotentialProfile_hidden_frontier setup mode runtime
    leaks plan anchor phase values execution.application.current.native.config frontier
    frame.agreement frame.inputs who event request.2.2.1 actor
    (frame.hidden who event request.2.2.1 actor surviving unsent)
  obtain ⟨key, queried, full⟩ := phaseProposalDomainValues_fullSupport_of_binding setup mode runtime
    leaks complete plan maximal values fullValues fuel serviceScheduler
    ((menu).toRawTrace _ fuel serviceScheduler trace) who rfl event payload binding request
  have actual : PublicationResult.success value ∈
      (phaseProposalBindingResults setup mode runtime leaks plan values PhaseProposalRates.zero
        who event payload binding (execution.recall who)
          (execution.observe (app) who)).support := by
    simp only [phaseProposalBindingResults, queried, PhaseProposalRates.zero, mix_zero]
    obtain ⟨choice, chosen, result⟩ := (PMF.mem_support_map_iff ..).mp (full value)
    exact (PMF.mem_support_map_iff ..).mpr
      ⟨choice, chosen, congrArg PublicationResult.success result⟩
  have query := phaseProposalBindingGraphView_query_eq_current setup mode runtime leaks plan
    anchor execution who event attempt frame.retired frame.failures (frame.archive who rfl)
  have frozen := phaseProposalBindingResults_eq_of_query setup mode runtime leaks plan values
    PhaseProposalRates.zero who event payload binding _ _ _ _ query
  rw [frozen] at actual
  have same : phaseProposalBindingResults setup mode runtime leaks plan values
      PhaseProposalRates.zero who event payload binding (anchor.recall who)
      (phaseProposalBindingGraphView setup mode runtime leaks anchor who
        (graph.playerObserve who execution.application.current.native.config)) =
      phaseProposalBindingResults setup mode runtime leaks plan values PhaseProposalRates.zero
        who event payload binding (anchor.recall who)
        (phaseProposalBindingGraphView setup mode runtime leaks anchor who
          (graph.playerObserve who frontier)) := by
    apply pmf_map_injective (f := cast (congrArg EventField.Action binding.symm))
      (fun first second equal => by
        simpa only [cast_cast, cast_eq] using
          congrArg (cast (congrArg EventField.Action binding)) equal)
    simpa only [phaseProposalBindingPotentialProfile_normalize,
      phaseProposalBindingPotentialProfile, nodeView_eq_bind binding code,
      dite_eq_left True.intro, ite_eq_left
        (show event ∈ phase.events ∧ who ∉ anchor.application.current.excluded from
          ⟨inside, active⟩)] using hidden
  rw [same] at actual
  refine ⟨ready, ?_⟩
  intro profile field filled
  have posterior := binding_potential_emitted_posterior setup mode runtime leaks plan values
    anchor phase frontier event ready who payload binding code inside active (.success value) actual
  have drained := phaseProposalBindingPotentialProfile_drain setup mode runtime leaks plan anchor
    phase commitment values
    (⟨{ anchor.application.current.native with config := filled },
      anchor.application.current.excluded⟩ : RecoveryState graph) rfl
  refine ⟨posterior.1, posterior.2.1.trans drained.symm, ?_⟩
  have atom := posterior.2.2
  rw [← same, ← frozen] at atom
  exact atom

open Classical in
/-- Appending one observed coordinate conditions the original joint on the
entire accumulated observation, retaining its literal supported atoms. -/
theorem posterior_append_observation {A B : Type} (law : PMF A)
    (old next : A → Bool) (field : A → B) (value : B) (before after : PMF A)
    (oldPresent : true ∈ (law.map old).support)
    (beforeEq : before = fiberPosterior law old true)
    (newPresent : value ∈ (before.map field).support)
    (afterEq : after = fiberPosterior before field value)
    (same : ∀ key ∈ law.support,
      next key = true ↔ old key = true ∧ field key = value) :
    true ∈ (law.map next).support ∧ after = fiberPosterior law next true := by
  let pair := fun key => (old key, field key)
  obtain ⟨key, supported, measured⟩ := (PMF.mem_support_map_iff ..).mp newPresent
  have conditioned := supported
  rw [beforeEq] at conditioned
  have parts := mem_support_fiberPosterior oldPresent conditioned
  have pairPresent : (true, value) ∈ (before.map pair).support :=
    (PMF.mem_support_map_iff ..).mpr ⟨key, supported, Prod.ext parts.1 measured⟩
  have fine : fiberPosterior before field value =
      fiberPosterior before pair (true, value) := by
    apply fiberPosterior_eq_of_support_fiber
    intro found member
    rw [beforeEq] at member
    have oldRead := (mem_support_fiberPosterior oldPresent member).1
    simp only [pair, Prod.mk.injEq, oldRead, true_and]
  refine ⟨(PMF.mem_support_map_iff ..).mpr
    ⟨key, parts.2, (same key parts.2).mpr ⟨parts.1, measured⟩⟩, ?_⟩
  rw [afterEq, fine, beforeEq]
  have projected := fiberPosterior_after_projection law pair Prod.fst true (true, value)
    (by simpa only [beforeEq, pair, Function.comp_def] using pairPresent)
  rw [show (Prod.fst ∘ pair) = old from rfl] at projected
  rw [projected]
  apply fiberPosterior_eq_of_support_fiber
  intro found member
  simpa only [pair, Prod.mk.injEq] using (same found member).symm

open Classical in
/-- The actual emitted-prefix cylinder determines the continuation at its
frontier. Properness is a factual statement about the active fields already
written by this trace; no source law or frontier matching is assumed. -/
theorem emitted_frontier_conditional
    (complete : leaks = MessageNetwork.completePendingObservation)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fullValues : ∀ who key, FullSupport (values who key))
    (fuel : Nat) (serviceScheduler : (app).Scheduler)
    (anchor : (app).Control)
    (anchorTrace : ((menu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      fuel serviceScheduler).Trace (some anchor))
    (phase : RuntimePhase (serviceGraph setup mode))
    (installed : anchor.execution.application.phases.head? = some phase)
    (commitment : phase.kind = .commitment)
    (entryExcluded : anchor.execution.application.entry.excluded =
      anchor.execution.application.current.excluded)
    (fresh : ∀ who, ∀ record ∈ anchor.execution.recall who,
      record.beforeView.application.2.attempt ≠ anchor.execution.application.attempt)
    (current : (app).Control)
    (trace : ((menu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      fuel serviceScheduler).Trace (some current))
    (kept : TracePrefix anchorTrace trace)
    (attempt : current.execution.application.attempt = anchor.execution.application.attempt)
    (excluded : current.execution.application.current.excluded =
      anchor.execution.application.current.excluded) :
    let profile := phaseProposalBindingPotentialProfile setup mode runtime leaks plan
      anchor.execution phase values
    let frontier := phaseProposalEmissionFrontier setup mode runtime leaks anchor.execution phase
      anchorTrace.length anchor.execution.application.current.native.config
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)) fuel
        serviceScheduler ((menu).toRawTrace _ fuel serviceScheduler trace)
    let observed := fun (execution : (app).Execution)
        (key : (serviceGraph setup mode).SemanticKey) => decide (
      ∀ message ∈ execution.network.inputs,
        message.payload.attempt = execution.application.attempt →
        ∀ event ∈ phase.events, ∀ candidate,
          message.payload.packet.call = .commitment event candidate →
          ∀ owner payload (binding :
              (serviceGraph setup mode).outputLayout event = .binding owner payload),
            (⟨.inr event, binding⟩ : FieldRef (serviceGraph setup mode).layout
              (.binding owner payload)).get? key.2.1 =
                some (execution.application.current.native.bindingResult candidate payload))
    (∀ event ∈ phase.events, ∀ owner ∉ anchor.execution.application.current.excluded,
      ∀ payload (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload),
      ∀ result, (⟨.inr event, binding⟩ : FieldRef (serviceGraph setup mode).layout
        (.binding owner payload)).get? frontier.store = some result →
          ∃ value, result = PublicationResult.success value) →
    true ∈ (((serviceGraph setup mode).canonicalContinuation profile
      anchor.execution.application.current.native.config).map
        (observed current.execution)).support ∧
    (serviceGraph setup mode).canonicalContinuation profile frontier =
      fiberPosterior ((serviceGraph setup mode).canonicalContinuation profile
        anchor.execution.application.current.native.config) (observed current.execution) true := by
  classical
  intro profile finalFrontier observed proper
  let graph := serviceGraph setup mode
  let sourceInitial := (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)
  let first := anchor.execution.application.current.native.config
  let law := graph.canonicalContinuation profile first
  let frontier := fun {point}
      (history : ((menu).protocol sourceInitial fuel serviceScheduler).Trace point) =>
    phaseProposalEmissionFrontier setup mode runtime leaks anchor.execution phase anchorTrace.length
      first sourceInitial fuel serviceScheduler ((menu).toRawTrace sourceInitial fuel
        serviceScheduler history)
  have read (execution : (app).Execution) (config : graph.Config) :
      observed execution (graph.semanticKey config) = true ↔
        PhaseProposalEmittedBindings runtime leaks execution phase config := by
    simp only [observed, graph, EventGraph.semanticKey, EventGraph.storeRecall,
      decide_eq_true_eq, PhaseProposalEmittedBindings]
  have represent : ∀ key ∈ law.support, ∃ config : graph.Config,
      graph.semanticKey config = key := by
    intro key supported
    obtain ⟨config, _member, equal⟩ := (PMF.mem_support_map_iff ..).mp supported
    exact ⟨config, equal⟩
  obtain ⟨noInputs, initialEmissions, origins⟩ := phaseProposal_fresh_entry_binding_origins setup
    mode runtime leaks bounds plan (setup.initialLaw.map encodeInputs) fuel serviceScheduler
      anchor anchorTrace phase installed commitment fresh
  have initialized : ∀ state ∈ sourceInitial.support, state.Ordered := by
    intro state member
    obtain ⟨draw, _drawn, rfl⟩ := (PMF.mem_support_map_iff ..).mp member
    exact PhaseRuntimeState.initial_ordered plan draw
  have anchorOrdered := (phaseApplication_seedOrder runtime leaks).history sourceInitial fuel
    serviceScheduler initialized ((menu).toRawTrace sourceInitial fuel serviceScheduler anchorTrace)
  have firstFrontier : frontier anchorTrace = first := by
    apply phaseProposalEmissionFrontier_before_anchor
    rw [(menu).toRawTrace_length]
  have along : ∀ {point} (history : ((menu).protocol sourceInitial fuel serviceScheduler).Trace
    point),
      TracePrefix anchorTrace history → ∃ next : (app).Control, point = some next ∧
        next.execution.application.Ordered ∧
        anchor.execution.application.attempt.generation ≤
          next.execution.application.attempt.generation ∧
        anchor.execution.application.attempt.phase ≤ next.execution.application.attempt.phase ∧
        anchor.execution.application.current.excluded ⊆
          next.execution.application.current.excluded ∧
        (next.execution.application.attempt = anchor.execution.application.attempt →
          next.execution.application.current.excluded =
            anchor.execution.application.current.excluded →
          (∀ event ∈ phase.events, ∀ owner ∉ anchor.execution.application.current.excluded,
            ∀ payload (binding : graph.outputLayout event = .binding owner payload),
            ∀ result, (⟨.inr event, binding⟩ : FieldRef graph.layout
              (.binding owner payload)).get? (frontier history).store = some result →
                ∃ value, result = PublicationResult.success value) →
          true ∈ (law.map (observed next.execution)).support ∧
          graph.canonicalContinuation profile (frontier history) =
            fiberPosterior law (observed next.execution) true) := by
    intro point history retained
    induction retained with
    | refl =>
      refine ⟨anchor, rfl, anchorOrdered, le_rfl, le_rfl, Finset.Subset.refl _, ?_⟩
      intro _ _ _
      have all : ∀ key, observed anchor.execution key = true := by
        intro key
        apply decide_eq_true
        intro message member same
        exact (noInputs message member same).elim
      obtain ⟨key, member⟩ := law.support_nonempty
      refine ⟨(PMF.mem_support_map_iff ..).mpr ⟨key, member, all key⟩, ?_⟩
      rw [firstFrontier]
      symm
      rw [fiberPosterior_eq_filter _ _ ⟨key, all key, member⟩]
      exact filter_of_support_subset law _ _ (fun found _ => all found)
    | @extend source target earlier retained joint legal reached ih =>
      obtain ⟨middle, rfl, middleOrdered, lowerGeneration, lowerPhase, lowerExcluded,
        previous⟩ := ih
      have actual : target ∈ ((app).transition sourceInitial fuel serviceScheduler (some middle)
          joint).support := reached
      obtain ⟨next, rfl, _recall⟩ := (app).transition_recall_prefix sourceInitial fuel
        serviceScheduler
        middle target joint actual
      have nextOrdered := (phaseApplication_seedOrder runtime leaks).transition sourceInitial fuel
        serviceScheduler initialized (some middle) (some next) joint middleOrdered actual
      have progress := (phaseApplication_namespace_progress runtime leaks).transition
        sourceInitial fuel
        serviceScheduler middle next joint actual middleOrdered
      have exclusions := (phaseApplication_exclusion_monotone runtime leaks).transition
        sourceInitial fuel
        serviceScheduler middle next joint actual
      refine ⟨next, rfl, nextOrdered, lowerGeneration.trans progress.1,
        lowerPhase.trans progress.2, lowerExcluded.trans exclusions, ?_⟩
      intro nextAttempt nextExcluded nextProper
      have middleAttempt : middle.execution.application.attempt =
          anchor.execution.application.attempt := by
        have generation := congrArg CommitAttemptId.generation nextAttempt
        have phaseRank := congrArg CommitAttemptId.phase nextAttempt
        cases left : middle.execution.application.attempt with
        | mk leftPhase leftGeneration =>
          cases right : anchor.execution.application.attempt with
          | mk rightPhase rightGeneration =>
            simp only [left, right] at lowerGeneration lowerPhase progress generation phaseRank ⊢
            congr 1 <;> omega
      have middleExcluded : middle.execution.application.current.excluded =
          anchor.execution.application.current.excluded :=
        Finset.Subset.antisymm (by simpa only [nextExcluded] using exclusions) lowerExcluded
      have extendRaw := ((menu).reaches_raw sourceInitial fuel serviceScheduler
        (TracePrefix.extend (TracePrefix.refl : TracePrefix earlier earlier)
          joint legal reached).reachesWithin).tracePrefix
      have priorProper : ∀ event ∈ phase.events,
          ∀ owner ∉ anchor.execution.application.current.excluded,
          ∀ payload (binding : graph.outputLayout event = .binding owner payload),
          ∀ result, (⟨.inr event, binding⟩ : FieldRef graph.layout
            (.binding owner payload)).get? (frontier earlier).store = some result →
              ∃ value, result = PublicationResult.success value := by
        intro event inside owner active payload binding result written
        apply nextProper event inside owner active payload binding result
        apply FieldRef.get?_preserved _ _ _ _ result written
        intro field value stored
        exact phaseProposalEmissionFrontier_prefix_preserves setup mode runtime leaks
          anchor.execution phase anchorTrace.length first sourceInitial fuel serviceScheduler
            field value
            stored extendRaw
      obtain ⟨oldPresent, oldLaw⟩ := previous middleAttempt middleExcluded priorProper
      have frame := phaseProposalEmissionFrontier_callback_frame setup mode runtime leaks bounds
        plan (setup.initialLaw.map encodeInputs) fuel serviceScheduler complete maximal anchor
          anchorTrace phase installed commitment entryExcluded origins initialEmissions middle
            earlier retained middleAttempt middleExcluded
      rcases middle with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
        have present : (joint who).isSome := by
          cases selected : joint who with
          | none =>
            have inactive := legal.2 who
            rw [selected] at inactive
            exact (inactive (by rfl)).elim
          | some response => rfl
        obtain ⟨response, selected⟩ := Option.isSome_iff_exists.mp present
        have nextEq : next = ⟨remaining, none, execution.respond (app) who response⟩ := by
          apply Option.some.inj
          simpa only [ReactiveApplication.transition, selected, Option.getD_some] using
            (PMF.mem_support_pure_iff _ _).mp actual
        subst next
        cases sent : response.transmission with
        | none =>
          have responseEq : response = ⟨none⟩ := by cases response; cases sent; rfl
          have stepF : frontier (earlier.extend joint legal reached) = frontier earlier := by
            dsimp only [frontier]
            rw [ReactiveApplication.ResponseMenu.toRawTrace, phaseProposalEmissionFrontier,
              ite_eq_left (by simpa only [(menu).toRawTrace_length] using retained.length_le)]
            simp only [phaseProposalBindingFrontierAdvance, middleAttempt, ↓reduceIte,
              selected, Option.getD_some, sent]
          simpa only [stepF, responseEq, ReactiveApplication.Execution.respond] using
            And.intro oldPresent oldLaw
        | some material =>
          have offered : (⟨some material⟩ : (app).Action) ∈
              PhaseCount.onePacketActions runtime leaks bounds who (execution.recall who)
                (execution.observe (app) who) := by
            have allowed := legal.2 who
            rw [selected] at allowed
            have responseEq : response = ⟨some material⟩ := by cases response; cases sent; rfl
            exact responseEq ▸ allowed.2
          obtain ⟨event, payload, binding, code, inside, request⟩ :=
            phaseProposal_nonsilent_binding_request setup mode runtime leaks bounds plan
              (setup.initialLaw.map encodeInputs) fuel serviceScheduler phase commitment remaining
                who execution earlier frame.installed material offered
          have unsent := PhaseCount.unsent_of_nonsilent runtime leaks bounds plan
            (serviceGraph_revealRelaxedOrdered setup mode) (setup.initialLaw.map encodeInputs)
              fuel serviceScheduler remaining who execution earlier _ request material offered
          have active : who ∉ anchor.execution.application.current.excluded := by
            change execution.application.current.excluded =
              anchor.execution.application.current.excluded at middleExcluded
            exact middleExcluded ▸ request.2.2.2.2
          have ready := (phaseProposalBindingPotentialProfile_hidden_frontier setup mode runtime
            leaks plan anchor.execution phase values execution.application.current.native.config
              (frontier earlier) frame.agreement frame.inputs who event request.2.2.1
                request.2.2.2.1
                (frame.hidden who event request.2.2.1 request.2.2.2.1 request.2.2.2.2 unsent)).1
          obtain ⟨serial, opening, evidence, materialEq, _bounded, _fresh⟩ :=
            PhaseCount.onePacket_binding_shape runtime leaks bounds plan
              (serviceGraph_revealRelaxedOrdered setup mode) (setup.initialLaw.map encodeInputs)
                fuel serviceScheduler remaining who execution earlier event payload binding
                  request material offered
          have packet : material.call.packet = .commitment event (who, .prepared serial) := by
            rw [materialEq]
          have recorded := phaseProposalEmissionFrontier_binding_recorded setup mode runtime leaks
            anchor.execution phase anchorTrace.length first sourceInitial fuel serviceScheduler
              remaining
              who execution ((menu).toRawTrace sourceInitial fuel serviceScheduler earlier) joint
                ((menu).legal_raw sourceInitial fuel serviceScheduler legal) _ reached response
                  selected
                  material sent event (who, .prepared serial) packet
                  payload binding code middleAttempt inside
                    (by simpa only [(menu).toRawTrace_length] using retained.length_le) ready
                      ((menu).toRawTrace sourceInitial fuel serviceScheduler
                        (earlier.extend joint legal reached)) TracePrefix.refl
          obtain ⟨value, resultEq⟩ := nextProper event inside who active payload binding _ recorded
          obtain ⟨ready', rowPresent, rowLaw, _rowAtom⟩ :=
            binding_frontier_proper_posterior setup mode
            runtime leaks bounds plan values complete maximal fullValues fuel serviceScheduler
              remaining who execution anchor.execution
                (by
                  have initialEq : sourceInitial = setup.initialLaw.map
                      (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) :=
                    PMF.map_comp _ _ _
                  exact initialEq ▸ earlier)
                  phase commitment (frontier earlier)
                  frame middleAttempt event payload binding code inside active request unsent value
          have stepF : frontier (earlier.extend joint legal reached) =
              phaseProposalBindingFrontierDrain setup mode runtime leaks anchor.execution phase
                ((frontier earlier).complete event ready'
                  (cast (congrArg EventField.Action binding.symm) (.success value))
                  (cast (congrArg EventField.Value binding.symm) (.success value))) := by
            dsimp only [frontier]
            rw [ReactiveApplication.ResponseMenu.toRawTrace, phaseProposalEmissionFrontier,
              ite_eq_left (by simpa only [(menu).toRawTrace_length] using retained.length_le)]
            rw [phaseProposalBindingFrontierAdvance_binding setup mode runtime leaks
              anchor.execution phase _ remaining who execution joint response selected material
                sent event (who, .prepared serial) packet payload binding code middleAttempt inside
                  ready']
            simp only [phaseProposalPreparedBindingAction, resultEq]
            rfl
          have cylinder := (phaseProposalEmissionFrontier_binding_step setup mode runtime leaks
            bounds plan (setup.initialLaw.map encodeInputs) fuel serviceScheduler anchor.execution
              phase anchorTrace.length first remaining who execution earlier joint legal response
                selected reached material sent event payload binding code request inside
                  middleAttempt retained.length_le frame.emissions ready').2
          apply posterior_append_observation law (observed execution)
            (observed (execution.respond (app) who response))
            (fun key => (⟨.inr event, binding⟩ : FieldRef graph.layout
              (.binding who payload)).get? key.2.1) (some (.success value))
            (graph.canonicalContinuation profile (frontier earlier))
            (graph.canonicalContinuation profile (frontier (earlier.extend joint legal reached)))
            oldPresent oldLaw rowPresent (by rw [stepF]; exact rowLaw.symm)
          intro key supported
          obtain ⟨config, rfl⟩ := represent key supported
          rw [read, read, cylinder config, resultEq]
          rfl
      | none =>
        have stepF : frontier (earlier.extend joint legal reached) = frontier earlier := by
          dsimp only [frontier]
          rw [ReactiveApplication.ResponseMenu.toRawTrace, phaseProposalEmissionFrontier,
            ite_eq_left (by simpa only [(menu).toRawTrace_length] using retained.length_le)]
          exact phaseProposalBindingFrontierAdvance_idle setup mode runtime leaks _ _ _ _ _ joint
        rw [stepF]
        cases remaining with
        | zero =>
          have equal := (PMF.mem_support_pure_iff _ _).mp actual
          cases Option.some.inj equal
          exact ⟨oldPresent, oldLaw⟩
        | succ remaining =>
          rw [ReactiveApplication.transition, PMF.mem_support_bind_iff] at actual
          obtain ⟨command, _chosen, moved⟩ := actual
          obtain ⟨after, moved, equal⟩ := (PMF.mem_support_map_iff ..).mp moved
          have executionEq : next.execution = after :=
            congrArg ReactiveApplication.Control.execution (Option.some.inj equal.symm)
          have same : ∀ key ∈ law.support,
              observed next.execution key = true ↔ observed execution key = true := by
            intro key supported
            obtain ⟨config, rfl⟩ := represent key supported
            rw [executionEq, read, read]
            exact (phaseProposalEmittedBindings_environment runtime leaks bounds plan
              (setup.initialLaw.map encodeInputs) fuel serviceScheduler
                ⟨remaining + 1, none, execution⟩ earlier after command moved phase config
                  (by simpa only [executionEq] using middleAttempt.trans nextAttempt.symm)).symm
          obtain ⟨key, supported, measured⟩ := (PMF.mem_support_map_iff ..).mp oldPresent
          refine ⟨(PMF.mem_support_map_iff ..).mpr
            ⟨key, supported, (same key supported).mpr measured⟩, ?_⟩
          exact oldLaw.trans (fiberPosterior_eq_of_support_fiber law _ _ true true
            (fun key supported => (same key supported).symm))
  obtain ⟨next, equal, _ordered, _generation, _phase, _excluded, result⟩ := along trace kept
  cases Option.some.inj equal
  exact result attempt excluded proper

omit [Fintype Player] in
/-- Full erased-history equality retains the literal public signal list. -/
theorem source_publicRecall_eq_of_erasedHistory
    (first second : setup.proposalRecoveryProtocol.History)
    (same : setup.proposalRecoveryErasedHistory first =
      setup.proposalRecoveryErasedHistory second) (who : Player) :
    setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace first.trace) =
      setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace second.trace) := by
  have information := congrFun (congrArg Prod.snd (congrArg Prod.fst same)) who
  change setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace first.trace)) =
    setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace second.trace))
    at information
  rw [setup.erasedInformation_publicRecall, setup.erasedInformation_publicRecall] at information
  have tails := congrArg (fun info => info.1.2) information
  have privateViews := congrArg (fun info => info.1.1.1) information
  have controls := congrArg (fun info => info.1.1.2) information
  have publicViews := congrArg (Option.map (ProtocolView.publicOnly who setup.program))
    privateViews
  simp only [Option.map_map, Function.comp_def, ProtocolView.publicOnly_eraseHistory] at publicViews
  have heads : setup.attemptPublicSignal who first.state =
      setup.attemptPublicSignal who second.state := Prod.ext publicViews controls
  have restore (history : setup.proposalRecoveryProtocol.History) :
      setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace history.trace) =
        setup.attemptPublicSignal who history.state ::
          (setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace history.trace)).tail
            := by
    unfold SourceProgram.Setup.attemptPublicRecall SourceProgram.Setup.attemptPublicSignal
    simp only [List.map_cons, List.tail_cons, setup.commitRecoverySignals_current]
  change (setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace first.trace)).tail =
    (setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace second.trace)).tail at tails
  rw [restore first, restore second, heads]
  exact congrArg (List.cons _) tails

/-- Replace only the source memories in an ordinary entry cursor. The physical
anchor, typed dictionaries and frozen graph configuration remain literal. -/
def PhaseProposalOrdinarySourceCursor.of_erasedHistory
    (anchor : (app).Control) (phase : RuntimePhase (serviceGraph setup mode))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
      block suffix)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (same : setup.proposalRecoveryErasedHistory ⟨some cursor.current, cursor.trace⟩ =
      setup.proposalRecoveryErasedHistory ⟨some current, trace⟩) :
    PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase block suffix := by
  have states : cursor.current.eraseHistory = current.eraseHistory :=
    Option.some.inj (congrArg Prod.fst (congrArg Prod.fst same))
  have excluded : cursor.current.excluded = current.excluded := congrArg (·.excluded) states
  have entryExcluded : cursor.current.entryExcluded = current.entryExcluded :=
    congrArg (·.entryExcluded) states
  have generation : cursor.current.generation = current.generation :=
    congrArg (·.generation) states
  have saved : ProtocolState.withHistory setup.program cursor.current.saved (fun _ => []) =
      ProtocolState.withHistory setup.program current.saved (fun _ => []) :=
    congrArg (·.saved) states
  have points : ProtocolState.withHistory setup.program cursor.current.point (fun _ => []) =
      ProtocolState.withHistory setup.program current.point (fun _ => []) :=
    congrArg (·.point) states
  have point : current.point = cursor.lift (ProtocolState.entry (block.prepend suffix)
      {cursor.source with history := ProtocolState.history setup.program current.point}) := by
    have replaced := congrArg
      (fun point => ProtocolState.withHistory setup.program point
        (ProtocolState.history setup.program current.point)) points
    simp only [ProtocolState.withHistory_withHistory, ProtocolState.withHistory_history] at replaced
    rw [cursor.point, ← cursor.origin.withHistory_lift, ProtocolState.withHistory_entry]
      at replaced
    exact replaced.symm
  have publicEq : setup.commitRecoveryPublic (some cursor.current) =
      setup.commitRecoveryPublic (some current) := by
    have ranks := congrArg (ProtocolState.remaining setup.program) saved
    simp only [ProtocolState.remaining_withHistory] at ranks
    simp only [SourceProgram.Setup.commitRecoveryPublic, excluded, generation, ranks]
  refine { cursor with
    source := {cursor.source with history := ProtocolState.history setup.program current.point}
    current := current
    trace := trace
    point := point
    agrees := cursor.agrees
    excluded := excluded ▸ cursor.excluded
    entryExcluded := entryExcluded ▸ cursor.entryExcluded
    savedCommit := ?_
    savedEnd := ?_
    live := ?_
    ahead := excluded ▸ cursor.ahead
    controls := ?_
    addresses := ?_
    proposals := ?_ }
  · intro positive
    have committing := congrArg (ProtocolState.atCommit setup.program) saved
    rw [(ProtocolState.withHistory_control _ _ _).2.1,
      (ProtocolState.withHistory_control _ _ _).2.1] at committing
    exact committing ▸ cursor.savedCommit positive
  · intro positive
    have endpoint := congrArg (ProtocolState.commitEnd setup.program) saved
    simp only [ProtocolState.commitEnd_withHistory] at endpoint
    exact endpoint ▸ cursor.savedEnd positive
  · intro who active
    exact cursor.live who (by simpa only [excluded] using active)
  · intro positive
    rw [← publicEq]
    exact cursor.controls positive
  · intro positive who
    rw [← source_publicRecall_eq_of_erasedHistory setup
      ⟨some cursor.current, cursor.trace⟩ ⟨some current, trace⟩ same who]
    exact cursor.addresses positive who
  · intro who active
    rw [← setup.proposalRecoveryArchive_eq_of_erased_history
      ⟨some cursor.current, cursor.trace⟩ ⟨some current, trace⟩ same who]
    exact cursor.proposals who (by simpa only [excluded] using active)

/-- Conditioning the complete ordinary source/graph coupling retains both
literal histories and their common issued-value cylinder. -/
theorem phaseProposalBindingPotentialProfile_conditioned_source_block_coupling
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (anchor : (app).Control)
    (anchorTrace : ((app).protocol initial horizon scheduler).Trace (some anchor))
    (phase : RuntimePhase (serviceGraph setup mode))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
      block suffix)
    (sourceObserved : setup.proposalRecoveryProtocol.History → Bool)
    (graphObserved : (serviceGraph setup mode).SemanticKey → Bool)
    (agrees : ∀ pair, PhaseProposalOrdinarySourceBlockResult setup mode block suffix
        cursor.refs cursor.embedding cursor.lift cursor.source cursor.current cursor.trace pair →
      sourceObserved pair.1 = graphObserved pair.2)
    (present : true ∈ (((serviceGraph setup mode).canonicalContinuation
      (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor.execution phase
        values) cursor.config).map graphObserved).support) :
    ∃ joint : PMF (setup.proposalRecoveryProtocol.History ×
        (serviceGraph setup mode).SemanticKey),
      joint.map Prod.fst = fiberPosterior
        (setup.proposalRecoveryModel.runBehavioralFrom
          (setup.proposalRecoveryNormalizedTrembledProfile
            0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
          block.length ⟨some cursor.current, cursor.trace⟩) sourceObserved true ∧
      joint.map Prod.snd = fiberPosterior
        ((serviceGraph setup mode).canonicalContinuation
          (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor.execution phase
            values) cursor.config) graphObserved true ∧
      (∀ pair ∈ joint.support,
        PhaseProposalOrdinarySourceBlockResult setup mode block suffix cursor.refs
          cursor.embedding cursor.lift cursor.source cursor.current cursor.trace pair ∧
        sourceObserved pair.1 = true ∧ graphObserved pair.2 = true) := by
  classical
  obtain ⟨ordinary, sourceMarginal, graphMarginal, supported, _fillMarginal⟩ :=
    phaseProposalBindingPotentialProfile_source_block_coupling setup mode runtime leaks plan
      initial horizon scheduler anchor anchorTrace phase values block suffix cursor
  have graphPresent : true ∈ (ordinary.map (graphObserved ∘ Prod.snd)).support := by
    rw [← PMF.map_comp, graphMarginal]
    exact present
  have sourcePresent : true ∈ (ordinary.map (sourceObserved ∘ Prod.fst)).support := by
    obtain ⟨pair, member, observed⟩ := (PMF.mem_support_map_iff ..).mp graphPresent
    exact (PMF.mem_support_map_iff ..).mpr
      ⟨pair, member, (agrees pair (supported pair member)).trans observed⟩
  have same : fiberPosterior ordinary (graphObserved ∘ Prod.snd) true =
      fiberPosterior ordinary (sourceObserved ∘ Prod.fst) true := by
    apply fiberPosterior_eq_of_support_fiber
    intro pair member
    rw [Function.comp_apply, Function.comp_apply, agrees pair (supported pair member)]
  let joint := fiberPosterior ordinary (graphObserved ∘ Prod.snd) true
  refine ⟨joint, ?_, ?_, ?_⟩
  · change (fiberPosterior ordinary (graphObserved ∘ Prod.snd) true).map Prod.fst = _
    rw [same, map_fiberPosterior_readout ordinary Prod.fst sourceObserved true sourcePresent,
      sourceMarginal]
  · change (fiberPosterior ordinary (graphObserved ∘ Prod.snd) true).map Prod.snd = _
    rw [map_fiberPosterior_readout ordinary Prod.snd graphObserved true graphPresent,
      graphMarginal]
  · intro pair member
    have retained := mem_support_fiberPosterior graphPresent member
    have result := supported pair retained.2
    exact ⟨result, (agrees pair result).trans retained.1, retained.1⟩

end EmissionConditioning


open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open scoped ENNReal

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (values : ∀ who (key : setup.ProposalRecoveryComponent who),
    PMF (setup.CommitRecoveryValueChoice who key.1))

/-- The original ordinary source policy with all future flags zero. -/
def sourceUnflaggedStrategy : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who :=
  setup.proposalRecoveryNormalizedTrembledProfile
    0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values

/-- The actual remaining commitment instructions, including the closing row. -/
def sourceCommitFuel (history : setup.proposalRecoveryProtocol.History) : Nat :=
  history.state.elim 0 fun current =>
    ProtocolState.remaining setup.program current.point -
      ProtocolState.commitEnd setup.program current.point

open Classical in
/-- Insert a choice at the actual source information, then run the original
zero-flag kernel through the remaining commitment instructions. -/
def sourceForcedBlock (who : Player) (history : setup.proposalRecoveryProtocol.History)
    (choice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who history.trace)) :
    PMF setup.proposalRecoveryProtocol.History :=
  let profile := sourceUnflaggedStrategy setup values
  (setup.proposalRecoveryModel.runBehavioralFrom
    (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) profile who
      ((profile who).commit (setup.proposalRecoveryModel.infoOf who history.trace) choice))
    1 history).bind
      (setup.proposalRecoveryModel.runBehavioralFrom profile (sourceCommitFuel setup history - 1))

omit [Fintype Player] in
private theorem suffix_injective
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) : Function.Injective lift := by
  induction origin with
  | initial => exact Function.injective_id
  | sampleTail fresh law next previous ih =>
      exact fun _ _ same => Sum.inr.inj (ih same)
  | commitTail fresh guard next previous ih =>
      exact fun _ _ same => Sum.inr.inj (ih same)
  | revealTail fresh selected unresolved next previous ih =>
      exact fun _ _ same => Sum.inr.inj (ih same)

open Classical in
/-- Pull a point through the actual suffix and its entry constructor. This
partial inverse does not inspect a source posterior or a selected source tag. -/
def residualEntry?
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} (program : SourceProgram Player L Γ O)
    (lift : ProtocolState program → ProtocolState whole) (point : ProtocolState whole) :
    Option (SourceProgram.Config Player L Γ) :=
  if present : ∃ entry, lift (ProtocolState.entry program entry) = point then
    some (Classical.choose present)
  else none

omit [Fintype Player] in
theorem residualEntry?_eq_some_iff
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) (point : ProtocolState whole)
    (entry : SourceProgram.Config Player L Γ) :
    residualEntry? program lift point = some entry ↔
      lift (ProtocolState.entry program entry) = point := by
  classical
  unfold residualEntry?
  split_ifs with present
  · constructor
    · intro same
      have chosen := Classical.choose_spec present
      exact Option.some.inj same ▸ chosen
    · intro same
      congr 1
      apply ProtocolState.entry_injective program
      apply suffix_injective origin
      exact (Classical.choose_spec present).trans same.symm
  · constructor
    · intro impossible
      cases impossible
    · intro same
      exact False.elim (present ⟨entry, same⟩)

omit [Fintype Player] in
private theorem residualEntry?_entry
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) (entry : SourceProgram.Config Player L Γ) :
    residualEntry? program lift (lift (ProtocolState.entry program entry)) = some entry :=
  (residualEntry?_eq_some_iff origin _ entry).mpr rfl



section NativeCheckpoint

variable (implementation : ReservedConcurrentImplementation setup)

local notation "nativeApplication" => implementation.application
local notation "nativeMenu" => PhaseCount.onePacketMenu implementation.runtime
  implementation.leaks implementation.bounds
local notation "nativeInitial" => implementation.initial
local notation "nativeProtocol" =>
  ReactiveApplication.ResponseMenu.protocol
    (PhaseCount.onePacketMenu implementation.runtime implementation.leaks
      implementation.bounds) implementation.initial
      implementation.horizon implementation.scheduler
local notation "sourceModel" => setup.proposalRecoveryModel

/-- Read an actual native trace at the source cut's two-stage initializer.
Only the equal PMF representation changes; its controls and responses stay literal. -/
def sourceCutTrace {state : (nativeProtocol).State}
    (trace : (nativeProtocol).Trace state) :
    ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace state :=
  (show ((setup.initialLaw.map encodeInputs).map
    (PhaseRuntimeState.initial implementation.plan)) = nativeInitial from
      PMF.map_comp _ _ _).symm ▸ trace

theorem trace_initializer_inverse
    {first second : PMF (nativeApplication).State} (same : first = second)
    {state : (nativeProtocol).State}
    (trace : ((nativeMenu).protocol second implementation.horizon
      implementation.scheduler).Trace state) :
    same ▸ (same.symm ▸ trace) = trace := by
  cases same
  rfl

private theorem trace_initializer_length
    {first second : PMF (nativeApplication).State} (same : first = second)
    {state : (nativeProtocol).State}
    (trace : ((nativeMenu).protocol first implementation.horizon
      implementation.scheduler).Trace state) :
    (same ▸ trace).length = trace.length := by
  cases same
  rfl

theorem tracePrefix_initializer
    {first second : PMF (nativeApplication).State} (same : first = second)
    {before after : (nativeProtocol).State}
    {prior : ((nativeMenu).protocol first implementation.horizon
      implementation.scheduler).Trace before}
    {trace : ((nativeMenu).protocol first implementation.horizon
      implementation.scheduler).Trace after}
    (retained : TracePrefix prior trace) :
    TracePrefix (same ▸ prior) (same ▸ trace) := by
  cases same
  exact retained

private theorem generated_initializer
    {first second : PMF (nativeApplication).State} (same : first = second)
    {state : (nativeProtocol).State}
    (trace : ((nativeMenu).protocol first implementation.horizon
      implementation.scheduler).Trace state) (owner : Player) :
    PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
      implementation.bounds second implementation.horizon implementation.scheduler owner
        ⟨state, same ▸ trace⟩ ↔
      PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds first implementation.horizon implementation.scheduler owner
          ⟨state, trace⟩ := by
  cases same
  rfl

private theorem emissionFrontier_initializer
    {first second : PMF (nativeApplication).State} (same : first = second)
    {before state : (nativeProtocol).State}
    (prior : ((nativeMenu).protocol first implementation.horizon
      implementation.scheduler).Trace before)
    (trace : ((nativeMenu).protocol first implementation.horizon
      implementation.scheduler).Trace state)
    (entry : (nativeApplication).Execution)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (config : (serviceGraph setup .concurrent).Config) :
    phaseProposalEmissionFrontier setup .concurrent implementation.runtime implementation.leaks
      entry phase (same ▸ prior).length config second implementation.horizon
        implementation.scheduler
        ((nativeMenu).toRawTrace second implementation.horizon implementation.scheduler
          (same ▸ trace)) =
      phaseProposalEmissionFrontier setup .concurrent implementation.runtime implementation.leaks
        entry phase prior.length config first implementation.horizon implementation.scheduler
          ((nativeMenu).toRawTrace first implementation.horizon implementation.scheduler trace)
            := by
  cases same
  rfl

open Classical in
def sourceBindingAt
    (attempt : CommitAttemptId) (event : (serviceGraph setup .concurrent).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload) :
    ∀ {state}, setup.proposalRecoveryProtocol.Trace state → Option (L.Val payload)
  | _, .start => none
  | _, @Trace.extend _ _ before _ prior joint _ _ =>
      match before with
      | none => sourceBindingAt attempt event owner payload binding prior
      | some current =>
        if current.generation = attempt.generation ∧
            instructionCount setup.program -
              ProtocolState.remaining setup.program current.saved = attempt.phase ∧
            instructionCount setup.program -
              ProtocolState.remaining setup.program current.point = event.val then
          match phaseRecoveryBindingData setup .concurrent event owner payload binding
              ((joint owner).map (·.semantic)) with
          | (.success value, false) => some value
          | _ => none
        else sourceBindingAt attempt event owner payload binding prior

omit [Fintype Player] in
private theorem sourceBindingAt_extend
    (attempt : CommitAttemptId) (event : (serviceGraph setup .concurrent).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (current : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (after : setup.proposalRecoveryProtocol.State)
    (realized : after ∈ (setup.proposalRecoveryProtocol.step (some current)
      ⟨joint, legal⟩).support)
    (generation : current.generation = attempt.generation)
    (saved : instructionCount setup.program -
      ProtocolState.remaining setup.program current.saved = attempt.phase)
    (position : instructionCount setup.program -
      ProtocolState.remaining setup.program current.point = event.val)
    (value : L.Val payload)
    (read : phaseRecoveryBindingData setup .concurrent event owner payload binding
      ((joint owner).map (·.semantic)) = (.success value, false)) :
    sourceBindingAt setup attempt event owner payload binding
      (prior.extend joint legal realized) = some value := by
  simp only [sourceBindingAt, generation, saved, position, and_self, ↓reduceIte]
  exact congrArg (fun data : PublicationResult (L.Val payload) × Bool =>
    match data with
    | (.success result, false) => some result
    | _ => none) read

omit [Fintype Player] in
private theorem sourceBindingAt_other_address
    (attempt : CommitAttemptId) (event : (serviceGraph setup .concurrent).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (current : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (after : setup.proposalRecoveryProtocol.State)
    (realized : after ∈ (setup.proposalRecoveryProtocol.step (some current)
      ⟨joint, legal⟩).support)
    (different : ¬ (current.generation = attempt.generation ∧
      instructionCount setup.program -
        ProtocolState.remaining setup.program current.saved = attempt.phase ∧
      instructionCount setup.program -
        ProtocolState.remaining setup.program current.point = event.val)) :
    sourceBindingAt setup attempt event owner payload binding
        (prior.extend joint legal realized) =
      sourceBindingAt setup attempt event owner payload binding prior := by
  simp only [sourceBindingAt, different, ↓reduceIte]

omit [Fintype Player] in
theorem sourceBindingAt_origin
    (attempt : CommitAttemptId) (event : (serviceGraph setup .concurrent).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    {state} (trace : setup.proposalRecoveryProtocol.Trace state) (value : L.Val payload)
    (read : sourceBindingAt setup attempt event owner payload binding trace = some value) :
    ∃ (current : CommitRecoveryState setup.program)
      (prior : setup.proposalRecoveryProtocol.Trace (some current))
      (joint : Player → Option (ProposalRecoveryMove Player L))
      (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
      (after : setup.proposalRecoveryProtocol.State)
      (realized : after ∈ (setup.proposalRecoveryProtocol.step (some current)
        ⟨joint, legal⟩).support),
      TracePrefix (prior.extend joint legal realized) trace ∧
      current.generation = attempt.generation ∧
      instructionCount setup.program -
        ProtocolState.remaining setup.program current.saved = attempt.phase ∧
      instructionCount setup.program -
        ProtocolState.remaining setup.program current.point = event.val ∧
      phaseRecoveryBindingData setup .concurrent event owner payload binding
        ((joint owner).map (·.semantic)) = (.success value, false) := by
  induction trace with
  | start => cases read
  | @extend before after prior joint legal realized ih =>
      cases before with
      | none =>
          obtain ⟨current, source, choices, offered, target, moved, priorPrefix, rest⟩ := ih read
          exact ⟨current, source, choices, offered, target, moved,
            TracePrefix.extend priorPrefix joint legal realized, rest⟩
      | some current =>
          by_cases addressed : current.generation = attempt.generation ∧
              instructionCount setup.program -
                ProtocolState.remaining setup.program current.saved = attempt.phase ∧
              instructionCount setup.program -
                ProtocolState.remaining setup.program current.point = event.val
          · have row : phaseRecoveryBindingData setup .concurrent event owner payload binding
                ((joint owner).map (·.semantic)) = (.success value, false) := by
              simp only [sourceBindingAt, addressed] at read
              cases data : phaseRecoveryBindingData setup .concurrent event owner payload binding
                  ((joint owner).map (·.semantic)) with
              | mk result omitted =>
                  cases result <;> cases omitted <;> simp_all
            exact ⟨current, prior, joint, legal, after, realized, .refl,
              addressed.1, addressed.2.1, addressed.2.2, row⟩
          · have earlier : sourceBindingAt setup attempt event owner payload binding prior =
                some value := by
              simpa only [sourceBindingAt, addressed, ↓reduceIte] using read
            obtain ⟨sourceState, source, choices, offered, target, moved, priorPrefix, rest⟩ :=
              ih earlier
            exact ⟨sourceState, source, choices, offered, target, moved,
              TracePrefix.extend priorPrefix joint legal realized, rest⟩

omit [Fintype Player] in
theorem source_initial_base_supported
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current)) :
    ProtocolState.base setup.program current.point ∈ setup.initialLaw.support ∧
      ProtocolState.base setup.program current.saved =
        ProtocolState.base setup.program current.point := by
  have invariant : ∀ {state : setup.commitRecoveryProtocol.State}
      (prior : setup.commitRecoveryProtocol.Trace state),
      state.elim True (fun current =>
        ProtocolState.base setup.program current.point ∈ setup.initialLaw.support ∧
          ProtocolState.base setup.program current.saved =
            ProtocolState.base setup.program current.point) := by
    intro state prior
    induction prior with
    | start => trivial
    | @extend before after prior joint legal reached ih =>
        cases before with
        | none =>
            obtain ⟨theta, supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp reached
            exact ⟨by simpa only [CommitRecoveryState.atPoint, ProtocolState.base_entry,
              Setup.initialConfig] using supported, rfl⟩
        | some before =>
            obtain ⟨after, moved, rfl⟩ := (PMF.mem_support_map_iff ..).mp reached
            have bases := before.step_base (ProtocolState.base setup.program before.point)
              rfl ih.2 joint after moved
            exact ⟨bases.1.symm ▸ ih.1, bases.2.trans bases.1.symm⟩
  exact invariant (setup.proposalRecoveryEraseTrace trace)

def source_native_initializer
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current)) :
    (nativeProtocol).Trace (some ⟨implementation.horizon, none,
      ReactiveApplication.Execution.initial nativeApplication
        (PhaseRuntimeState.initial implementation.plan
          (encodeInputs (ProtocolState.base setup.program current.point)))⟩) := by
  let joint : Player → Option (nativeApplication).Action := fun _ => none
  have legal : (nativeProtocol).Legal none joint := by
    constructor
    · simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.terminal]
    · intro who
      simp [joint, ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor]
  have moved : some (⟨implementation.horizon, none,
      ReactiveApplication.Execution.initial nativeApplication
        (PhaseRuntimeState.initial implementation.plan
          (encodeInputs (ProtocolState.base setup.program current.point)))⟩ :
        (nativeApplication).Control) ∈
      ((nativeProtocol).step none ⟨joint, legal⟩).support := by
    change _ ∈ ((setup.initialLaw.map fun theta =>
      PhaseRuntimeState.initial implementation.plan (encodeInputs theta)).map fun state =>
        some (⟨implementation.horizon, none,
          ReactiveApplication.Execution.initial nativeApplication state⟩ :
          (nativeApplication).Control)).support
    apply (PMF.mem_support_map_iff ..).mpr
    refine ⟨_, (PMF.mem_support_map_iff ..).mpr ?_, rfl⟩
    exact ⟨ProtocolState.base setup.program current.point,
      (source_initial_base_supported setup current trace).1, rfl⟩
  exact Trace.start.extend joint legal moved

omit [Fintype Player] in
private theorem source_initial_observation (who : Player)
    (first second : Vegas.State L setup.context)
    (same : sourceObserve who first = sourceObserve who second) :
    (serviceGraph setup .concurrent).playerObserve who
        (EventGraph.Config.initial (encodeInputs first)) =
      (serviceGraph setup .concurrent).playerObserve who
        (EventGraph.Config.initial (encodeInputs second)) := by
  let refs := ContextRefs.initial setup.context (outputLayout setup.program)
  have observed (state : Vegas.State L setup.context) :=
    checkpoint_playerStore setup (mode := .concurrent) refs 0
      (ContextRefs.initial_coversPrefix setup.program)
      (EventGraph.Config.initial (encodeInputs state))
      (EventOrder.Cut.empty_isPrefix (serviceGraph setup .concurrent).order)
      state (initialConfig_agrees setup.program state) who
  refine EventGraph.PlayerObservation.ext (serviceGraph setup .concurrent) ?_ ?_ ?_
  · rfl
  · exact (observed first).trans ((congrArg (encodeObservationStore who refs) same).trans
      (observed second).symm)
  · rfl

omit [Fintype Player] in
theorem source_address_prefix
    {first last : setup.commitRecoveryProtocol.State}
    {prior : setup.commitRecoveryProtocol.Trace first}
    {trace : setup.commitRecoveryProtocol.Trace last}
    (retained : TracePrefix prior trace) :
    (setup.recoveryAddressWord prior).IsPrefix (setup.recoveryAddressWord trace) := by
  induction retained with
  | refl => exact ⟨[], by simp only [List.append_nil]⟩
  | @extend source target earlier retained joint legal realized ih =>
      obtain ⟨tail, word⟩ := ih
      refine ⟨tail ++ [target.elim (none, (∅, 0, 0)) CommitRecoveryState.publicAddress], ?_⟩
      rw [setup.recoveryAddressWord_extend, ← word, List.append_assoc]

omit [Fintype Player] in
theorem source_address_length
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.recoveryAddressWord trace).length = trace.length := by
  induction trace with
  | start => rfl
  | extend prior joint legal realized ih =>
      simp only [setup.recoveryAddressWord_extend, List.length_append,
        List.length_singleton, Trace.length, ih]

omit [Fintype Player] in
private theorem source_row_addresses
    (current next : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some current))
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal (some current) joint)
    (realized : some next ∈
      (setup.commitRecoveryProtocol.step (some current) ⟨joint, legal⟩).support)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state)
    (retained : TracePrefix (prior.extend joint legal realized) trace) :
    ∃ index, index + 1 < trace.length ∧
      (setup.recoveryAddressWord trace)[index]? = some current.publicAddress ∧
      (setup.recoveryAddressWord trace)[index + 1]? = some next.publicAddress := by
  have endpoint : ∀ {state : setup.commitRecoveryProtocol.State}
      (path : setup.commitRecoveryProtocol.Trace state)
      (current : CommitRecoveryState setup.program),
      state = some current → ∃ index, path.length = index + 1 ∧
        (setup.recoveryAddressWord path)[index]? = some current.publicAddress := by
    intro state path
    cases path with
    | start => intro current impossible; cases impossible
    | @extend before after earlier actions offered moved =>
        intro current equal
        cases equal
        refine ⟨earlier.length, rfl, ?_⟩
        rw [setup.recoveryAddressWord_extend, List.getElem?_append_right
          (by rw [source_address_length]), source_address_length, Nat.sub_self]
        rfl
  obtain ⟨index, depth, last⟩ := endpoint prior current rfl
  have bounded := retained.length_le
  obtain ⟨tail, word⟩ := source_address_prefix setup retained
  refine ⟨index, by simp only [Trace.length, depth] at bounded; omega, ?_, ?_⟩
  · rw [← word, setup.recoveryAddressWord_extend, List.append_assoc,
      List.getElem?_append_left (by rw [source_address_length, depth]; omega)]
    exact last
  · rw [← word, setup.recoveryAddressWord_extend, List.append_assoc,
      List.getElem?_append_right (by rw [source_address_length, depth]),
      source_address_length, depth, Nat.sub_self]
    rfl

theorem source_checkpoint_binding_interval
    {state : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (witness : RecoverySourceWitness setup .concurrent implementation.plan state)
    (maximal : implementation.plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (rest : List (RuntimePhase (serviceGraph setup .concurrent)))
    (installed : state.phases = phase :: rest) (kind : phase.kind = .commitment) :
    let point := witness.checkpoint.residual.lift
      (ProtocolState.entry witness.checkpoint.residual.tail witness.checkpoint.source)
    ProtocolState.atCommit setup.program point = true ∧
      instructionCount setup.program - ProtocolState.remaining setup.program point = phase.low ∧
      instructionCount setup.program -
        ProtocolState.commitEnd setup.program point = phase.high := by
  have low : state.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons,
      Option.map_some, Option.getD_some]
  have committing := witness.checkpoint.compiled.atCommit_of_bindingPhase setup.program
    .concurrent witness.checkpoint.residual.tail witness.checkpoint.refs
    witness.checkpoint.source.revelations witness.checkpoint.registry witness.checkpoint.embedding
    witness.checkpoint.before state.attempt.phase phase kind low.symm witness.checkpoint.source
  have positioned := witness.checkpoint.saved_position
  have adjacent := witness.receipts.exclusion.frontier.adjacent
  have ending := witness.receipts.exclusion.frontier.last
  have chain := maximal.suffix witness.suffix
  rw [installed] at adjacent ending chain
  rcases witness with ⟨checkpoint, aligned, chronology, origins, native, binding, receipts,
    stored, remembered, order, suffixMember, archives, exclusions, failures⟩
  dsimp only at committing positioned ⊢
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, terminalAlignment, agrees, guards, preserves, unique, remaining, actor, atCommit,
    owners, commitEnd, automatic, history, withHistory, step, menus, readout, sourceTrace, views,
    historyAlignment, origin⟩
  dsimp only at committing positioned ⊢
  rcases commitPhase program with ⟨Δ, P, tail, block, reconstruct, boundary⟩
  subst program
  have positive : 0 < block.length := by
    cases block with
    | nil =>
        cases tail with
        | ret => cases committing
        | sample => cases committing
        | reveal => cases committing
        | commit => cases boundary
    | commit => simp only [CommitPrefix.length]; omega
  have exactPhase := compiledCommitPhase_eq_of_maximal setup.program .concurrent block tail
    embedding compiled positive boundary phase rest adjacent ending chain low.symm
  refine ⟨(atCommit _).trans committing, positioned.trans low, ?_⟩
  rw [commitEnd, block.commitEnd_entry_prepend tail boundary]
  have ranks := positioned
  rw [remaining, ProtocolState.remaining_entry, block.instructionCount_prepend] at ranks
  have bounded := ProtocolState.remaining_le_instructionCount setup.program
    (lift (ProtocolState.entry (block.prepend tail) source))
  rw [remaining, ProtocolState.remaining_entry, block.instructionCount_prepend] at bounded
  rw [exactPhase]
  change instructionCount setup.program - instructionCount tail =
    state.attempt.phase + block.length
  omega

omit [Fintype Player] in
theorem source_commit_rank_before_exit
    (distance : Nat) (start : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some start))
    (committing : ProtocolState.atCommit setup.program start.point = true)
    (rank : Nat)
    (position : rank = instructionCount setup.program -
      ProtocolState.remaining setup.program start.point + distance)
    (inside : rank < instructionCount setup.program -
      ProtocolState.commitEnd setup.program start.saved)
    (final : setup.commitRecoveryProtocol.History) (fuel : Nat)
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel ⟨some start, prior⟩ final)
    (enough : final.state.map (fun state => state.publicAddress.2.2) ≠
      some start.publicAddress.2.2 ∨ prior.length + distance < final.trace.length) :
    ∃ (current next : CommitRecoveryState setup.program)
      (retainedTrace : setup.commitRecoveryProtocol.Trace (some current))
      (joint : Player → Option (CommitRecoveryMove Player L))
      (legal : setup.commitRecoveryProtocol.Legal (some current) joint)
      (realized : some next ∈
        (setup.commitRecoveryProtocol.step (some current) ⟨joint, legal⟩).support),
      TracePrefix prior retainedTrace ∧
      TracePrefix (retainedTrace.extend joint legal realized) final.trace ∧
      current.saved = start.saved ∧ current.generation = start.generation ∧
      retainedTrace.length = prior.length + distance ∧
      instructionCount setup.program -
        ProtocolState.remaining setup.program current.point = rank := by
  induction distance generalizing start fuel with
  | zero =>
      rcases path.eq_or_step with same | ⟨joint, legal, reached, realized, restFuel, rest⟩
      · rcases enough with exited | longer
        · exact (exited (congrArg (fun history => history.state.map
            (fun state => state.publicAddress.2.2)) same.symm)).elim
        · have lengths := congrArg (fun history => history.trace.length) same
          change prior.length = final.trace.length at lengths
          omega
      · obtain ⟨next, member, reachedEq⟩ :=
          (PMF.mem_support_map_iff _ _ _).mp realized
        subst reached
        exact ⟨start, next, prior, joint, legal, realized, .refl,
          rest.tracePrefix, rfl, rfl, by simp only [Nat.add_zero], by omega⟩
  | succ distance ih =>
      rcases path.eq_or_step with same | ⟨joint, legal, reached, realized, restFuel, rest⟩
      · rcases enough with exited | longer
        · exact (exited (congrArg (fun history => history.state.map
            (fun state => state.publicAddress.2.2)) same.symm)).elim
        · have lengths := congrArg (fun history => history.trace.length) same
          change prior.length = final.trace.length at lengths
          omega
      · obtain ⟨next, member, reachedEq⟩ :=
          (PMF.mem_support_map_iff _ _ _).mp realized
        subst reached
        have frontier := setup.commitRecovery_blockFrontier prior
        rcases start.step_commit_inside_or_exit frontier committing joint next member with
          ⟨saved, generation, nextCommit, consumed, _beforeEnd⟩ | ⟨_changed, last⟩
        · have nextPosition : rank = instructionCount setup.program -
              ProtocolState.remaining setup.program next.point + distance := by
            have bounded := ProtocolState.remaining_le_instructionCount
              setup.program start.point
            omega
          have nextInside : rank < instructionCount setup.program -
              ProtocolState.commitEnd setup.program next.saved := by rwa [saved]
          have sameNamespace : next.publicAddress.2.2 = start.publicAddress.2.2 := by
            simp only [CommitRecoveryState.publicAddress, saved, generation]
          have nextEnough : final.state.map (fun state => state.publicAddress.2.2) ≠
              some next.publicAddress.2.2 ∨
              (prior.extend joint legal realized).length + distance < final.trace.length := by
            rcases enough with exited | longer
            · exact Or.inl (by rwa [sameNamespace])
            · exact Or.inr (by simp only [Trace.length]; omega)
          obtain ⟨current, target, retainedTrace, actions, available, supported,
            initial, complete, sameSaved, sameGeneration, depth, atRank⟩ :=
              ih next (prior.extend joint legal realized) nextCommit nextPosition
                nextInside restFuel rest nextEnough
          exact ⟨current, target, retainedTrace, actions, available, supported,
            (TracePrefix.extend .refl joint legal realized).trans initial,
            complete, sameSaved.trans saved, sameGeneration.trans generation,
            by simpa only [Trace.length, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using depth, atRank⟩
        · have bounded := ProtocolState.remaining_le_instructionCount
            setup.program start.point
          omega

omit [Fintype Player] in
private theorem source_rank_address_transfer
    (start : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some start))
    (committing : ProtocolState.atCommit setup.program start.point = true)
    (rank : Nat) (lower : instructionCount setup.program -
      ProtocolState.remaining setup.program start.point ≤ rank)
    (upper : rank < instructionCount setup.program -
      ProtocolState.commitEnd setup.program start.saved)
    (final : setup.commitRecoveryProtocol.History) (fuel : Nat)
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel ⟨some start, prior⟩ final)
    (enough : final.state.map (fun state => state.publicAddress.2.2) ≠
      some start.publicAddress.2.2 ∨ prior.length +
        (rank - (instructionCount setup.program -
          ProtocolState.remaining setup.program start.point)) < final.trace.length)
    (target : setup.commitRecoveryProtocol.History)
    (word : (setup.recoveryAddressWord final.trace).IsPrefix
      (setup.recoveryAddressWord target.trace)) :
    ∃ index beforeExcluded afterExcluded nextRank nextGeneration nextLow,
      index + 1 < target.trace.length ∧
      (setup.recoveryAddressWord target.trace)[index]? =
        some (some rank, beforeExcluded, start.publicAddress.2.2) ∧
      (setup.recoveryAddressWord target.trace)[index + 1]? =
        some (nextRank, afterExcluded, nextGeneration, nextLow) := by
  obtain ⟨current, next, retainedTrace, joint, legal, realized, _initial, complete,
    saved, generation, _depth, positioned⟩ := source_commit_rank_before_exit setup
      (rank - (instructionCount setup.program -
        ProtocolState.remaining setup.program start.point)) start prior committing rank
      (by omega) upper final fuel path enough
  obtain ⟨index, bounded, first, second⟩ :=
    source_row_addresses setup current next retainedTrace joint legal realized final.trace complete
  obtain ⟨tail, word⟩ := word
  have sourceLength := source_address_length setup final.trace
  have targetLength := source_address_length setup target.trace
  have lengths := congrArg List.length word
  simp only [List.length_append] at lengths
  refine ⟨index, current.excluded, next.excluded, next.publicAddress.1,
    next.generation, instructionCount setup.program -
      ProtocolState.remaining setup.program next.saved, by omega, ?_, ?_⟩
  · rw [← word, List.getElem?_append_left (by omega), first]
    simp only [CommitRecoveryState.publicAddress, positioned, saved, generation]
  · rw [← word, List.getElem?_append_left (by omega), second]
    rfl

theorem attempt_exit_of_prefix
    (before : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before))
    {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state)
    (retained : TracePrefix prior trace)
    (different : state.map (fun control => control.execution.application.attempt) ≠
      some before.execution.application.attempt) :
    ∃ (source target : (nativeProtocol).State) (retainedTrace : (nativeProtocol).Trace source)
      (joint : Player → Option (nativeApplication).Action)
      (legal : (nativeProtocol).Legal source joint)
      (realized : target ∈ ((nativeProtocol).step source ⟨joint, legal⟩).support),
      TracePrefix prior retainedTrace ∧
      TracePrefix (retainedTrace.extend joint legal realized) trace ∧
        source.map (fun control => control.execution.application.attempt) =
          some before.execution.application.attempt ∧
        target.map (fun control => control.execution.application.attempt) ≠
          some before.execution.application.attempt := by
  revert different
  induction retained with
  | refl => intro different; exact (different rfl).elim
  | @extend source target retainedTrace earlier joint legal realized ih =>
      intro different
      by_cases changed : source.map (fun control => control.execution.application.attempt) ≠
          some before.execution.application.attempt
      · obtain ⟨oldSource, oldTarget, oldPrefix, oldJoint, oldLegal, oldRealized,
          initial, final, same, exited⟩ := ih changed
        exact ⟨oldSource, oldTarget, oldPrefix, oldJoint, oldLegal, oldRealized,
          initial, .extend final joint legal realized, same, exited⟩
      · exact ⟨source, target, retainedTrace, joint, legal, realized, earlier, .refl,
          Classical.not_not.mp changed, different⟩

open Classical in
def sourceHandleMeaning
    (target : setup.proposalRecoveryProtocol.History)
    (control : (nativeApplication).Control)
    (handle : Handle (serviceGraph setup .concurrent)) : Option (Raw L) :=
  match handle.2 with
  | .initial _ => target.state.bind fun current =>
      match (EventGraphRuntime.State.initial
          (graph := serviceGraph setup .concurrent)
          (encodeInputs (ProtocolState.base setup.program current.point))).candidates.lookup
          handle with
      | .openable raw => some raw
      | .fresh | .unopenable => none
  | .prepared _ =>
      (control.execution.recall handle.1).findSome? fun entry =>
        entry.emitted.bind fun message =>
          match message.payload.packet.call with
          | .commitment event candidate =>
              if candidate = handle then
                match binding : (serviceGraph setup .concurrent).outputLayout event with
                | .binding owner payload =>
                    (sourceBindingAt setup message.payload.attempt event owner payload binding
                      target.trace).map fun value => (⟨payload, value⟩ : Raw L)
                | _ => none
              else none
          | _ => none

def sourceHandlePairs
    (target : setup.proposalRecoveryProtocol.History)
    (control : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (handle : Handle (serviceGraph setup .concurrent)) : Option (Raw L × Raw L) :=
  match control.execution.application.current.native.candidates.lookup handle with
  | .openable before =>
      ((sourceHandleMeaning setup implementation target control handle).orElse
        (fun _ => lost handle)).map fun after => (before, after)
  | .fresh | .unopenable => none

omit [Fintype Player] in
private theorem sourceHandlePairs_maps
    (target : setup.proposalRecoveryProtocol.History)
    (control : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (handle : Handle (serviceGraph setup .concurrent)) (before after : Raw L)
    (registered : control.execution.application.current.native.candidates.lookup handle =
      .openable before)
    (read : sourceHandleMeaning setup implementation target control handle = some after) :
    EventGraph.pairSwap (sourceHandlePairs setup implementation target control lost handle)
      before = after := by
  classical
  simp only [sourceHandlePairs, registered, read, Option.orElse_some, Option.map_some,
    EventGraph.pairSwap, Equiv.swap_apply_left]

omit [Fintype Player] in
private theorem sourceHandlePairs_none_of_absent
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (handle : Handle (serviceGraph setup .concurrent))
    (absent : sourceHandleMeaning setup implementation target reference handle = none)
    (retained : lost handle = none) :
    sourceHandlePairs setup implementation target reference lost handle = none := by
  unfold sourceHandlePairs
  cases reference.execution.application.current.native.candidates.lookup handle <;>
    simp only [absent, retained, Option.orElse_none, Option.map_none]

omit [Fintype Player] in
private theorem sourceHandlePairs_involutive
    (target : setup.proposalRecoveryProtocol.History)
    (control : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (handle : Handle (serviceGraph setup .concurrent)) :
    Function.Involutive
      (EventGraph.pairSwap (sourceHandlePairs setup implementation target control lost handle)) :=
  EventGraph.pairSwap_involutive _

omit [Fintype Player] in
theorem sourceBindingAt_of_origin
    (attempt : CommitAttemptId) (event : (serviceGraph setup .concurrent).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (current : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (after : setup.proposalRecoveryProtocol.State)
    (realized : after ∈ (setup.proposalRecoveryProtocol.step (some current)
      ⟨joint, legal⟩).support)
    (generation : current.generation = attempt.generation)
    (saved : instructionCount setup.program -
      ProtocolState.remaining setup.program current.saved = attempt.phase)
    (position : instructionCount setup.program -
      ProtocolState.remaining setup.program current.point = event.val)
    (data : PublicationResult (L.Val payload) × Bool)
    (read : phaseRecoveryBindingData setup .concurrent event owner payload binding
      ((joint owner).map (·.semantic)) = data)
    {state} (trace : setup.proposalRecoveryProtocol.Trace state)
    (kept : TracePrefix (prior.extend joint legal realized) trace) :
    sourceBindingAt setup attempt event owner payload binding trace =
      (match data with
      | (.success value, false) => some value
      | _ => none) := by
  induction kept with
  | refl =>
      simp only [sourceBindingAt, generation, saved, position, and_self, ↓reduceIte]
      cases data with
      | mk result missing =>
          cases result <;> cases missing <;>
            exact congrArg (fun row : PublicationResult (L.Val payload) × Bool =>
              match row with
              | (.success value, false) => some value
              | _ => none) read
  | @extend source target later earlier choices offered reached ih =>
      cases source with
      | none => exact ih
      | some next =>
          by_cases addressed : next.generation = attempt.generation ∧
              instructionCount setup.program -
                ProtocolState.remaining setup.program next.saved = attempt.phase ∧
              instructionCount setup.program -
                ProtocolState.remaining setup.program next.point = event.val
          · have before : TracePrefix prior later :=
              (TracePrefix.extend .refl joint legal realized).trans earlier
            have same := setup.proposalRecovery_prefix_eq_of_same_cursor current next prior
              later before (by
                change some (current.generation, _) = some (next.generation, _)
                rw [generation, addressed.1, position, addressed.2.2])
            have lengths := congrArg
              (fun history : setup.proposalRecoveryProtocol.History => history.trace.length) same
            have lower := earlier.length_le
            change prior.length = later.length at lengths
            simp only [Trace.length] at lower
            omega
          · rw [sourceBindingAt_other_address setup attempt event owner payload binding
              next later choices offered target reached addressed]
            exact ih

omit [Fintype Player] in
theorem source_information_before
    (focal : Player) {leftBefore leftAfter rightBefore rightAfter}
    (left : setup.proposalRecoveryProtocol.Trace leftBefore)
    (right : setup.proposalRecoveryProtocol.Trace rightBefore)
    (leftJoint rightJoint : Player → Option (ProposalRecoveryMove Player L))
    (leftLegal : setup.proposalRecoveryProtocol.Legal leftBefore leftJoint)
    (rightLegal : setup.proposalRecoveryProtocol.Legal rightBefore rightJoint)
    (leftReached : leftAfter ∈ (setup.proposalRecoveryProtocol.step leftBefore
      ⟨leftJoint, leftLegal⟩).support)
    (rightReached : rightAfter ∈ (setup.proposalRecoveryProtocol.step rightBefore
      ⟨rightJoint, rightLegal⟩).support)
    (same : setup.proposalRecoveryModel.infoOf focal
        (left.extend leftJoint leftLegal leftReached) =
      setup.proposalRecoveryModel.infoOf focal
        (right.extend rightJoint rightLegal rightReached)) :
    setup.proposalRecoveryModel.infoOf focal left =
        setup.proposalRecoveryModel.infoOf focal right ∧
      leftJoint focal = rightJoint focal := by
  have pair := (setup.proposalRecoverySignals.withOwnPlayRecall_infoOf_eq_iff focal
    (left.extend leftJoint leftLegal leftReached)
    (right.extend rightJoint rightLegal rightReached)).mp same
  have previous : setup.proposalRecoverySignals.infoOf focal left =
      setup.proposalRecoverySignals.infoOf focal right := by
    have past := congrArg Prod.snd pair.1
    change (setup.proposalRecoverySignals.infoOf focal left).1 ::
        (setup.proposalRecoverySignals.infoOf focal left).2 =
      (setup.proposalRecoverySignals.infoOf focal right).1 ::
        (setup.proposalRecoverySignals.infoOf focal right).2 at past
    exact Prod.ext (List.cons.inj past).1 (List.cons.inj past).2
  have activity : setup.proposalRecoveryProtocol.active leftBefore focal ↔
      setup.proposalRecoveryProtocol.active rightBefore focal := by
    apply not_iff_not.mp
    change LegalOption setup.proposalRecoveryProtocol leftBefore focal none ↔
      LegalOption setup.proposalRecoveryProtocol rightBefore focal none
    rw [← setup.proposalRecoveryMenu_adequate focal left none,
      ← setup.proposalRecoveryMenu_adequate focal right none]
    rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf]
    change (¬ setup.proposalRecoveryActive focal
      (setup.proposalRecoverySignals.infoOf focal left).1) ↔
      (¬ setup.proposalRecoveryActive focal
        (setup.proposalRecoverySignals.infoOf focal right).1)
    rw [previous]
  have remembered := pair.2
  rw [InfoSignals.ownPlay_extend, InfoSignals.ownPlay_extend] at remembered
  have first := setup.proposalRecoveryProtocol.legalOption_of_legal leftLegal focal
  have second := setup.proposalRecoveryProtocol.legalOption_of_legal rightLegal focal
  have words : setup.proposalRecoverySignals.ownPlay focal left =
        setup.proposalRecoverySignals.ownPlay focal right ∧
      leftJoint focal = rightJoint focal := by
    cases lc : leftJoint focal with
    | none =>
        rw [lc] at first remembered
        have rc := LegalOption.eq_none_of_inactive _ second (fun active =>
          first (activity.mpr active))
        rw [rc] at remembered
        exact ⟨remembered, rc.symm⟩
    | some move =>
        rw [lc] at first remembered
        obtain ⟨other, rc⟩ := LegalOption.exists_eq_some_of_active _ second
          (activity.mp first.1)
        rw [rc] at remembered
        have rows := List.cons.inj remembered
        exact ⟨rows.2, (congrArg some (congrArg Prod.snd rows.1)).trans rc.symm⟩
  exact ⟨(setup.proposalRecoverySignals.withOwnPlayRecall_infoOf_eq_iff focal left right).mpr
    ⟨previous, words.1⟩, words.2⟩

omit [Fintype Player] in
theorem source_address_row
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state)
    (index : Nat) (inside : index + 1 < trace.length) :
    ∃ (before after : setup.proposalRecoveryProtocol.State)
      (prior : setup.proposalRecoveryProtocol.Trace before)
      (joint : Player → Option (ProposalRecoveryMove Player L))
      (legal : setup.proposalRecoveryProtocol.Legal before joint)
      (reached : after ∈ (setup.proposalRecoveryProtocol.step before ⟨joint, legal⟩).support),
      TracePrefix (prior.extend joint legal reached) trace ∧ prior.length = index + 1 ∧
      (setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace trace))[index]? =
        some (before.elim (none, (∅, 0, 0)) CommitRecoveryState.publicAddress) ∧
      (setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace trace))[index + 1]? =
        some (after.elim (none, (∅, 0, 0)) CommitRecoveryState.publicAddress) ∧
      (setup.proposalRecoveryJointRecall trace).reverse[index + 1]? = some joint := by
  have wordLengths : ∀ {target} (path : setup.proposalRecoveryProtocol.Trace target),
      (setup.proposalRecoveryJointRecall path).length = path.length := by
    intro target path
    induction path with
    | start => rfl
    | extend prior joint legal reached ih =>
        simp only [Setup.proposalRecoveryJointRecall, List.length_cons, Trace.length, ih]
  have lengths : ∀ {target} (path : setup.proposalRecoveryProtocol.Trace target),
      (setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace path)).length =
        path.length := by
    intro target path
    induction path with
    | start => rfl
    | extend prior joint legal reached ih =>
        simp only [Setup.proposalRecoveryEraseTrace, setup.recoveryAddressWord_extend,
          List.length_append, List.length_singleton, Trace.length, ih]
  induction trace generalizing index with
  | start => simp only [Trace.length] at inside; omega
  | @extend before after prior joint legal reached ih =>
      by_cases earlier : index + 1 < prior.length
      · obtain ⟨source, target, old, choices, offered, moved, retainedTrace, depth, first, second,
          instruction⟩ :=
          ih index earlier
        refine ⟨source, target, old, choices, offered, moved,
          .extend retainedTrace joint legal reached, depth, ?_, ?_, ?_⟩
        · simp only [Setup.proposalRecoveryEraseTrace, setup.recoveryAddressWord_extend]
          rw [List.getElem?_append_left
            (l₁ := setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace prior))
            (i := index) (by rw [lengths]; omega)]
          exact first
        · simpa only [Setup.proposalRecoveryEraseTrace, setup.recoveryAddressWord_extend,
            List.getElem?_append_left (by rw [lengths]; exact earlier)] using second
        · simpa only [Setup.proposalRecoveryJointRecall, List.reverse_cons,
            List.getElem?_append_left (by rw [List.length_reverse, wordLengths]; exact earlier)]
              using instruction
      · have depth : prior.length = index + 1 := by
          simp only [Trace.length] at inside
          omega
        refine ⟨before, after, prior, joint, legal, reached, .refl, depth, ?_, ?_, ?_⟩
        · cases prior with
          | start => simp only [Trace.length] at depth; omega
          | extend old choices offered moved =>
              have position : old.length = index := by
                simp only [Trace.length] at depth
                omega
              simp only [Setup.proposalRecoveryEraseTrace, setup.recoveryAddressWord_extend]
              rw [List.getElem?_append_left
                (l₁ := setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace old) ++
                  [before.elim (none, (∅, 0, 0)) CommitRecoveryState.publicAddress])
                (i := index) (by
                rw [List.length_append, lengths, List.length_singleton, position]
                omega)]
              rw [List.getElem?_append_right
                (l₁ := setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace old))
                (i := index) (by rw [lengths, position])]
              simp only [lengths, position, Nat.sub_self, List.getElem?_cons_zero]
        · simp only [Setup.proposalRecoveryEraseTrace, setup.recoveryAddressWord_extend,
            List.getElem?_append_right (by rw [lengths, depth]),
            lengths, depth, Nat.sub_self, List.getElem?_cons_zero]
        · simp only [Setup.proposalRecoveryJointRecall, List.reverse_cons,
            List.getElem?_append_right (by rw [List.length_reverse, wordLengths, depth]),
            List.length_reverse, wordLengths, depth, Nat.sub_self, List.getElem?_cons_zero]

omit [Fintype Player] in
private theorem source_instruction_chunk_row
    {first last : setup.proposalRecoveryProtocol.State}
    (entry : setup.proposalRecoveryProtocol.Trace first)
    (trace : setup.proposalRecoveryProtocol.Trace last)
    (initialized : 0 < entry.length)
    (word : List (Player → Option (CommitRecoveryMove Player L)))
    (instructions : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace trace) =
      word.reverse ++ setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace entry))
    (slot : Nat) (inside : slot < word.length) :
    ∃ (before after : setup.proposalRecoveryProtocol.State)
      (prior : setup.proposalRecoveryProtocol.Trace before)
      (joint : Player → Option (ProposalRecoveryMove Player L))
      (legal : setup.proposalRecoveryProtocol.Legal before joint)
      (reached : after ∈ (setup.proposalRecoveryProtocol.step before ⟨joint, legal⟩).support),
      TracePrefix (prior.extend joint legal reached) trace ∧
      prior.length = entry.length + slot ∧
      Setup.proposalRecoveryJoint joint = word[slot] ∧
      (setup.recoveryAddressWord
        (setup.proposalRecoveryEraseTrace trace))[entry.length + slot - 1]? =
        some (before.elim (none, (∅, 0, 0)) CommitRecoveryState.publicAddress) ∧
      (setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace trace))[entry.length + slot]? =
        some (after.elim (none, (∅, 0, 0)) CommitRecoveryState.publicAddress) := by
  have lengths := congrArg List.length instructions
  simp only [setup.recoveryJointRecall_length, setup.proposalRecoveryEraseTrace_length,
    List.length_append, List.length_reverse] at lengths
  have position : entry.length + slot - 1 + 1 = entry.length + slot := by omega
  obtain ⟨before, after, prior, joint, legal, reached, retained, depth,
      beforeAddress, afterAddress, instruction⟩ :=
    source_address_row setup trace (entry.length + slot - 1) (by omega)
  rw [position] at depth afterAddress instruction
  have semantic :
      (setup.recoveryJointRecall
        (setup.proposalRecoveryEraseTrace trace)).reverse[entry.length + slot]? =
          some (Setup.proposalRecoveryJoint joint) := by
    rw [← setup.proposalRecoveryJointRecall_semantic, ← List.map_reverse, List.getElem?_map,
      instruction, Option.map_some]
  have selected :
      (setup.recoveryJointRecall
        (setup.proposalRecoveryEraseTrace trace)).reverse[entry.length + slot]? =
          some word[slot] := by
    rw [instructions, List.reverse_append, List.reverse_reverse,
      List.getElem?_append_right (by
        rw [List.length_reverse, setup.recoveryJointRecall_length,
          setup.proposalRecoveryEraseTrace_length]; omega)]
    simp only [List.length_reverse, setup.recoveryJointRecall_length,
      setup.proposalRecoveryEraseTrace_length, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem inside]
  exact ⟨before, after, prior, joint, legal, reached, retained, depth,
    Option.some.inj (semantic.symm.trans selected), beforeAddress, afterAddress⟩

omit [Fintype Player] in
theorem source_information_row
    (focal : Player) {before after}
    (prior : setup.proposalRecoveryProtocol.Trace before)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before joint)
    (realized : after ∈ (setup.proposalRecoveryProtocol.step before ⟨joint, legal⟩).support)
    {leftState rightState}
    (left : setup.proposalRecoveryProtocol.Trace leftState)
    (right : setup.proposalRecoveryProtocol.Trace rightState)
    (kept : TracePrefix (prior.extend joint legal realized) left)
    (same : setup.proposalRecoveryModel.infoOf focal left =
      setup.proposalRecoveryModel.infoOf focal right) :
    ∃ (otherBefore otherAfter : setup.proposalRecoveryProtocol.State)
      (other : setup.proposalRecoveryProtocol.Trace otherBefore)
      (choices : Player → Option (ProposalRecoveryMove Player L))
      (offered : setup.proposalRecoveryProtocol.Legal otherBefore choices)
      (reached : otherAfter ∈
        (setup.proposalRecoveryProtocol.step otherBefore ⟨choices, offered⟩).support),
      TracePrefix (other.extend choices offered reached) right ∧
      setup.proposalRecoveryModel.infoOf focal prior =
        setup.proposalRecoveryModel.infoOf focal other ∧
      setup.proposalRecoveryModel.infoOf focal (prior.extend joint legal realized) =
        setup.proposalRecoveryModel.infoOf focal (other.extend choices offered reached) ∧
      joint focal = choices focal := by
  induction left generalizing rightState with
  | start => cases kept
  | @extend leftBefore leftAfter earlier actions allowed moved ih =>
      cases right with
      | start =>
          have impossible := congrArg (fun information => information.1.2) same
          change _ :: _ = [] at impossible
          cases impossible
      | @extend otherBefore otherAfter other choices offered reached =>
          have previous := source_information_before setup focal earlier other actions choices
            allowed offered moved reached same
          cases kept with
          | refl =>
              exact ⟨_, _, other, choices, offered, reached,
                .refl, previous.1, same, previous.2⟩
          | extend retained _ _ _ =>
              obtain ⟨oldBefore, oldAfter, old, oldChoices, oldOffered, oldReached,
                oldKept, oldSame, oldAfterSame, oldOwn⟩ := ih other retained previous.1
              exact ⟨oldBefore, oldAfter, old, oldChoices, oldOffered, oldReached,
                .extend oldKept choices offered reached, oldSame, oldAfterSame, oldOwn⟩

omit [Fintype Player] in
theorem source_good_prefix
    (focal : Player) {before after}
    (prior : setup.proposalRecoveryProtocol.Trace before)
    (trace : setup.proposalRecoveryProtocol.Trace after)
    (kept : TracePrefix prior trace)
    (good : setup.proposalRecoveryForeignGood focal ⟨after, trace⟩) :
    setup.proposalRecoveryForeignGood focal ⟨before, prior⟩ := by
  induction kept with
  | refl => exact good
  | extend earlier joint legal reached ih =>
      apply ih
      intro owner foreign generated
      apply good owner foreign
      obtain ⟨record, member, failed⟩ := generated
      refine ⟨record, ?_, failed⟩
      rw [InfoSignals.ownPlay_extend]
      cases joint owner
      · exact member
      · exact List.mem_cons_of_mem _ member

omit [Fintype Player] in
theorem source_binding_at_rank :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program)
      (event : Fin (eventCount program)) (owner : Player) (payload : L.Ty),
      outputLayout program event = .binding owner payload →
      event.val = instructionCount program - ProtocolState.remaining program point →
      ProtocolState.atCommit program point = true ∧
      ProtocolState.actor program point = some owner ∧
      ∀ action ∈ ProtocolView.available owner program (CommitmentInterface.forfeiture program)
          (ProtocolState.observe owner program point),
        ∃ choice, decodeEventAction program event choice = some action := by
  intro Γ O program
  induction program with
  | ret => intro point event; exact Fin.elim0 event
  | sample name fresh law next ih =>
      intro point event owner payload shape rank
      cases point with
      | inl config =>
          have zero : event = ⟨0, by simp only [eventCount]; omega⟩ := by
            apply Fin.ext
            simpa only [instructionCount, ProtocolState.remaining, Sum.elim_inl,
              Nat.sub_self] using rank
          rw [zero] at shape ⊢
          cases shape
      | inr point =>
          refine Fin.cases ?_ (fun tail => ?_) event shape rank
          · intro shape rank
            have bound := ProtocolState.remaining_le_instructionCount next point
            simp only [Fin.val_zero, instructionCount, ProtocolState.remaining,
              Sum.elim_inr] at rank
            omega
          · intro shape rank
            have bound := ProtocolState.remaining_le_instructionCount next point
            apply ih point tail owner payload shape
            simp only [Fin.val_succ, instructionCount, ProtocolState.remaining,
              Sum.elim_inr] at rank
            omega
  | commit name author fresh guard next ih =>
      intro point event owner payload shape rank
      cases point with
      | inl config =>
          have zero : event = ⟨0, by simp only [eventCount]; omega⟩ := by
            apply Fin.ext
            simpa only [instructionCount, ProtocolState.remaining, Sum.elim_inl,
              Nat.sub_self] using rank
          rw [zero] at shape ⊢
          have same := EventField.binding.inj shape
          obtain ⟨rfl, rfl⟩ := same
          refine ⟨rfl, rfl, ?_⟩
          intro action available
          obtain ⟨choice, _admitted, rfl⟩ := available
          exact ⟨choice, rfl⟩
      | inr point =>
          refine Fin.cases ?_ (fun tail => ?_) event shape rank
          · intro shape rank
            have bound := ProtocolState.remaining_le_instructionCount next point
            simp only [Fin.val_zero, instructionCount, ProtocolState.remaining,
              Sum.elim_inr] at rank
            omega
          · intro shape rank
            have bound := ProtocolState.remaining_le_instructionCount next point
            apply ih point tail owner payload shape
            simp only [Fin.val_succ, instructionCount, ProtocolState.remaining,
              Sum.elim_inr] at rank
            omega
  | reveal published author name fresh source unresolved next ih =>
      intro point event owner payload shape rank
      cases point with
      | inl config =>
          have zero : event = ⟨0, by simp only [eventCount]; omega⟩ := by
            apply Fin.ext
            simpa only [instructionCount, ProtocolState.remaining, Sum.elim_inl,
              Nat.sub_self] using rank
          rw [zero] at shape ⊢
          cases shape
      | inr point =>
          refine Fin.cases ?_ (fun tail => ?_) event shape rank
          · intro shape rank
            have bound := ProtocolState.remaining_le_instructionCount next point
            simp only [Fin.val_zero, instructionCount, ProtocolState.remaining,
              Sum.elim_inr] at rank
            omega
          · intro shape rank
            have bound := ProtocolState.remaining_le_instructionCount next point
            apply ih point tail owner payload shape
            simp only [Fin.val_succ, instructionCount, ProtocolState.remaining,
              Sum.elim_inr] at rank
            omega

omit [Fintype Player] in
theorem source_foreign_binding_success
    (focal owner : Player) (foreign : owner ≠ focal)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (current : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (next : CommitRecoveryState setup.program)
    (reached : some next ∈
      (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩).support)
    (position : event.val = instructionCount setup.program -
      ProtocolState.remaining setup.program current.point)
    (active : owner ∉ current.excluded) (retained : owner ∉ next.excluded)
    (good : setup.proposalRecoveryForeignGood focal
      ⟨some next, prior.extend joint legal reached⟩) :
    ∃ value : L.Val payload,
      phaseRecoveryBindingData setup .concurrent event owner payload binding
        ((joint owner).map (·.semantic)) = (.success value, false) := by
  obtain ⟨committing, acting, decode⟩ := source_binding_at_rank setup.program current.point
    event owner payload binding position
  obtain ⟨move, chosen⟩ : ∃ move, joint owner = some move := by
    have offered := legal.2 owner
    cases chosen : joint owner with
    | none =>
        rw [chosen] at offered
        exact (offered ⟨acting, active⟩).elim
    | some move => exact ⟨move, rfl⟩
  have offered := legal.2 owner
  rw [chosen] at offered
  have available : move.semantic ∈ current.available owner := offered.2.1
  obtain ⟨encoded, decoded⟩ := decode move.semantic.action available.1
  have encoding := encodeEventAction?_decodeEventAction_eq_some setup.program event
    encoded move.semantic.action decoded
  have nativeReached : next ∈ (current.step (Setup.proposalRecoveryJoint joint)).support := by
    change some next ∈ ((current.step (Setup.proposalRecoveryJoint joint)).map some).support
      at reached
    obtain ⟨result, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
    cases Option.some.inj same
    exact member
  have missing : move.semantic.missing = false := by
    cases missing : move.semantic.missing with
    | false => rfl
    | true =>
        exfalso
        apply retained
        apply current.missed_excludes owner (Setup.proposalRecoveryJoint joint)
          committing acting _ next nativeReached
        simp only [Setup.proposalRecoveryJoint, chosen, Option.map_some,
          CommitRecoveryMove.missed, Option.elim_some, missing]
  have notFailed : ¬ move.semantic.action.IsFailure := by
    obtain ⟨Δ, P, name, actualOwner, actualPayload, fresh, guard, suffix, lift, entry,
      origin, point, _names⟩ := ProtocolState.exists_committing_entry setup.program
        current.point setup.namesNodup committing
    have ownerEq : actualOwner = owner := by
      have original := origin.actor_lift
        (ProtocolState.entry (.commit name actualOwner fresh guard suffix) entry)
      rw [← point] at original
      exact Option.some.inj (original.symm.trans acting)
    subst actualOwner
    rw [CommitRecoveryState.available, point, origin.recoveryAvailable] at available
    obtain ⟨atom, atomEq⟩ := CommitRecoveryMove.exists_bindingAtom_of_available
      owner name actualPayload fresh guard suffix (entry.view owner) move.semantic available
    intro failed
    apply good owner foreign
    refine ⟨(setup.proposalRecoveryModel.infoOf owner prior, move), ?_, ?_⟩
    · rw [InfoSignals.ownPlay_extend, chosen]
      exact List.mem_cons_self
    · change move.semantic.missing = false ∧ _
      refine ⟨missing, ?_⟩
      rw [← atomEq] at failed ⊢
      cases atom with
      | inl value => cases failed
      | inr omitted => trivial
  have proper : cast (congrArg EventField.Action binding) encoded ≠ .failure := by
    intro failed
    exact notFailed ((decodeEventAction_binding_failure_iff setup.program event owner
      payload binding encoded move.semantic.action decoded).mp failed)
  cases result : cast (congrArg EventField.Action binding) encoded with
  | failure => exact (proper result).elim
  | success value =>
      refine ⟨value, ?_⟩
      simp only [chosen, Option.map_some, phaseRecoveryBindingData, Option.elim_some,
        missing, Bool.false_eq_true, ↓reduceIte, Option.bind_some, encoding,
        Option.map_some, Option.getD_some, result]

omit [Fintype Player] in
theorem source_information_metadata
    (focal : Player) (first second : setup.proposalRecoveryProtocol.History)
    (information : setup.proposalRecoveryModel.infoOf focal first.trace =
      setup.proposalRecoveryModel.infoOf focal second.trace) :
    match first.state, second.state with
    | none, none => True
    | some a, some b => a.MetadataEq b
    | _, _ => False := by
  have signals := congrArg Prod.fst information
  change (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf focal first.trace).1 =
    (setup.proposalRecoverySignals.withOwnPlayRecall.infoOf focal second.trace).1 at signals
  rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf] at signals
  have semantic := congrArg (setup.proposalRecoveryEraseBaseInfo focal) signals
  rw [setup.proposalRecoveryEraseBaseInfo_observed,
    setup.proposalRecoveryEraseBaseInfo_observed] at semantic
  have word := congrArg (fun information : setup.commitRecoverySignals.InfoState focal =>
    (information.1 :: information.2).map fun signal =>
      (signal.1.map (ProtocolView.publicOnly focal setup.program), signal.2)) semantic
  have metadata := setup.commitRecovery_metadata_of_publicRecall focal
    (setup.proposalRecoveryEraseTrace first.trace)
    (setup.proposalRecoveryEraseTrace second.trace) word
  rcases first with ⟨firstState, firstTrace⟩
  rcases second with ⟨secondState, secondTrace⟩
  cases firstState <;> cases secondState <;> exact metadata

omit [Fintype Player] in
/-- A closed source fiber keeps every historical binding value, including
accepted values canceled by a later retry. Its hidden label changes are only
foreign publications, which cannot change an addressed binding read. -/
theorem sourceBindingAt_closed_key
    (wellFormed : setup.WellFormed) (focal owner : Player)
    (attempt : CommitAttemptId) (event : (serviceGraph setup .concurrent).EventId)
    (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (leftCurrent rightCurrent : CommitRecoveryState setup.program)
    (left : setup.proposalRecoveryProtocol.Trace (some leftCurrent))
    (right : setup.proposalRecoveryProtocol.Trace (some rightCurrent))
    (same : setup.proposalRecoveryClosedKey focal ⟨some leftCurrent, left⟩ =
      setup.proposalRecoveryClosedKey focal ⟨some rightCurrent, right⟩)
    (leftGood : setup.proposalRecoveryForeignGood focal ⟨some leftCurrent, left⟩)
    (rightGood : setup.proposalRecoveryForeignGood focal ⟨some rightCurrent, right⟩) :
    sourceBindingAt setup attempt event owner payload binding left =
      sourceBindingAt setup attempt event owner payload binding right := by
  have noReveal : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (named : Fin (eventCount program))
      (bound : outputLayout program named = .binding owner payload)
      (actor : Player) (name : VarId) (bit : Bool),
      encodeEventAction? program named (.reveal actor name bit) = none := by
    intro Γ O program
    induction program with
    | ret => intro named; exact Fin.elim0 named
    | sample name fresh law next ih =>
      intro named bound actor selected bit
      refine Fin.cases ?_ ?_ named bound
      · intro impossible; cases impossible
      · intro tail bound
        exact ih tail bound actor selected bit
    | commit name actor fresh guard next ih =>
      intro named bound selected field bit
      refine Fin.cases ?_ ?_ named bound
      · intro _bound
        rfl
      · intro tail bound
        exact ih tail bound selected field bit
    | reveal published actor name fresh selected unresolved next ih =>
      intro named bound author field bit
      refine Fin.cases ?_ ?_ named bound
      · intro impossible; cases impossible
      · intro tail bound
        exact ih tail bound author field bit
  have dataEq {first second : Player → Option (ProposalRecoveryMove Player L)}
      (labels : SourceProgram.Setup.ForeignDisclosureLabels focal first second) :
      phaseRecoveryBindingData setup .concurrent event owner payload binding
          ((first owner).map (·.semantic)) =
        phaseRecoveryBindingData setup .concurrent event owner payload binding
          ((second owner).map (·.semantic)) := by
    rcases labels with identical | ⟨author, name, _foreign, other, changed⟩
    · rw [identical]
    · by_cases owned : owner = author
      · subst author
        rcases changed with ⟨firstEq, secondEq⟩ | ⟨secondEq, firstEq⟩ <;>
          simp only [firstEq, secondEq, Option.map_some, phaseRecoveryBindingData,
            ProposalRecoveryMove.ordinary, ProposalRecoveryMove.failedDisclosure,
            Option.elim_some, Bool.false_eq_true, ↓reduceIte, Option.bind_some,
            noReveal setup.program event binding, Option.map_none, Option.getD_none]
      · rw [other owner owned]
  have preserved {first : CommitRecoveryState setup.program}
      {prior : setup.proposalRecoveryProtocol.Trace (some first)}
      {a b : setup.proposalRecoveryProtocol.History}
      (refines : setup.ProposalRecoveryForeignRefinement focal first prior a b) :
      sourceBindingAt setup attempt event owner payload binding a.trace =
        sourceBindingAt setup attempt event owner payload binding b.trace := by
    induction refines with
    | initial => rfl
    | @extend leftState rightState leftAfter rightAfter earlierLeft earlierRight earlier
        leftJoint rightJoint leftLegal rightLegal leftSupported rightSupported labels
        _public _proposal _changed _excluded ih =>
      have metadata := source_information_metadata setup focal
        ⟨leftState, earlierLeft⟩ ⟨rightState, earlierRight⟩ earlier.info_eq
      cases leftState with
      | none =>
        cases rightState with
        | none => simpa only [sourceBindingAt] using ih
        | some current => exact metadata.elim
      | some current =>
        cases rightState with
        | none => exact metadata.elim
        | some other =>
          have live := (ProtocolState.MetadataEq.controls setup.program current.point
            other.point metadata.1).1
          have saved := (ProtocolState.MetadataEq.controls setup.program current.saved
            other.saved metadata.2.1).1
          have addressEq : (current.generation = attempt.generation ∧
              instructionCount setup.program -
                ProtocolState.remaining setup.program current.saved = attempt.phase ∧
              instructionCount setup.program -
                ProtocolState.remaining setup.program current.point = event.val) ↔
              (other.generation = attempt.generation ∧
              instructionCount setup.program -
                ProtocolState.remaining setup.program other.saved = attempt.phase ∧
              instructionCount setup.program -
                ProtocolState.remaining setup.program other.point = event.val) := by
            rw [← live, ← saved, ← metadata.2.2.2.2]
          by_cases addressed : current.generation = attempt.generation ∧
              instructionCount setup.program -
                ProtocolState.remaining setup.program current.saved = attempt.phase ∧
              instructionCount setup.program -
                ProtocolState.remaining setup.program current.point = event.val
          · have rightAddress := addressEq.mp addressed
            have data := dataEq labels
            simp only [sourceBindingAt, ite_eq_left addressed, ite_eq_left rightAddress]
            split
            · split
              · rename_i _ _ leftEq _ _ rightEq
                exact congrArg some (PublicationResult.success.inj
                  (congrArg Prod.fst (leftEq.symm.trans (data.trans rightEq))))
              · have missing : ∀ value, phaseRecoveryBindingData setup .concurrent event
                    owner payload binding ((rightJoint owner).map (·.semantic)) =
                      (.success value, false) → False := by assumption
                apply False.elim
                apply missing
                exact data.symm.trans (by assumption)
            · split
              · have missing : ∀ value, phaseRecoveryBindingData setup .concurrent event
                    owner payload binding ((leftJoint owner).map (·.semantic)) =
                      (.success value, false) → False := by assumption
                apply False.elim
                apply missing
                exact data.trans (by assumption)
              · rfl
          · have rightAddress : ¬ (other.generation = attempt.generation ∧
                instructionCount setup.program -
                  ProtocolState.remaining setup.program other.saved = attempt.phase ∧
                instructionCount setup.program -
                  ProtocolState.remaining setup.program other.point = event.val) :=
              fun matched => addressed (addressEq.mpr matched)
            simpa only [sourceBindingAt, ite_eq_right addressed, ite_eq_right rightAddress] using ih
  obtain ⟨first, prior, refines⟩ := setup.proposalRecovery_refinement_of_closed_key focal
    wellFormed leftCurrent rightCurrent left right same leftGood rightGood
  exact preserved refines

omit [Fintype Player] in
theorem sourceBindingAt_same_information
    (focal owner : Player) (attempt : CommitAttemptId)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (current next : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (reached : some next ∈
      (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩).support)
    (generation : current.generation = attempt.generation)
    (saved : instructionCount setup.program -
      ProtocolState.remaining setup.program current.saved = attempt.phase)
    (position : instructionCount setup.program -
      ProtocolState.remaining setup.program current.point = event.val)
    (active : owner ∉ current.excluded) (retained : owner ∉ next.excluded)
    (old : L.Val payload)
    (read : phaseRecoveryBindingData setup .concurrent event owner payload binding
      ((joint owner).map (·.semantic)) = (.success old, false))
    (left right : setup.proposalRecoveryProtocol.History)
    (kept : TracePrefix (prior.extend joint legal reached) left.trace)
    (same : setup.proposalRecoveryModel.infoOf focal left.trace =
      setup.proposalRecoveryModel.infoOf focal right.trace)
    (good : setup.proposalRecoveryForeignGood focal right) :
    ∃ value : L.Val payload,
      sourceBindingAt setup attempt event owner payload binding right.trace = some value ∧
        (owner = focal → value = old) := by
  obtain ⟨beforeState, afterState, before, choices, offered, moved, retainedTrace,
    beforeInfo, afterInfo, own⟩ := source_information_row setup focal prior joint legal reached
      left.trace right.trace kept same
  have beforeMetadata := source_information_metadata setup focal
    ⟨some current, prior⟩ ⟨beforeState, before⟩ beforeInfo
  have afterMetadata := source_information_metadata setup focal
    ⟨some next, prior.extend joint legal reached⟩
    ⟨afterState, before.extend choices offered moved⟩ afterInfo
  cases beforeState with
  | none => exact beforeMetadata.elim
  | some other =>
      cases afterState with
      | none => exact afterMetadata.elim
      | some after =>
          have rankEq := (ProtocolState.MetadataEq.controls setup.program current.point
            other.point beforeMetadata.1).1
          have savedEq := (ProtocolState.MetadataEq.controls setup.program current.saved
            other.saved beforeMetadata.2.1).1
          have newPosition : instructionCount setup.program -
              ProtocolState.remaining setup.program other.point = event.val := by
            rw [← rankEq]
            exact position
          have newActive : owner ∉ other.excluded := by
            rw [← beforeMetadata.2.2.1]
            exact active
          have newRetained : owner ∉ after.excluded := by
            rw [← afterMetadata.2.2.1]
            exact retained
          obtain ⟨value, actual, literal⟩ : ∃ value : L.Val payload,
              phaseRecoveryBindingData setup .concurrent event owner payload binding
                ((choices owner).map (·.semantic)) = (.success value, false) ∧
                (owner = focal → value = old) := by
            by_cases ownRow : owner = focal
            · subst owner
              exact ⟨old, by rw [← own]; exact read, fun _ => rfl⟩
            · obtain ⟨value, actual⟩ := source_foreign_binding_success setup focal owner ownRow
                event payload
                binding other before choices offered after moved newPosition.symm newActive
                newRetained (source_good_prefix setup focal _ right.trace retainedTrace good)
              exact ⟨value, actual, fun same => (ownRow same).elim⟩
          refine ⟨value, ?_, literal⟩
          refine sourceBindingAt_of_origin setup attempt event owner payload binding
            other before choices offered _ moved ?_ ?_ newPosition (.success value, false) actual
              right.trace retainedTrace
          · exact beforeMetadata.2.2.2.2.symm.trans generation
          · rw [← savedEq]
            exact saved

/-- The actual forced source continuation completes its remaining commitment
prefix. The current choice is literal; only the subsequent rows use ordinary
updated queries. -/
theorem sourceForcedBlock_commit_support
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    {name : VarId} {who : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ who name payload)
    (rest : SourceProgram.CommitPrefix
      ((name, .commitment who payload) :: Γ) (insert name O) Δ P)
    (suffix : SourceProgram Player L Δ P)
    (lift : ProtocolState (.commit name who fresh guard (rest.prepend suffix)) →
      ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (.commit name who fresh guard (rest.prepend suffix))
      lift)
    (source : SourceProgram.Config Player L Γ)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (point : current.point = lift (.inl source))
    (ordinary : current.excluded = current.entryExcluded)
    (fuel : sourceCommitFuel setup ⟨some current, trace⟩ = rest.length + 1)
    (choice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who trace))
    (properChoice : ∀ move, choice.val.map (·.semantic) = some move →
      move.missing = false ∧ ¬ move.action.IsFailure)
    (final : setup.proposalRecoveryProtocol.History)
    (supported : final ∈
      (sourceForcedBlock setup values who ⟨some current, trace⟩ choice).support) :
    ∃ (finished : SourceProgram.Config Player L Δ)
      (last : CommitRecoveryState setup.program)
      (lastTrace : setup.proposalRecoveryProtocol.Trace (some last))
      (attempt : (SourceProgram.CommitPrefix.commit name who fresh guard rest).Attempt
        source current.excluded finished last.excluded),
      final = ⟨some last, lastTrace⟩ ∧
      last.point = lift (.inr (rest.liftPoint suffix (ProtocolState.entry suffix finished))) ∧
      last.excluded = current.excluded ∧ last.entryExcluded = current.excluded ∧
      last.generation = current.generation ∧
      setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace lastTrace) =
        attempt.joints.reverse ++ setup.recoveryJointRecall
          (setup.proposalRecoveryEraseTrace trace) ∧
      (∀ joint ∈ attempt.joints, ∀ owner move, joint owner = some move →
        move.missing = false ∧ ¬ move.action.IsFailure) ∧
      (attempt.joints.head?).map (fun joint => joint who) = some (choice.val.map (·.semantic)) := by
  classical
  let profile := sourceUnflaggedStrategy setup values
  let forced := Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature)
    profile who ((profile who).commit (setup.proposalRecoveryModel.infoOf who trace) choice)
  change final ∈ ((setup.proposalRecoveryModel.runBehavioralFrom forced 1
    ⟨some current, trace⟩).bind (setup.proposalRecoveryModel.runBehavioralFrom profile
      (sourceCommitFuel setup ⟨some current, trace⟩ - 1))).support at supported
  rw [fuel, Nat.add_sub_cancel] at supported
  obtain ⟨middle, firstSupport, finalSupport⟩ := (PMF.mem_support_bind_iff ..).mp supported
  rw [setup.proposalRecoveryModel.runBehavioralFrom_succ_localStep] at firstSupport
  obtain ⟨middle', chosenSupport, pureSupport⟩ := (PMF.mem_support_bind_iff ..).mp firstSupport
  have same : middle = middle' := (PMF.mem_support_pure_iff ..).mp pureSupport
  subst middle'
  obtain ⟨choices, drawn, localSupport⟩ := (PMF.mem_support_bind_iff ..).mp chosenSupport
  have marginals := (independentProduct_support_iff _ _).mp drawn
  have own : choices who = choice := by
    have selected := marginals who
    simpa only [forced, Profile.update_same,
      InformationModel.BehavioralPolicy.commit_self, PMF.mem_support_pure_iff] using selected
  have proper : ∀ owner move, Setup.proposalRecoveryJoint (fun owner => (choices owner).val) owner =
      some move → move.missing = false ∧ ¬ move.action.IsFailure := by
    intro owner move selected
    by_cases same : owner = who
    · subst owner
      change (choices who).val.map (·.semantic) = some move at selected
      rw [own] at selected
      exact properChoice move selected
    · have chosen : choices owner ∈ (profile owner
          (setup.proposalRecoveryModel.infoOf owner trace)).support := by
        simpa only [forced, Profile.update_of_ne _ _ same] using marginals owner
      have projected : (choices owner).val.map (·.semantic) ∈
          ((profile owner (setup.proposalRecoveryModel.infoOf owner trace)).map
            (fun item => item.val.map (·.semantic))).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨choices owner, chosen, rfl⟩
      rw [show profile = setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values from rfl,
        setup.proposalRecovery_ordinary_semantic_draw values] at projected
      obtain ⟨draw, _drawn, semantic⟩ := (PMF.mem_support_map_iff _ _ _).mp projected
      exact draw.property move (semantic.trans selected)
  obtain ⟨middleSource, after, headAttempt, monotone, headWord, middleState, middleWord,
      _middleLabels⟩ := proposalRecovery_localStep_commit_attempt setup fresh guard
        (rest.prepend suffix) lift origin source current trace point choices middle localSupport
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
      lastEntry, lastGeneration, lastWord, _lastLabels, tailProper⟩ :=
    proposalRecovery_ordinary_commit_block_support setup values rest suffix
      (fun point => lift (.inr point))
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
  · intro joint member owner move selected
    rw [CommitPrefix.Attempt.prepend_joints, tailWord] at member
    rcases List.mem_append.mp member with head | tail
    · rw [headWord, List.mem_singleton] at head
      subst joint
      exact proper owner move selected
    · exact tailProper joint tail owner move selected
  · rw [CommitPrefix.Attempt.prepend_joints, headWord]
    simp only [List.singleton_append, List.head?_cons, Option.map_some]
    change some ((choices who).val.map (·.semantic)) = _
    rw [own]

omit [Fintype Player] in
theorem source_commit_chunk
    {retired : List (RetiredCommitAttempt (serviceGraph setup .concurrent))}
    {history : setup.commitRecoveryProtocol.History}
    (origins : ArchivedSourceOrigins setup .concurrent retired history)
    (index : Nat) (positive : 0 < index) (bound : index < history.trace.length)
    (commit : ((proposalSourceSteps setup history.trace)[index]?).map
      (fun event => event.source.map
        (fun state => ProtocolState.atCommit setup.program state.point)) = some (some true)) :
    ∃ (state : PhaseRuntimeState (serviceGraph setup .concurrent))
      (checkpoint : RecoverySourceCheckpoint setup .concurrent state)
      (image : EventGraphRuntime.State (serviceGraph setup .concurrent))
      (closed : setup.commitRecoveryProtocol.History) (steps later : Nat),
      setup.commitRecoveryProtocol.ReachesWithin steps ⟨_, checkpoint.trace⟩ closed ∧
      setup.commitRecoveryProtocol.ReachesWithin later closed history ∧
      checkpoint.trace.length ≤ index ∧ index < closed.trace.length ∧
      setup.recoveryJointRecall closed.trace =
        (checkpoint.commitInstructionWord image).reverse ++
          setup.recoveryJointRecall checkpoint.trace ∧
      (∃ word, setup.recoveryAddressWord closed.trace =
          setup.recoveryAddressWord checkpoint.trace ++ word ∧
        word.map (fun address => address.2.1) = checkpoint.commitExclusionWord image ∧
        (CommitRecoveryState.atPoint
          (checkpoint.residual.lift
            (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
          state.entry.excluded state.generation).IntervalAddresses word ∧
        word.getLast? = closed.state.map CommitRecoveryState.publicAddress) ∧
      ((∃ record ∈ retired, image = record.state ∧ state.attempt = record.attempt) ∨
        ∃ (nextState : PhaseRuntimeState (serviceGraph setup .concurrent))
          (next : RecoverySourceCheckpoint setup .concurrent nextState)
          (phase : RuntimePhase (serviceGraph setup .concurrent))
          (remaining : List (RuntimePhase (serviceGraph setup .concurrent))),
          state.phases = phase :: remaining ∧ phase.kind = .commitment ∧
          nextState.generation = state.generation ∧
          phase.high = nextState.attempt.phase ∧
          image = nextState.entry.native ∧ closed = ⟨_, next.trace⟩) := by
  have readPrefix : ∀ {first last}
      (prior : setup.commitRecoveryProtocol.Trace first)
      (trace : setup.commitRecoveryProtocol.Trace last), TracePrefix prior trace →
      ∀ index, index < prior.length →
        (proposalSourceSteps setup trace)[index]? =
          (proposalSourceSteps setup prior)[index]? := by
    intro first last prior trace kept index inside
    induction kept with
    | refl => rfl
    | @extend source target earlier retained joint legal reached ih =>
        rw [proposalSourceSteps_extend, List.getElem?_append_left]
        · exact ih
        · rw [proposalSourceSteps_length]
          exact inside.trans_le retained.length_le
  induction origins generalizing index with
  | initial plan input supported =>
      have length :
          (RecoverySourceCheckpoint.initialized setup .concurrent plan input supported).trace.length
            = 1 := by
        have castLength : ∀ {first last : PhaseRuntimeState (serviceGraph setup .concurrent)}
            (same : first = last) (checkpoint : RecoverySourceCheckpoint setup .concurrent first),
            (cast (congrArg (RecoverySourceCheckpoint setup .concurrent) same)
              checkpoint).trace.length = checkpoint.trace.length := by
          intro first last same checkpoint
          cases same
          rfl
        unfold RecoverySourceCheckpoint.initialized
        rw [castLength (phaseInitial_eq_raw plan (encodeInputs input)).symm]
        rfl
      simp only [length] at bound
      omega
  | @append state checkpoint previous aligned record attempt retained saved agrees size
      closed steps path instructions addresses ih =>
      by_cases earlier : index < checkpoint.trace.length
      · obtain ⟨old, source, image, finished, first, later, before, onward,
            lower, upper, word, addressWord, kind⟩ := ih index positive earlier (by
          rw [← readPrefix checkpoint.trace closed.trace path.tracePrefix index earlier]
          exact commit)
        refine ⟨old, source, image, finished, first, later + steps, before,
          onward.trans path, lower, upper, word, addressWord, ?_⟩
        rcases kind with archived | advanced
        · obtain ⟨record', member, imageEq, attemptEq⟩ := archived
          exact Or.inl ⟨record', List.mem_append_left _ member, imageEq, attemptEq⟩
        · exact Or.inr advanced
      · exact ⟨state, checkpoint, record.state, closed, steps, 0, path, .refl 0 _,
          Nat.le_of_not_gt earlier, bound, instructions, addresses,
          Or.inl ⟨record, List.mem_append_right _ (List.mem_singleton_self _), rfl, attempt⟩⟩
  | @advance state nextState checkpoint next previous phase remaining installed advanced
      generation archives boundary aligned saved retained stored finished reachable fuel path
      instructions publicSteps publicAddresses addresses replay ih =>
      by_cases earlier : index < checkpoint.trace.length
      · obtain ⟨old, source, image, closed, first, later, before, onward,
            lower, upper, word, addressWord, kind⟩ := ih index positive earlier (by
          rw [← readPrefix checkpoint.trace next.trace path.tracePrefix index earlier]
          exact commit)
        refine ⟨old, source, image, closed, first, later + fuel, before,
          onward.trans path, lower, upper, word, addressWord, ?_⟩
        rcases kind with archived | completed
        · obtain ⟨record, member, imageEq, attemptEq⟩ := archived
          exact Or.inl ⟨record, by simpa only [archives] using member, imageEq, attemptEq⟩
        · exact Or.inr completed
      · by_cases binding : phase.kind = .commitment
        · exact ⟨state, checkpoint, nextState.entry.native, ⟨_, next.trace⟩, fuel, 0,
            path, .refl 0 _, Nat.le_of_not_gt earlier, bound, instructions binding,
            addresses binding,
            Or.inr ⟨nextState, next, phase, remaining, installed, binding, generation,
              boundary, rfl, rfl⟩⟩
        · obtain ⟨events, points, chain, head, appended, annotations, length, ranks⟩ :=
            replay binding
          have oldLength := proposalSourceSteps_length setup checkpoint.trace
          rw [appended, List.getElem?_append_right (by omega)] at commit
          cases found : events[index - (proposalSourceSteps setup checkpoint.trace).length]?
              with
          | none =>
              simp only [found, Option.map_none] at commit
              cases commit
          | some event =>
              have member := List.mem_of_getElem? found
              obtain ⟨first, last, source, target, step, readback, point⟩ :=
                annotations event member
              simp only [found, Option.map_some, source, Option.map_some,
                CommitRecoveryState.atPoint] at commit
              have impossible : ProtocolState.atCommit setup.program first.1 = true :=
                Option.some.inj (Option.some.inj commit)
              exact (Bool.false_ne_true (step.1.2.1.symm.trans impossible)).elim

omit [Fintype Player] in
theorem source_suffix_cells_of_prefix
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O)
    (lift : ProtocolState program → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program program lift)
    (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (point saved : ProtocolState program)
    (firstPoint : first.point = lift point) (firstSaved : first.saved = lift saved)
    (same : ProtocolState.base program saved = ProtocolState.base program point)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) (retained : TracePrefix prior trace) :
    ∃ (current : CommitRecoveryState setup.program) (live kept : ProtocolState program),
      state = some current ∧ current.point = lift live ∧ current.saved = lift kept ∧
      ProtocolState.base program live = ProtocolState.base program point ∧
      ProtocolState.base program kept = ProtocolState.base program point := by
  have automaticLift : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      {program : SourceProgram Player L Γ O}
      {lift : ProtocolState program → ProtocolState setup.program},
      ProtocolSuffix setup.program program lift → ∀ value,
        lift (ProtocolState.automaticCommitBlock program value) =
          ProtocolState.automaticCommitBlock setup.program (lift value) := by
    intro Γ O program lift suffix
    induction suffix with
    | initial => intro value; rfl
    | sampleTail _ _ _ _ ih => intro value; exact ih (.inr value)
    | commitTail _ _ _ _ ih => intro value; exact ih (.inr value)
    | revealTail _ _ _ _ _ ih => intro value; exact ih (.inr value)
  have automatic := automaticLift origin
  have closeCells (current : CommitRecoveryState setup.program)
      (live kept : ProtocolState program)
      (liveEq : current.point = lift live) (keptEq : current.saved = lift kept)
      (liveBase : ProtocolState.base program live = ProtocolState.base program point)
      (keptBase : ProtocolState.base program kept = ProtocolState.base program point) :
      ∃ (nextLive nextSaved : ProtocolState program),
        current.close.point = lift nextLive ∧ current.close.saved = lift nextSaved ∧
        ProtocolState.base program nextLive = ProtocolState.base program point ∧
        ProtocolState.base program nextSaved = ProtocolState.base program point := by
    let restored := ProtocolState.withHistory program kept
      (ProtocolState.history setup.program current.point)
    have restoreEq : current.restored = lift restored := by
      rw [CommitRecoveryState.restored, keptEq, ← origin.withHistory_lift]
    have restoreBase : ProtocolState.base program restored =
        ProtocolState.base program point :=
      (ProtocolState.base_withHistory program kept _).trans keptBase
    have exhaustedEq : ProtocolState.automaticCommitBlock setup.program current.restored =
        lift (ProtocolState.automaticCommitBlock program restored) := by
      rw [restoreEq, ← automatic]
    have exhaustedBase :
        ProtocolState.base program (ProtocolState.automaticCommitBlock program restored) =
          ProtocolState.base program point :=
      (ProtocolState.base_automaticCommitBlock program restored).trans restoreBase
    unfold CommitRecoveryState.close
    split
    · split
      · split
        · exact ⟨restored, restored, restoreEq, restoreEq, restoreBase, restoreBase⟩
        · exact ⟨ProtocolState.automaticCommitBlock program restored,
            ProtocolState.automaticCommitBlock program restored,
            exhaustedEq, exhaustedEq, exhaustedBase, exhaustedBase⟩
      · exact ⟨live, live, liveEq, liveEq, liveBase, liveBase⟩
    · split
      · exact ⟨live, kept, liveEq, keptEq, liveBase, keptBase⟩
      · exact ⟨live, live, liveEq, liveEq, liveBase, liveBase⟩
  induction retained with
  | refl => exact ⟨first, point, saved, rfl, firstPoint, firstSaved, rfl, same⟩
  | @extend before after earlier retained joint legal reached ih =>
      obtain ⟨current, live, kept, rfl, liveEq, keptEq, liveBase, keptBase⟩ := ih
      obtain ⟨next, nextSupport, rfl⟩ := (PMF.mem_support_map_iff ..).mp reached
      obtain ⟨raw, rawSupport, rfl⟩ := current.step_raw_result joint next nextSupport
      rw [liveEq, origin.recoveryStep_lift] at rawSupport
      obtain ⟨result, resultSupport, resultEq⟩ := (PMF.mem_support_map_iff ..).mp rawSupport
      have rawPoint : raw.val.1 = lift result.1 := (congrArg Prod.fst resultEq).symm
      have nextBase := (ProtocolState.base_recoveryStep program live current.excluded joint
        result resultSupport).trans liveBase
      obtain ⟨nextLive, nextSaved, nextPoint, nextKept, liveBase, keptBase⟩ :=
        closeCells (current.install raw.val raw.property) result.1 kept rawPoint keptEq
          nextBase keptBase
      exact ⟨_, nextLive, nextSaved, rfl, nextPoint, nextKept, liveBase, keptBase⟩

omit [Fintype Player] in
open Classical in
theorem source_saved_cell_readback
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O)
    (lift : ProtocolState program → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program program lift)
    (source : SourceProgram.Config Player L Γ) (unique : (Γ.map Prod.fst).Nodup)
    (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (startPoint : first.point = lift (ProtocolState.entry program source))
    (startSaved : first.saved = lift (ProtocolState.entry program source))
    {lastState : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (last : RecoverySourceCheckpoint setup .concurrent lastState)
    (retained : TracePrefix prior last.trace)
    {name : VarId} {kind : CellTy Player L}
    (terminalCell : HasVar setup.program.terminalCtx name kind) (value : CellVal L kind)
    (readback : ProtocolState.cell? setup.program first.point name kind = some value) :
    ((terminalRefs setup.program).get terminalCell).get?
      lastState.entry.native.config.store = some (cellValue value) := by
  classical
  have liftCell : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      {program : SourceProgram Player L Γ O}
      {lift : ProtocolState program → ProtocolState setup.program},
      ProtocolSuffix setup.program program lift → ∀ point,
      ProtocolState.cell? setup.program (lift point) name kind =
        ProtocolState.cell? program point name kind := by
    intro Γ O program lift origin point
    exact origin.cell?_lift point name kind
  have initialRead : SourceProgram.State.cell? source.state name kind = some value := by
    simpa only [startPoint, liftCell origin, ProtocolState.cell?_entry] using readback
  have lookupWitness : ∀ {Γ : SourceCtx Player L} (cells : Vegas.State L Γ)
      {value : CellVal L kind}, SourceProgram.State.cell? cells name kind = some value →
      ∃ selected : HasVar Γ name kind, cells.get selected = value := by
    intro Γ
    induction Γ with
    | nil => intro cells value found; cases found
    | cons head tail ih =>
        rcases head with ⟨current, currentKind⟩
        intro cells value found
        rw [SourceProgram.State.cell?.eq_2] at found
        split_ifs at found with same
        · rcases same with ⟨rfl, rfl⟩
          exact ⟨.here, Option.some.inj found⟩
        · obtain ⟨selected, equal⟩ := ih _ found
          exact ⟨.there selected, equal⟩
  obtain ⟨selected, initialValue⟩ := lookupWitness _ initialRead
  obtain ⟨current, live, saved, ending, point, _saved, cells, _kept⟩ :=
    source_suffix_cells_of_prefix setup program lift origin first prior
      (ProtocolState.entry program source) (ProtocolState.entry program source)
      startPoint startSaved rfl last.trace retained
  have finalPoint := congrArg CommitRecoveryState.point (Option.some.inj ending)
  have found : SourceProgram.State.cell? last.source.state name kind =
      some (source.state.get selected) := by
    have read := ProtocolState.cell?_eq_of_base name kind program live unique selected
    rw [cells, ProtocolState.base_entry] at read
    rw [← liftCell origin live, ← point, ← finalPoint] at read
    exact (ProtocolState.cell?_entry last.residual.tail last.source name kind).symm.trans
      ((liftCell last.origin (ProtocolState.entry last.residual.tail last.source)).symm.trans
        read)
  obtain ⟨lastCell, finalValue⟩ := lookupWitness _ found
  have terminalUnique : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O),
      (Γ.map Prod.fst).Nodup → (program.terminalCtx.map Prod.fst).Nodup := by
    intro Γ O program
    induction program with
    | ret payoffs => exact id
    | sample _ fresh _ _ ih => exact fun unique => ih (List.nodup_cons.mpr ⟨fresh, unique⟩)
    | commit _ _ fresh _ _ ih =>
        exact fun unique => ih (List.nodup_cons.mpr ⟨fresh, unique⟩)
    | reveal _ _ _ fresh _ _ _ ih =>
        exact fun unique => ih (List.nodup_cons.mpr ⟨fresh, unique⟩)
  have terminalRead : ∀ {Γ Δ : SourceCtx Player L} (same : Γ = Δ)
      (refs : ContextRefs (graphLayout setup.program) Γ) (cell : HasVar Γ name kind),
      (cast (congrArg (ContextRefs (graphLayout setup.program)) same) refs).get
        (cast (congrArg (fun context => HasVar context name kind) same) cell) =
          refs.get cell := by
    intro Γ Δ same refs cell
    cases same
    rfl
  let finalCell := cast (congrArg (fun context => HasVar context name kind)
    last.terminalAlignment.contextEq) (terminalRef last.residual.tail lastCell)
  have finalRef : (terminalRefs setup.program).get finalCell = last.refs.get lastCell := by
    rw [← last.terminalAlignment.refsEq]
    exact (terminalRead last.terminalAlignment.contextEq _ _).trans
      (terminalRefsWith_get_terminalRef last.residual.tail last.refs last.embedding.ref lastCell)
  have terminalEq : terminalCell = finalCell :=
    HasVar.eq_of_nodup (terminalUnique setup.program setup.namesNodup) _ _
  rw [terminalEq, finalRef, last.agrees lastCell, finalValue, initialValue]

omit [Fintype Player] in
theorem settle_retains_entry_history
    (phases : List (RuntimePhase (serviceGraph setup .concurrent))) (generation : Nat)
    (entry current : RecoveryState (serviceGraph setup .concurrent))
    (retired : List (RetiredCommitAttempt (serviceGraph setup .concurrent)))
    (kept : entry.native.config.history.IsPrefix current.native.config.history) :
    entry.native.config.history.IsPrefix
        (PhaseRuntimeState.settle phases generation entry current
          retired).entry.native.config.history ∧
      entry.native.config.history.IsPrefix
        (PhaseRuntimeState.settle phases generation entry current
          retired).current.native.config.history := by
  have saved : entry.native.config.history.IsPrefix
      (PhaseRuntimeState.settle phases generation entry current
          retired).entry.native.config.history := by
    induction phases generalizing generation entry current retired with
    | nil => exact List.prefix_refl _
    | cons phase remaining ih =>
        have drained := kept.trans (phase.drain_history_prefix current)
        simp only [PhaseRuntimeState.settle]
        split
        · split
          · have restored : entry.native.config.history.IsPrefix
                (phase.drain (PhaseRuntimeState.restore entry
                  (phase.drain current))).native.config.history := by
              simpa only [PhaseRuntimeState.restore] using
                phase.drain_history_prefix (PhaseRuntimeState.restore entry (phase.drain current))
            split
            · exact ⟨[], by simp [PhaseRuntimeState.restore]⟩
            · exact restored.trans (ih _ _ _ _ (⟨[], by simp⟩))
          · exact drained.trans (ih _ _ _ _ (⟨[], by simp⟩))
        · exact ⟨[], by simp⟩
  exact ⟨saved, saved.trans
    (PhaseRuntimeState.settle_historyCheckpoint phases generation entry current retired kept)⟩

omit [Fintype Player] in
private theorem completed_image_retained
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (remaining : List (RuntimePhase (serviceGraph setup .concurrent))) (generation : Nat)
    (entry current : RecoveryState (serviceGraph setup .concurrent))
    (retired : List (RetiredCommitAttempt (serviceGraph setup .concurrent)))
    (finished : phase.Finished (phase.drain current)) :
    (⟨⟨phase.low, generation⟩, (phase.drain current).native⟩ :
      RetiredCommitAttempt (serviceGraph setup .concurrent)) ∈
        (PhaseRuntimeState.settle (phase :: remaining) generation entry current retired).retired ∨
    ((phase.drain current).native.config.history.IsPrefix
      (PhaseRuntimeState.settle (phase :: remaining) generation entry current
        retired).entry.native.config.history ∧
    (phase.drain current).native.config.history.IsPrefix
      (PhaseRuntimeState.settle (phase :: remaining) generation entry current
        retired).current.native.config.history) := by
  classical
  by_cases failed : phase.kind = .commitment ∧
      (((phase.drain current).excluded \ entry.excluded) ∩ phase.owners).Nonempty
  · left
    by_cases surviving : (phase.owners \ (phase.drain current).excluded).Nonempty
    · rw [PhaseRuntimeState.settle_retry phase remaining generation entry current retired
        finished failed.1 failed.2 surviving]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · rw [PhaseRuntimeState.settle_exhausted phase remaining generation entry current retired
        finished failed.1 failed.2 surviving]
      exact (PhaseRuntimeState.settle_archive _ _ _ _ _).subset
        (List.mem_append_right _ (List.mem_singleton_self _))
  · right
    rw [PhaseRuntimeState.settle_clean phase remaining generation entry current retired
      finished failed]
    exact settle_retains_entry_history setup remaining generation
      (phase.drain current) (phase.drain current) retired ⟨[], by simp⟩

theorem saved_history_of_prefix
    (reference : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some reference))
    (before : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before))
    (retained : TracePrefix prior trace) :
    before.execution.application.entry.native.config.history.IsPrefix
        reference.execution.application.entry.native.config.history ∧
      before.execution.application.entry.native.config.history.IsPrefix
        reference.execution.application.current.native.config.history := by
  let remembered := before.execution.application.entry.native.config.history
  have invariant : (nativeApplication).Invariant (fun state => state.HistoryCheckpoint ∧
      remembered.IsPrefix state.entry.native.config.history) := by
    constructor
    · intro state owner material valid
      exact ⟨(phaseApplication_historyCheckpoint implementation.runtime
        implementation.leaks).submit state owner material valid.1, valid.2⟩
    · intro state message next valid accepted
      have history := (phaseApplication_historyCheckpoint implementation.runtime
        implementation.leaks).handle state message next valid.1 accepted
      refine ⟨history, ?_⟩
      change state.handle implementation.runtime message = some next at accepted
      unfold PhaseRuntimeState.handle at accepted
      split at accepted
      · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
        obtain ⟨event, _named, ready, action, supported⟩ :=
          handle_config_mem_step implementation.runtime _ native _ handled
        have extended : state.current.native.config.history.IsPrefix native.config.history := by
          rw [state.current.native.config.step_history event ready action native.config supported]
          exact ⟨_, rfl⟩
        exact valid.2.trans (settle_retains_entry_history setup state.phases state.generation
          state.entry (state.current.inclusionResult message.payload.packet.call native)
          state.retired (valid.1.trans extended)).1
      · cases accepted
    · intro state command next valid reached
      have history := (phaseApplication_historyCheckpoint implementation.runtime
        implementation.leaks).environment state command next valid.1 reached
      refine ⟨history, ?_⟩
      change next ∈ (state.environment implementation.runtime command).support at reached
      unfold PhaseRuntimeState.environment at reached
      split at reached
      · obtain ⟨native, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
        exact valid.2.trans (settle_retains_entry_history setup state.phases state.generation
          state.entry (state.current.environmentResult command native) state.retired
          (valid.1.trans (environmentStep_history_prefix implementation.runtime _ native
            command supported))).1
      · cases (PMF.mem_support_pure_iff _ _).mp reached
        exact valid.2
  let inputs := setup.initialLaw.map encodeInputs
  have raw : ((nativeApplication).protocol
      (inputs.map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some before) := by
    have initialEq :
        nativeInitial = inputs.map (PhaseRuntimeState.initial implementation.plan) := by
      simp only [ReservedConcurrentImplementation.initial, inputs, PMF.map_comp, Function.comp_def]
    rw [← initialEq]
    exact (nativeMenu).toRawTrace nativeInitial implementation.horizon
      implementation.scheduler prior
  have initial := phaseHistoryCheckpoint_history implementation.runtime implementation.leaks
    implementation.plan inputs implementation.horizon implementation.scheduler raw
  have final := invariant.tracePrefix (nativeMenu) nativeInitial implementation.horizon
    implementation.scheduler before reference prior trace retained ⟨initial, List.prefix_refl _⟩
  exact ⟨final.2, final.2.trans final.1⟩

open Classical in
theorem source_saved_binding_readback
    (reference : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some reference))
    {firstState : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (first : RecoverySourceCheckpoint setup .concurrent firstState)
    (last : RecoverySourceCheckpoint setup .concurrent reference.execution.application)
    (sourceRetained : TracePrefix first.trace last.trace)
    (name : VarId) (owner : Player) (payload : L.Ty)
    (terminalCell : HasVar setup.program.terminalCtx name (.commitment owner payload))
    (event : (serviceGraph setup .concurrent).EventId)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (field : ((terminalRefs setup.program).get terminalCell).field = .inr event)
    (value : PublicationResult (L.Val payload))
    (readback : ProtocolState.cell? setup.program
      (first.residual.lift (ProtocolState.entry first.residual.tail first.source))
        name (.commitment owner payload) = some value)
    (action : (serviceGraph setup .concurrent).Action event)
    (recorded : ⟨event, action⟩ ∈ reference.execution.application.entry.native.config.history) :
    value = cast (congrArg EventField.Action binding) action := by
  have sourceRead := source_saved_cell_readback setup first.residual.tail first.residual.lift
    first.origin first.source first.unique _ first.trace rfl rfl last sourceRetained
      terminalCell value readback
  let ref : FieldRef (serviceGraph setup .concurrent).layout (.binding owner payload) :=
    ⟨.inr event, binding⟩
  have refEq : (terminalRefs setup.program).get terminalCell = ref := by
    cases actual : (terminalRefs setup.program).get terminalCell with
    | mk actualField typed =>
        have same : actualField = .inr event := by simpa only [actual] using field
        cases same
        rfl
  rw [refEq] at sourceRead
  let inputs := setup.initialLaw.map encodeInputs
  have raw : ((nativeApplication).protocol
      (inputs.map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some reference) := by
    have initialEq :
        nativeInitial = inputs.map (PhaseRuntimeState.initial implementation.plan) := by
      simp only [ReservedConcurrentImplementation.initial, inputs, PMF.map_comp, Function.comp_def]
    rw [← initialEq]
    exact (nativeMenu).toRawTrace nativeInitial implementation.horizon
      implementation.scheduler trace
  obtain ⟨_draw, native⟩ := phaseNativeInvariant_history implementation.runtime implementation.leaks
    implementation.plan inputs implementation.horizon implementation.scheduler raw
  have bindings := phaseBindingRecord_history implementation.runtime implementation.leaks
    implementation.plan inputs implementation.horizon implementation.scheduler raw
  have actual := bindings.saved.recorded_binding_action native.saved.reachable
    event owner payload binding action recorded
  have stored := bindings.saved.binding_value ref value sourceRead
  exact stored.trans actual.symm

private theorem accepted_snapshot_receipt
    (reference : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some reference))
    (before : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before))
    (retained : TracePrefix prior trace)
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (selected : snapshot = before.execution.application.current.native ∨
      snapshot = before.execution.application.entry.native ∨
      ∃ record ∈ before.execution.application.retired, snapshot = record.state)
    (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent))
    (accepted : snapshot.accepted (.inr event) = some handle) :
    ∃ entry ∈ reference.execution.recall handle.1,
      ∃ message, entry.emitted = some message ∧ message.sender = handle.1 ∧
        message.payload.packet.call = .commitment event handle ∧
        (message.id, true) ∈ reference.execution.receipts := by
  classical
  let inputs := setup.initialLaw.map encodeInputs
  have raw : ((nativeApplication).protocol
      (inputs.map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some before) := by
    have initialEq :
        nativeInitial = inputs.map (PhaseRuntimeState.initial implementation.plan) := by
      simp only [ReservedConcurrentImplementation.initial, inputs, PMF.map_comp, Function.comp_def]
    rw [← initialEq]
    exact (nativeMenu).toRawTrace nativeInitial implementation.horizon
      implementation.scheduler prior
  have signed := phaseBindingAcceptedReceipts_history implementation.runtime implementation.leaks
    implementation.plan inputs implementation.horizon implementation.scheduler raw
  have table : SignedBindingTable
      (acceptingBindingOutputs implementation.runtime implementation.leaks before.execution)
      snapshot := by
    rcases selected with rfl | rfl | ⟨record, member, rfl⟩
    · exact signed.live
    · exact signed.saved
    · exact signed.retired record member
  obtain ⟨message, output, sender, call⟩ := table.2 event handle accepted
  obtain ⟨authored, received⟩ := List.mem_filter.mp output
  obtain ⟨entry, member, emitted⟩ := List.mem_filterMap.mp authored
  have rawPrefix : TracePrefix
      ((nativeMenu).toRawTrace nativeInitial implementation.horizon
        implementation.scheduler prior)
      ((nativeMenu).toRawTrace nativeInitial implementation.horizon
        implementation.scheduler trace) := by
    have mapPrefix : ∀ {first last : (nativeProtocol).State}
        (firstTrace : (nativeProtocol).Trace first) (lastTrace : (nativeProtocol).Trace last),
        TracePrefix firstTrace lastTrace → TracePrefix
          ((nativeMenu).toRawTrace nativeInitial implementation.horizon
            implementation.scheduler firstTrace)
          ((nativeMenu).toRawTrace nativeInitial implementation.horizon
            implementation.scheduler lastTrace) := by
      intro first last firstTrace lastTrace kept
      induction kept with
      | refl => exact .refl
      | extend _ joint legal realized ih =>
          exact .extend ih joint
            ((nativeMenu).legal_raw nativeInitial implementation.horizon
              implementation.scheduler legal) realized
    exact mapPrefix prior trace retained
  have recalled := (nativeApplication).reaches_recall_prefix nativeInitial
    implementation.horizon implementation.scheduler rawPrefix.reachesWithin
    before reference rfl rfl handle.1
  have receipts := (nativeApplication).reaches_receipts_prefix nativeInitial
    implementation.horizon implementation.scheduler rawPrefix.reachesWithin
    before reference rfl rfl
  exact ⟨entry, recalled.subset member, message, emitted, sender, call,
    receipts.subset (of_decide_eq_true received)⟩

theorem accepting_receipt_transition
    (identifier : MessageId Player)
    {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state)
    (received : ∃ control, state = some control ∧
      (identifier, true) ∈ control.execution.receipts) :
    ∃ (before after : (nativeApplication).Control)
      (prior : (nativeProtocol).Trace (some before))
      (joint : Player → Option (nativeApplication).Action)
      (legal : (nativeProtocol).Legal (some before) joint)
      (realized : some after ∈ ((nativeProtocol).step (some before) ⟨joint, legal⟩).support),
      TracePrefix (prior.extend joint legal realized) trace ∧
        (identifier, true) ∉ before.execution.receipts ∧
        (identifier, true) ∈ after.execution.receipts ∧
        before.actor = none ∧ after.actor = none ∧
        after.execution ∈ (before.execution.environmentStep (nativeApplication)
          (.include identifier)).support := by
  revert received
  induction trace with
  | start =>
      intro received
      obtain ⟨control, impossible, _⟩ := received
      cases impossible
  | @extend source target prior joint legal realized ih =>
      intro received
      obtain ⟨after, rfl, accepted⟩ := received
      have moved := realized
      change some after ∈ ((nativeApplication).transition nativeInitial
        implementation.horizon implementation.scheduler source joint).support at moved
      cases source with
      | none =>
          obtain ⟨initial, _supported, equal⟩ := PMF.support_map .. ▸ moved
          cases Option.some.inj equal
          exact (List.not_mem_nil accepted).elim
      | some before =>
          by_cases earlier : (identifier, true) ∈ before.execution.receipts
          · obtain ⟨old, next, retainedTrace, choice, available, reached,
              retained, absent, present, idle, nextIdle, included⟩ :=
              ih ⟨before, rfl, earlier⟩
            exact ⟨old, next, retainedTrace, choice, available, reached,
              .extend retained joint legal realized, absent, present, idle, nextIdle, included⟩
          · have environment : before.actor = none ∧ after.actor = none ∧
                after.execution ∈ (before.execution.environmentStep (nativeApplication)
                  (.include identifier)).support := by
              rcases before with ⟨remaining, actor, execution⟩
              cases actor with
              | some owner =>
                  cases (PMF.mem_support_pure_iff ..).mp moved
                  rw [(nativeApplication).respond_receipts] at accepted
                  exact (earlier accepted).elim
              | none =>
                  cases remaining with
                  | zero =>
                      cases (PMF.mem_support_pure_iff ..).mp moved
                      exact (earlier accepted).elim
                  | succ remaining =>
                      obtain ⟨command, _chosen, supported⟩ :=
                        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
                      obtain ⟨next, stepped, equal⟩ := PMF.support_map .. ▸ supported
                      cases Option.some.inj equal
                      have selected := (nativeApplication).new_accepting_receipt_command
                        execution next identifier earlier command stepped accepted
                      subst command
                      exact ⟨rfl, rfl, stepped⟩
            exact ⟨before, after, prior, joint, legal, realized, .refl,
              earlier, accepted, environment.1, environment.2.1, environment.2.2⟩

theorem receipt_lookup_eq
    (reference before : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some reference))
    (prior : (nativeProtocol).Trace (some before)) (retained : TracePrefix prior trace)
    (message selected : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (input : message ∈ reference.execution.network.inputs)
    (found : before.execution.network.lookup message.id = some selected) : selected = message := by
  let rawPrior := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler prior
  let rawTrace := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  have rawPrefix : TracePrefix rawPrior rawTrace := by
    have mapPrefix : ∀ {first last : (nativeProtocol).State}
        (firstTrace : (nativeProtocol).Trace first) (lastTrace : (nativeProtocol).Trace last),
        TracePrefix firstTrace lastTrace → TracePrefix
          ((nativeMenu).toRawTrace nativeInitial implementation.horizon
            implementation.scheduler firstTrace)
          ((nativeMenu).toRawTrace nativeInitial implementation.horizon
            implementation.scheduler lastTrace) := by
      intro first last firstTrace lastTrace kept
      induction kept with
      | refl => exact .refl
      | extend _ joint legal realized ih =>
          exact .extend ih joint
            ((nativeMenu).legal_raw nativeInitial implementation.horizon
              implementation.scheduler legal) realized
    exact mapPrefix prior trace retained
  obtain ⟨entry, recorded, _material, _transmission, emitted, _packet⟩ :=
    ((nativeApplication).history_provenance nativeInitial implementation.horizon
      implementation.scheduler rawPrior).lookup message.id selected found
  have recalled := (nativeApplication).reaches_recall_prefix nativeInitial
    implementation.horizon implementation.scheduler rawPrefix.reachesWithin
      before reference rfl rfl selected.sender
  have recallInput := (nativeApplication).history_inputRecall nativeInitial
    implementation.horizon implementation.scheduler rawTrace selected.sender
  have authored : selected ∈ (reference.execution.recall selected.sender).filterMap
      (fun entry => entry.emitted) :=
    List.mem_filterMap.mpr ⟨entry, recalled.subset recorded, emitted⟩
  change selected ∈
    (nativeApplication).outputs (reference.execution.recall selected.sender) at authored
  rw [← recallInput] at authored
  have same : selected.id = message.id := by
    simpa only [decide_eq_true_eq] using List.find?_some found
  exact (nativeApplication).input_identifier_injective_history nativeInitial
    implementation.horizon implementation.scheduler reference rawTrace selected message
      (List.mem_filter.mp authored).1 input same

theorem accepting_receipt_handler
    (before after : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before)) (identifier : MessageId Player)
    (absent : (identifier, true) ∉ before.execution.receipts)
    (present : (identifier, true) ∈ after.execution.receipts)
    (included : after.execution ∈ (before.execution.environmentStep (nativeApplication)
      (.include identifier)).support) :
    ∃ (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
      (native : EventGraphRuntime.State (serviceGraph setup .concurrent)),
      before.execution.network.lookup identifier = some message ∧
        message.payload.attempt = before.execution.application.attempt ∧
        before.execution.application.handle implementation.runtime message =
          some after.execution.application ∧
        EventGraphRuntime.handle implementation.runtime before.execution.application.current.native
          ⟨message.id, message.payload.packet.call⟩ = some native ∧
        after.execution.application = ({ before.execution.application with
          current := before.execution.application.current.inclusionResult
            message.payload.packet.call native } :
            PhaseRuntimeState (serviceGraph setup .concurrent)).normalize := by
  let inputs := setup.initialLaw.map encodeInputs
  have raw : ((nativeApplication).protocol
      (inputs.map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some before) := by
    have initialEq :
        nativeInitial = inputs.map (PhaseRuntimeState.initial implementation.plan) := by
      simp only [ReservedConcurrentImplementation.initial, inputs, PMF.map_comp, Function.comp_def]
    rw [← initialEq]
    exact (nativeMenu).toRawTrace nativeInitial implementation.horizon
      implementation.scheduler prior
  have executionEq := (PMF.mem_support_pure_iff ..).mp (by
    simpa only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] using included)
  have receipts : after.execution.receipts =
      (before.execution.includePending (nativeApplication) identifier).receipts :=
    by simpa only using
      congrArg (fun execution : (nativeApplication).Execution => execution.receipts) executionEq
  have application : after.execution.application =
      (before.execution.includePending (nativeApplication) identifier).application :=
    by simpa only using
      congrArg (fun execution : (nativeApplication).Execution => execution.application) executionEq
  cases found : before.execution.network.lookup identifier with
  | none =>
      rw [receipts] at present
      simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found] at present
      exact (absent present).elim
  | some message =>
      cases handled : before.execution.application.handle implementation.runtime message with
      | none =>
          rw [receipts] at present
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found, show (nativeApplication).handle before.execution.application message = none
              from handled, Option.isSome_none, List.mem_append, List.mem_singleton] at present
          rcases present with earlier | impossible
          · exact (absent earlier).elim
          · cases impossible
      | some next =>
          obtain ⟨native, accepted, normalized, _receipts, _rawStamp⟩ :=
            phase_inclusion_snapshot_bindingAccepted implementation.runtime implementation.leaks
              implementation.plan inputs implementation.horizon implementation.scheduler
              raw identifier message found next handled
          refine ⟨message, native, rfl,
            PhaseRuntimeState.handle_attempt_eq implementation.runtime _ next message handled,
            ?_, accepted, ?_⟩
          · rw [application]
            simpa only [ReactiveApplication.Execution.includePending,
              MessageNetwork.includePending, found,
              show (nativeApplication).handle before.execution.application message = some next
                from handled, Option.getD_some] using handled
          · rw [application]
            simpa only [ReactiveApplication.Execution.includePending,
              MessageNetwork.includePending, found,
              show (nativeApplication).handle before.execution.application message = some next
                from handled, Option.getD_some] using normalized

theorem accepted_closing_image
    (start before after : (nativeApplication).Control)
    (initialTrace : (nativeProtocol).Trace (some start))
    (prior : (nativeProtocol).Trace (some before))
    (retained : TracePrefix initialTrace prior)
    (same : start.execution.application.attempt = before.execution.application.attempt)
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal (some before) joint)
    (realized : some after ∈ ((nativeProtocol).step (some before) ⟨joint, legal⟩).support)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (installed : phase ∈ before.execution.application.phases.head?)
    (closed : after.execution.application.attempt ≠ before.execution.application.attempt)
    (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent))
    (accepted : start.execution.application.current.native.accepted (.inr event) = some handle) :
    ∃ current : RecoveryState (serviceGraph setup .concurrent),
      after.execution.application = ({ before.execution.application with current := current } :
        PhaseRuntimeState (serviceGraph setup .concurrent)).normalize ∧
      phase.Finished (phase.drain current) ∧
      (phase.drain current).native.BindingInvariant ∧
      (phase.drain current).FailureCoverage ∧
      PhaseClosingEffect implementation.runtime implementation.leaks
        before.execution after.execution current ∧
      (phase.drain current).native.accepted (.inr event) = some handle := by
  let inputs := setup.initialLaw.map encodeInputs
  have initialEq :
        nativeInitial = inputs.map (PhaseRuntimeState.initial implementation.plan) := by
    simp only [ReservedConcurrentImplementation.initial, inputs, PMF.map_comp, Function.comp_def]
  have initialized : ∀ state ∈ (nativeInitial).support, state.Ordered := by
    rw [initialEq]
    intro state member
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ member
    exact PhaseRuntimeState.initial_ordered implementation.plan draw
  have ordered := (phaseApplication_seedOrder implementation.runtime implementation.leaks).history
    nativeInitial implementation.horizon implementation.scheduler initialized
      ((nativeMenu).toRawTrace nativeInitial implementation.horizon
        implementation.scheduler initialTrace)
  have present := phase_prefix_accepted implementation.runtime implementation.leaks
    (nativeMenu) nativeInitial implementation.horizon implementation.scheduler
      start before initialTrace prior retained ordered same (.inr event) handle accepted
  have raw := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler prior
  rw [initialEq] at raw
  have moved : some after ∈ ((nativeApplication).transition
      (inputs.map (PhaseRuntimeState.initial implementation.plan)) implementation.horizon
      implementation.scheduler (some before) joint).support := by
    rw [← initialEq]
    exact realized
  obtain ⟨current, _idle, normalized, finished, binding, coverage, _excluded, _receipts, effect,
    _rawStamp⟩ :=
    phase_closed_transition_receipt_snapshot implementation.runtime implementation.leaks
      implementation.plan inputs implementation.horizon implementation.scheduler before after
        raw joint moved phase installed closed
  refine ⟨current, normalized, finished, binding, coverage, effect, ?_⟩
  rw [(phase.drain_tables current).1]
  exact PhaseClosingEffect.accepted_preserved implementation.runtime implementation.leaks
    effect (.inr event) handle present

theorem accepted_attempt_image
    (reference start : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some reference))
    (initialTrace : (nativeProtocol).Trace (some start))
    (retained : TracePrefix initialTrace trace)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (installed : phase ∈ start.execution.application.phases.head?)
    (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent))
    (accepted : start.execution.application.current.native.accepted (.inr event) = some handle) :
    (start.execution.application.attempt = reference.execution.application.attempt ∧
      reference.execution.application.current.native.accepted (.inr event) = some handle) ∨
    ∃ (before after : (nativeApplication).Control)
      (prior : (nativeProtocol).Trace (some before))
      (joint : Player → Option (nativeApplication).Action)
      (legal : (nativeProtocol).Legal (some before) joint)
      (realized : some after ∈ ((nativeProtocol).step (some before) ⟨joint, legal⟩).support)
      (current : RecoveryState (serviceGraph setup .concurrent)),
      TracePrefix initialTrace prior ∧ TracePrefix (prior.extend joint legal realized) trace ∧
      start.execution.application.attempt = before.execution.application.attempt ∧
      after.execution.application.attempt ≠ before.execution.application.attempt ∧
      phase ∈ before.execution.application.phases.head? ∧
      after.execution.application = ({ before.execution.application with current := current } :
        PhaseRuntimeState (serviceGraph setup .concurrent)).normalize ∧
      phase.Finished (phase.drain current) ∧
      (phase.drain current).native.BindingInvariant ∧
      (phase.drain current).FailureCoverage ∧
      PhaseClosingEffect implementation.runtime implementation.leaks
        before.execution after.execution current ∧
      (phase.drain current).native.accepted (.inr event) = some handle := by
  have initialized : ∀ state ∈ (nativeInitial).support, state.Ordered := by
    intro state member
    obtain ⟨draw, _supported, equal⟩ := PMF.support_map .. ▸ member
    cases equal
    exact PhaseRuntimeState.initial_ordered implementation.plan (encodeInputs draw)
  have ordered := (phaseApplication_seedOrder implementation.runtime implementation.leaks).history
    nativeInitial implementation.horizon implementation.scheduler initialized
      ((nativeMenu).toRawTrace nativeInitial implementation.horizon
        implementation.scheduler initialTrace)
  by_cases same : start.execution.application.attempt = reference.execution.application.attempt
  · exact Or.inl ⟨same, phase_prefix_accepted implementation.runtime implementation.leaks
      (nativeMenu) nativeInitial implementation.horizon implementation.scheduler
      start reference initialTrace trace retained ordered same (.inr event) handle accepted⟩
  · obtain ⟨source, target, prior, joint, legal, realized, initial, final, original, exited⟩ :=
      attempt_exit_of_prefix setup implementation start initialTrace trace retained (by
        simpa only [Option.map_some, ne_eq, Option.some.injEq] using Ne.symm same)
    obtain ⟨before, sourceEq, attemptEq⟩ := Option.map_eq_some_iff.mp original
    cases sourceEq
    obtain ⟨after, rfl, _recalled⟩ := (nativeApplication).transition_recall_prefix nativeInitial
      implementation.horizon implementation.scheduler before target joint realized
    have sameBefore : start.execution.application.attempt = before.execution.application.attempt :=
      attemptEq.symm
    have changed : after.execution.application.attempt ≠ before.execution.application.attempt := by
      simpa only [Option.map_some, attemptEq, ne_eq, Option.some.injEq] using exited
    have metadata := phase_attempt_metadata_of_prefix implementation.runtime implementation.leaks
      (nativeMenu) nativeInitial initialized implementation.horizon implementation.scheduler
      start before initialTrace prior initial ordered sameBefore
    have phaseBefore : phase ∈ before.execution.application.phases.head? := by
      have phases : start.execution.application.phases = before.execution.application.phases :=
        congrArg Prod.fst metadata
      exact (congrArg (fun phases => phase ∈ phases.head?) phases).mp installed
    obtain ⟨current, normalized, finished, binding, coverage, effect, present⟩ :=
      accepted_closing_image setup implementation start before after initialTrace prior initial
        sameBefore joint legal realized phase phaseBefore changed event handle accepted
    exact Or.inr ⟨before, after, prior, joint, legal, realized, current, initial, final,
      sameBefore, changed, phaseBefore, normalized, finished, binding, coverage, effect, present⟩

theorem clean_exit_excluded
    (state : PhaseRuntimeState (serviceGraph setup .concurrent))
    (witness : RecoverySourceWitness setup .concurrent implementation.plan state)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (remaining : List (RuntimePhase (serviceGraph setup .concurrent)))
    (installed : state.phases = phase :: remaining)
    (clean : ¬ (((phase.drain state.current).excluded \ state.entry.excluded) ∩
      phase.owners).Nonempty)
    (changed : state.normalize.attempt ≠ state.attempt) :
    (phase.drain state.current).excluded = state.entry.excluded ∧
      state.normalize.entry.excluded = state.entry.excluded := by
  have present : phase ∈ state.phases.head? := by
    simp only [installed, List.head?_cons, Option.mem_some_iff]
  have record := (witness.receipts.exclusion.installed phase present).phase_drain phase
  have positioned := witness.receipts.exclusion.frontier.positioned
  rw [installed] at positioned
  have within := phase.drain_within state.current positioned.2
  have equal : (phase.drain state.current).excluded = state.entry.excluded := by
    apply Finset.ext
    intro owner
    constructor
    · intro member
      by_contra absent
      obtain inherited | ⟨event, lower, acting, failed⟩ := (record.excluded owner).mp member
      · exact absent inherited
      · apply clean
        refine ⟨owner, Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨member, absent⟩, ?_⟩⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨event, (phase.mem_events event).mpr ⟨lower, within.2 event failed.completed⟩, ?_⟩
        simp only [acting, Option.toFinset_some, Finset.mem_singleton]
    · intro member
      exact (record.excluded owner).mpr (Or.inl member)
  refine ⟨equal, ?_⟩
  rw [PhaseRuntimeState.normalize_entry_excluded_of_changed state changed]
  change (PhaseRuntimeState.settle state.phases state.generation state.entry state.current
    state.retired).current.excluded = state.entry.excluded
  rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).1]
  exact (phase.drain_excluded state.current).symm.trans equal

theorem source_clean_interval
    (operational : implementation.Operational)
    (before after : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before))
    (trace : (nativeProtocol).Trace (some after))
    (retained : TracePrefix prior trace)
    (witness : RecoverySourceWitness setup .concurrent implementation.plan
      before.execution.application)
    (archived : witness.checkpoint.ArchivedProposals before.execution.network.inputs)
    (unchanged : after.execution.application.entry.excluded =
      before.execution.application.entry.excluded) :
    ∃ next : RecoverySourceWitness setup .concurrent implementation.plan
        after.execution.application,
      next.checkpoint.ArchivedProposals after.execution.network.inputs ∧
      ∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
        ⟨_, witness.checkpoint.trace⟩ ⟨_, next.checkpoint.trace⟩ ∧
        ∀ {state : setup.commitRecoveryProtocol.State}
          (middle : setup.commitRecoveryProtocol.Trace state),
          TracePrefix witness.checkpoint.trace middle →
          TracePrefix middle next.checkpoint.trace →
          (setup.commitRecoveryPublic state).1 = before.execution.application.entry.excluded := by
  obtain ⟨actual, equal, next, archivedNext, fuel, path⟩ :=
    witness.prefix_archived_source setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan operational.maximalPhases
      implementation.horizon implementation.scheduler before prior archived trace retained
  cases Option.some.inj equal
  refine ⟨next, archivedNext, fuel, path, ?_⟩
  intro state middle earlier later
  have grows : ∀ {first last : setup.commitRecoveryProtocol.State}
      (left : setup.commitRecoveryProtocol.Trace first)
      (right : setup.commitRecoveryProtocol.Trace last), TracePrefix left right →
      (setup.commitRecoveryPublic first).1 ⊆ (setup.commitRecoveryPublic last).1 := by
    intro first last left right kept
    induction kept with
    | refl => exact Finset.Subset.refl _
    | extend previous joint legal supported ih =>
        exact ih.trans (setup.commitRecovery_step_excluded_subset joint legal supported)
  have lower := grows witness.checkpoint.trace middle earlier
  have upper := grows middle next.checkpoint.trace later
  change before.execution.application.entry.excluded ⊆ _ at lower
  change _ ⊆ after.execution.application.entry.excluded at upper
  rw [unchanged] at upper
  exact Finset.Subset.antisymm upper lower

omit [Fintype Player] in
theorem source_selected_binding_terminal :
    ∀ {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
      (earlier : SourceProgram.CommitPrefix Γ O Δ P)
      (name : VarId) (owner : Player) (payload : L.Ty)
      (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
      {Ξ : SourceCtx Player L} {Q : Finset VarId}
      (rest : SourceProgram.CommitPrefix
        ((name, .commitment owner payload) :: Δ) (insert name P) Ξ Q)
      (suffix : SourceProgram Player L Ξ Q)
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (outputs : ∀ event, FieldRef (graphLayout setup.program)
        (outputLayout ((earlier.append (.commit name owner fresh guard rest)).prepend suffix)
          event)),
      ∃ cell : HasVar ((earlier.append (.commit name owner fresh guard rest)).prepend
          suffix).terminalCtx name (.commitment owner payload),
        ((terminalRefsWith ((earlier.append (.commit name owner fresh guard rest)).prepend
          suffix) refs outputs).get cell).field =
          (outputs ⟨earlier.length, by
            rw [← SourceProgram.CommitPrefix.eventCount_prepend,
              SourceProgram.CommitPrefix.length_append]
            simp only [SourceProgram.CommitPrefix.length]
            omega⟩).field := by
  intro Γ Δ O P earlier
  induction earlier with
  | nil =>
      intro name owner payload fresh guard Ξ Q rest suffix refs outputs
      exact ⟨terminalRef (rest.prepend suffix) .here,
        congrArg FieldRef.field
          (terminalRefsWith_get_terminalRef (rest.prepend suffix) _ _ .here)⟩
  | @commit Γ O Δ P oldName oldOwner oldPayload oldFresh oldGuard before ih =>
      intro name owner payload fresh guard Ξ Q rest suffix refs outputs
      dsimp only [SourceProgram.CommitPrefix.append, SourceProgram.CommitPrefix.prepend]
        at outputs ⊢
      let head : FieldRef (graphLayout setup.program) (.binding oldOwner oldPayload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      obtain ⟨cell, read⟩ := ih name owner payload fresh guard rest suffix (refs.cons head)
        (fun event => outputs event.succ)
      have inside : before.length < eventCount
          ((before.append (.commit name owner fresh guard rest)).prepend suffix) := by
        have count := (before.append (.commit name owner fresh guard rest)).eventCount_prepend
          suffix
        simp only [SourceProgram.CommitPrefix.length_append, SourceProgram.CommitPrefix.length]
          at count
        omega
      let selected : Fin (eventCount
          ((before.append (.commit name owner fresh guard rest)).prepend suffix)) :=
        ⟨before.length, inside⟩
      refine ⟨cell, ?_⟩
      calc
        _ = (outputs selected.succ).field := by
          simpa only [terminalRefsWith, head] using read
        _ = _ := congrArg (fun index => (outputs index).field) (Fin.ext rfl)

omit [Fintype Player] in
open Classical in
theorem source_clean_decoded_point
    {state nextState : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (checkpoint : RecoverySourceCheckpoint setup .concurrent state)
    (next : RecoverySourceCheckpoint setup .concurrent nextState)
    (image : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
    {fuel : Nat}
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩)
    (instructions : setup.recoveryJointRecall next.trace =
      (checkpoint.commitInstructionWord image).reverse ++
        setup.recoveryJointRecall checkpoint.trace)
    (unchanged : nextState.entry.excluded = state.entry.excluded) :
    match commitPhase checkpoint.residual.tail with
    | ⟨_, _, suffix, block, reconstruct, _⟩ =>
      let embedding := cast (congrArg (fun program => OutputEmbedding
        (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
          checkpoint.embedding
      let decoded := decodeCommitAttempt setup.program .concurrent block suffix embedding image
        checkpoint.source state.entry.excluded
      next.residual.lift (ProtocolState.entry next.residual.tail next.source) =
        checkpoint.residual.lift (cast (congrArg SourceProgram.ProtocolState reconstruct)
          (block.liftPoint suffix (ProtocolState.entry suffix decoded.1))) ∧
      ∀ (name : VarId) (kind : CellTy Player L),
        ProtocolState.cell? setup.program
          (next.residual.lift (ProtocolState.entry next.residual.tail next.source)) name kind =
            SourceProgram.State.cell? decoded.1.state name kind := by
  have selected := checkpoint.chosen_commit_trace image committing ⟨_, next.trace⟩
    path instructions
  generalize decomposition : commitPhase checkpoint.residual.tail = segment at selected ⊢
  rcases segment with ⟨Δ, P, suffix, block, reconstruct, _boundary⟩
  dsimp only at selected ⊢
  let embedding := cast (congrArg (fun program => OutputEmbedding
    (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
      checkpoint.embedding
  let decoded := decodeCommitAttempt setup.program .concurrent block suffix embedding image
    checkpoint.source state.entry.excluded
  let start := CommitRecoveryState.atPoint
    (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
      state.entry.excluded state.generation
  let point := checkpoint.residual.lift (cast (congrArg SourceProgram.ProtocolState reconstruct)
    (block.liftPoint suffix (ProtocolState.entry suffix decoded.1)))
  let installed := start.install (point, decoded.2.1)
    (fun _ member => decoded.2.2.excluded_subset member)
  obtain ⟨canonical, _reached, _word, equal, _addresses⟩ := selected
  have stateEq := congrArg (fun history : setup.commitRecoveryProtocol.History => history.state)
    equal
  have exactState : CommitRecoveryState.atPoint
      (next.residual.lift (ProtocolState.entry next.residual.tail next.source))
      nextState.entry.excluded nextState.generation = installed.close :=
    Option.some.inj stateEq
  have excluded : decoded.2.1 = state.entry.excluded := by
    have observed := congrArg CommitRecoveryState.excluded exactState
    change nextState.entry.excluded = installed.close.excluded at observed
    rw [CommitRecoveryState.close_excluded] at observed
    exact observed.symm.trans unchanged
  have clean : ¬ installed.NewFailure := by
    change ¬ (decoded.2.1 \ state.entry.excluded).Nonempty
    rw [excluded, Finset.sdiff_self]
    exact Finset.not_nonempty_empty
  have observed := congrArg CommitRecoveryState.point exactState
  rw [CommitRecoveryState.close_point_of_no_new_failure installed clean] at observed
  refine ⟨observed, ?_⟩
  have liftCell : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      {program : SourceProgram Player L Γ O}
      {lift : ProtocolState program → ProtocolState setup.program},
      ProtocolSuffix setup.program program lift → ∀ point name kind,
        ProtocolState.cell? setup.program (lift point) name kind =
          ProtocolState.cell? program point name kind := by
    intro Γ O program lift origin point name kind
    exact origin.cell?_lift point name kind
  have castCell : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      {first last : SourceProgram Player L Γ O} (same : first = last)
      (point : ProtocolState first) (name : VarId) (kind : CellTy Player L),
      ProtocolState.cell? last (cast (congrArg SourceProgram.ProtocolState same) point) name kind =
        ProtocolState.cell? first point name kind := by
    intro Γ O first last same point name kind
    cases same
    rfl
  have blockCell : ∀ {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
      (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
      (point : ProtocolState suffix) (name : VarId) (kind : CellTy Player L),
      ProtocolState.cell? (block.prepend suffix) (block.liftPoint suffix point) name kind =
        ProtocolState.cell? suffix point name kind := by
    intro Γ Δ O P block
    induction block with
    | nil => intro suffix point name kind; rfl
    | commit _ _ _ _ _ ih => intro suffix point name kind; exact ih suffix point name kind
  intro name kind
  refine (congrArg (fun point => ProtocolState.cell? setup.program point name kind)
    observed).trans ?_
  change ProtocolState.cell? setup.program
      (checkpoint.residual.lift (cast (congrArg SourceProgram.ProtocolState reconstruct)
        (block.liftPoint suffix (ProtocolState.entry suffix decoded.1)))) name kind = _
  exact (liftCell checkpoint.origin _ name kind).trans
    ((castCell reconstruct _ name kind).trans
      ((blockCell block suffix _ name kind).trans
        (ProtocolState.cell?_entry suffix decoded.1 name kind)))


omit [Fintype Player] in
open Classical in
theorem source_decoded_failure_point
    {state nextState : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (checkpoint : RecoverySourceCheckpoint setup .concurrent state)
    (next : RecoverySourceCheckpoint setup .concurrent nextState)
    (image : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
    {fuel : Nat}
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩)
    (instructions : setup.recoveryJointRecall next.trace =
      (checkpoint.commitInstructionWord image).reverse ++
        setup.recoveryJointRecall checkpoint.trace)
    (generation : nextState.generation = state.generation) :
    match commitPhase checkpoint.residual.tail with
    | ⟨Δ, P, suffix, block, reconstruct, _⟩ =>
      let embedding := cast (congrArg (fun program => OutputEmbedding
        (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
          checkpoint.embedding
      let decoded := decodeCommitAttempt setup.program .concurrent block suffix embedding image
        checkpoint.source state.entry.excluded
      ∀ {Ξ : SourceCtx Player L} {Q : Finset VarId}
        (earlier : SourceProgram.CommitPrefix checkpoint.residual.context
          checkpoint.residual.names Ξ Q)
        (name : VarId) (owner : Player) (payload : L.Ty)
        (fresh : name ∉ Ξ.map Prod.fst) (guard : SourceGuard L Ξ owner name payload)
        (rest : SourceProgram.CommitPrefix ((name, .commitment owner payload) :: Ξ)
          (insert name Q) Δ P),
        earlier.append (.commit name owner fresh guard rest) = block →
        SourceProgram.State.cell? decoded.1.state name (.commitment owner payload) = some .failure →
        ProtocolState.cell? setup.program
          (next.residual.lift (ProtocolState.entry next.residual.tail next.source))
          name (.commitment owner payload) = some .failure := by
  have selected := checkpoint.chosen_commit_trace image committing ⟨_, next.trace⟩
    path instructions
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, alignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, history, memory, steps, menus, readout, priorTrace, views,
    historyAlignment, origin⟩
  dsimp only at committing selected ⊢
  generalize decomposition : commitPhase program = segment at selected ⊢
  rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
  subst program
  dsimp only at selected ⊢
  intro Ξ Q earlier name owner payload fresh guard rest splitBlock failedCell
  let decoded := decodeCommitAttempt setup.program .concurrent block suffix embedding image
    source state.entry.excluded
  let start := CommitRecoveryState.atPoint
    (lift (ProtocolState.entry (block.prepend suffix) source))
      state.entry.excluded state.generation
  let point := lift (block.liftPoint suffix (ProtocolState.entry suffix decoded.1))
  let installed := start.install (point, decoded.2.1)
    (fun _ member => decoded.2.2.excluded_subset member)
  obtain ⟨canonical, _reached, _word, equal, _addresses⟩ := selected
  have stateEq := congrArg (fun h : setup.commitRecoveryProtocol.History => h.state) equal
  have exactState : CommitRecoveryState.atPoint
      (next.residual.lift (ProtocolState.entry next.residual.tail next.source))
      nextState.entry.excluded nextState.generation = installed.close :=
    Option.some.inj stateEq
  have liftCell : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      {program : SourceProgram Player L Γ O}
      {lift : ProtocolState program → ProtocolState setup.program},
      ProtocolSuffix setup.program program lift → ∀ point name kind,
        ProtocolState.cell? setup.program (lift point) name kind =
          ProtocolState.cell? program point name kind := by
    intro Γ O program lift origin point name kind
    exact origin.cell?_lift point name kind
  have blockCell : ∀ {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
      (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
      (point : ProtocolState suffix) (name : VarId) (kind : CellTy Player L),
      ProtocolState.cell? (block.prepend suffix) (block.liftPoint suffix point) name kind =
        ProtocolState.cell? suffix point name kind := by
    intro Γ Δ O P block
    induction block with
    | nil => intro suffix point name kind; rfl
    | commit _ _ _ _ _ ih => intro suffix point name kind; exact ih suffix point name kind
  have decodedRead : ProtocolState.cell? setup.program point name
      (.commitment owner payload) = some .failure := by
    change ProtocolState.cell? setup.program
      (lift (block.liftPoint suffix (ProtocolState.entry suffix decoded.1))) _ _ = _
    exact (liftCell origin _ _ _).trans
      ((blockCell block suffix _ _ _).trans
        ((ProtocolState.cell?_entry suffix decoded.1 _ _).trans failedCell))
  have ordinary (same : installed.close.point = point) :
      ProtocolState.cell? setup.program
        (next.residual.lift (ProtocolState.entry next.residual.tail next.source))
        name (.commitment owner payload) = some .failure := by
    have observed := congrArg CommitRecoveryState.point exactState
    change next.residual.lift (ProtocolState.entry next.residual.tail next.source) =
      installed.close.point at observed
    exact (congrArg (fun point => ProtocolState.cell? setup.program point
      name (.commitment owner payload)) (observed.trans same)).trans decodedRead
  by_cases finished : installed.Finished
  · by_cases failed : installed.NewFailure
    · by_cases survives : installed.Survives
      · have changed := congrArg CommitRecoveryState.generation exactState
        rw [installed.close_of_retry finished failed survives] at changed
        change nextState.generation = state.generation + 1 at changed
        omega
      · have autoPreserves : ∀ {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
            (block : SourceProgram.CommitPrefix Γ O Δ P) (entry : Config Player L Γ)
            (name : VarId) (kind : CellTy Player L) (value : CellVal L kind),
            SourceProgram.State.cell? entry.state name kind = some value →
            SourceProgram.State.cell? (block.automatic entry).state name kind = some value := by
          intro Γ Δ O P block
          induction block with
          | nil => intro entry name kind value found; exact found
          | @commit Γ O Δ P introduced actor payload fresh guard later ih =>
              intro entry name kind value found
              apply ih (automaticCommit introduced actor _ entry) name kind value
              have different : introduced ≠ name := by
                intro same
                apply fresh
                simpa only [same] using SourceProgram.State.mem_of_cell?_eq_some found
              change SourceProgram.State.cell?
                (Env.cons (Val := CellVal (Player := Player) L) (x := introduced)
                  (τ := .commitment actor payload) PublicationResult.failure entry.state)
                name kind = some value
              rw [SourceProgram.State.cell?_cons_of_ne _ _ different]
              exact found
        have autoAppend : ∀ {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
            (first : SourceProgram.CommitPrefix Γ O Δ P) (last : SourceProgram.CommitPrefix Δ P Ξ Q)
            (entry : Config Player L Γ),
            (first.append last).automatic entry = last.automatic (first.automatic entry) := by
          intro Γ Δ Ξ O P Q first
          induction first with
          | nil => intro last entry; rfl
          | commit _ _ _ _ _ ih => intro last entry; exact ih last _
        let past := ProtocolState.history setup.program point
        have autoReadAt (entry : Config Player L Γ) : SourceProgram.State.cell?
            (block.automatic entry).state name (.commitment owner payload) =
              some .failure := by
          rw [← splitBlock, autoAppend]
          change SourceProgram.State.cell? (rest.automatic
            (automaticCommit name owner payload (earlier.automatic entry))).state _ _ = _
          apply autoPreserves
          exact SourceProgram.State.cell?_cons_self (L := L)
            (kind := .commitment owner payload) PublicationResult.failure _
        have autoRead := autoReadAt { source with history := past }
        have exhaustedPoint : installed.exhausted.point =
            lift (block.liftPoint suffix (ProtocolState.entry suffix
              (block.automatic { source with history := past }))) := by
          change ProtocolState.automaticCommitBlock setup.program
            (ProtocolState.withHistory setup.program
              (lift (ProtocolState.entry (block.prepend suffix) source)) past) = _
          rw [← memory, ProtocolState.withHistory_entry, ← automatic,
            block.automaticCommitBlock_entry_prepend suffix boundary]
        have observed := congrArg CommitRecoveryState.point exactState
        rw [installed.close_of_exhausted finished failed survives, exhaustedPoint] at observed
        change next.residual.lift
          (ProtocolState.entry next.residual.tail next.source) = _ at observed
        exact (congrArg (fun point => ProtocolState.cell? setup.program point
          name (.commitment owner payload)) observed).trans
            ((liftCell origin _ _ _).trans ((blockCell block suffix _ _ _).trans
              ((ProtocolState.cell?_entry suffix _ _ _).trans autoRead)))
    · apply ordinary
      exact CommitRecoveryState.close_point_of_no_new_failure installed failed
  · apply ordinary
    have savedCommit : ProtocolState.atCommit setup.program installed.saved = true :=
      (commits _).trans committing
    simp only [CommitRecoveryState.close, finished, savedCommit, ↓reduceIte]
    rfl

theorem accepted_binding_inclusion
    (reference : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some reference))
    (before : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before)) (retained : TracePrefix prior trace)
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (selected : snapshot = before.execution.application.current.native ∨
      snapshot = before.execution.application.entry.native ∨
      ∃ record ∈ before.execution.application.retired, snapshot = record.state)
    (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent))
    (accepted : snapshot.accepted (.inr event) = some handle) :
    ∃ (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
      (first last : (nativeApplication).Control)
      (retainedTrace : (nativeProtocol).Trace (some first))
      (joint : Player → Option (nativeApplication).Action)
      (legal : (nativeProtocol).Legal (some first) joint)
      (realized : some last ∈ ((nativeProtocol).step (some first) ⟨joint, legal⟩).support)
      (native : EventGraphRuntime.State (serviceGraph setup .concurrent)),
      TracePrefix (retainedTrace.extend joint legal realized) trace ∧
      message ∈ reference.execution.network.inputs ∧
      (message.id, true) ∈ reference.execution.receipts ∧
      message.sender = handle.1 ∧
      message.payload.packet.call = .commitment event handle ∧
      message.payload.attempt = first.execution.application.attempt ∧
      first.execution.application.handle implementation.runtime message =
        some last.execution.application ∧
      first.execution.network.lookup message.id = some message ∧
      EventGraphRuntime.handle implementation.runtime first.execution.application.current.native
        ⟨message.id, message.payload.packet.call⟩ = some native ∧
      native.accepted (.inr event) = some handle ∧
      PhaseClosingEffect implementation.runtime implementation.leaks first.execution last.execution
        (first.execution.application.current.inclusionResult message.payload.packet.call native) ∧
      last.execution.application = ({ first.execution.application with
        current := first.execution.application.current.inclusionResult
          message.payload.packet.call native } :
          PhaseRuntimeState (serviceGraph setup .concurrent)).normalize := by
  obtain ⟨entry, recorded, message, emitted, sender, call, receipt⟩ :=
    accepted_snapshot_receipt setup implementation reference trace before prior retained
      snapshot selected event handle accepted
  have rawTrace := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  have recallInput := (nativeApplication).history_inputRecall nativeInitial
    implementation.horizon implementation.scheduler rawTrace handle.1
  have authored : message ∈ (reference.execution.recall handle.1).filterMap
      (fun entry => entry.emitted) := List.mem_filterMap.mpr ⟨entry, recorded, emitted⟩
  change message ∈ (nativeApplication).outputs (reference.execution.recall handle.1) at authored
  rw [← recallInput] at authored
  have input := (List.mem_filter.mp authored).1
  obtain ⟨first, last, retainedTrace, joint, legal, realized, onward,
      absent, present, _idle, _nextIdle, included⟩ :=
    accepting_receipt_transition setup implementation message.id trace ⟨reference, rfl, receipt⟩
  obtain ⟨packet, native, found, attempt, acceptedCall, handled, normalized⟩ :=
    accepting_receipt_handler setup implementation first last retainedTrace message.id
      absent present included
  have firstPrefix : TracePrefix retainedTrace trace :=
    (TracePrefix.extend .refl joint legal realized).trans onward
  have equal := receipt_lookup_eq setup implementation reference first trace
    retainedTrace firstPrefix
    message packet input found
  subst packet
  refine ⟨message, first, last, retainedTrace, joint, legal, realized, native,
    onward, input, receipt, sender, call, attempt, acceptedCall, found, handled, ?_,
    Or.inl ⟨message.id, message, native, found, included, handled, rfl⟩, normalized⟩
  have tables := handle_commitment_tables implementation.runtime
    first.execution.application.current.native native message.id event handle
      (by simpa only [call] using handled)
  rw [tables.2.1, Function.update_self]

theorem sourceHandleMeaning_of_emission
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some reference))
    (handle : Handle (serviceGraph setup .concurrent))
    (record : (nativeApplication).PlayerEntry)
    (recorded : record ∈ reference.execution.recall handle.1)
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (emitted : record.emitted = some message)
    (event : (serviceGraph setup .concurrent).EventId)
    (call : message.payload.packet.call = .commitment event handle)
    (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (value : Option (L.Val payload))
    (read : sourceBindingAt setup message.payload.attempt event owner payload binding
      target.trace = value) :
    sourceHandleMeaning setup implementation target reference handle =
      value.map (fun result => (⟨payload, result⟩ : Raw L)) := by
  classical
  let rawTrace := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  have inputRecall := (nativeApplication).history_inputRecall nativeInitial implementation.horizon
    implementation.scheduler rawTrace
  have clean := (PhaseCount.onePacketMenu_countClean implementation.runtime implementation.leaks
    implementation.bounds implementation.scheduler).history nativeInitial implementation.horizon
      (fun state _ => PhaseCount.countClean_initial implementation.runtime implementation.leaks
        state) trace
  have input (entry : (nativeApplication).PlayerEntry)
      (member : entry ∈ reference.execution.recall handle.1)
      (sent : Message Player (nativeApplication).Payload) (output : entry.emitted = some sent) :
      sent ∈ reference.execution.network.inputs := by
    have authored : sent ∈ (nativeApplication).outputs (reference.execution.recall handle.1) :=
      List.mem_filterMap.mpr ⟨entry, member, output⟩
    rw [← inputRecall handle.1] at authored
    exact (List.mem_filter.mp authored).1
  have present := input record recorded message emitted
  have permitted := (PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message present)
  have correct := permitted.2.1
  unfold CountCallCorrect at correct
  dsimp only [PhaseCount.nativeMessage] at correct
  rw [call] at correct
  obtain ⟨_, _, _, ⟨serial, prepared⟩, _⟩ := correct
  let locate := fun entry : (nativeApplication).PlayerEntry =>
    entry.emitted.bind fun sent => match sent.payload.packet.call with
      | .commitment named candidate => if candidate = handle then
          match shape : (serviceGraph setup .concurrent).outputLayout named with
          | .binding owner payload =>
              (sourceBindingAt setup sent.payload.attempt named owner payload shape
                target.trace).map fun value => (⟨payload, value⟩ : Raw L)
          | _ => none
        else none
      | _ => none
  have atRecord : locate record = value.map (fun result => (⟨payload, result⟩ : Raw L)) := by
    simp only [locate, emitted, Option.bind_some, call, ite_true]
    split
    · rename_i other otherPayload fieldEq
      obtain ⟨rfl, rfl⟩ := EventField.binding.inj (fieldEq.symm.trans binding)
      exact congrArg (Option.map (fun result => (⟨otherPayload, result⟩ : Raw L))) read
    · rename_i notBinding
      exact (notBinding owner payload binding).elim
  have constant : ∀ entry ∈ reference.execution.recall handle.1,
      locate entry = none ∨
        locate entry = value.map (fun result => (⟨payload, result⟩ : Raw L)) := by
    intro entry member
    cases output : entry.emitted with
    | none => exact Or.inl (by simp only [locate, output, Option.bind_none])
    | some sent =>
        cases packet : sent.payload.packet.call with
        | opening | malformed =>
            exact Or.inl (by simp only [locate, output, Option.bind_some, packet])
        | commitment named candidate =>
            by_cases same : candidate = handle
            · subst candidate
              have sentInput := input entry member sent output
              have sentPermitted := (PhaseCount.permits_eq_true_iff _ _).mp
                (clean.2 sent sentInput)
              have identity := PhaseCount.commitment_eq_of_handle
                reference.execution.network.inputs message sent permitted sentPermitted
                present sentInput (fun left leftInput right rightInput identified =>
                  (nativeApplication).input_identifier_injective_history nativeInitial
                    implementation.horizon implementation.scheduler reference rawTrace
                    left right leftInput rightInput identified) call packet
              subst sent
              exact Or.inr (by
                simpa only [locate, output, emitted, Option.bind_some] using atRecord)
            · exact Or.inl (by
                simp only [locate, output, Option.bind_some, packet, ite_eq_right same])
  cases value with
  | none =>
      unfold sourceHandleMeaning
      rw [prepared]
      change (reference.execution.recall handle.1).findSome? locate = none
      cases found : (reference.execution.recall handle.1).findSome? locate with
      | none => rfl
      | some raw =>
          obtain ⟨entry, member, result⟩ := List.exists_of_findSome?_eq_some found
          have empty : locate entry = none := (constant entry member).elim id id
          rw [empty] at result
          cases result
  | some value =>
      simp only [Option.map_some] at atRecord constant ⊢
      have hasValue : ((reference.execution.recall handle.1).findSome? locate).isSome :=
        List.findSome?_isSome_iff.mpr ⟨record, recorded, by rw [atRecord]; rfl⟩
      obtain ⟨raw, found⟩ := Option.isSome_iff_exists.mp hasValue
      obtain ⟨entry, member, result⟩ := List.exists_of_findSome?_eq_some found
      have same : raw = (⟨payload, value⟩ : Raw L) := by
        rcases constant entry member with empty | same
        · rw [empty] at result
          cases result
        · exact Option.some.inj (result.symm.trans same)
      unfold sourceHandleMeaning
      rw [prepared]
      exact found.trans (congrArg some same)

theorem accepted_snapshot_catalogue
    (reference : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some reference))
    (before : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before))
    (retained : TracePrefix prior trace)
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (selected : snapshot = before.execution.application.current.native ∨
      snapshot = before.execution.application.entry.native ∨
      ∃ record ∈ before.execution.application.retired, snapshot = record.state)
    (owner : Player) (payload : L.Ty)
    (field : FieldRef (serviceGraph setup .concurrent).layout (.binding owner payload))
    (handle : Handle (serviceGraph setup .concurrent))
    (accepted : snapshot.accepted field.field = some handle) :
    snapshot.BindingInvariant ∧
      reference.execution.application.current.native.candidates.lookup handle =
        snapshot.candidates.lookup handle := by
  let inputs := setup.initialLaw.map encodeInputs
  have raw : ((nativeApplication).protocol
      (inputs.map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some before) := by
    rw [show inputs.map (PhaseRuntimeState.initial implementation.plan) = nativeInitial by
      simp only [inputs, ReservedConcurrentImplementation.initial, PMF.map_comp,
        Function.comp_def]]
    exact (nativeMenu).toRawTrace nativeInitial implementation.horizon
      implementation.scheduler prior
  have current := phaseBindingRecord_history implementation.runtime implementation.leaks
    implementation.plan inputs implementation.horizon implementation.scheduler raw
  have invariant : snapshot.BindingInvariant ∧
      KeepsFixedCandidates snapshot before.execution.application.current.native := by
    rcases selected with rfl | rfl | ⟨record, member, rfl⟩
    · exact ⟨current.active, fun _ _ => rfl⟩
    · exact ⟨current.saved, current.fixed⟩
    · obtain ⟨binding, _reachable, fixed⟩ := phaseRetiredBindings_history
        implementation.runtime implementation.leaks implementation.plan inputs
        implementation.horizon implementation.scheduler raw record member
      exact ⟨binding, fixed⟩
  have fixed := invariant.1.accepted_fixed field.field handle accepted
  have original := invariant.2 handle fixed
  let stable := phaseApplication_preservesFixedCandidates implementation.runtime
    implementation.leaks
  have preserved : (nativeApplication).Invariant (fun state =>
      state.current.native.candidates.lookup handle = snapshot.candidates.lookup handle) := by
    constructor
    · intro state owner material known
      exact (stable.submit state owner material handle
        (by rw [known]; exact fixed)).trans known
    · intro state message next known handled
      exact (stable.handle state message next handled handle
        (by rw [known]; exact fixed)).trans known
    · intro state command next known reached
      exact (stable.environment state command next reached handle
        (by rw [known]; exact fixed)).trans known
  exact ⟨invariant.1, preserved.tracePrefix (nativeMenu) nativeInitial implementation.horizon
    implementation.scheduler before reference prior trace retained original⟩

open Classical in
def sourceSnapshotPair
    (target : setup.proposalRecoveryProtocol.History)
    (control : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (field : (serviceGraph setup .concurrent).Field) :
    Option (((serviceGraph setup .concurrent).layout field).Value ×
      ((serviceGraph setup .concurrent).layout field).Value) :=
  if (serviceGraph setup .concurrent).fieldPublic field then none else
    (snapshot.config.store field).bind fun before =>
      match field with
      | .inl input => target.state.map fun current =>
          (before, encodeInputs (ProtocolState.base setup.program current.point) input)
      | .inr event =>
          match nodeView (serviceGraph setup .concurrent) event with
          | .bind _owner payload shape _ =>
              match cast (congrArg EventField.Value shape) before with
              | .failure => none
              | .success first =>
                  (snapshot.accepted (.inr event)).bind fun handle =>
                    ((sourceHandleMeaning setup implementation target control handle).orElse
                      (fun _ => lost handle)).bind fun raw =>
                        (raw.as? payload).map fun second =>
                          (cast (congrArg EventField.Value shape.symm) (.success first),
                            cast (congrArg EventField.Value shape.symm) (.success second))
          | .resolve .. | .sample .. => none

omit [Fintype Player] in
private theorem sourceSnapshotPair_public
    (target : setup.proposalRecoveryProtocol.History)
    (control : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (field : (serviceGraph setup .concurrent).Field)
    (visible : (serviceGraph setup .concurrent).fieldPublic field) :
    sourceSnapshotPair setup implementation target control lost snapshot field = none := by
  classical
  simp only [sourceSnapshotPair, visible, ↓reduceIte]

omit [Fintype Player] in
private theorem sourceSnapshotPair_binding
    (target : setup.proposalRecoveryProtocol.History)
    (control : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId) (owner : Player) (payload : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (first second : ((serviceGraph setup .concurrent).outputLayout event).Value)
    (paired : sourceSnapshotPair setup implementation target control lost snapshot (.inr event) =
      some (first, second)) :
    first ≠ cast (congrArg EventField.Value shape.symm) .failure ∧
      second ≠ cast (congrArg EventField.Value shape.symm) .failure := by
  classical
  unfold sourceSnapshotPair at paired
  split at paired
  · cases paired
  · obtain ⟨before, _stored, paired⟩ := Option.bind_eq_some_iff.mp paired
    dsimp only at paired
    cases descriptor : nodeView (serviceGraph setup .concurrent) event with
    | bind other ty outputEq codeEq =>
        have kinds := EventField.binding.inj (outputEq.symm.trans shape)
        obtain ⟨rfl, rfl⟩ := kinds
        rw [descriptor] at paired
        dsimp only at paired
        cases result : cast (congrArg EventField.Value outputEq) before with
        | failure =>
            rw [result] at paired
            cases paired
        | success value =>
            rw [result] at paired
            obtain ⟨handle, _accepted, paired⟩ := Option.bind_eq_some_iff.mp paired
            obtain ⟨raw, _meaning, paired⟩ := Option.bind_eq_some_iff.mp paired
            obtain ⟨next, _typed, pairEq⟩ := Option.map_eq_some_iff.mp paired
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj pairEq
            constructor <;> intro impossible <;>
              have contradiction := congrArg (cast (congrArg EventField.Value shape)) impossible
            all_goals
              simp only [cast_cast, cast_eq] at contradiction
              cases contradiction
    | resolve other ty ref checks outputEq codeEq =>
        simp only [descriptor] at paired
        cases paired
    | sample ty law outputEq codeEq =>
        simp only [descriptor] at paired
        cases paired

omit [Fintype Player] in
theorem sourceSnapshotPair_binding_value
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId) (owner : Player) (payload : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (code : cast (congrArg (EventCode (serviceGraph setup .concurrent).layout) shape)
      ((serviceGraph setup .concurrent).nodes event) = .bind owner payload)
    (node : nodeView (serviceGraph setup .concurrent) event = .bind owner payload shape code)
    (handle : Handle (serviceGraph setup .concurrent)) (old next : L.Val payload)
    (stored : snapshot.config.store (.inr event) =
      some (cast (congrArg EventField.Value shape.symm) (.success old)))
    (accepted : snapshot.accepted (.inr event) = some handle)
    (meaning : sourceHandleMeaning setup implementation target reference handle =
      some (⟨payload, next⟩ : Raw L)) :
    sourceSnapshotPair setup implementation target reference lost snapshot (.inr event) =
      some (cast (congrArg EventField.Value shape.symm) (.success old),
        cast (congrArg EventField.Value shape.symm) (.success next)) := by
  classical
  have hidden : ¬ (serviceGraph setup .concurrent).fieldPublic (.inr event) := by
    change ¬ ((serviceGraph setup .concurrent).outputLayout event).IsPublic
    rw [shape]
    exact not_false
  simp only [sourceSnapshotPair, hidden, ↓reduceIte, stored, Option.bind_some, node,
    cast_cast, cast_eq, accepted, meaning, Option.orElse_some, Raw.as?, ↓reduceDIte,
    Option.map_some]

def sourceSnapshotPairs
    (target : setup.proposalRecoveryProtocol.History)
    (control : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent)) :
    (serviceGraph setup .concurrent).SwapPairs where
  pair := sourceSnapshotPair setup implementation target control lost snapshot
  public_none := sourceSnapshotPair_public setup implementation target control lost snapshot
  binding_success := sourceSnapshotPair_binding setup implementation target control lost snapshot

def sourceSnapshotState
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent)) :
    EventGraphRuntime.State (serviceGraph setup .concurrent) :=
  snapshot.swap (HiddenSwap.ofPairs
    (sourceSnapshotPairs setup implementation target reference lost snapshot)
    (sourceHandlePairs setup implementation target reference lost))

def sourceSnapshotAssignment
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : PhaseRuntimeState (serviceGraph setup .concurrent)) :
    PhaseRuntimeState (serviceGraph setup .concurrent) :=
  { before with
    entry := { before.entry with
      native := sourceSnapshotState setup implementation target reference lost before.entry.native }
    current := { before.current with
      native := sourceSnapshotState setup implementation target reference lost
        before.current.native }
    retired := before.retired.map fun record => { record with
      state := sourceSnapshotState setup implementation target reference lost record.state } }

omit [Fintype Player] in
theorem sourceSnapshotPair_accept_other
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (ready : before.config.cut.Ready event)
    (action : (serviceGraph setup .concurrent).Action event)
    (value : ((serviceGraph setup .concurrent).outputLayout event).Value)
    (handle : Handle (serviceGraph setup .concurrent))
    (field : (serviceGraph setup .concurrent).Field)
    (different : field ≠ Sum.inr event) :
    sourceSnapshotPair setup implementation target reference lost
        { before.complete event ready action value with
          accepted := Function.update before.accepted (.inr event) (some handle)
          candidates := before.candidates.freeze handle } field =
      sourceSnapshotPair setup implementation target reference lost before field := by
  classical
  have store :
      (before.complete event ready action value).config.store field =
        before.config.store field := by
    cases field with
    | inl input => rfl
    | inr query =>
        exact Config.complete_output_of_ne before.config event query ready action value
          (fun same => different (congrArg Sum.inr same))
  unfold sourceSnapshotPair
  split
  · rfl
  · change ((before.complete event ready action value).config.store field).bind _ = _
    rw [store]
    cases field with
    | inl input => rfl
    | inr query =>
        simp only [Function.update_of_ne different]

omit [Fintype Player] in
private theorem sourceSnapshotSwap_accept_before
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (ready : before.config.cut.Ready event)
    (action : (serviceGraph setup .concurrent).Action event)
    (value : ((serviceGraph setup .concurrent).outputLayout event).Value)
    (handle : Handle (serviceGraph setup .concurrent)) :
    let after : EventGraphRuntime.State (serviceGraph setup .concurrent) :=
      { before.complete event ready action value with
        accepted := Function.update before.accepted (.inr event) (some handle)
        candidates := before.candidates.freeze handle }
    before.swap (HiddenSwap.ofPairs
        (sourceSnapshotPairs setup implementation target reference lost after)
        (sourceHandlePairs setup implementation target reference lost)) =
      before.swap (HiddenSwap.ofPairs
        (sourceSnapshotPairs setup implementation target reference lost before)
        (sourceHandlePairs setup implementation target reference lost)) := by
  classical
  dsimp only
  let after : EventGraphRuntime.State (serviceGraph setup .concurrent) :=
    { before.complete event ready action value with
      accepted := Function.update before.accepted (.inr event) (some handle)
      candidates := before.candidates.freeze handle }
  have other (field : (serviceGraph setup .concurrent).Field)
      (different : field ≠ Sum.inr event) :
      (sourceSnapshotPairs setup implementation target reference lost after).pair field =
        (sourceSnapshotPairs setup implementation target reference lost before).pair field :=
    sourceSnapshotPair_accept_other setup implementation target reference lost before event
      ready action value handle field different
  have absent : before.config.outputs event = none := by
    cases read : before.config.outputs event with
    | none => rfl
    | some value =>
        exact False.elim (ready.1 ((before.config.output_available event).mp
          (by simp only [read, Option.isSome_some])))
  have sameConfig :
      before.config.swap (ValueSwap.ofPairs
        (sourceSnapshotPairs setup implementation target reference lost after)) =
      before.config.swap (ValueSwap.ofPairs
        (sourceSnapshotPairs setup implementation target reference lost before)) := by
    apply Config.ext_fields
    · funext input
      change EventGraph.pairSwap
        ((sourceSnapshotPairs setup implementation target reference lost after).pair (.inl input))
          _ = _
      rw [other (.inl input) (by simp)]
      rfl
    · rfl
    · funext query
      change (before.config.outputs query).map _ = (before.config.outputs query).map _
      by_cases same : query = event
      · subst query
        rw [absent]
        rfl
      · change (before.config.outputs query).map
          (EventGraph.pairSwap ((sourceSnapshotPairs setup implementation target reference lost
            after).pair (.inr query))) = _
        rw [other (.inr query) (fun equal => same (Sum.inr.inj equal))]
        rfl
    · change before.config.history.map _ = before.config.history.map _
      apply List.map_congr_left
      intro completion member
      have different : completion.event ≠ event := by
        intro same
        apply ready.1
        apply (before.config.history_exact event).mp
        exact same ▸ List.mem_map.mpr ⟨completion, member, rfl⟩
      have pairs := other (.inr completion.event)
        (fun same => different (Sum.inr.inj same))
      change Completion.mk completion.event
        ((sourceSnapshotPairs setup implementation target reference lost after).action
          completion.event completion.action) = _
      congr 1
      change (sourceSnapshotPairs setup implementation target reference lost after).action
        completion.event completion.action =
        (sourceSnapshotPairs setup implementation target reference lost before).action
          completion.event completion.action
      unfold SwapPairs.action
      rw [pairs]
  change State.mk _ _ _ _ _ = State.mk _ _ _ _ _
  simp only [State.mk.injEq]
  refine ⟨sameConfig, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

omit [Fintype Player] in
private theorem sourceSnapshot_handle_binding
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (before after : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (id : MessageId Player) (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent)) (owner : Player) (payload : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (old next : L.Val payload)
    (original : before.candidates.lookup handle = .openable (⟨payload, old⟩ : Raw L))
    (registered : reference.execution.application.current.native.candidates.lookup handle =
      .openable (⟨payload, old⟩ : Raw L))
    (meaning : sourceHandleMeaning setup implementation target reference handle =
      some (⟨payload, next⟩ : Raw L))
    (accepted : EventGraphRuntime.handle runtime before ⟨id, .commitment event handle⟩ =
      some after) :
    EventGraphRuntime.handle runtime
        (before.swap (HiddenSwap.ofPairs
          (sourceSnapshotPairs setup implementation target reference lost before)
          (sourceHandlePairs setup implementation target reference lost)))
        ⟨id, .commitment event handle⟩ =
      some (after.swap (HiddenSwap.ofPairs
        (sourceSnapshotPairs setup implementation target reference lost after)
        (sourceHandlePairs setup implementation target reference lost))) := by
  classical
  obtain ⟨ready, timely, actualOwner, actualPayload, actualShape, code, node, sender,
    handleOwner, vacant, unused⟩ :=
    handle_commitment_conditions runtime before after id event handle accepted
  obtain ⟨rfl, rfl⟩ := EventField.binding.inj (shape.symm.trans actualShape)
  have result : before.bindingResult handle payload = .success old := by
    simp only [State.bindingResult, original, Raw.as?, ↓reduceDIte, cast_eq, Option.elim_some]
  have afterEq : after =
      { before.complete event ready
          (cast (congrArg EventField.Action shape.symm) (.success old))
          (cast (congrArg EventField.Value shape.symm) (.success old)) with
        accepted := Function.update before.accepted (.inr event) (some handle)
        candidates := before.candidates.freeze handle } := by
    have actual := handle_commitment_eq runtime before id event handle owner payload shape code
      node ready timely sender handleOwner vacant unused
    rw [result] at actual
    exact Option.some.inj (accepted.symm.trans actual)
  let swap := HiddenSwap.ofPairs
    (sourceSnapshotPairs setup implementation target reference lost after)
    (sourceHandlePairs setup implementation target reference lost)
  have handlePair : sourceHandlePairs setup implementation target reference lost handle =
      some ((⟨payload, old⟩ : Raw L), (⟨payload, next⟩ : Raw L)) := by
    simp only [sourceHandlePairs, registered, meaning, Option.orElse_some, Option.map_some]
  have fieldPair :
      (sourceSnapshotPairs setup implementation target reference lost after).pair (.inr event) =
        some (cast (congrArg EventField.Value shape.symm) (.success old),
          cast (congrArg EventField.Value shape.symm) (.success next)) := by
    apply sourceSnapshotPair_binding_value setup implementation target reference lost after
      event owner payload shape code node handle old next
    · rw [afterEq]
      exact Config.complete_output_same _ _ _ _ _
    · rw [afterEq]
      simp only [Function.update_self]
    · exact meaning
  have compatible : BindCompatible swap event handle :=
    HiddenSwap.bindCompatible_ofPairs _ _ shape old next fieldPair handlePair
  have preEq : before.swap swap =
      before.swap (HiddenSwap.ofPairs
        (sourceSnapshotPairs setup implementation target reference lost before)
        (sourceHandlePairs setup implementation target reference lost)) := by
    dsimp only [swap]
    rw [afterEq]
    exact sourceSnapshotSwap_accept_before setup implementation target reference lost before
      event ready _ _ handle
  rw [← preEq]
  have replay := handle_swap runtime swap before ⟨id, .commitment event handle⟩
    (by
      intro state actualEvent actualHandle _ packet
      obtain ⟨rfl, rfl⟩ := Payload.commitment.inj packet
      exact compatible)
    (by
      intro actualEvent opening _
      obtain ⟨candidate, raw, impossible⟩ := opening
      cases impossible)
  rw [replay, accepted, Option.map_some]

omit [Fintype Player] in
private theorem sourceSnapshot_handle_failed_binding
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (before after : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (id : MessageId Player) (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent)) (owner : Player) (payload : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (failed : before.bindingResult handle payload = .failure)
    (unchanged : sourceHandlePairs setup implementation target reference lost handle = none)
    (accepted : EventGraphRuntime.handle runtime before ⟨id, .commitment event handle⟩ =
      some after) :
    EventGraphRuntime.handle runtime
        (sourceSnapshotState setup implementation target reference lost before)
        ⟨id, .commitment event handle⟩ =
      some (sourceSnapshotState setup implementation target reference lost after) := by
  classical
  obtain ⟨ready, timely, actualOwner, actualPayload, actualShape, code, node, sender,
    handleOwner, vacant, unused⟩ :=
    handle_commitment_conditions runtime before after id event handle accepted
  obtain ⟨rfl, rfl⟩ := EventField.binding.inj (shape.symm.trans actualShape)
  have afterEq : after =
      { before.complete event ready
          (cast (congrArg EventField.Action shape.symm) (PublicationResult.failure :
            PublicationResult (L.Val payload)))
          (cast (congrArg EventField.Value shape.symm) (PublicationResult.failure :
            PublicationResult (L.Val payload))) with
        accepted := Function.update before.accepted (.inr event) (some handle)
        candidates := before.candidates.freeze handle } := by
    have actual := handle_commitment_eq runtime before id event handle owner payload shape code
      node ready timely sender handleOwner vacant unused
    rw [failed] at actual
    exact Option.some.inj (accepted.symm.trans actual)
  let swap := HiddenSwap.ofPairs
    (sourceSnapshotPairs setup implementation target reference lost after)
    (sourceHandlePairs setup implementation target reference lost)
  have eventNone : (sourceSnapshotPairs setup implementation target reference lost after).pair
      (.inr event) = none := by
    simp only [sourceSnapshotPairs, sourceSnapshotPair]
    split
    · rfl
    · simp only [afterEq, State.complete, Config.store, Config.complete_output_same,
        Option.bind_some, node, cast_cast, cast_eq]
  have compatible : BindCompatible swap event handle :=
    HiddenSwap.bindCompatible_ofPairs_none _ _ eventNone unchanged
  have beforeEq : before.swap swap =
      sourceSnapshotState setup implementation target reference lost before := by
    dsimp only [swap, sourceSnapshotState]
    rw [afterEq]
    exact sourceSnapshotSwap_accept_before setup implementation target reference lost before
      event ready _ _ handle
  change EventGraphRuntime.handle runtime
      (sourceSnapshotState setup implementation target reference lost before)
      ⟨id, .commitment event handle⟩ = some (after.swap swap)
  rw [← beforeEq]
  have replay := handle_swap runtime swap before ⟨id, .commitment event handle⟩
    (by
      intro state actualEvent actualHandle _ packet
      obtain ⟨rfl, rfl⟩ := Payload.commitment.inj packet
      exact compatible)
    (by
      intro actualEvent opening _
      obtain ⟨candidate, raw, impossible⟩ := opening
      cases impossible)
  rw [replay, accepted, Option.map_some]

omit [Fintype Player] in
theorem sourceSnapshotPair_submit
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (who : Player) (material : WitnessedSubmission (serviceGraph setup .concurrent)) :
    sourceSnapshotPair setup implementation target reference lost
        (submitStep (material.call.register before who) who material.call.packet) =
      sourceSnapshotPair setup implementation target reference lost before := by
  have registered := material.call.register_facts who before
  have configEq := (submitStep_config (material.call.register before who) who
    material.call.packet).trans registered.1
  have acceptedEq := congrArg PublicView.accepted
    ((submitStep_publicView (material.call.register before who) who material.call.packet).trans
      registered.2)
  change (submitStep (material.call.register before who) who material.call.packet).accepted =
    before.accepted at acceptedEq
  funext field
  unfold sourceSnapshotPair
  rw [configEq, acceptedEq]

omit [Fintype Player] in
private theorem sourceSnapshot_submit
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (who : Player) (material : WitnessedSubmission (serviceGraph setup .concurrent)) :
    let swap := HiddenSwap.ofPairs
      (sourceSnapshotPairs setup implementation target reference lost before)
      (sourceHandlePairs setup implementation target reference lost)
    let after := submitStep (material.call.register before who) who material.call.packet
    submitStep (((material.swap swap).call).register (before.swap swap) who) who
        (material.swap swap).call.packet =
      after.swap (HiddenSwap.ofPairs
        (sourceSnapshotPairs setup implementation target reference lost after)
        (sourceHandlePairs setup implementation target reference lost)) := by
  classical
  dsimp only
  rw [WitnessedSubmission.submit_swap]
  have pairsEq :
      sourceSnapshotPairs setup implementation target reference lost
          (submitStep (material.call.register before who) who material.call.packet) =
        sourceSnapshotPairs setup implementation target reference lost before := by
    unfold sourceSnapshotPairs
    congr 1
    exact sourceSnapshotPair_submit setup implementation target reference lost before who material
  rw [pairsEq]

omit [Fintype Player] in
theorem sourceSnapshotPair_complete_public
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (ready : before.config.cut.Ready event)
    (action : (serviceGraph setup .concurrent).Action event)
    (value : ((serviceGraph setup .concurrent).outputLayout event).Value)
    (visible : (serviceGraph setup .concurrent).fieldPublic (.inr event)) :
    sourceSnapshotPair setup implementation target reference lost
        (before.complete event ready action value) =
      sourceSnapshotPair setup implementation target reference lost before := by
  classical
  funext field
  by_cases same : field = Sum.inr event
  · subst field
    simp only [sourceSnapshotPair, visible, ↓reduceIte]
  · have store : (before.complete event ready action value).config.store field =
        before.config.store field := by
      cases field with
      | inl input => rfl
      | inr query =>
          exact Config.complete_output_of_ne before.config event query ready action value
            (fun equal => same (congrArg Sum.inr equal))
    unfold sourceSnapshotPair
    split
    · rfl
    · change ((before.complete event ready action value).config.store field).bind _ = _
      rw [store]
      rfl

omit [Fintype Player] in
theorem sourceSnapshotPair_sample
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (before after : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (supported : after ∈ (environmentStep runtime before (.executeSample event)).support) :
    sourceSnapshotPair setup implementation target reference lost after =
      sourceSnapshotPair setup implementation target reference lost before := by
  classical
  by_cases ready : before.config.cut.Ready event
  · cases node : nodeView (serviceGraph setup .concurrent) event with
    | bind owner payload shape code =>
        rw [environmentStep_executeSample_of_nonsample runtime before event ready (by
          intro other law output code sample
          rw [node] at sample
          cases sample), PMF.mem_support_pure_iff] at supported
        cases supported
        rfl
    | resolve owner payload binding checks shape code =>
        rw [environmentStep_executeSample_of_nonsample runtime before event ready (by
          intro other law output code sample
          rw [node] at sample
          cases sample), PMF.mem_support_pure_iff] at supported
        cases supported
        rfl
    | sample payload law shape code =>
        rw [environmentStep_executeSample_eq runtime before event ready payload law
          shape code node, Config.step, PMF.map_comp, PMF.support_map] at supported
        obtain ⟨value, _positive, rfl⟩ := supported
        exact sourceSnapshotPair_complete_public setup implementation target reference lost
          before event ready _ value (by
            change ((serviceGraph setup .concurrent).outputLayout event).IsPublic
            rw [shape]
            trivial)
  · rw [environmentStep_executeSample_of_not_ready runtime before event ready,
      PMF.mem_support_pure_iff] at supported
    cases supported
    rfl

omit [Fintype Player] in
private theorem sourceSnapshotPair_completeFailure
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (ready : before.config.cut.Ready event) :
    sourceSnapshotPair setup implementation target reference lost
        (before.completeFailure event ready) =
      sourceSnapshotPair setup implementation target reference lost before := by
  classical
  have absent : before.config.outputs event = none := by
    cases read : before.config.outputs event with
    | none => rfl
    | some value =>
        exact False.elim (ready.1 ((before.config.output_available event).mp
          (by simp only [read, Option.isSome_some])))
  have acceptedEq : (before.completeFailure event ready).accepted = before.accepted := by
    unfold State.completeFailure
    split <;> rfl
  funext field
  by_cases same : field = Sum.inr event
  · subst field
    cases node : nodeView (serviceGraph setup .concurrent) event with
    | bind owner payload shape code =>
        have hidden : ¬ (serviceGraph setup .concurrent).fieldPublic (.inr event) := by
          change ¬ ((serviceGraph setup .concurrent).outputLayout event).IsPublic
          rw [shape]
          exact not_false
        simp [sourceSnapshotPair, hidden, State.completeFailure, node, State.complete,
          Config.store, Config.complete, absent]
    | resolve owner payload binding checks shape code =>
        have visible : (serviceGraph setup .concurrent).fieldPublic (.inr event) := by
          change ((serviceGraph setup .concurrent).outputLayout event).IsPublic
          rw [shape]
          trivial
        exact (sourceSnapshotPair_public setup implementation target reference lost
          (before.completeFailure event ready) (.inr event) visible).trans
            (sourceSnapshotPair_public setup implementation target reference lost before
              (.inr event) visible).symm
    | sample => simp only [State.completeFailure, node]
  · have storeEq : (before.completeFailure event ready).config.store field =
        before.config.store field := by
      cases field with
      | inl input =>
          unfold State.completeFailure
          split <;> rfl
      | inr query =>
          have different : query ≠ event := fun equal => same (congrArg Sum.inr equal)
          unfold State.completeFailure
          split
          · exact Config.complete_output_of_ne _ _ _ _ _ _ different
          · exact Config.complete_output_of_ne _ _ _ _ _ _ different
          · rfl
    unfold sourceSnapshotPair
    rw [storeEq, acceptedEq]

omit [Fintype Player] in
private theorem sourceSnapshotPair_expiry
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (before after : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (supported : after ∈ (environmentStep runtime before (.expire event)).support) :
    sourceSnapshotPair setup implementation target reference lost after =
      sourceSnapshotPair setup implementation target reference lost before := by
  classical
  have stutter (law : environmentStep runtime before (.expire event) = PMF.pure before) :
      sourceSnapshotPair setup implementation target reference lost after =
        sourceSnapshotPair setup implementation target reference lost before := by
    rw [law, PMF.mem_support_pure_iff] at supported
    cases supported
    rfl
  by_cases ready : before.config.cut.Ready event
  · cases activated : before.activatedAt event with
    | none =>
        exact stutter
          (environmentStep_expire_of_not_activated runtime before event ready activated)
    | some entered =>
      by_cases due : runtime.deadline event ≤ before.clock - entered
      · cases node : nodeView (serviceGraph setup .concurrent) event with
        | bind owner payload shape code =>
          rw [environmentStep_expire_bind_eq runtime before event ready entered activated due
            owner payload shape code node, PMF.mem_support_pure_iff] at supported
          subst after
          simpa only [State.completeFailure, node] using
            sourceSnapshotPair_completeFailure setup implementation target reference lost
              before event ready
        | resolve owner payload binding checks shape code =>
          rw [environmentStep_expire_resolve_eq runtime before event ready entered activated due
            owner payload binding checks shape code node, PMF.mem_support_pure_iff] at supported
          subst after
          exact sourceSnapshotPair_complete_public setup implementation target reference lost
            before event ready _ _ (by
              change ((serviceGraph setup .concurrent).outputLayout event).IsPublic
              rw [shape]
              trivial)
        | sample payload law shape code =>
          exact stutter (environmentStep_expire_sample_eq runtime before event ready entered
            activated due payload law shape code node)
      · exact stutter
          (environmentStep_expire_of_not_due runtime before event ready entered activated due)
  · exact stutter (environmentStep_expire_of_not_ready runtime before event ready)

omit [Fintype Player] in
private theorem sourceSnapshot_environment
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (before : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (command : EnvironmentCommand (serviceGraph setup .concurrent)) :
    environmentStep runtime (sourceSnapshotState setup implementation target reference lost before)
        command =
      (environmentStep runtime before command).map
        (sourceSnapshotState setup implementation target reference lost) := by
  classical
  unfold sourceSnapshotState
  rw [environmentStep_swap runtime _ before command
    (fun address _ _ _ _ _ => ValueSwap.ofPairs_expiryFixed _ address)]
  apply GameTheory.Math.Probability.map_congr_on_support
  intro after supported
  have pairsEq : sourceSnapshotPairs setup implementation target reference lost after =
      sourceSnapshotPairs setup implementation target reference lost before := by
    unfold sourceSnapshotPairs
    congr 1
    cases command with
    | advanceClock =>
      simp only [environmentStep, PMF.mem_support_pure_iff] at supported
      subst after
      rfl
    | executeSample event =>
      exact sourceSnapshotPair_sample setup implementation target reference lost runtime
        before after event supported
    | expire event =>
      exact sourceSnapshotPair_expiry setup implementation target reference lost runtime
        before after event supported
  rw [pairsEq]

omit [Fintype Player] in
theorem sourceSnapshot_reveal_fixed_initial
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (source : CommitRecoveryState setup.program) (present : target.state = some source)
    (event : (serviceGraph setup .concurrent).EventId)
    (input : (serviceGraph setup .concurrent).InputId)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup .concurrent).layout (.binding owner payload))
    (checks : List (GuardCheck (serviceGraph setup .concurrent).layout payload))
    (shape : (serviceGraph setup .concurrent).outputLayout event = .publication payload)
    (code : cast (congrArg (EventCode (serviceGraph setup .concurrent).layout) shape)
      ((serviceGraph setup .concurrent).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (serviceGraph setup .concurrent) event =
      .resolve owner payload binding checks shape code)
    (field : binding.field = .inl input)
    (kind : (serviceGraph setup .concurrent).inputLayout input = .binding owner payload)
    (value : L.Val payload)
    (stored : before.config.store (.inl input) =
      some (cast (congrArg EventField.Value kind.symm) (.success value)))
    (initial : encodeInputs (ProtocolState.base setup.program source.point) input =
      cast (congrArg EventField.Value kind.symm) (.success value))
    (accepted : before.accepted (.inl input) = some (owner, .initial input))
    (registered : reference.execution.application.current.native.candidates.lookup
      (owner, .initial input) = .openable (⟨payload, value⟩ : Raw L)) :
    RevealFixed (HiddenSwap.ofPairs
      (sourceSnapshotPairs setup implementation target reference lost before)
      (sourceHandlePairs setup implementation target reference lost)) before event := by
  classical
  have targetCandidate := State.initial_candidate_binding_success
    (encodeInputs (ProtocolState.base setup.program source.point)) input owner payload kind value
    (by rw [initial]; simp only [cast_cast, cast_eq])
  have meaning : sourceHandleMeaning setup implementation target reference
      (owner, .initial input) = some (⟨payload, value⟩ : Raw L) := by
    simp only [sourceHandleMeaning, present, Option.bind_some, targetCandidate]
  rw [RevealFixed, node]
  constructor
  · change EventGraph.pairSwap
      (sourceSnapshotPair setup implementation target reference lost before binding.field) = id
    rw [field]
    unfold sourceSnapshotPair
    split
    · rfl
    · simp only [stored, Option.bind_some, present, Option.map_some, initial]
      simp [EventGraph.pairSwap]
  · intro candidate retainedHandle
    rw [field, accepted] at retainedHandle
    have same : candidate = (owner, .initial input) := (Option.some.inj retainedHandle).symm
    subst candidate
    change EventGraph.pairSwap
      (sourceHandlePairs setup implementation target reference lost (owner, .initial input)) = id
    simp [sourceHandlePairs, registered, meaning, EventGraph.pairSwap]

omit [Fintype Player] in
theorem sourceSnapshot_reveal_fixed_output
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (event bound : (serviceGraph setup .concurrent).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup .concurrent).layout (.binding owner payload))
    (checks : List (GuardCheck (serviceGraph setup .concurrent).layout payload))
    (shape : (serviceGraph setup .concurrent).outputLayout event = .publication payload)
    (code : cast (congrArg (EventCode (serviceGraph setup .concurrent).layout) shape)
      ((serviceGraph setup .concurrent).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (serviceGraph setup .concurrent) event =
      .resolve owner payload binding checks shape code)
    (field : binding.field = .inr bound)
    (boundShape : (serviceGraph setup .concurrent).outputLayout bound = .binding owner payload)
    (boundCode : cast (congrArg (EventCode (serviceGraph setup .concurrent).layout) boundShape)
      ((serviceGraph setup .concurrent).nodes bound) = .bind owner payload)
    (boundNode : nodeView (serviceGraph setup .concurrent) bound =
      .bind owner payload boundShape boundCode)
    (handle : Handle (serviceGraph setup .concurrent)) (value : L.Val payload)
    (stored : before.config.store (.inr bound) =
      some (cast (congrArg EventField.Value boundShape.symm) (.success value)))
    (accepted : before.accepted (.inr bound) = some handle)
    (registered : reference.execution.application.current.native.candidates.lookup handle =
      .openable (⟨payload, value⟩ : Raw L))
    (meaning : sourceHandleMeaning setup implementation target reference handle =
      some (⟨payload, value⟩ : Raw L)) :
    RevealFixed (HiddenSwap.ofPairs
      (sourceSnapshotPairs setup implementation target reference lost before)
      (sourceHandlePairs setup implementation target reference lost)) before event := by
  classical
  rw [RevealFixed, node]
  constructor
  · change EventGraph.pairSwap
      (sourceSnapshotPair setup implementation target reference lost before binding.field) = id
    rw [field, sourceSnapshotPair_binding_value setup implementation target reference lost
      before bound owner payload boundShape boundCode boundNode handle value value
      stored accepted meaning]
    simp [EventGraph.pairSwap]
  · intro candidate present
    rw [field, accepted] at present
    have same : candidate = handle := (Option.some.inj present).symm
    subst candidate
    change EventGraph.pairSwap
      (sourceHandlePairs setup implementation target reference lost handle) = id
    simp [sourceHandlePairs, registered, meaning, EventGraph.pairSwap]

omit [Fintype Player] in
theorem sourceSnapshot_handle_opening
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (before : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (id : MessageId Player) (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent)) (raw : Raw L)
    (fixed : before.config.cut.Ready event → RevealFixed (HiddenSwap.ofPairs
      (sourceSnapshotPairs setup implementation target reference lost before)
      (sourceHandlePairs setup implementation target reference lost)) before event) :
    EventGraphRuntime.handle runtime
        (sourceSnapshotState setup implementation target reference lost before)
        ⟨id, .opening event handle raw⟩ =
      (EventGraphRuntime.handle runtime before ⟨id, .opening event handle raw⟩).map
        (sourceSnapshotState setup implementation target reference lost) := by
  classical
  let swap := HiddenSwap.ofPairs
    (sourceSnapshotPairs setup implementation target reference lost before)
    (sourceHandlePairs setup implementation target reference lost)
  have replay := handle_swap runtime swap before ⟨id, .opening event handle raw⟩
    (by intro next other candidate _ impossible; cases impossible)
    (by
      intro other packet ready
      obtain ⟨candidate, value, equal⟩ := packet
      have same : event = other := (Payload.opening.inj equal).1
      subst other
      exact fixed ready)
  cases step : EventGraphRuntime.handle runtime before ⟨id, .opening event handle raw⟩ with
  | none => simpa only [step, Option.map_none, sourceSnapshotState, swap] using replay
  | some after =>
      obtain ⟨ready, _timely, owner, payload, binding, checks, shape, code, value, result,
        _node, _sender, _owner, _accepted, _raw, _catalogue, _stored, _evaluated, completed⟩ :=
        handle_opening_conditions runtime before after id event handle raw step
      have visible : (serviceGraph setup .concurrent).fieldPublic (.inr event) := by
        change ((serviceGraph setup .concurrent).outputLayout event).IsPublic
        rw [shape]
        trivial
      have pairEq : sourceSnapshotPairs setup implementation target reference lost after =
          sourceSnapshotPairs setup implementation target reference lost before := by
        unfold sourceSnapshotPairs
        congr 1
        rw [completed]
        exact sourceSnapshotPair_complete_public setup implementation target reference lost
          before event ready _ _ visible
      simpa only [step, Option.map_some, sourceSnapshotState, pairEq, swap] using replay

omit [Fintype Player] in
private theorem sourceSnapshotPair_drain
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (before : RecoveryState (serviceGraph setup .concurrent)) :
    sourceSnapshotPair setup implementation target reference lost (phase.drain before).native =
      sourceSnapshotPair setup implementation target reference lost before.native := by
  suffices ∀ fuel (state : RecoveryState (serviceGraph setup .concurrent)),
      sourceSnapshotPair setup implementation target reference lost
          (phase.drainFuel fuel state).native =
        sourceSnapshotPair setup implementation target reference lost state.native from
    this _ before
  intro fuel
  induction fuel with
  | zero => intro state; rfl
  | succ fuel ih =>
      intro state
      unfold RuntimePhase.drainFuel
      split
      · rename_i pending
        rw [ih]
        exact sourceSnapshotPair_completeFailure setup implementation target reference lost
          state.native _ _
      · rfl

omit [Fintype Player] in
private theorem sourceSnapshotPair_restore
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (entry current : RecoveryState (serviceGraph setup .concurrent)) :
    sourceSnapshotPair setup implementation target reference lost
        (PhaseRuntimeState.restore entry current).native =
      sourceSnapshotPair setup implementation target reference lost entry.native := rfl

omit [Fintype Player] in
theorem sourceSnapshotAssignment_normalize
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : PhaseRuntimeState (serviceGraph setup .concurrent)) :
    (sourceSnapshotAssignment setup implementation target reference lost before).normalize =
      sourceSnapshotAssignment setup implementation target reference lost before.normalize := by
  classical
  let image (state : RecoveryState (serviceGraph setup .concurrent)) :=
    { state with native :=
        sourceSnapshotState setup implementation target reference lost state.native }
  let retire (record : RetiredCommitAttempt (serviceGraph setup .concurrent)) :=
    { record with state :=
        sourceSnapshotState setup implementation target reference lost record.state }
  have excluded (state : RecoveryState (serviceGraph setup .concurrent)) :
      (image state).excluded = state.excluded := rfl
  have drain (phase : RuntimePhase (serviceGraph setup .concurrent))
      (state : RecoveryState (serviceGraph setup .concurrent)) :
      phase.drain (image state) = image (phase.drain state) := by
    have pairsEq : sourceSnapshotPairs setup implementation target reference lost
        (phase.drain state).native =
        sourceSnapshotPairs setup implementation target reference lost state.native := by
      unfold sourceSnapshotPairs
      congr 1
      exact sourceSnapshotPair_drain setup implementation target reference lost phase state
    change phase.drain (state.swap (HiddenSwap.ofPairs
      (sourceSnapshotPairs setup implementation target reference lost state.native)
      (sourceHandlePairs setup implementation target reference lost))) = _
    rw [phase.drain_swap _ state (fun event => ValueSwap.ofPairs_expiryFixed _ event)]
    dsimp only [image, sourceSnapshotState, RecoveryState.swap]
    rw [pairsEq]
  have restore (entry current : RecoveryState (serviceGraph setup .concurrent)) :
      PhaseRuntimeState.restore (image entry) (image current) =
        image (PhaseRuntimeState.restore entry current) := by
    have pairsEq : sourceSnapshotPairs setup implementation target reference lost
        (PhaseRuntimeState.restore entry current).native =
        sourceSnapshotPairs setup implementation target reference lost entry.native := by
      rfl
    dsimp only [image, sourceSnapshotState]
    rw [pairsEq]
    rfl
  have finished (phase : RuntimePhase (serviceGraph setup .concurrent))
      (state : RecoveryState (serviceGraph setup .concurrent)) :
      phase.Finished (image state) ↔ phase.Finished state :=
    RuntimePhase.finished_swap _ phase state
  have settle : ∀ (phases : List (RuntimePhase (serviceGraph setup .concurrent)))
      generation entry current retired,
      PhaseRuntimeState.settle phases generation (image entry) (image current)
          (retired.map retire) =
        sourceSnapshotAssignment setup implementation target reference lost
          (PhaseRuntimeState.settle phases generation entry current retired) := by
    intro phases
    induction phases with
    | nil => intro generation entry current retired; rfl
    | cons phase remaining ih =>
      intro generation entry current retired
      simp only [PhaseRuntimeState.settle, drain, finished, excluded]
      by_cases done : phase.Finished (phase.drain current)
      · simp only [done, ↓reduceIte]
        by_cases missed : phase.kind = .commitment ∧
            (((phase.drain current).excluded \ entry.excluded) ∩ phase.owners).Nonempty
        · simp only [missed, and_self, ↓reduceIte]
          by_cases survives : (phase.owners \ (phase.drain current).excluded).Nonempty
          · simp only [survives, ↓reduceIte, restore, drain]
            simp only [sourceSnapshotAssignment, image, retire, List.map_append,
              List.map_cons, List.map_nil]
          · simp only [survives, ↓reduceIte, restore, drain]
            have next := ih generation
              (phase.drain (PhaseRuntimeState.restore entry (phase.drain current)))
              (phase.drain (PhaseRuntimeState.restore entry (phase.drain current)))
              (retired ++ [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩])
            rw [List.map_append, List.map_cons, List.map_nil] at next
            exact next
        · simp only [missed, ↓reduceIte]
          exact ih generation (phase.drain current) (phase.drain current) retired
      · simp only [done, ↓reduceIte]
        rfl
  exact settle before.phases before.generation before.entry before.current before.retired

omit [Fintype Player] in
theorem properBinding_opening
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent)) (owner : Player) (payload : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (value : L.Val payload)
    (packet : material.call.packet = .commitment event handle)
    (prepared : PhaseProposal.bindingPreparation material = some (⟨payload, value⟩ : Raw L)) :
    material.call.opening = some (⟨payload, value⟩ : Raw L) := by
  classical
  unfold PhaseProposal.bindingPreparation at prepared
  rw [packet] at prepared
  dsimp only at prepared
  rw [shape] at prepared
  obtain ⟨sampled, typed, same⟩ := Option.map_eq_some_iff.mp prepared
  have sampledEq : sampled = value := eq_of_heq (Raw.mk.inj same).2
  subst sampled
  obtain ⟨raw, opening, decoded⟩ := Option.bind_eq_some_iff.mp typed
  have rawEq : raw = (⟨payload, value⟩ : Raw L) := by
    rcases raw with ⟨ty, data⟩
    unfold Raw.as? at decoded
    split at decoded
    · rename_i sameType
      cases sameType
      simp only [cast_eq, Option.some.injEq] at decoded
      cases decoded
      rfl
    · contradiction
  exact opening.trans (congrArg some rawEq)

omit [Fintype Player] in
theorem properBinding_calls_eq
    (first second : WitnessedSubmission (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent)) (owner : Player) (payload : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (value : L.Val payload)
    (firstPacket : first.call.packet = .commitment event handle)
    (secondPacket : second.call.packet = .commitment event handle)
    (firstPrepared : PhaseProposal.bindingPreparation first = some (⟨payload, value⟩ : Raw L))
    (secondPrepared : PhaseProposal.bindingPreparation second = some (⟨payload, value⟩ : Raw L)) :
    first.call = second.call := by
  have firstOpening := properBinding_opening setup first event handle owner payload shape value
    firstPacket firstPrepared
  have secondOpening := properBinding_opening setup second event handle owner payload shape value
    secondPacket secondPrepared
  cases firstCall : first.call
  cases secondCall : second.call
  simp only [firstCall, secondCall] at firstPacket secondPacket firstOpening secondOpening ⊢
  congr 1
  · exact firstPacket.trans secondPacket.symm
  · exact firstOpening.trans secondOpening.symm

omit [Fintype Player] in
theorem sourceSnapshotAssignment_submit
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : PhaseRuntimeState (serviceGraph setup .concurrent))
    (who : Player) (material : WitnessedSubmission (serviceGraph setup .concurrent)) :
    let swap := HiddenSwap.ofPairs
      (sourceSnapshotPairs setup implementation target reference lost before.current.native)
      (sourceHandlePairs setup implementation target reference lost)
    (sourceSnapshotAssignment setup implementation target reference lost before).submit
        who (material.swap swap) =
      sourceSnapshotAssignment setup implementation target reference lost
        (before.submit who material) := by
  classical
  dsimp only
  have native := sourceSnapshot_submit setup implementation target reference lost
    before.current.native who material
  dsimp only at native
  change ({ sourceSnapshotAssignment setup implementation target reference lost before with
    current := ⟨_, before.current.excluded⟩ } :
      PhaseRuntimeState (serviceGraph setup .concurrent)) = _
  change submitStep _ _ _ = sourceSnapshotState setup implementation target reference lost
    (submitStep (material.call.register before.current.native who) who material.call.packet)
    at native
  dsimp only [sourceSnapshotAssignment, sourceSnapshotState]
  rw [native]
  rfl

omit [Fintype Player] in
theorem sourceSnapshotAssignment_handle_binding
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (before after : PhaseRuntimeState (serviceGraph setup .concurrent))
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent)) (owner : Player) (payload : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (packet : message.payload.packet.call = .commitment event handle)
    (meaning :
      (∃ old next : L.Val payload,
        before.current.native.candidates.lookup handle = .openable (⟨payload, old⟩ : Raw L) ∧
        reference.execution.application.current.native.candidates.lookup handle =
          .openable (⟨payload, old⟩ : Raw L) ∧
        sourceHandleMeaning setup implementation target reference handle =
          some (⟨payload, next⟩ : Raw L)) ∨
      (before.current.native.bindingResult handle payload = .failure ∧
        sourceHandlePairs setup implementation target reference lost handle = none))
    (accepted : before.handle runtime message = some after) :
    (sourceSnapshotAssignment setup implementation target reference lost before).handle
        runtime message =
      some (sourceSnapshotAssignment setup implementation target reference lost after) := by
  classical
  unfold PhaseRuntimeState.handle at accepted ⊢
  have gate :
      (message.payload.tokenValid
          (sourceSnapshotAssignment setup implementation target reference lost before).attempt &&
        (sourceSnapshotAssignment setup implementation target reference lost before).allows
          message.payload.packet.call &&
        !(sourceSnapshotAssignment setup implementation target reference lost
            before).current.excludedCall message.payload.packet.call) =
      (message.payload.tokenValid before.attempt && before.allows message.payload.packet.call &&
        !before.current.excludedCall message.payload.packet.call) := rfl
  rw [gate]
  split at accepted
  · rename_i admitted
    rw [ite_eq_left admitted]
    cases nativeStep : EventGraphRuntime.handle runtime before.current.native
        ⟨message.id, message.payload.packet.call⟩ with
    | none => simp only [nativeStep, Option.map_none, reduceCtorEq] at accepted
    | some native =>
      have nativeAccepted : EventGraphRuntime.handle runtime before.current.native
          ⟨message.id, .commitment event handle⟩ = some native := by
        simpa only [packet] using nativeStep
      have replay : EventGraphRuntime.handle runtime
          (sourceSnapshotState setup implementation target reference lost before.current.native)
          ⟨message.id, .commitment event handle⟩ =
          some (sourceSnapshotState setup implementation target reference lost native) := by
        rcases meaning with ⟨old, next, original, registered, read⟩ | ⟨failed, unchanged⟩
        · exact sourceSnapshot_handle_binding setup implementation target reference lost
            runtime before.current.native native message.id event handle owner payload shape
            old next original registered read nativeAccepted
        · exact sourceSnapshot_handle_failed_binding setup implementation target reference lost
            runtime before.current.native native message.id event handle owner payload shape
            failed unchanged nativeAccepted
      have actual : ({ before with current :=
          before.current.inclusionResult message.payload.packet.call native } :
            PhaseRuntimeState (serviceGraph setup .concurrent)).normalize = after := by
        exact Option.some.inj (by simpa only [nativeStep, Option.map_some] using accepted)
      change Option.map _ (EventGraphRuntime.handle runtime
        (sourceSnapshotState setup implementation target reference lost before.current.native)
        ⟨message.id, message.payload.packet.call⟩) = _
      rw [packet, replay, Option.map_some]
      have updated :
          ({ sourceSnapshotAssignment setup implementation target reference lost before with
            current :=
              (sourceSnapshotAssignment setup implementation target reference lost
                  before).current.inclusionResult (.commitment event handle)
                  (sourceSnapshotState setup implementation target reference lost native) } :
                    PhaseRuntimeState (serviceGraph setup .concurrent)) =
          sourceSnapshotAssignment setup implementation target reference lost
            { before with
              current := before.current.inclusionResult (.commitment event handle) native } := rfl
      rw [updated, sourceSnapshotAssignment_normalize]
      simpa only [packet] using congrArg
        (fun state => some
          (sourceSnapshotAssignment setup implementation target reference lost state))
        actual
  · cases accepted

omit [Fintype Player] in
theorem sourceSnapshotAssignment_handle_opening
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (before : PhaseRuntimeState (serviceGraph setup .concurrent))
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent)) (raw : Raw L)
    (packet : message.payload.packet.call = .opening event handle raw)
    (fixed :
      (message.payload.tokenValid before.attempt && before.allows message.payload.packet.call &&
        !before.current.excludedCall message.payload.packet.call) = true →
      before.current.native.config.cut.Ready event → RevealFixed (HiddenSwap.ofPairs
      (sourceSnapshotPairs setup implementation target reference lost before.current.native)
      (sourceHandlePairs setup implementation target reference lost)) before.current.native event) :
    (sourceSnapshotAssignment setup implementation target reference lost before).handle
        runtime message =
      (before.handle runtime message).map
        (sourceSnapshotAssignment setup implementation target reference lost) := by
  classical
  unfold PhaseRuntimeState.handle
  have gate :
      (message.payload.tokenValid
          (sourceSnapshotAssignment setup implementation target reference lost before).attempt &&
        (sourceSnapshotAssignment setup implementation target reference lost before).allows
          message.payload.packet.call &&
        !(sourceSnapshotAssignment setup implementation target reference lost
            before).current.excludedCall message.payload.packet.call) =
      (message.payload.tokenValid before.attempt && before.allows message.payload.packet.call &&
        !before.current.excludedCall message.payload.packet.call) := rfl
  rw [gate]
  split
  · rename_i admitted
    change Option.map _ (EventGraphRuntime.handle runtime
        (sourceSnapshotState setup implementation target reference lost before.current.native)
        ⟨message.id, message.payload.packet.call⟩) = _
    rw [packet, sourceSnapshot_handle_opening setup implementation target reference lost
      runtime before.current.native message.id event handle raw (fixed admitted), Option.map_map,
      Option.map_map]
    congr 1
    funext native
    change
      ({ sourceSnapshotAssignment setup implementation target reference lost before with
        current := (sourceSnapshotAssignment setup implementation target reference lost
            before).current.inclusionResult (.opening event handle raw)
            (sourceSnapshotState setup implementation target reference lost native) } :
              PhaseRuntimeState (serviceGraph setup .concurrent)).normalize = _
    have updated :
        ({ sourceSnapshotAssignment setup implementation target reference lost before with
          current := (sourceSnapshotAssignment setup implementation target reference lost
              before).current.inclusionResult (.opening event handle raw)
              (sourceSnapshotState setup implementation target reference lost native) } :
                PhaseRuntimeState (serviceGraph setup .concurrent)) =
        sourceSnapshotAssignment setup implementation target reference lost
          { before with
            current := before.current.inclusionResult (.opening event handle raw) native } := by
      simp only [sourceSnapshotAssignment, RecoveryState.inclusionResult, sourceSnapshotState,
        RecoveryState.publicationFailed_swap]
    rw [updated, sourceSnapshotAssignment_normalize]
    rfl
  · rfl

omit [Fintype Player] in
theorem sourceSnapshotAssignment_environment
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (before : PhaseRuntimeState (serviceGraph setup .concurrent))
    (command : EnvironmentCommand (serviceGraph setup .concurrent)) :
    (sourceSnapshotAssignment setup implementation target reference lost before).environment
        runtime command =
      (before.environment runtime command).map
        (sourceSnapshotAssignment setup implementation target reference lost) := by
  classical
  unfold PhaseRuntimeState.environment
  have allowed : (sourceSnapshotAssignment setup implementation target reference lost
      before).commandAllowed command = before.commandAllowed command := rfl
  rw [allowed]
  split
  · change ((environmentStep runtime
      (sourceSnapshotState setup implementation target reference lost before.current.native)
      command).map _) = _
    rw [sourceSnapshot_environment, PMF.map_comp, PMF.map_comp]
    congr 1
    funext native
    dsimp only [Function.comp_apply]
    have updated :
        ({ sourceSnapshotAssignment setup implementation target reference lost before with
          current :=
            (sourceSnapshotAssignment setup implementation target reference lost
              before).current.environmentResult command
                (sourceSnapshotState setup implementation target reference lost native) } :
                  PhaseRuntimeState (serviceGraph setup .concurrent)) =
        sourceSnapshotAssignment setup implementation target reference lost
          { before with current := before.current.environmentResult command native } := by
      cases command <;> rfl
    rw [updated, sourceSnapshotAssignment_normalize]
  · rw [PMF.pure_map]

omit [Fintype Player] in
theorem sourceSnapshotAssignment_rejected_binding
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (runtime : EventGraphRuntime (serviceGraph setup .concurrent))
    (before : PhaseRuntimeState (serviceGraph setup .concurrent))
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent))
    (packet : message.payload.packet.call = .commitment event handle)
    (rejected : before.handle runtime message = none) :
    (sourceSnapshotAssignment setup implementation target reference lost before).handle
        runtime message = none := by
  classical
  let swap := HiddenSwap.ofPairs
    (sourceSnapshotPairs setup implementation target reference lost before.current.native)
    (sourceHandlePairs setup implementation target reference lost)
  unfold PhaseRuntimeState.handle at rejected ⊢
  have gate :
      (message.payload.tokenValid
          (sourceSnapshotAssignment setup implementation target reference lost before).attempt &&
        (sourceSnapshotAssignment setup implementation target reference lost before).allows
          message.payload.packet.call &&
        !(sourceSnapshotAssignment setup implementation target reference lost
            before).current.excludedCall message.payload.packet.call) =
      (message.payload.tokenValid before.attempt && before.allows message.payload.packet.call &&
        !before.current.excludedCall message.payload.packet.call) := rfl
  rw [gate]
  split at rejected
  · rename_i admitted
    rw [ite_eq_left admitted]
    have nativeNone : EventGraphRuntime.handle runtime before.current.native
        ⟨message.id, message.payload.packet.call⟩ = none :=
      Option.map_eq_none_iff.mp rejected
    have replay := handle_swap runtime swap before.current.native
      ⟨message.id, message.payload.packet.call⟩
      (by
        intro native actualEvent actualHandle accepted _
        rw [nativeNone] at accepted
        cases accepted)
      (by
        intro actualEvent opening _
        obtain ⟨candidate, raw, impossible⟩ := opening
        rw [packet] at impossible
        cases impossible)
    change Option.map _ (EventGraphRuntime.handle runtime
      (before.current.native.swap swap) ⟨message.id, message.payload.packet.call⟩) = none
    rw [replay, nativeNone, Option.map_none, Option.map_none]
  · rename_i denied
    rw [ite_eq_right denied]

omit [Fintype Player] in
theorem sourceSnapshotAssignment_public
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : PhaseRuntimeState (serviceGraph setup .concurrent)) :
    (sourceSnapshotAssignment setup implementation target reference lost before).publicView =
      before.publicView := by
  simp only [sourceSnapshotAssignment, sourceSnapshotState, PhaseRuntimeState.publicView,
    State.swap_publicView, List.map_map, Function.comp_def, PhaseRuntimeState.attempt]

theorem sourceSnapshot_binding_available
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (left right : (nativeApplication).Execution)
    (application : right.application = sourceSnapshotAssignment setup implementation
      target reference lost left.application)
    (network : left.network = right.network)
    (leftRecall : PhaseCount.CountRecall implementation.runtime implementation.leaks left)
    (rightRecall : PhaseCount.CountRecall implementation.runtime implementation.leaks right)
    (owner : Player) (event : (serviceGraph setup .concurrent).EventId) (serial : Nat)
    (first second : Option (Raw L))
    (evidence : EvidenceRequest (serviceGraph setup .concurrent))
    (bounded : implementation.bounds.AllowsOpening second)
    (member : (⟨some ⟨⟨.commitment event (owner, .prepared serial), first⟩, evidence⟩⟩ :
      (nativeApplication).Action) ∈ PhaseCount.onePacketActions implementation.runtime
        implementation.leaks implementation.bounds owner (left.recall owner)
          (left.observe nativeApplication owner)) :
    (⟨some ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩⟩ :
      (nativeApplication).Action) ∈ PhaseCount.onePacketActions implementation.runtime
        implementation.leaks implementation.bounds owner (right.recall owner)
          (right.observe nativeApplication owner) := by
  classical
  let source : WitnessedSubmission (serviceGraph setup .concurrent) :=
    ⟨⟨.commitment event (owner, .prepared serial), first⟩, evidence⟩
  let replacement : WitnessedSubmission (serviceGraph setup .concurrent) :=
    ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩
  rw [PhaseCount.mem_onePacketActions] at member ⊢
  have permitted : PhaseCount.permits ((nativeApplication).outputs (left.recall owner))
      (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
        (left.recall owner) (left.observe nativeApplication owner) source) = true := by
    rcases member.2 with impossible | ⟨material, transmitted, allowed⟩
    · cases impossible
    · cases Option.some.inj transmitted
      exact allowed
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp permitted).2.1
  have call : (PhaseCount.nativeMessage (PhaseCount.localEnvelope implementation.runtime
      implementation.leaks owner (left.recall owner)
        (left.observe nativeApplication owner) source)).payload.call =
      .commitment event (owner, .prepared serial) := PhaseCount.maskPacket_call _ _
  unfold CountCallCorrect at correct
  rw [call] at correct
  have absent := correct.2.1
  have resolved : evidence.resolve owner
      (source.call.candidateAfter owner
        (left.observe nativeApplication owner).application.1.candidates)
      ((ReactiveApplication.ResponseMenu.knownPackets (left.recall owner)
        (left.observe nativeApplication owner)).map PhaseCount.nativeMessage) = none := by
    change (PhaseCount.maskPacket (left.observe nativeApplication owner).application.2
      ⟨source.call.packet, _, _⟩).evidence = none at absent
    unfold PhaseCount.maskPacket at absent
    split at absent <;> split at absent <;> exact absent
  have outputs : (nativeApplication).outputs (left.recall owner) =
      (nativeApplication).outputs (right.recall owner) := by
    rw [← leftRecall.1 owner, ← rightRecall.1 owner, network]
  have serials : (nativeApplication).submissionCount (left.recall owner) =
      (nativeApplication).submissionCount (right.recall owner) := by
    rw [← leftRecall.2.1 owner, ← rightRecall.2.1 owner, network]
  have publicEq : left.application.publicView = right.application.publicView := by
    rw [application, sourceSnapshotAssignment_public]
  have nativePublic : left.application.current.native.publicView =
      right.application.current.native.publicView := by
    rw [application]
    simp only [sourceSnapshotAssignment, sourceSnapshotState, State.swap_publicView]
  have envelope : PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
      (left.recall owner) (left.observe nativeApplication owner) source =
      PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
        (right.recall owner) (right.observe nativeApplication owner) replacement := by
    unfold PhaseCount.localEnvelope
    rw [resolved]
    change (⟨(owner, _), ⟨left.application.publicView.attempt,
      PhaseCount.maskPacket left.application.publicView
        ⟨.commitment event (owner, .prepared serial), none,
          left.application.current.native.publicView.tokenFor
            (.commitment event (owner, .prepared serial))⟩⟩⟩ :
      Message Player (CommitAttemptPacket (serviceGraph setup .concurrent))) = _
    rw [serials, publicEq, nativePublic]
    rfl
  constructor
  · have sourceBound := member.1
    rw [PhaseCount.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem] at sourceBound
    have sourceBounds := (implementation.bounds.submissions_mem _ _).mp sourceBound
    rw [PhaseCount.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
    apply (implementation.bounds.submissions_mem _ _).mpr
    exact ⟨⟨sourceBounds.1.1, bounded⟩, trivial⟩
  · right
    refine ⟨replacement, rfl, ?_⟩
    rw [← outputs, ← envelope]
    exact permitted

def sourceSnapshot_binding_trace
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (left : (nativeApplication).Execution) (right : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some right))
    (application : right.execution.application = sourceSnapshotAssignment setup implementation
      target reference lost left.application)
    (network : left.network = right.execution.network)
    (leftRecall : PhaseCount.CountRecall implementation.runtime implementation.leaks left)
    (owner : Player) (acting : right.actor = some owner)
    (event : (serviceGraph setup .concurrent).EventId) (serial : Nat)
    (first second : Option (Raw L))
    (evidence : EvidenceRequest (serviceGraph setup .concurrent))
    (bounded : implementation.bounds.AllowsOpening second)
    (member : (⟨some ⟨⟨.commitment event (owner, .prepared serial), first⟩, evidence⟩⟩ :
      (nativeApplication).Action) ∈ PhaseCount.onePacketActions implementation.runtime
        implementation.leaks implementation.bounds owner (left.recall owner)
          (left.observe nativeApplication owner)) :
    (nativeProtocol).Trace (some {
      right with
      actor := none
      execution := right.execution.respond nativeApplication owner
        ⟨some ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩⟩ }) := by
  classical
  let replacement : (nativeApplication).Action :=
    ⟨some ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩⟩
  have rightRecall := PhaseCount.countRecall_history implementation.runtime implementation.leaks
    ((nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler prior)
  have available := sourceSnapshot_binding_available setup implementation target reference lost
    left right.execution application network leftRecall rightRecall owner event serial
      first second evidence bounded member
  rcases right with ⟨remaining, actor, execution⟩
  dsimp only at acting
  subst actor
  exact Classical.choose (HiddenSwap.phase_respond_trace_prefix
    implementation.bounds nativeInitial implementation.horizon implementation.scheduler
    remaining execution owner replacement prior available)

private theorem submittedArchived
    (execution : (nativeApplication).Execution)
    (witness : RecoverySourceWitness setup .concurrent implementation.plan execution.application)
    (archived : witness.checkpoint.ArchivedProposals execution.network.inputs)
    (owner : Player) (material : WitnessedSubmission (serviceGraph setup .concurrent)) :
    (witness.submit implementation.runtime implementation.leaks owner
      material).checkpoint.ArchivedProposals
        (execution.respond nativeApplication owner ⟨some material⟩).network.inputs := by
  obtain ⟨weakNext, weakArchived, fuel, path⟩ := witness.respond_archived_source
    implementation.runtime implementation.leaks execution archived owner
      ⟨some material⟩
  have counts := setup.commitRecovery_same_generation_length path _ _ rfl rfl rfl
  dsimp only [CommitRecoveryState.atPoint] at counts
  have firstRank := witness.checkpoint.saved_position
  have lastRank := weakNext.checkpoint.saved_position
  have firstBound := ProtocolState.remaining_le_instructionCount setup.program
    (witness.checkpoint.residual.lift (ProtocolState.entry
      witness.checkpoint.residual.tail witness.checkpoint.source))
  have lastBound := ProtocolState.remaining_le_instructionCount setup.program
    (weakNext.checkpoint.residual.lift (ProtocolState.entry
      weakNext.checkpoint.residual.tail weakNext.checkpoint.source))
  have unchanged :
      (⟨_, weakNext.checkpoint.trace⟩ : setup.commitRecoveryProtocol.History) =
        ⟨_, witness.checkpoint.trace⟩ := by
    apply path.eq_of_trace_length_eq
    change witness.checkpoint.trace.length = weakNext.checkpoint.trace.length
    change instructionCount setup.program - ProtocolState.remaining setup.program
        (witness.checkpoint.residual.lift (ProtocolState.entry
          witness.checkpoint.residual.tail witness.checkpoint.source)) =
        execution.application.attempt.phase at firstRank
    change instructionCount setup.program - ProtocolState.remaining setup.program
        (weakNext.checkpoint.residual.lift (ProtocolState.entry
          weakNext.checkpoint.residual.tail weakNext.checkpoint.source)) =
        execution.application.attempt.phase at lastRank
    omega
  intro observer survives
  let labels := nativeArchiveLabels setup (PhaseProposal.sourceArchive
    (execution.respond nativeApplication owner ⟨some material⟩).network.inputs)
  have sameArchive := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    setup.proposalRecoveryArchive observer ((sourceModel).infoOf observer
      (setup.proposalRecoveryLiftTrace labels history.trace))) unchanged
  exact sameArchive.symm.trans (weakArchived observer survives)

def checkpointSelectionStep (operational : implementation.Operational)
    {before after : (nativeProtocol).State} (priorTrace : (nativeProtocol).Trace before)
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal before joint)
    (realized : after ∈ ((nativeProtocol).step before ⟨joint, legal⟩).support)
    (previous : before.elim PUnit (fun control =>
      {witness : RecoverySourceWitness setup .concurrent implementation.plan
          control.execution.application //
        witness.checkpoint.ArchivedProposals control.execution.network.inputs})) :
    {selected : after.elim PUnit (fun control =>
      {witness : RecoverySourceWitness setup .concurrent implementation.plan
          control.execution.application //
        witness.checkpoint.ArchivedProposals control.execution.network.inputs}) //
      match before, after, previous, selected with
      | none, none, _, _ => False
      | none, some control, _, last =>
          ∃ (theta : State L setup.context) (drawn : theta ∈ setup.initialLaw.support),
            control.execution.application =
              PhaseRuntimeState.initial implementation.plan (encodeInputs theta) ∧
            (⟨_, last.val.checkpoint.trace⟩ : setup.commitRecoveryProtocol.History) =
              ⟨_, (RecoverySourceCheckpoint.initialized setup .concurrent
                implementation.plan theta drawn).trace⟩
      | some _, none, _, _ => False
      | some _, some _, first, last =>
          ∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
            ⟨_, first.val.checkpoint.trace⟩ ⟨_, last.val.checkpoint.trace⟩} := by
  classical
  change after ∈ ((nativeApplication).transition nativeInitial implementation.horizon
    implementation.scheduler before joint).support at realized
  cases before with
  | none =>
    have initialized : ∃ draw : State L setup.context,
        draw ∈ setup.initialLaw.support ∧ after = some
          ⟨implementation.horizon, none, ReactiveApplication.Execution.initial nativeApplication
            (PhaseRuntimeState.initial implementation.plan (encodeInputs draw))⟩ := by
      change after ∈ ((nativeInitial).map fun state => some
        (⟨implementation.horizon, none, ReactiveApplication.Execution.initial nativeApplication
          state⟩ : (nativeApplication).Control)).support at realized
      obtain ⟨physical, physicalSupport, rfl⟩ := PMF.support_map .. ▸ realized
      have initialEq : nativeInitial = setup.initialLaw.map
          (fun draw => PhaseRuntimeState.initial implementation.plan (encodeInputs draw)) :=
        rfl
      rw [initialEq] at physicalSupport
      obtain ⟨draw, drawn, rfl⟩ := PMF.support_map .. ▸ physicalSupport
      exact ⟨draw, drawn, rfl⟩
    apply Classical.choice
    obtain ⟨draw, drawn, targetEq⟩ := initialized
    subst after
    exact ⟨⟨⟨RecoverySourceWitness.initialized setup .concurrent implementation.plan draw drawn,
      RecoverySourceWitness.initialized_archivedProposals setup .concurrent
        implementation.plan draw drawn⟩, draw, drawn, rfl, rfl⟩⟩
  | some control =>
    change {witness : RecoverySourceWitness setup .concurrent implementation.plan
        control.execution.application //
      witness.checkpoint.ArchivedProposals control.execution.network.inputs} at previous
    let witness := previous.val
    have archived := previous.property
    rcases control with ⟨remaining, actor, execution⟩
    cases actor with
    | some owner =>
      have offered := legal.2 owner
      cases selected : joint owner with
      | none =>
        simp [selected, ReactiveApplication.ResponseMenu.protocol,
          ReactiveApplication.actor] at offered
      | some action =>
        change after ∈ ((nativeApplication).transition nativeInitial implementation.horizon
          implementation.scheduler (some ⟨remaining, some owner, execution⟩) joint).support
          at realized
        simp only [ReactiveApplication.transition, selected, Option.getD_some] at realized
        cases (PMF.mem_support_pure_iff _ _).mp realized
        rcases action with ⟨transmission⟩
        cases transmission with
        | none => exact ⟨previous, 0, .refl 0 _⟩
        | some material =>
          -- Keep the concrete SAME checkpoint at a callback. An arbitrary
          -- witness of the weaker existential would lose this equation.
          let next := witness.submit implementation.runtime implementation.leaks owner material
          have nextArchived := submittedArchived setup implementation execution
            witness archived owner material
          exact ⟨⟨next, nextArchived⟩, 0, .refl 0 _⟩
    | none =>
      cases remaining with
      | zero =>
        change after ∈ (PMF.pure (some ⟨0, none, execution⟩)).support at realized
        cases (PMF.mem_support_pure_iff _ _).mp realized
        exact ⟨previous, 0, .refl 0 _⟩
      | succ remaining =>
        have selected : ∃ command : (nativeApplication).Command,
            command ∈ (implementation.scheduler execution.environmentRecall
              (execution.observeEnvironment nativeApplication)).support ∧
            ∃ next : (nativeApplication).Execution,
              next ∈ (execution.environmentStep nativeApplication command).support ∧
              after = some ⟨remaining, command.actor? nativeApplication, next⟩ := by
          obtain ⟨command, chosen, moved⟩ := Set.mem_iUnion₂.mp
            (PMF.support_bind .. ▸ realized)
          obtain ⟨next, reached, same⟩ := PMF.support_map .. ▸ moved
          exact ⟨command, chosen, next, reached, same.symm⟩
        let command := Classical.choose selected
        let next := Classical.choose (Classical.choose_spec selected).2
        have reached := (Classical.choose_spec (Classical.choose_spec selected).2).1
        have targetEq := (Classical.choose_spec (Classical.choose_spec selected).2).2
        change next ∈ (execution.environmentStep nativeApplication command).support at reached
        change after = some ⟨remaining, command.actor? nativeApplication, next⟩ at targetEq
        generalize nextEq : next = nextExecution at reached targetEq
        generalize commandEq : command = nextCommand at reached targetEq
        have counted : ((nativeMenu).protocol
            (setup.initialLaw.map fun draw => PhaseRuntimeState.initial implementation.plan
              (encodeInputs draw)) implementation.horizon implementation.scheduler).Trace
            (some ⟨remaining + 1, none, execution⟩) := by
          exact priorTrace
        let continuation := witness.environment_archived_source implementation.runtime
          implementation.leaks implementation.bounds implementation.plan
          operational.maximalPhases implementation.horizon implementation.scheduler
          ⟨remaining + 1, none, execution⟩ counted archived nextCommand nextExecution reached
        subst after
        exact ⟨⟨Classical.choose continuation, (Classical.choose_spec continuation).1⟩,
          (Classical.choose_spec continuation).2⟩

/-- The actual chronological source witness and its retained proposal archive.
Its checkpoint describes the saved entry used by `canonicalSource`. -/
def checkpointSelection (operational : implementation.Operational)
    {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state) :
    state.elim PUnit (fun control =>
      {witness : RecoverySourceWitness setup .concurrent implementation.plan
          control.execution.application //
        witness.checkpoint.ArchivedProposals control.execution.network.inputs}) := by
  classical
  let witnessFiber := fun state : ((nativeMenu).protocol nativeInitial implementation.horizon
      implementation.scheduler).State =>
    state.elim PUnit (fun control =>
      {witness : RecoverySourceWitness setup .concurrent implementation.plan
          control.execution.application //
        witness.checkpoint.ArchivedProposals control.execution.network.inputs})
  let rec cofold {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state) :
      witnessFiber state := match trace with
    | .start => PUnit.unit
    | .extend priorTrace joint legal realized =>
        (checkpointSelectionStep setup implementation operational priorTrace joint legal realized
          (cofold priorTrace)).val
  exact cofold trace

/-- The chronological selection retains its own earlier source checkpoint. -/
theorem checkpointSelection_prefix (operational : implementation.Operational)
    (first last : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some first))
    (trace : (nativeProtocol).Trace (some last)) (kept : TracePrefix prior trace) :
    TracePrefix (checkpointSelection setup implementation operational prior).val.checkpoint.trace
      (checkpointSelection setup implementation operational trace).val.checkpoint.trace := by
  classical
  have retained : ∀ {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state),
      TracePrefix prior trace →
      match state, checkpointSelection setup implementation operational trace with
      | none, _ => False
      | some _, selected =>
          TracePrefix
            (checkpointSelection setup implementation operational prior).val.checkpoint.trace
            selected.val.checkpoint.trace := by
    intro state trace initialKept
    induction initialKept with
    | refl => exact .refl
    | @extend before after previous earlier joint legal realized ih =>
        have moved := (checkpointSelectionStep setup implementation operational previous joint
          legal realized (checkpointSelection setup implementation operational previous)).property
        cases before with
        | none => exact False.elim ih
        | some control =>
            cases after with
            | none => exact moved
            | some next =>
                obtain ⟨fuel, path⟩ := moved
                exact ih.trans path.tracePrefix
  exact retained trace kept

private theorem native_invariant_of_transition
    (inputs : (serviceGraph setup .concurrent).Inputs)
    (before after : (nativeApplication).Control)
    (joint : Player → Option (nativeApplication).Action)
    (valid : before.execution.application.Invariant inputs)
    (reached : some after ∈ ((nativeApplication).transition nativeInitial
      implementation.horizon implementation.scheduler (some before) joint).support) :
    after.execution.application.Invariant inputs := by
  let invariant := phaseApplication_invariant implementation.runtime implementation.leaks inputs
  rcases before with ⟨remaining, actor, execution⟩
  cases actor with
  | some owner =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact invariant.respond execution owner _ valid
  | none =>
      cases remaining with
      | zero =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          exact valid
      | succ remaining =>
          obtain ⟨command, _chosen, moved⟩ := Set.mem_iUnion₂.mp
            (PMF.support_bind .. ▸ reached)
          obtain ⟨next, supported, equal⟩ := PMF.support_map .. ▸ moved
          cases Option.some.inj equal
          exact invariant.environmentStep execution next command valid supported

/-- The chronological checkpoint and the physical input environment originate
from the same supported setup draw. This follows the actual selection, including
all callbacks, dispatcher transitions and canceled attempts. -/
theorem checkpointSelection_initializer (operational : implementation.Operational)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control)) :
    ∃ (theta : State L setup.context) (drawn : theta ∈ setup.initialLaw.support),
      control.execution.application.Invariant (encodeInputs theta) ∧
      TracePrefix
        (RecoverySourceCheckpoint.initialized setup .concurrent implementation.plan
          theta drawn).trace
        (checkpointSelection setup implementation operational trace).val.checkpoint.trace := by
  have initialized : ∀ {state : (nativeProtocol).State}
      (trace : (nativeProtocol).Trace state),
      match state, checkpointSelection setup implementation operational trace with
      | none, _ => True
      | some control, selected =>
          ∃ (theta : State L setup.context) (drawn : theta ∈ setup.initialLaw.support),
            control.execution.application.Invariant (encodeInputs theta) ∧
            TracePrefix
              (RecoverySourceCheckpoint.initialized setup .concurrent implementation.plan
                theta drawn).trace selected.val.checkpoint.trace := by
    intro state trace
    induction trace with
    | start => trivial
    | @extend before after prior joint legal realized ih =>
        have moved := (checkpointSelectionStep setup implementation operational prior joint
          legal realized (checkpointSelection setup implementation operational prior)).property
        cases before with
        | none =>
            cases after with
            | none => exact False.elim moved
            | some next =>
                obtain ⟨theta, drawn, physical, source⟩ := moved
                refine ⟨theta, drawn, ?_, ?_⟩
                · rw [physical]
                  exact (PhaseRuntimeState.initial_invariant implementation.plan
                    (encodeInputs theta)).1
                · have same : setup.commitRecoveryProtocol.ReachesWithin 0
                      (⟨_, (RecoverySourceCheckpoint.initialized setup .concurrent
                        implementation.plan theta drawn).trace⟩ :
                        setup.commitRecoveryProtocol.History)
                      ⟨_, (checkpointSelection setup implementation operational
                        (prior.extend joint legal realized)).val.checkpoint.trace⟩ := by
                    change setup.commitRecoveryProtocol.ReachesWithin 0 _
                      (⟨_, (checkpointSelectionStep setup implementation operational prior joint
                        legal realized (checkpointSelection setup implementation operational
                          prior)).val.val.checkpoint.trace⟩ : setup.commitRecoveryProtocol.History)
                    rw [source]
                    exact .refl 0 _
                  exact same.tracePrefix
        | some previous =>
            cases after with
            | none => exact False.elim moved
            | some next =>
                obtain ⟨theta, drawn, native, retained⟩ := ih
                obtain ⟨fuel, path⟩ := moved
                exact ⟨theta, drawn, native_invariant_of_transition setup implementation
                  (encodeInputs theta) previous next joint native realized,
                    retained.trans path.tracePrefix⟩
  exact initialized trace

/-- Selection keeps the same full source entry while its native attempt is unchanged. -/
theorem checkpointSelection_eq_of_attempt (operational : implementation.Operational)
    (first last : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some first))
    (trace : (nativeProtocol).Trace (some last)) (kept : TracePrefix prior trace)
    (attemptEq : first.execution.application.attempt = last.execution.application.attempt) :
    (⟨_, (checkpointSelection setup implementation operational prior).val.checkpoint.trace⟩ :
      setup.commitRecoveryProtocol.History) =
      ⟨_, (checkpointSelection setup implementation operational trace).val.checkpoint.trace⟩ := by
  let firstCheckpoint :=
    (checkpointSelection setup implementation operational prior).val.checkpoint
  let lastCheckpoint :=
    (checkpointSelection setup implementation operational trace).val.checkpoint
  have retained := checkpointSelection_prefix setup implementation operational first last
    prior trace kept
  have phase := congrArg CommitAttemptId.phase attemptEq
  have generation : first.execution.application.generation =
      last.execution.application.generation := congrArg CommitAttemptId.generation attemptEq
  apply setup.commitRecovery_ancestor_eq_of_control_eq retained.reachesWithin (.refl 0 _)
  change first.execution.application.generation * (instructionCount setup.program + 1) +
      (instructionCount setup.program - ProtocolState.remaining setup.program
        (firstCheckpoint.residual.lift
          (ProtocolState.entry firstCheckpoint.residual.tail firstCheckpoint.source))) + 1 =
    last.execution.application.generation * (instructionCount setup.program + 1) +
      (instructionCount setup.program - ProtocolState.remaining setup.program
        (lastCheckpoint.residual.lift
          (ProtocolState.entry lastCheckpoint.residual.tail lastCheckpoint.source))) + 1
  rw [firstCheckpoint.saved_position, lastCheckpoint.saved_position, generation, phase]

/-- The closed source annotation selected by the actual chronological native
prefix. Publication labels are read from that prefix's own original archive. -/
def canonicalSource (operational : implementation.Operational)
    (history : (nativeProtocol).History) : setup.proposalRecoveryProtocol.History :=
  match history with
  | ⟨none, _⟩ => setup.proposalRecoveryProtocol.initHistory
  | ⟨some control, trace⟩ =>
    let witness := (checkpointSelection setup implementation operational trace).val
    ⟨_, setup.proposalRecoveryLiftTrace
      (nativeArchiveLabels setup (PhaseProposal.sourceArchive control.execution.network.inputs))
      witness.checkpoint.trace⟩

/-- The selected current checkpoint can be carried back to the actual fresh
entry without replacing its residual, typed references or source history. -/
theorem checkpointSelection_at_entry (operational : implementation.Operational)
    (entry current : (nativeApplication).Control)
    (entryTrace : (nativeProtocol).Trace (some entry))
    (trace : (nativeProtocol).Trace (some current))
    (retained : TracePrefix entryTrace trace)
    (same : entry.execution.application.attempt = current.execution.application.attempt) :
    ∃ witness : RecoverySourceWitness setup .concurrent implementation.plan
        entry.execution.application,
      witness.checkpoint.ArchivedProposals entry.execution.network.inputs ∧
      (⟨_, witness.checkpoint.trace⟩ : setup.commitRecoveryProtocol.History) =
        ⟨_, (checkpointSelection setup implementation operational trace).val.checkpoint.trace⟩ ∧
      ∃ saved : entry.execution.application.entry = current.execution.application.entry,
        witness.checkpoint =
          (checkpointSelection setup implementation operational trace).val.checkpoint.transfer
            saved (congrArg CommitAttemptId.generation same)
              (congrArg CommitAttemptId.phase same) := by
  classical
  let earlier := (checkpointSelection setup implementation operational entryTrace).val
  let selected := (checkpointSelection setup implementation operational trace).val
  have historyEq := checkpointSelection_eq_of_attempt setup implementation operational
    entry current entryTrace trace retained same
  have initialized : ∀ state ∈ (nativeInitial).support, state.Ordered := by
    intro state member
    obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp member
    exact PhaseRuntimeState.initial_ordered implementation.plan (encodeInputs draw)
  have ordered := (phaseApplication_seedOrder implementation.runtime implementation.leaks).history
    nativeInitial implementation.horizon implementation.scheduler initialized
      ((nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler
        entryTrace)
  have saved := (phase_attempt_progress_of_prefix implementation.runtime implementation.leaks
    nativeMenu nativeInitial initialized implementation.horizon implementation.scheduler
      entry current entryTrace trace retained ordered).2.2 same
  let represented := selected.checkpoint.transfer saved
    (congrArg CommitAttemptId.generation same) (congrArg CommitAttemptId.phase same)
  have representation : (⟨_, represented.trace⟩ : setup.commitRecoveryProtocol.History) =
      ⟨_, earlier.checkpoint.trace⟩ :=
    (selected.checkpoint.transfer_history saved (congrArg CommitAttemptId.generation same)
      (congrArg CommitAttemptId.phase same)).trans historyEq.symm
  have sourceMemory : represented.source.history = earlier.checkpoint.source.history := by
    have points := congrArg CommitRecoveryState.point
      (Option.some.inj (congrArg History.state representation))
    have memory := congrArg (ProtocolState.history setup.program) points
    change ProtocolState.history setup.program
        (represented.residual.lift (ProtocolState.entry represented.residual.tail
          represented.source)) = ProtocolState.history setup.program
        (earlier.checkpoint.residual.lift (ProtocolState.entry earlier.checkpoint.residual.tail
          earlier.checkpoint.source)) at memory
    simpa only [represented.history, earlier.checkpoint.history, ProtocolState.history_entry]
      using memory
  let witness : RecoverySourceWitness setup .concurrent implementation.plan
      entry.execution.application := {
    earlier with
    checkpoint := represented
    aligned := fun who active => (congrFun sourceMemory who).trans (earlier.aligned who active)
    chronology := ⟨(congrArg (fun history : setup.commitRecoveryProtocol.History =>
      setup.recoveryAddressWord history.trace) representation).trans earlier.chronology.addresses,
        earlier.chronology.consumed⟩
    origins := representation.symm ▸ earlier.origins }
  have archived : witness.checkpoint.ArchivedProposals entry.execution.network.inputs := by
    intro who active
    have lifted := congrArg (fun history : setup.commitRecoveryProtocol.History =>
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who
        (setup.proposalRecoveryLiftTrace
          (nativeArchiveLabels setup (PhaseProposal.sourceArchive entry.execution.network.inputs))
          history.trace))) representation
    exact lifted.trans
      ((checkpointSelection setup implementation operational entryTrace).property who active)
  exact ⟨witness, archived, representation.trans historyEq, saved, rfl⟩


theorem source_checkpoint_addresses_in_cut
    (reference : (nativeApplication).Control)
    (trace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some reference))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
      implementation.horizon implementation.scheduler reference trace who event)
    (witness : RecoverySourceWitness setup .concurrent implementation.plan
      reference.execution.application) :
    (setup.recoveryAddressWord witness.checkpoint.trace).IsPrefix
      (setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace cut.completed.trace)) := by
  have recalled := setup.commitRecovery_publicRecall_addresses who
    (setup.proposalRecoveryEraseTrace cut.trace)
  have actual := cut.native_readback.2.1
  have numeric : setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace cut.trace) =
      reference.execution.application.sourcePublicAddressWord implementation.plan event.val :=
    List.reverse_injective (List.append_cancel_right (recalled.symm.trans actual))
  have savedPrefix : (setup.recoveryAddressWord witness.checkpoint.trace).IsPrefix
      (setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace cut.trace)) := by
    rw [witness.chronology.addresses, numeric]
    unfold PhaseRuntimeState.sourcePublicAddressWord
    simp only [Nat.sub_self, List.range_zero, List.map_nil, List.append_nil]
    exact ⟨_, rfl⟩
  exact savedPrefix.trans (source_address_prefix setup
    (setup.proposalRecoveryEraseTrace_prefix cut.future))

private theorem source_callback_binding_address
    (operational : implementation.Operational)
    (reference : (nativeApplication).Control)
    (trace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some reference))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
      implementation.horizon implementation.scheduler reference trace who event)
    (before : (nativeApplication).Control)
    (prior : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some before))
    (retained : TracePrefix prior trace)
    (owner : Player) (named : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout named = .binding owner payload)
    (request : before.execution.application.SeedRequest owner
      ⟨before.execution.application.attempt, named⟩) :
    ∃ index beforeExcluded afterExcluded nextRank nextGeneration nextLow,
      index + 1 < cut.completed.trace.length ∧
      (setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace cut.completed.trace))[index]? =
        some (some named.val, beforeExcluded, before.execution.application.generation,
          before.execution.application.attempt.phase) ∧
      (setup.recoveryAddressWord
        (setup.proposalRecoveryEraseTrace cut.completed.trace))[index + 1]? =
        some (nextRank, afterExcluded, nextGeneration, nextLow) := by
  classical
  let initial := (setup.initialLaw.map encodeInputs).map
    (PhaseRuntimeState.initial implementation.plan)
  have initialEq : nativeInitial = initial := by
    simp only [initial, ReservedConcurrentImplementation.initial, PMF.map_comp,
      Function.comp_def]
  obtain ⟨priorNative, finalNative, retainedNative⟩ :
      ∃ (first : (nativeProtocol).Trace (some before))
        (last : (nativeProtocol).Trace (some reference)), TracePrefix first last := by
    rw [initialEq]
    exact ⟨prior, trace, retained⟩
  let selected := checkpointSelection setup implementation operational priorNative
  obtain ⟨phase, rest, installed, kind, inside⟩ :=
    phase_ready_binding_phase implementation.runtime implementation.leaks implementation.plan
      (serviceGraph_revealRelaxedOrdered setup .concurrent)
      operational.maximalPhases (setup.initialLaw.map encodeInputs) implementation.horizon
      implementation.scheduler ((nativeMenu).toRawTrace initial implementation.horizon
        implementation.scheduler prior) owner named payload binding request.2.2.1
  have bounds := (phase.mem_events named).mp inside
  have geometry := source_checkpoint_binding_interval setup implementation selected.val
    operational.maximalPhases phase rest installed kind
  let start := CommitRecoveryState.atPoint
    (selected.val.checkpoint.residual.lift (ProtocolState.entry
      selected.val.checkpoint.residual.tail selected.val.checkpoint.source))
    before.execution.application.entry.excluded before.execution.application.generation
  let target : setup.commitRecoveryProtocol.History :=
    ⟨cut.completed.state, setup.proposalRecoveryEraseTrace cut.completed.trace⟩
  by_cases same : before.execution.application.attempt = reference.execution.application.attempt
  · have initialized : ∀ state ∈ initial.support, state.Ordered := by
      intro state supported
      obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_ordered implementation.plan draw
    have ordered := (phaseApplication_seedOrder implementation.runtime implementation.leaks).history
      initial implementation.horizon implementation.scheduler initialized
      ((nativeMenu).toRawTrace initial implementation.horizon implementation.scheduler prior)
    have metadata := phase_attempt_metadata_of_prefix implementation.runtime implementation.leaks
      (nativeMenu) initial initialized implementation.horizon implementation.scheduler
      before reference prior trace retained ordered same
    have phaseEq : phase = cut.phase := by
      have heads := congrArg (fun pair => pair.1.head?) metadata
      simpa only [installed, List.head?_cons, cut.installed, Option.some.injEq] using heads
    subst phase
    obtain ⟨entryRest, entryInstalled⟩ := List.head?_eq_some_iff.mp cut.entryInstalled
    have entryGeometry := source_checkpoint_binding_interval setup implementation cut.witness
      operational.maximalPhases cut.phase entryRest entryInstalled cut.commitment
    let entryPoint := cut.witness.checkpoint.residual.lift
      (ProtocolState.entry cut.witness.checkpoint.residual.tail cut.witness.checkpoint.source)
    let entry := CommitRecoveryState.atPoint entryPoint
      cut.entry.execution.application.entry.excluded cut.entry.execution.application.generation
    have entryHistory : (⟨some cut.cursor.current,
        setup.proposalRecoveryEraseTrace cut.cursor.trace⟩ : setup.commitRecoveryProtocol.History) =
        ⟨some entry, cut.witness.checkpoint.trace⟩ := by
      have converted := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
        (⟨history.state, setup.proposalRecoveryEraseTrace history.trace⟩ :
          setup.commitRecoveryProtocol.History)) cut.cursorHistory
      simpa only [setup.proposalRecoveryEraseTrace_lift] using converted
    have path := (setup.proposalRecoveryEraseTrace_prefix (cut.past.trans cut.future)).reachesWithin
    change setup.commitRecoveryProtocol.ReachesWithin _
      ⟨some cut.cursor.current, setup.proposalRecoveryEraseTrace cut.cursor.trace⟩ target at path
    rw [entryHistory] at path
    obtain ⟨finished, last, lastTrace, attempt, completed, _point, _excluded, _generation,
      _live, _agrees, words, _labels⟩ := cut.blockResult
    have lengths := congrArg List.length words
    simp only [setup.recoveryJointRecall_length, setup.proposalRecoveryEraseTrace_length,
      List.length_append, List.length_reverse, attempt.joints_length] at lengths
    have initialLength := congrArg (fun history : setup.commitRecoveryProtocol.History =>
      history.trace.length) entryHistory
    have finalLength := congrArg (fun history : setup.proposalRecoveryProtocol.History =>
      history.trace.length) completed
    have enough : cut.witness.checkpoint.trace.length +
        (named.val - (instructionCount setup.program -
          ProtocolState.remaining setup.program entry.point)) < target.trace.length := by
      have size := cut.size
      dsimp only [entry, entryPoint, CommitRecoveryState.atPoint] at *
      rw [setup.proposalRecoveryEraseTrace_length] at initialLength
      simp only [target, setup.proposalRecoveryEraseTrace_length]
      omega
    obtain ⟨index, old, next, nextRank, nextGeneration, nextLow, bounded, first, second⟩ :=
      source_rank_address_transfer setup entry cut.witness.checkpoint.trace entryGeometry.1
        named.val (by simpa only [entry, entryPoint, CommitRecoveryState.atPoint,
          entryGeometry.2.1] using bounds.1)
        (by simpa only [entry, entryPoint, CommitRecoveryState.atPoint,
          entryGeometry.2.2] using bounds.2) target _ path (Or.inr enough) target
        ⟨[], by simp only [List.append_nil]⟩
    have sameNamespace := cut.sameAttempt.trans same.symm
    have generation := congrArg CommitAttemptId.generation sameNamespace
    change cut.entry.execution.application.generation =
      before.execution.application.generation at generation
    have low := congrArg CommitAttemptId.phase sameNamespace
    refine ⟨index, old, next, nextRank, nextGeneration, nextLow, ?_, ?_, second⟩
    · simpa only [target, setup.proposalRecoveryEraseTrace_length] using bounded
    · simpa only [entry, entryPoint, CommitRecoveryState.atPoint,
        CommitRecoveryState.publicAddress, cut.witness.checkpoint.saved_position,
        generation, low] using first
  · obtain ⟨last, stateEq, follower, _archived, fuel, path⟩ :=
      selected.val.prefix_archived_source setup .concurrent implementation.runtime
        implementation.leaks implementation.bounds implementation.plan operational.maximalPhases
        implementation.horizon implementation.scheduler before priorNative selected.property
        finalNative retainedNative
    cases Option.some.inj stateEq
    let final : setup.commitRecoveryProtocol.History := ⟨_, follower.checkpoint.trace⟩
    have exited : final.state.map (fun state => state.publicAddress.2.2) ≠
        some start.publicAddress.2.2 := by
      simp only [final, start, Option.map_some, CommitRecoveryState.atPoint,
        CommitRecoveryState.publicAddress, follower.checkpoint.saved_position,
        selected.val.checkpoint.saved_position]
      intro equal
      apply same
      have pairEq := Option.some.inj equal
      change (reference.execution.application.attempt.generation,
          reference.execution.application.attempt.phase) =
        (before.execution.application.attempt.generation,
          before.execution.application.attempt.phase) at pairEq
      exact congrArg (fun pair : Nat × Nat => CommitAttemptId.mk pair.2 pair.1) pairEq.symm
    obtain ⟨index, old, next, nextRank, nextGeneration, nextLow, bounded, first, second⟩ :=
      source_rank_address_transfer setup start selected.val.checkpoint.trace geometry.1 named.val
        (by simpa only [start, CommitRecoveryState.atPoint, geometry.2.1] using bounds.1)
        (by simpa only [start, CommitRecoveryState.atPoint, geometry.2.2] using bounds.2)
        final fuel path (Or.inl exited) target
        (source_checkpoint_addresses_in_cut setup values implementation reference trace
          who event cut follower)
    refine ⟨index, old, next, nextRank, nextGeneration, nextLow, ?_, ?_, second⟩
    · simpa only [target, setup.proposalRecoveryEraseTrace_length] using bounded
    · simpa only [start, CommitRecoveryState.atPoint, CommitRecoveryState.publicAddress,
        selected.val.checkpoint.saved_position] using first

theorem source_emitted_binding_address
    (operational : implementation.Operational)
    (reference : (nativeApplication).Control)
    (trace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some reference))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
      implementation.horizon implementation.scheduler reference trace who event)
    (owner : Player) (record : (nativeApplication).PlayerEntry)
    (recorded : record ∈ reference.execution.recall owner)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (transmitted : record.action.transmission = some material)
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (emitted : record.emitted = some message)
    (named : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent)) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout named = .binding owner payload)
    (call : message.payload.packet.call = .commitment named handle) :
    ∃ index beforeExcluded afterExcluded nextRank nextGeneration nextLow,
      index + 1 < cut.completed.trace.length ∧
      (setup.recoveryAddressWord (setup.proposalRecoveryEraseTrace cut.completed.trace))[index]? =
        some (some named.val, beforeExcluded, message.payload.attempt.generation,
          message.payload.attempt.phase) ∧
      (setup.recoveryAddressWord
        (setup.proposalRecoveryEraseTrace cut.completed.trace))[index + 1]? =
        some (nextRank, afterExcluded, nextGeneration, nextLow) := by
  let initial := (setup.initialLaw.map encodeInputs).map
    (PhaseRuntimeState.initial implementation.plan)
  let raw := (nativeMenu).toRawTrace initial implementation.horizon implementation.scheduler trace
  obtain ⟨actual, sent, _sender, packet⟩ := PhaseCount.recalled_submission_emitted
    implementation.runtime implementation.leaks initial implementation.horizon
    implementation.scheduler raw owner record recorded material transmitted
  have sameMessage : actual = message := Option.some.inj (sent.symm.trans emitted)
  subst actual
  have namedMaterial := packet.symm.trans call
  obtain ⟨before, prior, retained, _acting, viewed, request⟩ :=
    phase_recorded_binding_request implementation.runtime implementation.leaks implementation.bounds
      implementation.plan (setup.initialLaw.map encodeInputs) implementation.horizon
      (serviceGraph_revealRelaxedOrdered setup .concurrent) implementation.scheduler trace
      owner record recorded material transmitted named handle namedMaterial
  have emittedNamespace := phase_recalled_emission_attempt implementation.runtime
    implementation.leaks
    initial implementation.horizon implementation.scheduler raw owner record recorded
      message emitted
  rw [viewed] at emittedNamespace
  change message.payload.attempt = before.execution.application.attempt at emittedNamespace
  obtain ⟨index, old, next, nextRank, nextGeneration, nextLow, bounded, first, second⟩ :=
    source_callback_binding_address setup values implementation operational reference trace
      who event
      cut before prior retained owner named payload binding request
  refine ⟨index, old, next, nextRank, nextGeneration, nextLow, bounded, ?_, second⟩
  simpa only [emittedNamespace, PhaseRuntimeState.attempt] using first

omit [Fintype Player] in
theorem source_commit_chunk_at_rank
    (start : CommitRecoveryState setup.program)
    (entry : setup.proposalRecoveryProtocol.Trace (some start))
    (committing : ProtocolState.atCommit setup.program start.point = true)
    (final : setup.proposalRecoveryProtocol.History)
    (retained : TracePrefix entry final.trace)
    (word : List (Player → Option (CommitRecoveryMove Player L)))
    (instructions : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace final.trace) =
      word.reverse ++ setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace entry))
    (slot : Nat) (inside : slot < word.length)
    (rank : Nat)
    (position : rank = instructionCount setup.program -
      ProtocolState.remaining setup.program start.point + slot)
    (within : rank < instructionCount setup.program -
      ProtocolState.commitEnd setup.program start.saved) :
    ∃ (current next : CommitRecoveryState setup.program)
      (prior : setup.proposalRecoveryProtocol.Trace (some current))
      (joint : Player → Option (ProposalRecoveryMove Player L))
      (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
      (moved : some next ∈
        (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩).support),
      TracePrefix (prior.extend joint legal moved) final.trace ∧
      prior.length = entry.length + slot ∧
      SourceProgram.Setup.proposalRecoveryJoint joint = word[slot] ∧
      current.saved = start.saved ∧ current.generation = start.generation ∧
      instructionCount setup.program -
        ProtocolState.remaining setup.program current.point = rank := by
  have length := congrArg List.length instructions
  simp only [setup.recoveryJointRecall_length, setup.proposalRecoveryEraseTrace_length,
    List.length_append, List.length_reverse] at length
  have initialized : 0 < entry.length := by
    have positive : ∀ {state} (path : setup.proposalRecoveryProtocol.Trace state),
        state ≠ none → 0 < path.length := by
      intro state path
      cases path with
      | start => intro impossible; exact (impossible rfl).elim
      | extend prior joint legal moved => intro _; simp only [Trace.length]; omega
    exact positive entry (by intro impossible; cases impossible)
  have semanticPrefix := setup.proposalRecoveryEraseTrace_prefix retained
  obtain ⟨current, next, semantic, actions, available, realized,
      _entryPrefix, semanticKept, saved, generation, depth, atRank⟩ :=
    source_commit_rank_before_exit setup slot start
      (setup.proposalRecoveryEraseTrace entry) committing rank position within
      ⟨final.state, setup.proposalRecoveryEraseTrace final.trace⟩ _
      semanticPrefix.reachesWithin (Or.inr (by
        simp only [setup.proposalRecoveryEraseTrace_length]
        omega))
  obtain ⟨before, after, prior, joint, legal, moved, kept, actualDepth,
      actualJoint, _beforeAddress, _afterAddress⟩ :=
    source_instruction_chunk_row setup entry final.trace initialized word instructions slot inside
  have beforeKept : TracePrefix (setup.proposalRecoveryEraseTrace prior)
      (setup.proposalRecoveryEraseTrace final.trace) :=
    setup.proposalRecoveryEraseTrace_prefix
      ((TracePrefix.extend .refl joint legal moved).trans kept)
  have semanticBefore : TracePrefix semantic
      (setup.proposalRecoveryEraseTrace final.trace) :=
    (TracePrefix.extend .refl actions available realized).trans semanticKept
  have sameBefore := beforeKept.eq_of_same_length semanticBefore (by
    simpa only [setup.proposalRecoveryEraseTrace_length, actualDepth] using depth.symm)
  have beforeEq : before = some current := congrArg History.state sameBefore
  subst before
  have sameAfter := (setup.proposalRecoveryEraseTrace_prefix kept).eq_of_same_length
    semanticKept (by
      simp only [setup.proposalRecoveryEraseTrace_length, Trace.length, actualDepth] at depth ⊢
      omega)
  have afterEq : after = some next := congrArg History.state sameAfter
  subst after
  exact ⟨current, next, prior, joint, legal, moved, kept, actualDepth, actualJoint,
    saved, generation, atRank⟩


theorem accepted_snapshot_value_of_no_generated_unusable
    (reference : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some reference))
    (snapshot : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (selected : snapshot = reference.execution.application.current.native ∨
      snapshot = reference.execution.application.entry.native ∨
      ∃ record ∈ reference.execution.application.retired, snapshot = record.state)
    (owner : Player)
    (good : ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
      implementation.leaks implementation.bounds nativeInitial implementation.horizon
      implementation.scheduler owner ⟨some reference, trace⟩)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (candidate : Handle (serviceGraph setup .concurrent))
    (accepted : snapshot.accepted (.inr event) = some candidate) :
    ∃ value : L.Val payload, snapshot.bindingResult candidate payload = .success value := by
  let inputs := setup.initialLaw.map encodeInputs
  have initialEq : nativeInitial = inputs.map (PhaseRuntimeState.initial implementation.plan) := by
    simp only [ReservedConcurrentImplementation.initial, inputs, PMF.map_comp, Function.comp_def]
  have raw := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  have physical := PhaseCount.physicalBindings_history implementation.runtime implementation.leaks
    implementation.bounds implementation.plan inputs implementation.horizon
    implementation.scheduler (initialEq ▸ trace)
  have bindings := phaseBindingRecord_history implementation.runtime implementation.leaks
    implementation.plan inputs implementation.horizon implementation.scheduler (initialEq ▸ raw)
  have valid : snapshot.BindingInvariant ∧
      KeepsFixedCandidates snapshot reference.execution.application.current.native := by
    rcases selected with rfl | rfl | ⟨record, member, rfl⟩
    · exact ⟨bindings.active, fun _ _ => rfl⟩
    · exact ⟨bindings.saved, bindings.fixed⟩
    · have retired := phaseRetiredBindings_history implementation.runtime implementation.leaks
        implementation.plan inputs implementation.horizon implementation.scheduler
        (initialEq ▸ raw) record member
      exact ⟨retired.1, retired.2.2⟩
  have owned : candidate.1 = owner := by
    obtain ⟨other, typed⟩ := valid.1.accepted_typed (.inr event) candidate accepted
    exact (EventField.binding.inj (typed.symm.trans binding)).1
  obtain ⟨record, recorded, message, emitted, sender, call, _receipt⟩ :=
    accepted_snapshot_receipt setup implementation reference trace reference trace .refl
      snapshot selected event candidate accepted
  have authored : message ∈ (nativeApplication).outputs
      (reference.execution.recall candidate.1) :=
    List.mem_filterMap.mpr ⟨record, recorded, emitted⟩
  rw [← (nativeApplication).history_inputRecall nativeInitial implementation.horizon
    implementation.scheduler raw candidate.1] at authored
  have member := (List.mem_filter.mp authored).1
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp
    (physical.clean.2 message member)).2.1
  change CountCallCorrect _ (PhaseCount.nativeMessage message) at correct
  simp only [CountCallCorrect, PhaseCount.nativeMessage, call] at correct
  obtain ⟨_bindingOwned, _noEvidence, _candidateOwner, ⟨serial, slot⟩, _unused⟩ := correct
  have candidateEq : candidate = (owner, .prepared serial) := Prod.ext owned slot
  subst candidate
  obtain ⟨entry, recalled, material, sent, _emitted, state, known, emission⟩ :=
    physical.origins.inputs message member
  rw [sender] at recalled
  have materialCall : material.call.packet = .commitment event (owner, .prepared serial) := by
    exact (phase_emit_call state message.sender known material).symm.trans
      ((congrArg (fun packet : CommitAttemptPacket (serviceGraph setup .concurrent) =>
        packet.packet.call) emission).trans call)
  rcases material with ⟨⟨packet, opening⟩, evidence⟩
  dsimp only at materialCall
  subst packet
  have declared : entry.action =
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩ :=
    congrArg (fun transmission => (⟨transmission⟩ : (nativeApplication).Action)) sent
  obtain ⟨value, decoded⟩ := phaseProposal_recalled_binding_preparation_value
    implementation.runtime implementation.leaks implementation.bounds nativeInitial
    implementation.horizon implementation.scheduler reference trace owner good event payload
    binding serial opening evidence entry recalled declared
  obtain ⟨before, prior, _prefix, _acting, viewed, offered, _recalled⟩ :=
    (nativeMenu).recorded_response_prefix nativeInitial implementation.horizon
      implementation.scheduler reference trace owner entry recalled
  rw [declared] at offered
  have fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh :=
    viewed ▸ PhaseCount.onePacket_binding_fresh implementation.runtime implementation.leaks
      implementation.bounds implementation.plan inputs implementation.horizon
      implementation.scheduler (initialEq ▸ prior) owner event serial opening evidence offered
  have meaning := phase_recorded_material_binding_result implementation.runtime
    implementation.leaks (nativeMenu) nativeInitial implementation.horizon implementation.scheduler
    reference trace owner event payload serial opening evidence entry recalled declared fresh
  rw [decoded, Option.elim_some] at meaning
  have fixed := valid.2 (owner, .prepared serial)
    (valid.1.accepted_fixed (.inr event) (owner, .prepared serial) accepted)
  refine ⟨value, ?_⟩
  unfold EventGraphRuntime.State.bindingResult at meaning ⊢
  rwa [fixed] at meaning

omit [Fintype Player] in
theorem source_commit_instruction_word_length
    {state : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (checkpoint : RecoverySourceCheckpoint setup .concurrent state)
    (image : EventGraphRuntime.State (serviceGraph setup .concurrent)) :
    (checkpoint.commitInstructionWord image).length =
      ProtocolState.remaining setup.program
        (checkpoint.residual.lift
          (ProtocolState.entry checkpoint.residual.tail checkpoint.source)) -
      ProtocolState.commitEnd setup.program
        (checkpoint.residual.lift
          (ProtocolState.entry checkpoint.residual.tail checkpoint.source)) := by
  rw [checkpoint.remaining, checkpoint.commitEnd]
  unfold RecoverySourceCheckpoint.commitInstructionWord
  generalize decomposition : commitPhase checkpoint.residual.tail = segment
  rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
  dsimp only
  rw [CommitPrefix.Attempt.joints_length, ← reconstruct, ProtocolState.remaining_entry,
    block.commitEnd_entry_prepend suffix boundary, block.instructionCount_prepend]
  omega

omit [Fintype Player] in
open Classical in
theorem source_decoded_binding_row
    {state : PhaseRuntimeState (serviceGraph setup .concurrent)}
    (checkpoint : RecoverySourceCheckpoint setup .concurrent state)
    (image : EventGraphRuntime.State (serviceGraph setup .concurrent))
    (closed : setup.commitRecoveryProtocol.History) {fuel : Nat}
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, checkpoint.trace⟩ closed)
    (instructions : setup.recoveryJointRecall closed.trace =
      (checkpoint.commitInstructionWord image).reverse ++
        setup.recoveryJointRecall checkpoint.trace)
    (final : setup.proposalRecoveryProtocol.History)
    (closedKept : TracePrefix closed.trace (setup.proposalRecoveryEraseTrace final.trace))
    (current next : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (moved : some next ∈
      (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩).support)
    (rowKept : TracePrefix (prior.extend joint legal moved) final.trace)
    (lower : checkpoint.trace.length ≤ prior.length)
    (upper : prior.length < closed.trace.length) :
    current.saved = checkpoint.residual.lift
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) ∧
    current.generation = state.generation ∧
    match commitPhase checkpoint.residual.tail with
    | ⟨_, _, suffix, block, reconstruct, _⟩ =>
      let embedding := cast (congrArg (fun program => OutputEmbedding
        (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
          checkpoint.embedding
      let decoded := decodeCommitAttempt setup.program .concurrent block suffix embedding image
        checkpoint.source state.entry.excluded
      ∃ (event : (serviceGraph setup .concurrent).EventId) (owner : Player) (payload : L.Ty)
        (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload),
        event.val = instructionCount setup.program -
          ProtocolState.remaining setup.program current.point ∧
      (BindingReceiptOrder state.attempt.phase state.entry.excluded image.accepted →
        image.accepted (.inr event) ≠ none → owner ∉ current.excluded) ∧
      (owner ∉ current.excluded → ∃ (Δ : SourceCtx Player L) (P : Finset VarId) (name : VarId)
        (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
        (earlier : SourceProgram.CommitPrefix checkpoint.residual.context
          checkpoint.residual.names Δ P)
        (rest : SourceProgram.CommitPrefix
          ((name, .commitment owner payload) :: Δ) (insert name P) _ _),
        earlier.length = prior.length - checkpoint.trace.length ∧
        earlier.append (.commit name owner fresh guard rest) = block ∧
        (∃ selected : Fin (eventCount (block.prepend suffix)),
          selected.val = earlier.length ∧ embedding.event selected = event) ∧
        (∃ terminalCell : HasVar setup.program.terminalCtx name (.commitment owner payload),
          ((terminalRefs setup.program).get terminalCell).field = .inr event) ∧
        phaseRecoveryBindingData setup .concurrent event owner payload binding
          ((joint owner).map (·.semantic)) =
            ((image.accepted (.inr event)).elim PublicationResult.failure
              (fun handle => image.bindingResult handle payload),
              (image.accepted (.inr event)).isNone) ∧
        SourceProgram.State.cell? decoded.1.state name (.commitment owner payload) =
          some ((image.accepted (.inr event)).elim PublicationResult.failure
            (fun handle => image.bindingResult handle payload))) := by
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, alignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, history, memory, steps, menus, readout, entryTrace, views,
    historyAlignment, origin⟩
  dsimp only at instructions lower ⊢
  dsimp only [RecoverySourceCheckpoint.commitInstructionWord] at instructions
  generalize decomposition : commitPhase program = segment at instructions ⊢
  rcases segment with ⟨Ξ, Q, suffix, block, reconstruct, boundary⟩
  subst program
  dsimp only [cast_eq] at instructions ⊢
  let start := CommitRecoveryState.atPoint
    (lift (ProtocolState.entry (block.prepend suffix) source))
      state.entry.excluded state.generation
  let decoded := decodeCommitAttempt setup.program .concurrent block suffix embedding image
    source state.entry.excluded
  let slot := prior.length - entryTrace.length
  have lengths := congrArg List.length instructions
  simp only [setup.recoveryJointRecall_length, List.length_append, List.length_reverse]
    at lengths
  have inside : slot < decoded.2.2.joints.length := by
    dsimp only [slot, decoded]
    omega
  have blockInside : slot < block.length := by
    simpa only [decoded.2.2.joints_length] using inside
  have committing : ProtocolState.atCommit (block.prepend suffix)
      (ProtocolState.entry (block.prepend suffix) source) = true := by
    cases block with
    | nil => simp only [SourceProgram.CommitPrefix.length] at blockInside; omega
    | commit => rfl
  obtain ⟨closedLift, liftedKept, erasedClosed⟩ :=
    setup.proposalRecoveryEraseTrace_prefix_inverse final.trace closed.trace closedKept
  obtain ⟨entryLift, entryKept, erasedEntry⟩ :=
    setup.proposalRecoveryEraseTrace_prefix_inverse closedLift entryTrace
      (by rw [erasedClosed]; exact path.tracePrefix)
  have entryLength : entryLift.length = entryTrace.length := by
    rw [← erasedEntry, setup.proposalRecoveryEraseTrace_length]
  have word : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace closedLift) =
      decoded.2.2.joints.reverse ++
        setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace entryLift) := by
    rw [erasedClosed, erasedEntry]
    exact instructions
  have wholeCommit : ProtocolState.atCommit setup.program start.point = true :=
    (commits _).trans committing
  have window := block.length_le_commit_window suffix source
  rw [← origin.commitEnd_lift, ← ranks] at window
  have remaining := ProtocolState.remaining_le_instructionCount setup.program start.point
  have within : instructionCount setup.program -
      ProtocolState.remaining setup.program start.point + slot <
        instructionCount setup.program - ProtocolState.commitEnd setup.program start.saved := by
    change block.length + ProtocolState.commitEnd setup.program start.saved ≤
      ProtocolState.remaining setup.program start.point at window
    omega
  obtain ⟨actual, after, trace, actions, allowed, reached, kept, depth, row,
      saved, generation, atRank⟩ :=
    source_commit_chunk_at_rank setup start entryLift wholeCommit ⟨_, closedLift⟩ entryKept
      decoded.2.2.joints word slot inside _ rfl within
  have sameDepth : trace.length = prior.length := by rw [depth, entryLength]; dsimp [slot]; omega
  have oldKept : TracePrefix trace final.trace :=
    (TracePrefix.extend .refl actions allowed reached).trans (kept.trans liftedKept)
  have actualKept : TracePrefix prior final.trace :=
    (TracePrefix.extend .refl joint legal moved).trans rowKept
  have sameBefore := oldKept.eq_of_same_length actualKept sameDepth
  have sameState : actual = current := Option.some.inj (congrArg History.state sameBefore)
  subst actual
  have sameAfter := (kept.trans liftedKept).eq_of_same_length rowKept
    (by simpa only [Trace.length] using congrArg Nat.succ sameDepth)
  have sameWord := congrArg (fun h : setup.proposalRecoveryProtocol.History =>
    setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace h.trace)) sameAfter
  have sameJoint : Setup.proposalRecoveryJoint actions = Setup.proposalRecoveryJoint joint :=
    (List.cons.inj sameWord).1
  have literal : Setup.proposalRecoveryJoint joint = decoded.2.2.joints[slot] :=
    sameJoint.symm.trans row
  refine ⟨saved, generation, ?_⟩
  obtain ⟨Δ, P, name, owner, payload, fresh, guard, earlier, rest, size, splitBlock⟩ :=
    block.exists_binding_split slot blockInside
  subst block
  let selected : Fin (eventCount ((earlier.append (.commit name owner fresh guard rest)).prepend
      suffix)) := ⟨slot, by
    have count := (earlier.append (.commit name owner fresh guard rest)).eventCount_prepend suffix
    omega⟩
  have offset : state.attempt.phase = instructionCount setup.program -
      ProtocolState.remaining setup.program start.point := by
    have count := compiled.countEq
    simp only [eventCount_eq_instructionCount] at count
    change _ = instructionCount setup.program -
      ProtocolState.remaining setup.program (lift (ProtocolState.entry _ source))
    rw [ranks, ProtocolState.remaining_entry]
    exact Nat.eq_sub_of_add_eq count
  have atSlot : selected.val = earlier.length := size.symm
  have layoutDecode : ∀ {A B C : SourceCtx Player L} {U V W : Finset VarId}
      (prefixBlock : SourceProgram.CommitPrefix A U B V)
      (name : VarId) (actor : Player) (domain : L.Ty)
      (fresh : name ∉ B.map Prod.fst) (guard : SourceGuard L B actor name domain)
      (rest : SourceProgram.CommitPrefix ((name, .commitment actor domain) :: B)
        (insert name V) C W) (suffix : SourceProgram Player L C W)
      (index : Fin (eventCount
        ((prefixBlock.append (.commit name actor fresh guard rest)).prepend suffix))),
      index.val = prefixBlock.length →
      ∃ layout : outputLayout
          ((prefixBlock.append (.commit name actor fresh guard rest)).prepend suffix) index =
            .binding actor domain,
        ∀ result, decodeEventAction
          ((prefixBlock.append (.commit name actor fresh guard rest)).prepend suffix) index
            (cast (congrArg EventField.Action layout.symm) result) =
              some (.commit actor name domain result) := by
    intro A B C U V W prefixBlock
    induction prefixBlock with
    | nil =>
        intro name actor domain fresh guard rest suffix index coordinate
        rcases index with ⟨index, bounded⟩
        have zero : index = 0 := coordinate
        subst index
        exact ⟨rfl, fun _ => rfl⟩
    | commit old author oldFresh oldGuard tail ih =>
        intro name actor domain fresh guard rest suffix index
        refine Fin.cases ?_ (fun index coordinate => ?_) index
        · intro impossible
          simp only [Fin.val_zero, SourceProgram.CommitPrefix.length] at impossible
          omega
        · exact ih name actor domain fresh guard rest suffix index (by
            simpa only [Fin.val_succ, SourceProgram.CommitPrefix.length,
              Nat.add_right_cancel_iff] using coordinate)
  obtain ⟨localLayout, localDecode⟩ :=
    layoutDecode earlier name owner payload fresh guard rest suffix selected atSlot
  let event := embedding.event selected
  have binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload :=
    (embedding.layout_eq selected).trans localLayout
  have selectedEq : embedding.event selected = event := rfl
  have position : event.val = instructionCount setup.program -
      ProtocolState.remaining setup.program current.point := by
    change (embedding.event selected).val = _
    rw [compiled.rankEq, offset, atRank]
  let later : SourceProgram.CommitPrefix Δ P Ξ Q := .commit name owner fresh guard rest
  let prefixEmbedding := cast (congrArg (OutputEmbedding (inputLayout setup.context)
    (outputLayout setup.program)) (earlier.prepend_append later suffix)) embedding
  let middle := decodeCommitAttempt setup.program .concurrent earlier (later.prepend suffix)
    prefixEmbedding image source state.entry.excluded
  let synthetic := CommitRecoveryState.atPoint current.point middle.2.1 current.generation
  obtain ⟨jointAt, cellAt⟩ := decodeCommitAttempt_joint_at_rank setup.program .concurrent earlier
    fresh guard rest suffix embedding state.attempt.phase compiled.rankEq selected atSlot image
    source state.entry.excluded synthetic rfl
  have exactJoint : Setup.proposalRecoveryJoint joint = synthetic.commitJoint owner name payload
      ((image.accepted (.inr event)).elim PublicationResult.failure
        (fun handle => image.bindingResult handle payload))
      (image.accepted (.inr event)).isNone := by
    have literalSome : decoded.2.2.joints[slot]? =
        some (Setup.proposalRecoveryJoint joint) := by
      rw [List.getElem?_eq_getElem inside, ← literal]
    have decodedSome := jointAt
    rw [size, selectedEq] at decodedSome
    exact Option.some.inj (literalSome.symm.trans decodedSome)
  have receiptActive :
      BindingReceiptOrder state.attempt.phase state.entry.excluded image.accepted →
      image.accepted (.inr event) ≠ none → owner ∉ current.excluded := by
    intro ordered received
    obtain ⟨candidate, accepted⟩ : ∃ candidate, image.accepted (.inr event) = some candidate := by
      cases accepted : image.accepted (.inr event) with
      | none => exact (received accepted).elim
      | some candidate => exact ⟨candidate, rfl⟩
    have selectedRank := compiled.rankEq selected
    change event.val = state.attempt.phase + selected.val at selectedRank
    rw [atSlot] at selectedRank
    have order := ordered event owner payload candidate (by omega) binding accepted
    have middleActive : owner ∉ synthetic.excluded := by
      change owner ∉ middle.2.1
      rw [decodeCommitAttempt_excluded_eq]
      intro excluded
      rcases Finset.mem_union.mp excluded with inherited | missing
      · exact order.1 inherited
      · obtain ⟨index, before, acting, absent⟩ :=
          (mem_commitMissingOwners setup.program .concurrent earlier (later.prepend suffix)
            prefixEmbedding image owner).mp missing
        let original := Fin.cast (congrArg eventCount
          (earlier.prepend_append later suffix).symm) index
        have same := OutputEmbedding.event_cast setup.program
          (earlier.prepend_append later suffix) embedding original index rfl
        have ranked := compiled.rankEq original
        rw [same] at ranked
        change (prefixEmbedding.event index).val = state.attempt.phase + index.val at ranked
        obtain ⟨author, domain, _owned, layout⟩ :=
          earlier.binding_before_length (later.prepend suffix) index before
        have output : (serviceGraph setup .concurrent).outputLayout
            (prefixEmbedding.event index) = .binding author domain :=
          (prefixEmbedding.layout_eq index).trans layout
        have authorEq : author = owner := Option.some.inj
          (((serviceGraph setup .concurrent).actor?_of_outputLayout_binding output).symm.trans
            acting)
        subst author
        exact order.2 (prefixEmbedding.event index) (by omega) (by omega) domain output absent
    have own := congrFun exactJoint owner
    simp only [CommitRecoveryState.commitJoint, middleActive, not_false_eq_true,
      and_self, ↓reduceIte, Setup.proposalRecoveryJoint] at own
    have allowed := legal.2 owner
    cases chosen : joint owner with
    | none => simp only [chosen, Option.map_none] at own; cases own
    | some move => rw [chosen] at allowed; exact allowed.1.2
  refine ⟨event, owner, payload, binding, position, receiptActive, ?_⟩
  intro active
  obtain ⟨_committing, acting, _decode⟩ := source_binding_at_rank setup.program current.point
    event owner payload binding position
  obtain ⟨move, own⟩ : ∃ move, joint owner = some move := by
    cases chosen : joint owner with
    | some move => exact ⟨move, rfl⟩
    | none =>
        have offered := legal.2 owner
        rw [chosen] at offered
        exact (offered ⟨acting, active⟩).elim
  have middleActive : owner ∉ synthetic.excluded := by
    intro excluded
    have observed := congrFun exactJoint owner
    simp only [Setup.proposalRecoveryJoint, own, Option.map_some,
      CommitRecoveryState.commitJoint, excluded, not_true_eq_false, and_false,
      ↓reduceIte] at observed
    cases observed
  have ownSemantic : (joint owner).map (·.semantic) = some
      ⟨.commit owner name payload
        ((image.accepted (.inr event)).elim PublicationResult.failure
          (fun handle => image.bindingResult handle payload)),
        (image.accepted (.inr event)).isNone⟩ := by
    simpa only [Setup.proposalRecoveryJoint, CommitRecoveryState.commitJoint,
      middleActive, not_false_eq_true, and_self, ↓reduceIte] using congrFun exactJoint owner
  have decodedAction (result : PublicationResult (L.Val payload)) :
      decodeEventAction setup.program event
        (cast (congrArg EventField.Action binding.symm) result) =
          some (.commit owner name payload result) := by
    subst event
    rw [views.actionEq]
    simpa only [cast_cast] using localDecode result
  have data : phaseRecoveryBindingData setup .concurrent event owner payload binding
      ((joint owner).map (·.semantic)) =
        ((image.accepted (.inr event)).elim PublicationResult.failure
          (fun handle => image.bindingResult handle payload),
          (image.accepted (.inr event)).isNone) := by
    have encoded := encodeEventAction?_decodeEventAction_eq_some setup.program event _ _
      (decodedAction ((image.accepted (.inr event)).elim PublicationResult.failure
        (fun handle => image.bindingResult handle payload)))
    rw [ownSemantic]
    cases accepted : image.accepted (.inr event) with
    | none => simp only [phaseRecoveryBindingData, Option.elim_none,
        Option.isNone_none, Option.elim_some, ↓reduceIte]
    | some handle =>
        simp only [accepted, Option.elim_some, Option.isNone_some] at encoded ⊢
        simp only [phaseRecoveryBindingData, Option.elim_some, Bool.false_eq_true,
          ↓reduceIte, Option.bind_some, encoded, Option.map_some, cast_cast, cast_eq,
          Option.getD_some]
  obtain ⟨localCell, localField⟩ := source_selected_binding_terminal setup earlier name owner
    payload fresh guard rest suffix refs embedding.ref
  let terminalCell : HasVar setup.program.terminalCtx name (.commitment owner payload) :=
    cast (congrArg (fun context => HasVar context name (.commitment owner payload))
      alignment.contextEq) localCell
  have castGet {A B : SourceCtx Player L} (same : A = B)
      (table : ContextRefs (graphLayout setup.program) A)
      (cell : HasVar A name (.commitment owner payload)) :
      (cast (congrArg (ContextRefs (graphLayout setup.program)) same) table).get
          (cast (congrArg (fun context => HasVar context name (.commitment owner payload))
            same) cell) = table.get cell := by
    cases same
    rfl
  have terminalField : ((terminalRefs setup.program).get terminalCell).field = .inr event := by
    rw [← alignment.refsEq]
    exact (congrArg FieldRef.field (castGet alignment.contextEq _ localCell)).trans
      (localField.trans (by
        change (Sum.inr (embedding.event _) :
          FieldId setup.context.length (eventCount setup.program)) = Sum.inr event
        congr 1
        exact (congrArg embedding.event (Fin.ext atSlot.symm)).trans selectedEq))
  refine ⟨Δ, P, name, fresh, guard, earlier, rest, size, rfl,
    ⟨selected, atSlot, selectedEq⟩, ⟨terminalCell, terminalField⟩, data, ?_⟩
  exact cellAt (earlier.names_nodup unique) middleActive

omit [Fintype Player] in
theorem source_commit_step_readback
    (current next : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (moved : some next ∈
      (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩).support)
    (committing : ProtocolState.atCommit setup.program current.point = true)
    {target} (whole : setup.proposalRecoveryProtocol.Trace target)
    (retained : TracePrefix (prior.extend joint legal moved) whole) :
    ((proposalSourceSteps setup (setup.proposalRecoveryEraseTrace whole))[prior.length]?).map
      (fun event => event.source.map
        (fun state => ProtocolState.atCommit setup.program state.point)) = some (some true) := by
  induction retained with
  | refl =>
      have size : (proposalSourceSteps setup
          (setup.proposalRecoveryEraseTrace prior)).length = prior.length := by
        rw [proposalSourceSteps_length, setup.proposalRecoveryEraseTrace_length]
      rw [Setup.proposalRecoveryEraseTrace, proposalSourceSteps_extend,
        List.getElem?_append_right
          (l₁ := proposalSourceSteps setup (setup.proposalRecoveryEraseTrace prior)) (by omega),
        size, Nat.sub_self]
      simp only [List.getElem?_cons_zero, Option.map_some, committing]
  | @extend source target earlier retained actions allowed reached ih =>
      rw [Setup.proposalRecoveryEraseTrace, proposalSourceSteps_extend,
        List.getElem?_append_left]
      · exact ih
      · rw [proposalSourceSteps_length, setup.proposalRecoveryEraseTrace_length]
        have size := retained.length_le
        simp only [Trace.length] at size
        omega

theorem canonicalSource_foreignGood (operational : implementation.Operational)
    (who : Player) (history : (nativeProtocol).History)
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
        implementation.leaks implementation.bounds nativeInitial implementation.horizon
        implementation.scheduler owner history) :
    setup.proposalRecoveryForeignGood who
      (canonicalSource setup implementation operational history) := by
  classical
  rcases history with ⟨_ | reference, trace⟩
  · intro owner different ⟨record, member, _bad⟩
    cases member
  let witness := (checkpointSelection setup implementation operational trace).val
  let final := canonicalSource setup implementation operational ⟨some reference, trace⟩
  have erased : setup.proposalRecoveryEraseTrace final.trace = witness.checkpoint.trace :=
    setup.proposalRecoveryEraseTrace_lift _ _
  let inputs := setup.initialLaw.map encodeInputs
  have initialEq : nativeInitial = inputs.map (PhaseRuntimeState.initial implementation.plan) := by
    simp only [ReservedConcurrentImplementation.initial, inputs, PMF.map_comp, Function.comp_def]
  have raw := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  intro owner different ⟨record, remembered, bad⟩
  obtain ⟨before, after, prior, joint, legal, moved, kept, _view, own⟩ :=
    setup.proposalRecoveryModel.exists_tracePrefix_of_mem_ownPlay final.trace remembered
  have offered := legal.2 owner; rw [own] at offered
  obtain ⟨current, rfl⟩ : ∃ current, before = some current := by
    cases before with
    | none => cases offered.1
    | some current => exact ⟨current, rfl⟩
  have flags := ProposalRecoveryMove.generatedPreparationFailure_flags record.2.semantic bad
  have committing : ProtocolState.atCommit setup.program current.point = true := by
    rw [← ProtocolState.atCommit_observe setup.program current.point owner]
    exact ProtocolView.atCommit_of_generatedPreparationFailure owner setup.program _
      record.2.semantic offered.2.1 bad
  change after ∈ ((current.step (Setup.proposalRecoveryJoint joint)).map some).support at moved
  obtain ⟨next, nativeMoved, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp moved
  have moved : some next ∈
      (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨next, nativeMoved, rfl⟩
  have positivePath : ∀ {state} (path : setup.proposalRecoveryProtocol.Trace state),
      state ≠ none → 0 < path.length := by
    intro state path
    cases path with
    | start => intro impossible; exact (impossible rfl).elim
    | extend => intro _; simp only [Trace.length]; omega
  have positive : 0 < prior.length := positivePath prior (by intro impossible; cases impossible)
  have bound : prior.length < witness.checkpoint.trace.length := by
    have size := kept.length_le
    rw [← erased, setup.proposalRecoveryEraseTrace_length]
    simp only [Trace.length] at size
    omega
  obtain ⟨state, checkpoint, image, closed, fuel, later, path, onward, lower, upper,
      instructions, _addresses, kind⟩ :=
    source_commit_chunk setup witness.origins prior.length positive bound
      (by
        rw [← erased]
        exact source_commit_step_readback setup current next prior joint legal moved committing
          final.trace kept)
  have literal : ∀ event actor payload
      (binding : (serviceGraph setup .concurrent).outputLayout event = .binding actor payload),
      event.val = instructionCount setup.program -
        ProtocolState.remaining setup.program current.point →
      actor = owner ∧ phaseRecoveryBindingData setup .concurrent event actor payload binding
        ((joint actor).map (·.semantic)) = (.failure, false) := by
    intro event actor payload binding position
    obtain ⟨_committing, acting, decode⟩ := source_binding_at_rank setup.program current.point
      event actor payload binding position
    have same : actor = owner := Option.some.inj (acting.symm.trans offered.1.1)
    subst actor
    obtain ⟨encoded, decoded⟩ := decode record.2.semantic.action offered.2.1.1
    have encoding := encodeEventAction?_decodeEventAction_eq_some setup.program event
      encoded record.2.semantic.action decoded
    have failed := (decodeEventAction_binding_failure_iff setup.program event owner payload
      binding encoded record.2.semantic.action decoded).mpr flags.2
    exact ⟨rfl, by simp only [own, Option.map_some, phaseRecoveryBindingData, Option.elim_some,
      flags.1, Bool.false_eq_true, ↓reduceIte, Option.bind_some, encoding,
      Option.map_some, Option.getD_some, failed]⟩
  have finish : ∀ (state : PhaseRuntimeState (serviceGraph setup .concurrent))
      (checkpoint : RecoverySourceCheckpoint setup .concurrent state)
      (image : EventGraphRuntime.State (serviceGraph setup .concurrent))
      (closed : setup.commitRecoveryProtocol.History) (fuel later : Nat),
      setup.commitRecoveryProtocol.ReachesWithin fuel ⟨_, checkpoint.trace⟩ closed →
      setup.commitRecoveryProtocol.ReachesWithin later closed ⟨_, witness.checkpoint.trace⟩ →
      checkpoint.trace.length ≤ prior.length → prior.length < closed.trace.length →
      setup.recoveryJointRecall closed.trace =
        (checkpoint.commitInstructionWord image).reverse ++
          setup.recoveryJointRecall checkpoint.trace →
      (image = reference.execution.application.current.native ∨
        image = reference.execution.application.entry.native ∨
        ∃ record ∈ reference.execution.application.retired, image = record.state) ∨
      (∃ (nextState : PhaseRuntimeState (serviceGraph setup .concurrent))
        (nextCheckpoint : RecoverySourceCheckpoint setup .concurrent nextState),
        nextState.generation = state.generation ∧ closed = ⟨_, nextCheckpoint.trace⟩ ∧
        ∀ record ∈ reference.execution.application.retired, state.attempt ≠ record.attempt) →
      False := by
    intro state checkpoint image closed fuel later path onward lower upper instructions branch
    have geometry := source_decoded_binding_row setup checkpoint image closed path instructions
      final (by rw [erased]; exact onward.tracePrefix) current next prior joint legal moved
      kept lower upper
    obtain ⟨saved, generation, geometry⟩ := geometry
    generalize decomposition : commitPhase checkpoint.residual.tail = segment at geometry
    rcases segment with ⟨Ξ, Q, suffix, block, reconstruct, boundary⟩
    dsimp only at geometry
    obtain ⟨event, actor, payload, binding, position, _receiptActive, geometry⟩ := geometry
    obtain ⟨sameOwner, badData⟩ := literal event actor payload binding position
    subst actor
    obtain ⟨Δ, P, name, fresh, guard, earlier, rest, _size, splitBlock, _selected,
      ⟨terminalCell, terminalField⟩, data, cell⟩ := geometry offered.1.2
    have data := badData.symm.trans data
    have failed := (congrArg Prod.fst data).symm
    have accepted : ∃ handle, image.accepted (.inr event) = some handle := by
      cases found : image.accepted (.inr event) with
      | none =>
          exact (Bool.false_ne_true (by
            simpa only [found, Option.isNone_none] using congrArg Prod.snd data)).elim
      | some handle => exact ⟨handle, rfl⟩
    rcases branch with selected | ⟨nextState, nextCheckpoint, sameGeneration, rfl, absent⟩
    · obtain ⟨handle, accepted⟩ := accepted
      obtain ⟨value, good⟩ := accepted_snapshot_value_of_no_generated_unusable setup
        implementation reference trace image selected owner (foreign owner different)
        event payload binding handle accepted
      rw [accepted, Option.elim_some, good] at failed
      cases failed
    have sourceCommit : ProtocolState.atCommit checkpoint.residual.tail
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true := by
      rw [← reconstruct, ← splitBlock, earlier.prepend_append]
      cases earlier <;> rfl
    have failurePoint := source_decoded_failure_point setup checkpoint nextCheckpoint image
      sourceCommit path instructions sameGeneration (Ξ := Δ) (Q := P)
    rw [decomposition] at failurePoint
    have read := source_saved_cell_readback setup nextCheckpoint.residual.tail
      nextCheckpoint.residual.lift nextCheckpoint.origin nextCheckpoint.source
      nextCheckpoint.unique _ nextCheckpoint.trace rfl rfl witness.checkpoint
      onward.tracePrefix terminalCell .failure
      (failurePoint earlier name owner payload fresh guard rest splitBlock
        (cell.trans (congrArg some failed)))
    have stored := FieldRef.get?_preserved ((terminalRefs setup.program).get terminalCell)
      _ _ witness.stored _ read
    have mask : owner ∉ next.excluded := by
      have noMiss : ∀ actor,
          CommitRecoveryMove.missed (Setup.proposalRecoveryJoint joint actor) = false := by
        intro actor; by_cases same : actor = owner
        · subst actor
          simp only [Setup.proposalRecoveryJoint, own, Option.map_some,
            CommitRecoveryMove.missed, Option.elim_some, flags.1]
        · have allowed := legal.2 actor
          cases chosen : joint actor with
          | none => simp [Setup.proposalRecoveryJoint, chosen, CommitRecoveryMove.missed]
          | some move =>
              rw [chosen] at allowed
              exact (same (Option.some.inj (allowed.1.1.symm.trans offered.1.1))).elim
      obtain ⟨result, supported, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp nativeMoved
      have rawSupported : result.1 ∈ (ProtocolState.recoveryStep setup.program current.point
          current.excluded (Setup.proposalRecoveryJoint joint)).support := by
        rw [← map_val_pmfToSubtype
          (ProtocolState.recoveryStep setup.program current.point current.excluded
            (Setup.proposalRecoveryJoint joint))
          (fun result supported => ProtocolState.recoveryStep_excluded_monotone
            setup.program current.point current.excluded _ result supported)]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, supported, rfl⟩
      have same := (ProtocolState.recoveryStep_noMiss_observe owner setup.program
        current.point current.point rfl committing current.excluded current.excluded
        offered.1.2 offered.1.2 _ _ rfl noMiss _ rawSupported _ rawSupported).2
      rw [← equal, CommitRecoveryState.close_excluded]
      exact Eq.mpr (congrArg (fun excluded : Finset Player => owner ∉ excluded) same)
        offered.1.2
    obtain ⟨before, after, old, actions, allowed, reached, retained, depth, first, second, _word⟩ :=
      source_address_row setup final.trace (prior.length - 1) (by
        rw [← setup.proposalRecoveryEraseTrace_length final.trace, erased]; omega)
    have oldKept : TracePrefix old final.trace :=
      (TracePrefix.extend .refl actions allowed reached).trans retained
    have priorKept : TracePrefix prior final.trace :=
      (TracePrefix.extend .refl joint legal moved).trans kept
    have sameBefore := oldKept.eq_of_same_length priorKept (by omega)
    have sameAfter := retained.eq_of_same_length kept (by simp only [Trace.length]; omega)
    have beforeEq : before = some current := congrArg History.state sameBefore
    have afterEq : after = some next := congrArg History.state sameAfter
    have wordEq := (congrArg (fun path => setup.recoveryAddressWord path) erased).trans
      witness.chronology.addresses
    have first := ((congrArg (fun word => word[prior.length - 1]?) wordEq).symm.trans first).trans
      (congrArg (fun state : setup.proposalRecoveryProtocol.State =>
        some (state.elim (none, (∅, 0, 0)) CommitRecoveryState.publicAddress)) beforeEq)
    have second := ((congrArg (fun word => word[prior.length - 1 + 1]?) wordEq).symm.trans
      second).trans (congrArg (fun state : setup.proposalRecoveryProtocol.State =>
        some (state.elim (none, (∅, 0, 0)) CommitRecoveryState.publicAddress)) afterEq)
    obtain ⟨provider, location, _active, completed, handle, accepted⟩ :=
      PhaseRuntimeState.sourcePublicAddressWord_gap_provider implementation.runtime
        implementation.leaks implementation.plan inputs implementation.horizon
        implementation.scheduler (initialEq ▸ raw) event owner payload binding
        (prior.length - 1) current.publicAddress next.publicAddress first second
        (congrArg some position.symm) mask (by
          intro record member equal
          apply absent record member
          exact congrArg (fun pair : Nat × Nat => (⟨pair.2, pair.1⟩ : CommitAttemptId))
            (by simpa only [CommitRecoveryState.publicAddress, saved,
              checkpoint.saved_position, generation] using equal))
    have selected : provider = reference.execution.application.current.native ∨
        provider = reference.execution.application.entry.native ∨
        ∃ record ∈ reference.execution.application.retired, provider = record.state := by
      rcases location with ⟨same, _⟩ | ⟨j, same, _⟩
      · exact Or.inl same
      · exact Or.inr (Or.inr ⟨_, List.getElem_mem j.isLt, same⟩)
    obtain ⟨value, good⟩ := accepted_snapshot_value_of_no_generated_unusable setup
      implementation reference trace provider selected owner (foreign owner different)
      event payload binding handle accepted
    obtain ⟨_draw, valid⟩ := witness.native
    have valueEq := witness.binding.active.binding_value
      ((terminalRefs setup.program).get terminalCell) .failure stored
    rw [terminalField] at valueEq
    have recorded : ∃ action : (serviceGraph setup .concurrent).Action event,
        ⟨event, action⟩ ∈ reference.execution.application.current.native.config.history ∧
        cast (congrArg EventField.Action binding) action = .success value := by
      rcases location with ⟨rfl, _below⟩ | ⟨j, rfl, below⟩
      · obtain ⟨action, member, meaning⟩ :=
          witness.binding.active.completed_binding_action valid.active.reachable
            event owner payload binding completed
        exact ⟨action, member, by simpa only [accepted, Option.elim_some, good] using meaning⟩
      · have member := List.getElem_mem j.isLt
        obtain ⟨bindings, ⟨input, actual⟩, _fixed⟩ := phaseRetiredBindings_history
          implementation.runtime implementation.leaks implementation.plan inputs
          implementation.horizon implementation.scheduler (initialEq ▸ raw) _ member
        obtain ⟨action, recorded, meaning⟩ := bindings.completed_binding_action actual.reachable
          event owner payload binding completed
        have owned : ⟨event, action⟩ ∈
            ((serviceGraph setup .concurrent).ownCompletions owner
              reference.execution.application.retired[j].state.config.history).filter
                (fun completion => completion.event.val <
                  reference.execution.application.retired[j].attempt.phase) := by
          simp only [List.mem_filter, EventGraph.ownCompletions]
          refine ⟨⟨recorded, ?_⟩, by simpa using below⟩
          simp [(serviceGraph setup .concurrent).actor?_of_outputLayout_binding binding]
        have ownPrefix := phaseRetiredOwnPrefix_history implementation.runtime implementation.leaks
          implementation.plan inputs implementation.horizon implementation.scheduler
          (initialEq ▸ raw) _ member owner
        have currentOwned := Eq.mp (congrArg
          (fun history : List (serviceGraph setup .concurrent).Completion =>
            (⟨event, action⟩ : (serviceGraph setup .concurrent).Completion) ∈ history)
          ownPrefix) owned
        let archivedImage := reference.execution.application.retired[j.val].state
        have receivedAt : archivedImage.accepted (.inr event) = some handle := accepted
        have valueAt : archivedImage.bindingResult handle payload = .success value := good
        have resolved := (congrArg (fun candidate => Option.elim candidate
          PublicationResult.failure (fun handle => archivedImage.bindingResult handle payload))
          receivedAt).trans valueAt
        exact ⟨action, (List.mem_filter.mp (List.mem_filter.mp currentOwned).1).1,
          meaning.trans resolved⟩
    obtain ⟨action, recorded, meaning⟩ := recorded
    have currentMeaning := witness.binding.active.recorded_binding_action valid.active.reachable
      event owner payload binding action recorded
    have impossible := meaning.symm.trans (currentMeaning.trans valueEq.symm)
    cases impossible
  by_cases archived : ∃ record ∈ reference.execution.application.retired,
      state.attempt = record.attempt
  · obtain ⟨record, member, attempt⟩ := archived
    obtain ⟨index, inside, recordEq⟩ := List.mem_iff_getElem.mp member
    obtain ⟨oldState, old, _recall, _origins, _archive, oldAttempt, _retained, _cut,
      _agrees, _positive, oldClosed, oldFuel, oldLater, oldPath, oldWord, oldOnward⟩ :=
      witness.origins.get index inside
    erw [recordEq] at oldAttempt oldWord
    have sameAttempt := oldAttempt.trans attempt.symm
    have sameControl : setup.commitRecoveryControl (some (CommitRecoveryState.atPoint
        (old.residual.lift (ProtocolState.entry old.residual.tail old.source))
          oldState.entry.excluded oldState.generation)) =
        setup.commitRecoveryControl (some (CommitRecoveryState.atPoint
          (checkpoint.residual.lift
            (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
            state.entry.excluded state.generation)) := by
      have generation := congrArg CommitAttemptId.generation sameAttempt
      have phase := congrArg CommitAttemptId.phase sameAttempt
      simp only [Setup.commitRecoveryControl, Option.elim_some, CommitRecoveryState.control,
        CommitRecoveryState.atPoint, old.saved_position, checkpoint.saved_position]
      change oldState.generation = state.generation at generation
      rw [generation, phase]
    have same := setup.commitRecovery_ancestor_eq_of_control_eq
      (oldPath.trans oldOnward) (path.trans onward) sameControl
    have sameDepth : old.trace.length = checkpoint.trace.length :=
      congrArg (fun h : setup.commitRecoveryProtocol.History => h.trace.length) same
    have samePoint :
        old.residual.lift (ProtocolState.entry old.residual.tail old.source) =
          checkpoint.residual.lift
            (ProtocolState.entry checkpoint.residual.tail checkpoint.source) :=
      congrArg CommitRecoveryState.point (Option.some.inj (congrArg History.state same))
    have oldLength := congrArg List.length oldWord
    have newLength := congrArg List.length instructions
    simp only [setup.recoveryJointRecall_length, List.length_append, List.length_reverse,
      source_commit_instruction_word_length, samePoint, sameDepth] at oldLength newLength
    exact finish oldState old record.state oldClosed oldFuel oldLater oldPath oldOnward
      (by omega) (by omega) oldWord (Or.inl (Or.inr (Or.inr ⟨record, member, rfl⟩)))
  · rcases kind with ⟨record, member, _imageEq, attempt⟩ |
        ⟨nextState, nextCheckpoint, phase, remaining, _phases, _commit, generation,
          _boundary, _image, closedEq⟩
    · exact archived ⟨record, member, attempt⟩
    · exact finish state checkpoint image closed fuel later path onward lower upper instructions
        (Or.inr ⟨nextState, nextCheckpoint, generation, closedEq,
          fun record member equal => archived ⟨record, member, equal⟩⟩)

omit [Fintype Player] in
private theorem source_binding_success_of_proper
    (current : CommitRecoveryState setup.program)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (owner : Player) (payload : L.Ty)
    (event : (serviceGraph setup .concurrent).EventId)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (position : event.val = instructionCount setup.program -
      ProtocolState.remaining setup.program current.point)
    (active : owner ∉ current.excluded)
    (usable : ∀ move, SourceProgram.Setup.proposalRecoveryJoint joint owner = some move →
      move.missing = false ∧ ¬ move.action.IsFailure) :
    ∃ value : L.Val payload,
      phaseRecoveryBindingData setup .concurrent event owner payload binding
        ((joint owner).map (·.semantic)) = (.success value, false) := by
  obtain ⟨_committing, acting, decode⟩ := source_binding_at_rank setup.program current.point
    event owner payload binding position
  obtain ⟨move, chosen⟩ : ∃ move, joint owner = some move := by
    have offered := legal.2 owner
    cases selected : joint owner with
    | none =>
        rw [selected] at offered
        exact (offered ⟨acting, active⟩).elim
    | some move => exact ⟨move, rfl⟩
  have offered := legal.2 owner
  rw [chosen] at offered
  have available : move.semantic ∈ current.available owner := offered.2.1
  obtain ⟨encoded, decoded⟩ := decode move.semantic.action available.1
  have encoding := encodeEventAction?_decodeEventAction_eq_some setup.program event
    encoded move.semantic.action decoded
  have proper := usable move.semantic (by
    simp only [SourceProgram.Setup.proposalRecoveryJoint, chosen, Option.map_some])
  have nonfailure : cast (congrArg EventField.Action binding) encoded ≠ .failure := by
    intro failed
    exact proper.2 ((decodeEventAction_binding_failure_iff setup.program event owner
      payload binding encoded move.semantic.action decoded).mp failed)
  cases result : cast (congrArg EventField.Action binding) encoded with
  | failure => exact (nonfailure result).elim
  | success value =>
      refine ⟨value, ?_⟩
      simp only [chosen, Option.map_some, phaseRecoveryBindingData, Option.elim_some,
        proper.1, Bool.false_eq_true, ↓reduceIte, Option.bind_some, encoding,
        Option.map_some, Option.getD_some, result]

private theorem sourceForcedBlock_binding_value
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (who : Player) (acting : ProtocolState.actor setup.program current.point = some who)
    (ordinary : current.excluded = current.entryExcluded)
    (choice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who trace))
    (properChoice : ∀ move, choice.val.map (·.semantic) = some move →
      move.missing = false ∧ ¬ move.action.IsFailure)
    (final : setup.proposalRecoveryProtocol.History)
    (supported : final ∈
      (sourceForcedBlock setup values who ⟨some current, trace⟩ choice).support)
    (attemptId : CommitAttemptId)
    (generation : current.generation = attemptId.generation)
    (saved : instructionCount setup.program -
      ProtocolState.remaining setup.program current.saved = attemptId.phase)
    (owner : Player) (active : owner ∉ current.excluded)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (lower : instructionCount setup.program -
      ProtocolState.remaining setup.program current.point ≤ event.val)
    (upper : event.val < instructionCount setup.program -
      ProtocolState.commitEnd setup.program current.saved) :
    ∃ value : L.Val payload,
      sourceBindingAt setup attemptId event owner payload binding final.trace = some value := by
  obtain ⟨Γ, O, name, actor, domain, fresh, guard, next, lift, entry,
      origin, atEntry, _unique⟩ := ProtocolState.exists_committing_entry setup.program
    current.point setup.namesNodup committing
  have actorEq : actor = who := by
    have read := origin.actor_lift
      (ProtocolState.entry (.commit name actor fresh guard next) entry)
    rw [← atEntry] at read
    exact Option.some.inj (read.symm.trans acting)
  subst actor
  obtain ⟨Δ, P, suffix, rest, reconstruct, boundary⟩ := commitPhase next
  cases reconstruct
  let block : SourceProgram.CommitPrefix Γ O Δ P := .commit name who fresh guard rest
  have sameEnd : ProtocolState.commitEnd setup.program current.point =
      ProtocolState.commitEnd setup.program current.saved := by
    rcases setup.commitRecovery_blockFrontier (setup.proposalRecoveryEraseTrace trace) with
      ⟨_saved, _live, sameEnd⟩ | same
    · exact sameEnd
    · rw [same]
  have endpoint : ProtocolState.commitEnd setup.program current.saved =
      instructionCount suffix := by
    rw [← sameEnd, atEntry, origin.commitEnd_lift]
    exact block.commitEnd_entry_prepend suffix boundary entry
  have distance : block.length + ProtocolState.commitEnd setup.program current.saved =
      ProtocolState.remaining setup.program current.point := by
    rw [endpoint, atEntry, origin.remaining_lift, ProtocolState.remaining_entry]
    exact (block.instructionCount_prepend suffix).symm
  have fuel : sourceCommitFuel setup ⟨some current, trace⟩ = rest.length + 1 := by
    change ProtocolState.remaining setup.program current.point -
      ProtocolState.commitEnd setup.program current.point = rest.length + 1
    rw [sameEnd]
    change rest.length + 1 + ProtocolState.commitEnd setup.program current.saved = _ at distance
    omega
  obtain ⟨finished, last, lastTrace, attempt, finalEq, _lastPoint,
      lastExcluded, _lastEntry, _lastGeneration, word, proper, _head⟩ :=
    sourceForcedBlock_commit_support setup values fresh guard rest suffix lift origin
      entry current trace atEntry ordinary fuel choice properChoice final supported
  have wordFinal : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace final.trace) =
      attempt.joints.reverse ++ setup.recoveryJointRecall
        (setup.proposalRecoveryEraseTrace trace) := by
    rw [finalEq]
    exact word
  have targetPrefix : TracePrefix trace final.trace := by
    unfold sourceForcedBlock at supported
    obtain ⟨middle, first, tail⟩ := (PMF.mem_support_bind_iff ..).mp supported
    exact ((setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ 1
      ⟨some current, trace⟩ middle first).tracePrefix).trans
        ((setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ _
          middle final tail).tracePrefix)
  let offset := event.val - (instructionCount setup.program -
    ProtocolState.remaining setup.program current.point)
  have bounded := ProtocolState.remaining_le_instructionCount setup.program current.point
  have inside : offset < attempt.joints.length := by
    rw [attempt.joints_length]
    dsimp only [offset]
    change rest.length + 1 + ProtocolState.commitEnd setup.program current.saved = _ at distance
    change event.val - _ < rest.length + 1
    omega
  obtain ⟨before, after, prior, joint, legal, moved, retained, _depth,
      row, sameSaved, sameGeneration, position⟩ :=
    source_commit_chunk_at_rank setup current trace committing final targetPrefix attempt.joints
      wordFinal offset inside event.val (by dsimp only [offset]; omega) upper
  have monotone := setup.commitRecovery_public_excluded_of_reaches
    (setup.proposalRecoveryEraseTrace_prefix
      ((TracePrefix.extend .refl joint legal moved).trans retained)).reachesWithin
  have beforeActive : owner ∉ before.excluded := by
    change before.excluded ⊆ (setup.commitRecoveryPublic final.state).1 at monotone
    rw [finalEq] at monotone
    change before.excluded ⊆ last.excluded at monotone
    exact fun member => active (lastExcluded ▸ monotone member)
  obtain ⟨value, actual⟩ := source_binding_success_of_proper setup before joint legal owner
    payload event binding position.symm beforeActive (by
      intro move chosen
      rw [row] at chosen
      exact proper _ (List.getElem_mem inside) owner move chosen)
  refine ⟨value, sourceBindingAt_of_origin setup attemptId event owner payload binding
    before prior joint legal (some after) moved (sameGeneration.trans generation) ?_ position
    (.success value, false) actual final.trace retained⟩
  rw [sameSaved]
  exact saved

theorem sourceHandleMeaning_of_current_emission
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
    (owner : Player) (active : owner ∉ cut.cursor.current.excluded)
    (record : (nativeApplication).PlayerEntry)
    (recorded : record ∈ reference.execution.recall owner)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (transmitted : record.action.transmission = some material)
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (emitted : record.emitted = some message)
    (current : message.payload.attempt = reference.execution.application.attempt)
    (named : (serviceGraph setup .concurrent).EventId)
    (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout named = .binding owner payload)
    (handle : Handle (serviceGraph setup .concurrent))
    (call : message.payload.packet.call = .commitment named handle) :
    ∃ value : L.Val payload,
      sourceHandleMeaning setup implementation G reference handle = some ⟨payload, value⟩ := by
  classical
  let initial := (setup.initialLaw.map encodeInputs).map
    (PhaseRuntimeState.initial implementation.plan)
  let raw := (nativeMenu).toRawTrace initial implementation.horizon implementation.scheduler trace
  obtain ⟨actual, sent, sender, packet⟩ := PhaseCount.recalled_submission_emitted
    implementation.runtime implementation.leaks initial implementation.horizon
      implementation.scheduler raw owner record recorded material transmitted
  have actualEq : actual = message := Option.some.inj (sent.symm.trans emitted)
  subst actual
  obtain ⟨callback, callbackTrace, retained, _acting, viewed, request⟩ :=
    phase_recorded_binding_request implementation.runtime implementation.leaks implementation.bounds
      implementation.plan (setup.initialLaw.map encodeInputs) implementation.horizon
      (serviceGraph_revealRelaxedOrdered setup .concurrent) implementation.scheduler trace
      owner record recorded material transmitted named handle (packet.symm.trans call)
  have emittedNamespace := phase_recalled_emission_attempt implementation.runtime
    implementation.leaks initial implementation.horizon implementation.scheduler raw owner record
      recorded message emitted
  rw [viewed] at emittedNamespace
  change message.payload.attempt = callback.execution.application.attempt at emittedNamespace
  have sameAttempt : callback.execution.application.attempt =
      reference.execution.application.attempt := emittedNamespace.symm.trans current
  obtain ⟨phase, rest, installed, kind, inside⟩ :=
    phase_ready_binding_phase implementation.runtime implementation.leaks implementation.plan
      (serviceGraph_revealRelaxedOrdered setup .concurrent) operational.maximalPhases
      (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
      ((nativeMenu).toRawTrace initial implementation.horizon
        implementation.scheduler callbackTrace)
      owner named payload binding request.2.2.1
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered implementation.plan draw
  have ordered := (phaseApplication_seedOrder implementation.runtime implementation.leaks).history
    initial implementation.horizon implementation.scheduler initialized
    ((nativeMenu).toRawTrace initial implementation.horizon implementation.scheduler callbackTrace)
  have metadata := phase_attempt_metadata_of_prefix implementation.runtime implementation.leaks
    (nativeMenu) initial initialized implementation.horizon implementation.scheduler
    callback reference callbackTrace trace retained ordered sameAttempt
  have phaseEq : phase = cut.phase := by
    have heads := congrArg (fun pair => pair.1.head?) metadata
    simpa only [installed, List.head?_cons, cut.installed, Option.some.injEq] using heads
  subst phase
  have namedBounds := (cut.phase.mem_events named).mp inside
  have eventBounds := (cut.phase.mem_events event).mp cut.inside
  have positive : 0 < cut.block.length := by have size := cut.size; omega
  have startRank : instructionCount setup.program -
      ProtocolState.remaining setup.program cut.cursor.current.point = cut.phase.low := by
    rw [cut.cursor.point, cut.cursor.origin.remaining_lift, ProtocolState.remaining_entry]
    have count := cut.cursor.compiled.countEq
    rw [eventCount_eq_instructionCount, eventCount_eq_instructionCount] at count
    have offset := cut.offset
    omega
  have startEnd : instructionCount setup.program -
      ProtocolState.commitEnd setup.program cut.cursor.current.saved = cut.phase.high := by
    rw [cut.cursor.savedEnd positive]
    have count := cut.cursor.compiled.countEq
    rw [eventCount_eq_instructionCount, eventCount_eq_instructionCount,
      cut.block.instructionCount_prepend] at count
    have offset := cut.offset
    have size := cut.size
    omega
  have startCommit : ProtocolState.atCommit setup.program cut.cursor.current.point = true := by
    rw [cut.cursor.point, cut.cursor.origin.atCommit_lift]
    have entryCommit : ∀ {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
        (block : SourceProgram.CommitPrefix Γ O Δ P)
        (suffix : SourceProgram Player L Δ P) (entry : SourceProgram.Config Player L Γ),
        0 < block.length → ProtocolState.atCommit (block.prepend suffix)
          (ProtocolState.entry (block.prepend suffix) entry) = true := by
      intro Γ Δ O P block
      cases block with
      | nil => intro suffix entry impossible; cases Nat.not_lt_zero _ impossible
      | commit => intro suffix entry _; rfl
    exact entryCommit cut.block cut.suffix cut.cursor.source positive
  have startOrdinary : cut.cursor.current.excluded = cut.cursor.current.entryExcluded :=
    cut.cursor.excluded.trans cut.cursor.entryExcluded.symm
  obtain ⟨finished, last, lastTrace, attempt, completed, _lastPoint,
      excluded, _lastEntry, _lastGeneration, word, _labels, proper⟩ :=
    proposalRecovery_ordinary_commit_block_support setup values cut.block cut.suffix
      cut.cursor.lift cut.cursor.origin cut.cursor.source cut.cursor.current cut.cursor.trace
      cut.cursor.point startOrdinary cut.completed cut.sourceSupported
  have wordFinal : setup.recoveryJointRecall
      (setup.proposalRecoveryEraseTrace cut.completed.trace) = attempt.joints.reverse ++
        setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace cut.cursor.trace) := by
    rw [completed]
    exact word
  have rowAt (rank : Nat) (bounds : cut.phase.low ≤ rank ∧ rank < cut.phase.high) :
      ∃ (before after : CommitRecoveryState setup.program)
        (prior : setup.proposalRecoveryProtocol.Trace (some before))
        (joint : Player → Option (ProposalRecoveryMove Player L))
        (legal : setup.proposalRecoveryProtocol.Legal (some before) joint)
        (moved : some after ∈
          (setup.proposalRecoveryProtocol.step (some before) ⟨joint, legal⟩).support),
        TracePrefix (prior.extend joint legal moved) cut.completed.trace ∧
        prior.length = cut.cursor.trace.length + (rank - cut.phase.low) ∧
        SourceProgram.Setup.proposalRecoveryJoint joint = attempt.joints[rank - cut.phase.low]'(by
          rw [attempt.joints_length]; have size := cut.size; omega) ∧
        before.saved = cut.cursor.current.saved ∧
        before.generation = cut.cursor.current.generation ∧
        instructionCount setup.program -
          ProtocolState.remaining setup.program before.point = rank := by
    exact source_commit_chunk_at_rank setup cut.cursor.current cut.cursor.trace startCommit
      cut.completed (cut.past.trans cut.future) attempt.joints wordFinal
      (rank - cut.phase.low) (by rw [attempt.joints_length]; have size := cut.size; omega)
      rank (by rw [startRank]; omega) (by rw [startEnd]; exact bounds.2)
  have activeAt {state : CommitRecoveryState setup.program}
      {prior : setup.proposalRecoveryProtocol.Trace (some state)}
      (kept : TracePrefix prior cut.completed.trace) : owner ∉ state.excluded := by
    have monotone := setup.commitRecovery_public_excluded_of_reaches
      (setup.proposalRecoveryEraseTrace_prefix kept).reachesWithin
    change state.excluded ⊆ (setup.commitRecoveryPublic cut.completed.state).1 at monotone
    rw [completed] at monotone
    change state.excluded ⊆ last.excluded at monotone
    exact fun member => active (excluded ▸ monotone member)
  obtain ⟨atCut, afterCut, cutPrior, cutJoint, cutLegal, cutMoved,
      cutKept, cutDepth, _cutRow, cutSaved, cutGeneration, _cutPosition⟩ :=
    rowAt event.val eventBounds
  have cutBefore : TracePrefix cutPrior cut.completed.trace := by
    have rowPrefix : TracePrefix cutPrior (cutPrior.extend cutJoint cutLegal cutMoved) :=
      TracePrefix.extend (E := setup.proposalRecoveryProtocol) (prefixTrace := cutPrior)
        (prior := cutPrior) (source := some atCut) (target := some afterCut)
        .refl cutJoint cutLegal cutMoved
    exact rowPrefix.trans cutKept
  have cutEq := cutBefore.eq_of_same_length cut.future (cutDepth.trans cut.clock.symm)
  have sameCut : atCut = cut.current := Option.some.inj (congrArg History.state cutEq)
  subst atCut
  have currentExcluded : cut.current.excluded = cut.cursor.current.excluded := by
    have lower := setup.commitRecovery_public_excluded_of_reaches
      (setup.proposalRecoveryEraseTrace_prefix cut.past).reachesWithin
    have upper := setup.commitRecovery_public_excluded_of_reaches
      (setup.proposalRecoveryEraseTrace_prefix cut.future).reachesWithin
    change cut.cursor.current.excluded ⊆ cut.current.excluded at lower
    change cut.current.excluded ⊆ (setup.commitRecoveryPublic cut.completed.state).1 at upper
    rw [completed] at upper
    change cut.current.excluded ⊆ last.excluded at upper
    exact Finset.Subset.antisymm (by simpa only [excluded] using upper) lower
  have cutOrdinary := (setup.commitRecovery_clean_rank_of_reaches who
    (setup.proposalRecoveryEraseTrace_prefix cut.past).reachesWithin
    cut.cursor.current cut.current rfl rfl startOrdinary.symm currentExcluded cut.survives).1
  have entryState := congrArg History.state cut.cursorHistory
  have startGeneration : cut.cursor.current.generation = message.payload.attempt.generation := by
    have eq := congrArg (fun state => state.map (·.generation)) entryState
    have atEntry : cut.cursor.current.generation = cut.entry.execution.application.generation := by
      simpa only [Option.map_some, Option.some.injEq, CommitRecoveryState.atPoint] using eq
    exact atEntry.trans (congrArg CommitAttemptId.generation (cut.sameAttempt.trans current.symm))
  have startSaved : instructionCount setup.program -
      ProtocolState.remaining setup.program cut.cursor.current.saved =
        message.payload.attempt.phase := by
    have eq := congrArg (fun state => state.map fun current => instructionCount setup.program -
      ProtocolState.remaining setup.program current.saved) entryState
    have atEntry : instructionCount setup.program -
        ProtocolState.remaining setup.program cut.cursor.current.saved =
          cut.entry.execution.application.attempt.phase := by
      simpa only [Option.map_some, Option.some.injEq, CommitRecoveryState.atPoint,
        cut.witness.checkpoint.saved_position] using eq
    exact atEntry.trans (congrArg CommitAttemptId.phase (cut.sameAttempt.trans current.symm))
  have gPrefix : TracePrefix g.trace G.trace := by
    have support := supported
    unfold sourceForcedBlock at support
    obtain ⟨middle, first, tail⟩ := (PMF.mem_support_bind_iff ..).mp support
    exact ((setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ 1
      g middle first).tracePrefix).trans
        ((setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ _
          middle G tail).tracePrefix)
  obtain ⟨value, read⟩ : ∃ value : L.Val payload,
      sourceBindingAt setup message.payload.attempt named owner payload binding G.trace =
        some value := by
    by_cases earlier : named.val < event.val
    · obtain ⟨before, after, prior, joint, legal, moved, kept, depth, row,
          saved, generation, position⟩ := rowAt named.val namedBounds
      have rowBefore : TracePrefix prior cut.completed.trace := by
        have rowPrefix : TracePrefix prior (prior.extend joint legal moved) :=
          TracePrefix.extend (E := setup.proposalRecoveryProtocol) (prefixTrace := prior)
            (prior := prior) (source := some before) (target := some after)
            .refl joint legal moved
        exact rowPrefix.trans kept
      obtain ⟨old, actual⟩ := source_binding_success_of_proper setup before joint legal
        owner payload named binding position.symm (activeAt rowBefore) (by
          intro move chosen
          rw [row] at chosen
          exact proper _ (List.getElem_mem _) owner move chosen)
      have past : TracePrefix (prior.extend joint legal moved) cut.trace := by
        obtain ⟨state, targetPrefix, retained, length⟩ := setup.proposalRecovery_prefix_at_depth
          cut.trace (prior.extend joint legal moved).length (by
            simp only [Trace.length]; rw [depth, cut.clock]; omega)
        have same := kept.eq_of_same_length (retained.trans cut.future) length.symm
        cases same
        exact retained
      obtain ⟨value, atG, _focal⟩ := sourceBindingAt_same_information setup who owner
        message.payload.attempt named payload binding before after prior joint legal moved
        (generation.trans startGeneration) (by rw [saved]; exact startSaved) position
        (activeAt rowBefore) (activeAt kept) old actual ⟨some cut.current, cut.trace⟩ g
        past sameInfo.symm good
      obtain ⟨beforeG, priorG, jointG, legalG, afterG, movedG, keptG,
          generationG, savedG, positionG, actualG⟩ :=
        sourceBindingAt_origin setup message.payload.attempt named owner payload binding
          g.trace value atG
      exact ⟨value, sourceBindingAt_of_origin setup message.payload.attempt named owner
        payload binding beforeG priorG jointG legalG afterG movedG generationG savedG positionG
        (.success value, false) actualG G.trace (keptG.trans gPrefix)⟩
    · have metadata := source_information_metadata setup who ⟨some cut.current, cut.trace⟩
        g sameInfo.symm
      rcases g with ⟨state, targetTrace⟩
      cases state with
      | none => exact metadata.elim
      | some target =>
          have controls := ProtocolState.MetadataEq.controls setup.program cut.current.point
            target.point metadata.1
          have savedControls := ProtocolState.MetadataEq.controls setup.program cut.current.saved
            target.saved metadata.2.1
          exact sourceForcedBlock_binding_value setup values target targetTrace
            (controls.2.1 ▸ cut.atCommit) who
            ((source_binding_at_rank setup.program target.point event who cut.payload
              cut.binding (by rw [← controls.1]; exact cut.rank.symm)).2.1)
            (metadata.2.2.1.symm.trans (cutOrdinary.symm.trans metadata.2.2.2.1))
            choice properChoice G supported message.payload.attempt
            (metadata.2.2.2.2.symm.trans (cutGeneration.trans startGeneration))
            (by rw [← savedControls.1, cutSaved]; exact startSaved)
            owner (by rw [← metadata.2.2.1, currentExcluded]; exact active)
            named payload binding (by rw [← controls.1, cut.rank]; omega)
            (by rw [← savedControls.2.2.1, cutSaved, startEnd]; exact namedBounds.2)
  have inputRecall := (nativeApplication).history_inputRecall initial implementation.horizon
    implementation.scheduler raw
  have input : message ∈ reference.execution.network.inputs := by
    have authored : message ∈ (nativeApplication).outputs (reference.execution.recall owner) :=
      List.mem_filterMap.mpr ⟨record, recorded, emitted⟩
    rw [← inputRecall owner] at authored
    exact (List.mem_filter.mp authored).1
  have clean := (PhaseCount.onePacketMenu_countClean implementation.runtime implementation.leaks
    implementation.bounds implementation.scheduler).history initial implementation.horizon
      (fun state _ => PhaseCount.countClean_initial implementation.runtime implementation.leaks
        state) trace
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input)).2.1
  unfold CountCallCorrect at correct
  dsimp only [PhaseCount.nativeMessage] at correct
  rw [call] at correct
  obtain ⟨_bindingOwned, _uncertified, handleOwner, _prepared, _unused⟩ := correct
  have authored : record ∈ reference.execution.recall handle.1 := by
    change handle.1 = message.sender at handleOwner
    rw [handleOwner, sender]
    exact recorded
  have nativeTrace : (nativeProtocol).Trace (some reference) := by
    rw [show nativeInitial = initial by
      simp only [initial, ReservedConcurrentImplementation.initial, PMF.map_comp,
        Function.comp_def]]
    exact trace
  exact ⟨value, sourceHandleMeaning_of_emission setup implementation G reference nativeTrace handle
    record authored message emitted named call owner payload binding (some value) read⟩

open Classical in
/-- Follow the supplied literal binding word whenever its current action is
available. Other instructions use the original causal ordinary profile. -/
def sourceBlockWordStrategy (word : SourceProgram.History Player L) :
    ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner :=
  fun owner information =>
    if offered : ∃ choice : setup.proposalRecoveryModel.Choice owner information,
        ∃ action ∈ word owner,
          choice.val = some (ProposalRecoveryMove.ordinary ⟨action, false⟩) then
      PMF.pure (Classical.choose offered)
    else sourceUnflaggedStrategy setup values owner information

open Classical in
/-- Static cut and causal completion of the actual current source block.
The historical focal word is read from this native history. Foreign words
remain fixed; each later focal draw uses its updated source information. -/
def sourceForcedBlockJoint (who : Player) (history : (nativeProtocol).History)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (entry : setup.proposalRecoveryProtocol.History)
    (foreignWord : SourceProgram.History Player L) (value : L.Val payload) :
    PMF (setup.proposalRecoveryProtocol.History × setup.proposalRecoveryProtocol.History) :=
  match history.state, entry.state with
  | some control, some current =>
    if binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload then
      let chosen := decodeEventAction setup.program event
        (cast (congrArg EventField.Action binding.symm) (PublicationResult.success value))
      let prior := phaseCommitRecallWord setup.program .concurrent implementation.runtime
        implementation.leaks control.execution.application.attempt.phase event.val
        control.execution.application.generation (control.execution.recall who)
      let word : SourceProgram.History Player L := fun owner =>
        if owner = who then prior ++ chosen.toList else
          (foreignWord owner).drop
            ((ProtocolState.history setup.program current.point owner).length)
      let profile := sourceBlockWordStrategy setup values word
      let before := event.val -
        (instructionCount setup.program - ProtocolState.remaining setup.program current.point)
      (setup.proposalRecoveryModel.runBehavioralFrom profile before entry).bind fun cut =>
        (setup.proposalRecoveryModel.runBehavioralFrom profile
          (sourceCommitFuel setup cut) cut).map fun completed => (cut, completed)
    else PMF.pure (entry, entry)
  | _, _ => PMF.pure (entry, entry)

/-- The actual emitted binding packets and their addressed typed owner word. -/
def issuedLedger
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low : Nat)
    (control : (nativeApplication).Control) (high : Nat) (owner : Player)
    (word : DecisionView owner Δ) : Prop :=
  ∀ (named : (serviceGraph setup .concurrent).EventId) (valueType : L.Ty)
    (shape : (serviceGraph setup .concurrent).outputLayout named = .binding owner valueType)
    (candidate : Handle (serviceGraph setup .concurrent))
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent))),
    message ∈ (nativeApplication).outputs (control.execution.recall owner) →
    message.payload.attempt = control.execution.application.attempt →
    message.payload.packet.call = .commitment named candidate →
    low ≤ named.val ∧ named.val < high →
    ∃ (serial : Nat) (opening : Option (Raw L))
      (evidence : EvidenceRequest (serviceGraph setup .concurrent))
      (entry : (nativeApplication).PlayerEntry),
      candidate = (owner, .prepared serial) ∧
      entry ∈ control.execution.recall owner ∧
      entry.emitted = some message ∧
      entry.action = ⟨some ⟨⟨.commitment named (owner, .prepared serial), opening⟩, evidence⟩⟩ ∧
      entry.beforeView.application.1.candidates (.prepared serial) = .fresh ∧
      (opening.bind fun raw => raw.as? valueType).elim .failure PublicationResult.success =
        (phaseRecoveryBindingData setup .concurrent named owner valueType shape
          (CommitRecoveryMove.lift (block.wordAction owner (named.val - low) word))).1

/-- A fixed actual emitted packet determines its remembered raw response.
This uses authentic envelope uniqueness, not equality of alias menus. -/
theorem recorded_emission_unique
    {control : (nativeApplication).Control}
    (trace : (nativeProtocol).Trace (some control)) (owner : Player)
    (left right : (nativeApplication).PlayerEntry)
    (leftMember : left ∈ control.execution.recall owner)
    (rightMember : right ∈ control.execution.recall owner)
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (leftEmitted : left.emitted = some message) (rightEmitted : right.emitted = some message) :
    left = right := by
  have order := (nativeApplication).emissionOrder_history implementation.scheduler nativeInitial
    implementation.horizon ((nativeMenu).toRawTrace nativeInitial implementation.horizon
      implementation.scheduler trace)
  have outputUnique : ((nativeApplication).outputs (control.execution.recall owner)).Nodup := by
    apply List.Nodup.of_map Message.id
    rw [order owner]
    exact List.nodup_range.map (fun _ _ equal => (Prod.mk.inj equal).2)
  have unique : ∀ (past : List (nativeApplication).PlayerEntry),
      ((nativeApplication).outputs past).Nodup →
      ∀ first ∈ past, ∀ second ∈ past,
        first.emitted = some message → second.emitted = some message → first = second := by
    intro past
    induction past with
    | nil => simp only [List.not_mem_nil, false_implies, implies_true]
    | cons head rest ih =>
        intro distinct first firstMember second secondMember firstSent secondSent
        rcases List.mem_cons.mp firstMember with firstHead | firstTail
        · subst first
          rcases List.mem_cons.mp secondMember with secondHead | secondTail
          · exact secondHead.symm
          · have missing : message ∉ (nativeApplication).outputs rest := by
              exact (show message ∉ (nativeApplication).outputs rest ∧
                ((nativeApplication).outputs rest).Nodup by
                  simpa only [ReactiveApplication.outputs, List.filterMap_cons, firstSent,
                    List.nodup_cons] using distinct).1
            exact False.elim (missing (List.mem_filterMap.mpr
              ⟨second, secondTail, secondSent⟩))
        · rcases List.mem_cons.mp secondMember with secondHead | secondTail
          · subst second
            have missing : message ∉ (nativeApplication).outputs rest := by
              exact (show message ∉ (nativeApplication).outputs rest ∧
                ((nativeApplication).outputs rest).Nodup by
                  simpa only [ReactiveApplication.outputs, List.filterMap_cons, secondSent,
                    List.nodup_cons] using distinct).1
            exact False.elim (missing (List.mem_filterMap.mpr
              ⟨first, firstTail, firstSent⟩))
          · apply ih _ first firstTail second secondTail firstSent secondSent
            cases sent : head.emitted with
            | none => simpa only [ReactiveApplication.outputs, List.filterMap_cons, sent] using
                distinct
            | some packet =>
                exact (show packet ∉ (nativeApplication).outputs rest ∧
                  ((nativeApplication).outputs rest).Nodup by
                    simpa only [ReactiveApplication.outputs, List.filterMap_cons, sent,
                      List.nodup_cons] using distinct).2
  exact unique _ outputUnique left leftMember right rightMember leftEmitted rightEmitted

/-- On an actual raw history the issued cylinder is precisely the equality
of the addressed result readouts with any one supported retained word. -/
theorem issuedLedger_iff_results
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low : Nat)
    {control : (nativeApplication).Control}
    (trace : (nativeProtocol).Trace (some control)) (high : Nat) (owner : Player)
    (reference word : DecisionView owner Δ)
    (retained : issuedLedger setup implementation block low control high owner reference) :
    issuedLedger setup implementation block low control high owner word ↔
      ∀ (named : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
        (shape : (serviceGraph setup .concurrent).outputLayout named = .binding owner payload)
        (candidate : Handle (serviceGraph setup .concurrent))
        (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent))),
        message ∈ (nativeApplication).outputs (control.execution.recall owner) →
        message.payload.attempt = control.execution.application.attempt →
        message.payload.packet.call = .commitment named candidate →
        low ≤ named.val ∧ named.val < high →
        (phaseRecoveryBindingData setup .concurrent named owner payload shape
          (CommitRecoveryMove.lift (block.wordAction owner (named.val - low) word))).1 =
        (phaseRecoveryBindingData setup .concurrent named owner payload shape
          (CommitRecoveryMove.lift (block.wordAction owner (named.val - low) reference))).1 := by
  constructor
  · intro belongs named payload shape candidate message emitted attempt packet inside
    obtain ⟨serial, opening, evidence, entry, slot, member, sent, action, fresh, result⟩ :=
      belongs named payload shape candidate message emitted attempt packet inside
    obtain ⟨oldSerial, oldOpening, oldEvidence, oldEntry, oldSlot, oldMember, oldSent,
      oldAction, oldFresh, oldResult⟩ :=
      retained named payload shape candidate message emitted attempt packet inside
    have same := recorded_emission_unique setup implementation trace owner entry oldEntry
      member oldMember message sent oldSent
    have raw := congrArg (fun response : (nativeApplication).Action =>
      response.transmission.bind fun material => material.call.opening)
        (action.symm.trans ((congrArg ReactiveApplication.PlayerEntry.action same).trans oldAction))
    change opening = oldOpening at raw
    rw [← result, ← oldResult, raw]
  · intro results named payload shape candidate message emitted attempt packet inside
    obtain ⟨serial, opening, evidence, entry, slot, member, sent, action, fresh, result⟩ :=
      retained named payload shape candidate message emitted attempt packet inside
    exact ⟨serial, opening, evidence, entry, slot, member, sent, action, fresh,
      result.trans
        (results named payload shape candidate message emitted attempt packet inside).symm⟩

/-- An actual signed binding packet retains its unique raw preparation,
fresh slot and immutable typed meaning in the original recalled response. -/
theorem issued_binding_record
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (owner : Player) (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (candidate : Handle (serviceGraph setup .concurrent))
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (member : message ∈ control.execution.network.inputs)
    (call : message.payload.packet.call = .commitment event candidate) :
    ∃ (serial : Nat) (opening : Option (Raw L))
      (evidence : EvidenceRequest (serviceGraph setup .concurrent))
      (record : (nativeApplication).PlayerEntry),
      candidate = (owner, .prepared serial) ∧ message.sender = owner ∧
      record ∈ control.execution.recall owner ∧ record.emitted = some message ∧
      record.action = ⟨some
        ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩ ∧
      record.beforeView.application.1.candidates (.prepared serial) = .fresh ∧
      record.beforeView.application.2.attempt = message.payload.attempt ∧
      control.execution.application.current.native.bindingResult candidate payload =
        (opening.bind fun raw => raw.as? payload).elim .failure PublicationResult.success := by
  let inputs := setup.initialLaw.map encodeInputs
  have initialEq : nativeInitial = inputs.map (PhaseRuntimeState.initial implementation.plan) := by
    simp only [ReservedConcurrentImplementation.initial, inputs, PMF.map_comp, Function.comp_def]
  have raw := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  have physical := PhaseCount.physicalBindings_history implementation.runtime implementation.leaks
    implementation.bounds implementation.plan inputs implementation.horizon
      implementation.scheduler (initialEq ▸ trace)
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp
    (physical.clean.2 message member)).2.1
  change CountCallCorrect _ (PhaseCount.nativeMessage message) at correct
  simp only [CountCallCorrect, PhaseCount.nativeMessage, call] at correct
  obtain ⟨owned, _noEvidence, candidateOwner, ⟨serial, slot⟩, _unused⟩ := correct
  have sender : message.sender = owner := by
    exact (show owner = message.sender from by
      simpa only [bindingOwnedBy, binding, decide_eq_true_eq, Message.sender] using owned).symm
  have candidateEq : candidate = (owner, .prepared serial) :=
    Prod.ext (candidateOwner.trans sender) slot
  subst candidate
  obtain ⟨record, recorded, material, transmitted, emitted, state, known, emission⟩ :=
    physical.origins.inputs message member
  rw [sender] at recorded
  have materialCall : material.call.packet = .commitment event (owner, .prepared serial) :=
    (phase_emit_call state message.sender known material).symm.trans
      ((congrArg (fun packet : CommitAttemptPacket (serviceGraph setup .concurrent) =>
        packet.packet.call) emission).trans call)
  rcases material with ⟨⟨packet, opening⟩, evidence⟩
  dsimp only at materialCall
  subst packet
  have declared : record.action =
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩ :=
    congrArg (fun transmission => (⟨transmission⟩ : (nativeApplication).Action)) transmitted
  obtain ⟨before, prior, _retained, _acting, viewed, available, _recalled⟩ :=
    (nativeMenu).recorded_response_prefix nativeInitial implementation.horizon
      implementation.scheduler control trace owner record recorded
  rw [declared] at available
  have fresh : record.beforeView.application.1.candidates (.prepared serial) = .fresh :=
    viewed ▸ PhaseCount.onePacket_binding_fresh implementation.runtime implementation.leaks
      implementation.bounds implementation.plan inputs implementation.horizon
        implementation.scheduler (initialEq ▸ prior) owner event serial opening evidence available
  have sameNamespace := phase_recalled_emission_attempt implementation.runtime implementation.leaks
    nativeInitial implementation.horizon implementation.scheduler raw owner record recorded message
      emitted
  have meaning := phase_recorded_material_binding_result implementation.runtime
    implementation.leaks (nativeMenu) nativeInitial implementation.horizon implementation.scheduler
      control trace owner event payload serial opening evidence record recorded declared fresh
  exact ⟨serial, opening, evidence, record, rfl, sender, recorded, emitted, declared, fresh,
    sameNamespace.symm, meaning⟩

/-- A current-attempt emitted binding was authored by an owner active at
that attempt's saved entry. Later exclusion cannot create an inherited SEND. -/
theorem issued_binding_owner_active
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (owner : Player) (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (candidate : Handle (serviceGraph setup .concurrent))
    (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (member : message ∈ control.execution.network.inputs)
    (current : message.payload.attempt = control.execution.application.attempt)
    (call : message.payload.packet.call = .commitment event candidate) :
    owner ∉ control.execution.application.entry.excluded := by
  let inputs := setup.initialLaw.map encodeInputs
  let initial := inputs.map (PhaseRuntimeState.initial implementation.plan)
  have initialEq : nativeInitial = initial := by
    simp only [ReservedConcurrentImplementation.initial, initial, inputs, PMF.map_comp,
      Function.comp_def]
  have counted : ((nativeMenu).protocol initial implementation.horizon
      implementation.scheduler).Trace (some control) := initialEq ▸ trace
  obtain ⟨serial, opening, evidence, record, slot, _sender, recorded, _emitted,
      declared, _fresh, sameNamespace, _meaning⟩ :=
    issued_binding_record setup implementation control trace owner event payload binding candidate
      message member call
  let material : WitnessedSubmission (serviceGraph setup .concurrent) :=
    ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩
  obtain ⟨before, prior, retained, _acting, viewed, request⟩ := phase_recorded_binding_request
    implementation.runtime implementation.leaks implementation.bounds implementation.plan inputs
      implementation.horizon (serviceGraph_revealRelaxedOrdered setup .concurrent)
        implementation.scheduler counted owner record recorded material
          (by rw [declared]) event (owner, .prepared serial) rfl
  have sameAttempt : before.execution.application.attempt =
      control.execution.application.attempt := by
    rw [viewed] at sameNamespace
    exact sameNamespace.trans current
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state supported
    obtain ⟨input, _member, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered implementation.plan input
  have ordered := (phaseApplication_seedOrder implementation.runtime implementation.leaks).history
    initial implementation.horizon implementation.scheduler initialized
      ((nativeMenu).toRawTrace initial implementation.horizon implementation.scheduler prior)
  have saved := (phase_attempt_progress_of_prefix implementation.runtime implementation.leaks
    (nativeMenu) initial initialized implementation.horizon implementation.scheduler before control
      prior counted retained ordered).2.2 sameAttempt
  have coverage := phaseFailureCoverage_history implementation.runtime implementation.leaks
    implementation.plan inputs implementation.horizon implementation.scheduler
      ((nativeMenu).toRawTrace initial implementation.horizon implementation.scheduler prior)
  intro excluded
  exact request.2.2.2.2 (coverage.inherited (by rwa [saved]))

omit [Fintype Player] in
private theorem attempt_entry_view_surviving
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (finished : SourceProgram.Config Player L Δ) (after : Finset Player)
    (attempt : block.Attempt entry excluded finished after)
    (owner : Player) (active : owner ∉ after) :
    block.entryView owner (finished.view owner) = entry.view owner := by
  have projection : ∀ {A B : SourceCtx Player L} {U V : Finset VarId}
      (initialBlock : SourceProgram.CommitPrefix A U B V)
      (tail : SourceProgram Player L B V) (final : SourceProgram.Config Player L B),
      ProtocolView.entryView owner (initialBlock.prepend tail)
        (ProtocolState.observe owner (initialBlock.prepend tail)
          (initialBlock.liftPoint tail (ProtocolState.entry tail final))) =
        initialBlock.entryView owner (final.view owner) := by
    intro A B U V initialBlock
    induction initialBlock with
    | nil =>
        intro tail final
        exact ProtocolView.entryView_observe_entry owner tail final
    | commit name actor fresh guard rest ih =>
        intro tail final
        change (ProtocolView.entryView owner (rest.prepend tail)
          (ProtocolState.observe owner (rest.prepend tail)
            (rest.liftPoint tail (ProtocolState.entry tail final)))).back
              (decide (actor = owner)) = _
        rw [ih]
        rfl
  exact (projection block suffix finished).symm.trans (attempt.entryView suffix owner active)

omit [Fintype Player] in
/-- A clean typed attempt reads the actual active owners' actions from its
complete views. Inherited excluded rows remain literal absent joints. -/
theorem commitAttempt_wordAction
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) :
    ∀ (_suffix : SourceProgram Player L Δ P)
      (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player)
      (finished : SourceProgram.Config Player L Δ) (after : Finset Player)
      (attempt : block.Attempt entry excluded finished after), after = excluded →
      attempt.joints = (List.range block.length).map (fun index owner =>
        if owner ∈ excluded then none else
          CommitRecoveryMove.lift (block.wordAction owner index (finished.view owner))) := by
  induction block with
  | nil =>
      intro suffix entry excluded finished after attempt same
      cases attempt
      rfl
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      intro suffix entry excluded finished after attempt same
      cases same
      cases attempt with
      | active active result missed valid later =>
          cases missed with
          | true =>
              have included : owner ∈ excludeCommit excluded owner true := by
                simp only [excludeCommit, ↓reduceIte, Finset.mem_insert, true_or]
              exact (active (later.excluded_subset included)).elim
          | false =>
              have read := attempt_entry_view_surviving rest suffix
                (commitSuccessor name guard entry result) excluded finished excluded later
                  owner active
              have cell : (((rest.entryView owner (finished.view owner)).1.cells name
                  (.commitment owner payload) .here).getD .failure) = result := by
                rw [read]
                simp only [SourceProgram.Config.view, commitSuccessor, sourceObserve_commitment,
                  ite_true, Option.getD_some]
                rfl
              have tail := ih suffix _ excluded finished excluded later rfl
              simp only [SourceProgram.CommitPrefix.length, List.range_succ_eq_map,
                List.map_cons, List.map_map, Function.comp_def,
                SourceProgram.CommitPrefix.Attempt.joints, tail]
              congr 1
              funext observer
              by_cases own : observer = owner
              · subst observer
                simp only [active, ↓reduceIte, SourceProgram.CommitPrefix.wordAction,
                  cell, CommitRecoveryMove.lift, Option.map_some]
              · by_cases inactive : observer ∈ excluded
                · simp only [own, inactive, ↓reduceIte]
                · simp only [own, Ne.symm own, inactive, ↓reduceIte,
                    SourceProgram.CommitPrefix.wordAction, CommitRecoveryMove.lift,
                    Option.map_none]
      | excluded inactive later =>
          have tail := ih suffix _ excluded finished excluded later rfl
          simp only [SourceProgram.CommitPrefix.length, List.range_succ_eq_map, List.map_cons,
            List.map_map, Function.comp_def, SourceProgram.CommitPrefix.Attempt.joints, tail]
          congr 1
          funext observer
          by_cases inherited : observer ∈ excluded
          · simp only [inherited, ↓reduceIte]
          · have foreign : owner ≠ observer := fun own => inherited (own ▸ inactive)
            simp only [inherited, ↓reduceIte, SourceProgram.CommitPrefix.wordAction,
              ite_eq_right foreign, CommitRecoveryMove.lift, Option.map_none]

omit [Fintype Player] in
/-- The completed compiler dictionary contains every binding field of the
actual typed attempt, including inherited automatic failures. -/
theorem commitAttempt_binding_present
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (block.prepend suffix)) (refs : ContextRefs (graphLayout setup.program) Γ)
      (store : Store (graphLayout setup.program))
      (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player)
      (finished : SourceProgram.Config Player L Δ) (after : Finset Player)
      (_attempt : block.Attempt entry excluded finished after),
      (commitBlockRefs setup.program block suffix embedding refs).Agrees finished.state store →
      ∀ (index : Fin (eventCount (block.prepend suffix))), index.val < block.length →
      ∀ (owner : Player) (payload : L.Ty)
        (binding : (serviceGraph setup .concurrent).outputLayout (embedding.event index) =
          .binding owner payload),
        ((⟨.inr (embedding.event index), binding⟩ :
          FieldRef (graphLayout setup.program) (.binding owner payload)).get? store).isSome =
            true := by
  induction block with
  | nil =>
      intro suffix embedding refs store entry excluded finished after attempt agreement index inside
      exact (Nat.not_lt_zero _ inside).elim
  | @commit Γ O Δ P name actor domain fresh guard rest ih =>
      intro suffix embedding refs store entry excluded finished after attempt agreement index
      let zero : Fin (eventCount ((SourceProgram.CommitPrefix.commit name actor fresh guard
          rest).prepend suffix)) := ⟨0, by
        simp only [SourceProgram.CommitPrefix.prepend, eventCount]
        omega⟩
      let field : FieldRef (graphLayout setup.program) (.binding actor domain) :=
        ⟨.inr (embedding.event zero), by
          simpa only [zero, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
            Fin.cases_zero, graphLayout, EventGraph.fieldLayout, Sum.elim_inr]
              using embedding.layout_eq zero⟩
      let tailEmbedding := embedding.tail (rest.prepend suffix)
        (by simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      let tailRefs := refs.cons (name := name) (cell := .commitment actor domain) field
      cases attempt with
      | active active result missed valid later =>
          have middle : tailRefs.Agrees (commitSuccessor name guard entry result).state store :=
            commitBlockRefs_agrees_entry setup.program rest suffix tailEmbedding tailRefs store
              _ _ finished after later agreement
          refine Fin.cases ?_ ?_ index
          · intro _inside owner payload binding
            have shape : EventField.binding actor domain = .binding owner payload := by
              simpa only [zero, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
                Fin.cases_zero] using (embedding.layout_eq zero).symm.trans binding
            cases shape
            change (field.get? store).isSome = true
            have stored := middle HasVar.here
            change field.get? store = some result at stored
            rw [stored]
            rfl
          · intro tail inside owner payload binding
            exact ih suffix tailEmbedding tailRefs store _ _ finished after later agreement tail
              (by change tail.val + 1 < rest.length + 1 at inside; omega) owner payload binding
      | excluded inactive later =>
          have middle : tailRefs.Agrees (automaticCommit name actor domain entry).state store :=
            commitBlockRefs_agrees_entry setup.program rest suffix tailEmbedding tailRefs store
              _ _ finished after later agreement
          refine Fin.cases ?_ ?_ index
          · intro _inside owner payload binding
            have shape : EventField.binding actor domain = .binding owner payload := by
              simpa only [zero, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
                Fin.cases_zero] using (embedding.layout_eq zero).symm.trans binding
            cases shape
            change (field.get? store).isSome = true
            have stored := middle HasVar.here
            change field.get? store = some .failure at stored
            rw [stored]
            rfl
          · intro tail inside owner payload binding
            exact ih suffix tailEmbedding tailRefs store _ _ finished after later agreement tail
              (by change tail.val + 1 < rest.length + 1 at inside; omega) owner payload binding

omit [Fintype Player] in
/-- At an active row, the coupled complete source view reads the exact typed
field in the graph semantic word. No source and graph history is identified. -/
theorem commitAttempt_binding_result
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (refs : ContextRefs (graphLayout setup.program) Γ)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (store : Store (graphLayout setup.program))
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (finished : SourceProgram.Config Player L Δ) (after : Finset Player)
    (attempt : block.Attempt entry excluded finished after) (same : after = excluded)
    (agreement : (commitBlockRefs setup.program block suffix embedding refs).Agrees
      finished.state store)
    (owner : Player) (active : owner ∉ excluded)
    (index : Fin (eventCount (block.prepend suffix))) (inside : index.val < block.length)
    (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout (embedding.event index) =
      .binding owner payload) :
    (phaseRecoveryBindingData setup .concurrent (embedding.event index) owner payload binding
      (CommitRecoveryMove.lift (block.wordAction owner index.val (finished.view owner)))).1 =
      ((⟨.inr (embedding.event index), binding⟩ :
        FieldRef (graphLayout setup.program) (.binding owner payload)).get? store).getD .failure
          := by
  let filled := fillCommitPrefix setup.program block suffix embedding store entry
  have graphWord := phaseProposalBindingWord_of_ordinary_attempt setup.program block suffix
    embedding refs store entry entry excluded finished after attempt same agreement
  have sourceWord := commitAttempt_wordAction block suffix entry excluded finished after attempt
    same
  have row := congrArg (fun items => (items[index.val]?).map (fun joint => joint owner))
    (graphWord.trans sourceWord)
  have moves : CommitRecoveryMove.lift (block.wordAction owner index.val (filled.view owner)) =
      CommitRecoveryMove.lift (block.wordAction owner index.val (finished.view owner)) := by
    simp only [phaseProposalBindingWord, List.getElem?_map, List.getElem?_range, inside,
      ↓reduceIte, Option.map_some, active] at row
    exact Option.some.inj row
  have owned : eventOwner? (block.prepend suffix) index = some owner := by
    rw [eventOwner?_eq_actor]
    exact EventGraph.actor?_of_outputLayout_binding (toEventGraph (block.prepend suffix))
      ((embedding.layout_eq index).symm.trans binding)
  obtain ⟨action, _native, chosen, _decoded⟩ := compiledCommitPrefix_wordAction_decodable
    block suffix owner index inside owned (filled.view owner)
  have read := fillCommitPrefix_wordAction setup.program block suffix embedding actions store
    entry owner index inside payload binding
  have decoded : decodeEventAction setup.program (embedding.event index)
      (cast (congrArg EventField.Action binding.symm)
        (((⟨.inr (embedding.event index), binding⟩ :
          FieldRef (graphLayout setup.program) (.binding owner payload)).get? store).getD
            .failure)) = some action := read.symm.trans chosen
  have encoded := encodeEventAction?_decodeEventAction_eq_some setup.program
    (embedding.event index) _ action decoded
  have fieldRead : (phaseRecoveryBindingData setup .concurrent (embedding.event index)
      owner payload binding
      (CommitRecoveryMove.lift (block.wordAction owner index.val (filled.view owner)))).1 =
      ((⟨.inr (embedding.event index), binding⟩ :
        FieldRef (graphLayout setup.program) (.binding owner payload)).get? store).getD
          .failure := by
    rw [chosen]
    simp only [CommitRecoveryMove.lift, Option.map_some, phaseRecoveryBindingData,
      Option.elim_some, Bool.false_eq_true, ↓reduceIte, Option.bind_some, encoded,
      Option.map_some, Option.getD_some, cast_cast, cast_eq]
  exact (congrArg (fun move => (phaseRecoveryBindingData setup .concurrent
    (embedding.event index) owner payload binding move).1) moves.symm).trans fieldRead

omit [Fintype Player] in
/-- A successful selected source action and its exact completed graph field
are the same event in the original ordinary block. -/
theorem commitAttempt_selected_binding
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (refs : ContextRefs (graphLayout setup.program) Γ)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (store : Store (graphLayout setup.program))
    (entry : SourceProgram.Config Player L Γ) (excluded : Finset Player)
    (finished : SourceProgram.Config Player L Δ) (after : Finset Player)
    (attempt : block.Attempt entry excluded finished after) (same : after = excluded)
    (agreement : (commitBlockRefs setup.program block suffix embedding refs).Agrees
      finished.state store)
    (owner : Player) (active : owner ∉ excluded)
    (index : Fin (eventCount (block.prepend suffix))) (inside : index.val < block.length)
    (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout (embedding.event index) =
      .binding owner payload) (value : L.Val payload) :
    block.wordAction owner index.val (finished.view owner) =
        decodeEventAction setup.program (embedding.event index)
          (cast (congrArg EventField.Action binding.symm) (PublicationResult.success value)) ↔
      (⟨.inr (embedding.event index), binding⟩ :
        FieldRef (graphLayout setup.program) (.binding owner payload)).get? store =
          some (.success value) := by
  let result := (phaseRecoveryBindingData setup .concurrent (embedding.event index) owner payload
    binding (CommitRecoveryMove.lift (block.wordAction owner index.val (finished.view owner)))).1
  have read : result = ((⟨.inr (embedding.event index), binding⟩ :
      FieldRef (graphLayout setup.program) (.binding owner payload)).get? store).getD .failure :=
    commitAttempt_binding_result setup block suffix embedding refs actions store entry excluded
      finished after attempt same agreement owner active index inside payload binding
  have present := commitAttempt_binding_present setup block suffix embedding refs store entry
    excluded finished after attempt agreement index inside owner payload binding
  have decode := phaseCommitWordAction_decode setup .concurrent block suffix embedding actions
    owner index inside payload binding (finished.view owner)
  change decodeEventAction setup.program (embedding.event index)
    (cast (congrArg EventField.Action binding.symm) result) =
      block.wordAction owner index.val (finished.view owner) at decode
  constructor
  · intro selected
    have owned : eventOwner? (block.prepend suffix) index = some owner := by
      rw [eventOwner?_eq_actor]
      exact EventGraph.actor?_of_outputLayout_binding (toEventGraph (block.prepend suffix))
        ((embedding.layout_eq index).symm.trans binding)
    obtain ⟨action, _native, chosen, _decoded⟩ := compiledCommitPrefix_wordAction_decodable
      block suffix owner index inside owned (finished.view owner)
    have actual := encodeEventAction?_decodeEventAction_eq_some setup.program
      (embedding.event index) _ action (decode.trans chosen)
    have forced := encodeEventAction?_decodeEventAction_eq_some setup.program
      (embedding.event index) _ action (selected.symm.trans chosen)
    have encoded := congrArg (cast (congrArg EventField.Action binding))
      (Option.some.inj (actual.symm.trans forced))
    have resultEq : result = .success value := by
      simpa only [cast_cast, cast_eq] using encoded
    obtain ⟨storedValue, stored⟩ := Option.isSome_iff_exists.mp present
    rw [stored, Option.getD_some] at read
    exact stored.trans (congrArg some (read.symm.trans resultEq))
  · intro stored
    rw [stored, Option.getD_some] at read
    rw [read] at decode
    exact decode.symm

/-- The issued cylinder fixes exactly the immutable typed meanings of the
actual original outputs; no historical policy support premise is needed. -/
theorem issuedLedger_iff_binding_results
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low : Nat)
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (high : Nat) (owner : Player) (word : DecisionView owner Δ) :
    issuedLedger setup implementation block low control high owner word ↔
      ∀ (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
        (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
        (candidate : Handle (serviceGraph setup .concurrent))
        (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent))),
        message ∈ (nativeApplication).outputs (control.execution.recall owner) →
        message.payload.attempt = control.execution.application.attempt →
        message.payload.packet.call = .commitment event candidate →
        low ≤ event.val ∧ event.val < high →
        (phaseRecoveryBindingData setup .concurrent event owner payload binding
          (CommitRecoveryMove.lift (block.wordAction owner (event.val - low) word))).1 =
          control.execution.application.current.native.bindingResult candidate payload := by
  have raw := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  have recalled := (nativeApplication).history_inputRecall nativeInitial implementation.horizon
    implementation.scheduler raw
  constructor
  · intro ledger event payload binding candidate message emitted attempt packet interval
    obtain ⟨serial, opening, evidence, record, slot, recorded, sent, declared, fresh, result⟩ :=
      ledger event payload binding candidate message emitted attempt packet interval
    subst candidate
    exact result.symm.trans (phase_recorded_material_binding_result implementation.runtime
      implementation.leaks (nativeMenu) nativeInitial implementation.horizon
        implementation.scheduler control trace owner event payload serial opening evidence record
          recorded declared fresh).symm
  · intro results event payload binding candidate message emitted attempt packet interval
    have member : message ∈ control.execution.network.inputs := by
      rw [← recalled owner] at emitted
      exact (List.mem_filter.mp emitted).1
    obtain ⟨serial, opening, evidence, record, slot, _sender, recorded, sent, declared,
        fresh, _namespace, meaning⟩ :=
      issued_binding_record setup implementation control trace owner event payload binding candidate
        message member packet
    refine ⟨serial, opening, evidence, record, slot, recorded, sent, declared, fresh, ?_⟩
    exact meaning.symm.trans
      (results event payload binding candidate message emitted attempt packet interval).symm

/-- The all-owner source ledger and the actual complete emitted-field cylinder
are the same event in one coupled ordinary block. -/
theorem issuedLedger_iff_emitted_bindings
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (refs : ContextRefs (graphLayout setup.program) Γ)
    (low : Nat) (rank : ∀ index, (embedding.event index).val = low + index.val)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (phaseLow : phase.low = low) (phaseHigh : phase.high = low + block.length)
    (store : Store (graphLayout setup.program))
    (entry : SourceProgram.Config Player L Γ)
    (finished : SourceProgram.Config Player L Δ) (after : Finset Player)
    (attempt : block.Attempt entry control.execution.application.entry.excluded finished after)
    (same : after = control.execution.application.entry.excluded)
    (agreement : (commitBlockRefs setup.program block suffix embedding refs).Agrees
      finished.state store) :
    (∀ owner, issuedLedger setup implementation block low control (low + block.length) owner
      (finished.view owner)) ↔
    (∀ message ∈ control.execution.network.inputs,
      message.payload.attempt = control.execution.application.attempt →
      ∀ event ∈ phase.events, ∀ candidate,
        message.payload.packet.call = .commitment event candidate →
        ∀ owner payload (binding : (serviceGraph setup .concurrent).outputLayout event =
            .binding owner payload),
          (⟨.inr event, binding⟩ : FieldRef (graphLayout setup.program)
            (.binding owner payload)).get? store =
              some (control.execution.application.current.native.bindingResult candidate
                payload)) := by
  have raw := (nativeMenu).toRawTrace nativeInitial implementation.horizon
    implementation.scheduler trace
  have inputRecall := (nativeApplication).history_inputRecall nativeInitial implementation.horizon
    implementation.scheduler raw
  have atIndex (event : (serviceGraph setup .concurrent).EventId)
      (interval : low ≤ event.val ∧ event.val < low + block.length) :
      ∃ index : Fin (eventCount (block.prepend suffix)),
        index.val = event.val - low ∧ index.val < block.length ∧ embedding.event index = event := by
    let index : Fin (eventCount (block.prepend suffix)) := ⟨event.val - low, by
      have count := block.eventCount_prepend suffix
      omega⟩
    refine ⟨index, rfl, by dsimp only [index]; omega, ?_⟩
    apply Fin.ext
    rw [rank]
    dsimp only [index]
    omega
  constructor
  · intro ledger message member current event inside candidate call owner payload binding
    obtain ⟨serial, opening, evidence, record, _slot, _sender, recorded, emitted,
        _declared, _fresh, _namespace, _meaning⟩ :=
      issued_binding_record setup implementation control trace owner event payload binding candidate
        message member call
    have output : message ∈ (nativeApplication).outputs (control.execution.recall owner) :=
      List.mem_filterMap.mpr ⟨record, recorded, emitted⟩
    have active := issued_binding_owner_active setup implementation control trace owner event
      payload binding candidate message member current call
    have interval : low ≤ event.val ∧ event.val < low + block.length := by
      simpa only [phaseLow, phaseHigh] using (phase.mem_events event).mp inside
    obtain ⟨index, position, bounded, named⟩ := atIndex event interval
    have sourceResult := (issuedLedger_iff_binding_results setup implementation block low control
      trace (low + block.length) owner (finished.view owner)).mp (ledger owner)
        event payload binding candidate message output current call interval
    have read := commitAttempt_binding_result setup block suffix embedding refs actions store entry
      control.execution.application.entry.excluded finished after attempt same agreement owner
        active index bounded payload (named.symm ▸ binding)
    have present := commitAttempt_binding_present setup block suffix embedding refs store entry
      control.execution.application.entry.excluded finished after attempt agreement index bounded
        owner payload (named.symm ▸ binding)
    cases named
    rw [position] at read
    obtain ⟨result, stored⟩ := Option.isSome_iff_exists.mp present
    rw [stored, Option.getD_some] at read
    exact stored.trans (congrArg some (read.symm.trans sourceResult))
  · intro emissions owner
    apply (issuedLedger_iff_binding_results setup implementation block low control trace
      (low + block.length) owner (finished.view owner)).mpr
    intro event payload binding candidate message output current call interval
    have member : message ∈ control.execution.network.inputs := by
      rw [← inputRecall owner] at output
      exact (List.mem_filter.mp output).1
    have active := issued_binding_owner_active setup implementation control trace owner event
      payload binding candidate message member current call
    have inside : event ∈ phase.events := (phase.mem_events event).mpr (by
      simpa only [phaseLow, phaseHigh] using interval)
    obtain ⟨index, position, bounded, named⟩ := atIndex event interval
    have read := commitAttempt_binding_result setup block suffix embedding refs actions store entry
      control.execution.application.entry.excluded finished after attempt same agreement owner
        active index bounded payload (named.symm ▸ binding)
    have emitted := emissions message member current event inside candidate call owner payload
      binding
    cases named
    rw [position] at read
    rw [emitted, Option.getD_some] at read
    exact read

/-- The genuine compiler codec turns the retained emitted cylinder into
literal source-action agreement at the addressed owned rows. -/
theorem issuedLedger_iff_actions
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (low : Nat)
    (rank : ∀ index, (embedding.event index).val = low + index.val)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    {control : (nativeApplication).Control}
    (trace : (nativeProtocol).Trace (some control)) (owner : Player)
    (reference word : DecisionView owner Δ)
    (retained : issuedLedger setup implementation block low control (low + block.length)
      owner reference) :
    issuedLedger setup implementation block low control (low + block.length) owner word ↔
      ∀ (named : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
        (_shape : (serviceGraph setup .concurrent).outputLayout named = .binding owner payload)
        (candidate : Handle (serviceGraph setup .concurrent))
        (message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent))),
        message ∈ (nativeApplication).outputs (control.execution.recall owner) →
        message.payload.attempt = control.execution.application.attempt →
        message.payload.packet.call = .commitment named candidate →
        low ≤ named.val ∧ named.val < low + block.length →
        block.wordAction owner (named.val - low) word =
          block.wordAction owner (named.val - low) reference := by
  rw [issuedLedger_iff_results setup implementation block low trace (low + block.length)
    owner reference word retained]
  constructor
  · intro results named payload shape candidate message emitted attempt packet interval
    have inside : named.val - low < block.length := by omega
    let index : Fin (eventCount (block.prepend suffix)) :=
      ⟨named.val - low, by have count := block.eventCount_prepend suffix; omega⟩
    have namedEq : embedding.event index = named := by
      apply Fin.ext
      rw [rank]
      dsimp only [index]
      omega
    have compared := results named payload shape candidate message emitted attempt packet interval
    have layout : (serviceGraph setup .concurrent).outputLayout (embedding.event index) =
        .binding owner payload := namedEq.symm ▸ shape
    apply (phaseCommitWordAction_eq_iff_result setup .concurrent block suffix embedding actions
      owner index inside payload layout word reference).mpr
    simpa only [namedEq] using compared
  · intro same named payload shape candidate message emitted attempt packet interval
    rw [same named payload shape candidate message emitted attempt packet interval]

/-- At a genuine unsent owned callback the actual emitted cylinder fixes
exactly the earlier owned source actions. Pending foreign rows elsewhere in
the static block do not change this owner's conditional query. -/
theorem issuedLedger_iff_prefix_at_request
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix)) (low : Nat)
    (rank : ∀ index, (embedding.event index).val = low + index.val)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    {control : (nativeApplication).Control}
    (trace : (nativeProtocol).Trace (some control))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (installed : control.execution.application.phases.head? = some phase)
    (phaseLow : phase.low = low) (phaseHigh : phase.high = low + block.length)
    (owner : Player) (selected : (serviceGraph setup .concurrent).EventId)
    (selectedPayload : L.Ty)
    (selectedShape : (serviceGraph setup .concurrent).outputLayout selected =
      .binding owner selectedPayload)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, selected⟩)
    (selectedInside : low ≤ selected.val ∧ selected.val < low + block.length)
    (unsent : ∀ message ∈ (nativeApplication).outputs (control.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, selected⟩)
    (reference word : DecisionView owner Δ)
    (retained : issuedLedger setup implementation block low control (low + block.length)
      owner reference) :
    issuedLedger setup implementation block low control (low + block.length) owner word ↔
      ∀ position < selected.val - low,
        block.wordAction owner position word = block.wordAction owner position reference := by
  let inputs := setup.initialLaw.map encodeInputs
  have actual : ((nativeMenu).protocol (inputs.map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some control) := by
    have initialEq : inputs.map (PhaseRuntimeState.initial implementation.plan) =
        implementation.initial := by
      simp only [inputs, PMF.map_comp, ReservedConcurrentImplementation.initial, Function.comp_def]
    rw [initialEq]
    exact trace
  have raw := (nativeMenu).toRawTrace _ implementation.horizon implementation.scheduler actual
  have ordered := serviceGraph_revealRelaxedOrdered setup .concurrent
  have address : control.execution.application.attempt.phase = low := by
    simp only [PhaseRuntimeState.attempt, installed, Option.map_some, Option.getD_some, phaseLow]
  rw [issuedLedger_iff_actions setup implementation block suffix embedding low rank actions trace
    owner reference word retained]
  constructor
  · intro agrees position bounded
    have blockBound : position < block.length := by omega
    let index : Fin (eventCount (block.prepend suffix)) :=
      ⟨position, by have count := block.eventCount_prepend suffix; omega⟩
    by_cases owns : eventOwner? (block.prepend suffix) index = some owner
    · obtain ⟨other, payload, _member, layout⟩ :=
        block.binding_before_length suffix index blockBound
      have sameOwner : other = owner := by
        have actor := EventGraph.actor?_of_outputLayout_binding
          (toEventGraph (block.prepend suffix)) layout
        rw [eventOwner?_eq_actor, actor] at owns
        exact Option.some.inj owns
      subst other
      have shape : (serviceGraph setup .concurrent).outputLayout (embedding.event index) =
          .binding owner payload := (embedding.layout_eq index).trans layout
      have interval : low ≤ (embedding.event index).val ∧
          (embedding.event index).val < low + block.length := by
        rw [rank]
        dsimp only [index]
        omega
      have inside : embedding.event index ∈ phase.events := by
        apply (phase.mem_events _).mpr
        simpa only [phaseLow, phaseHigh] using interval
      have earlier : (embedding.event index).val < selected.val := by
        rw [rank]
        dsimp only [index]
        omega
      obtain ⟨candidate, owned, accepted, _read⟩ := phase_ready_earlier_binding_read
        implementation.runtime implementation.leaks implementation.bounds implementation.plan
        inputs implementation.horizon implementation.scheduler actual ordered phase installed
        owner selected selectedPayload selectedShape request.2.2.1 request.2.2.2.2
        (embedding.event index) payload shape inside earlier
      have stamped := phaseLiveBindingStamp_history implementation.runtime implementation.leaks
        implementation.plan inputs implementation.horizon implementation.scheduler raw
      rcases stamped (embedding.event index) candidate accepted with old |
          ⟨message, emitted, _sender, packet, attempt⟩
      · rw [address] at old
        omega
      · rw [owned] at emitted
        have same := agrees (embedding.event index) payload shape candidate message emitted
          attempt packet interval
        have offset : (embedding.event index).val - low = position := by
          rw [rank]
          dsimp only [index]
          omega
        simpa only [offset] using same
    · rw [compiledCommitPrefix_wordAction_none_of_unowned block suffix owner index owns word,
        compiledCommitPrefix_wordAction_none_of_unowned block suffix owner index owns reference]
  · intro agrees named payload shape candidate message emitted attempt packet interval
    obtain ⟨serial, opening, evidence, entry, slot, member, sent, action, _fresh, _result⟩ :=
      retained named payload shape candidate message emitted attempt packet interval
    have stamped := phase_recalled_emission_attempt implementation.runtime implementation.leaks
      _ implementation.horizon implementation.scheduler raw owner entry member message sent
    have before : entry.beforeView.application.2.attempt =
        control.execution.application.attempt := stamped.symm.trans attempt
    have earlier := phase_recorded_binding_rank_lt_of_unsent_request implementation.runtime
      implementation.leaks implementation.bounds implementation.plan inputs implementation.horizon
      ordered implementation.scheduler actual owner entry member
      ⟨⟨.commitment named (owner, .prepared serial), opening⟩, evidence⟩
      (by rw [action]) named (owner, .prepared serial) rfl before selected request unsent
    exact agrees (named.val - low) (by omega)

open Classical in
/-- Conditioning the actual retained owner cylinder at its next unsent
binding gives the chronological source kernel at the updated earlier view.
The complete word retains repeated-owner dependence; it is not a table of
independently sampled answers. -/
theorem issuedLedger_owned_word_conditional
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
    (earlier : SourceProgram.CommitPrefix Γ O Δ P)
    (later : SourceProgram.CommitPrefix ((name, .commitment owner payload) :: Δ)
      (insert name P) Ξ Q) (suffix : SourceProgram Player L Ξ Q)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      ((earlier.append (.commit name owner fresh guard later)).prepend suffix)) (low : Nat)
    (rank : ∀ index, (embedding.event index).val = low + index.val)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction ((earlier.append (.commit name owner fresh guard later)).prepend suffix)
        index (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    {control : (nativeApplication).Control} (trace : (nativeProtocol).Trace (some control))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (installed : control.execution.application.phases.head? = some phase)
    (phaseLow : phase.low = low)
    (phaseHigh : phase.high = low + (earlier.append (.commit name owner fresh guard later)).length)
    (selected : (serviceGraph setup .concurrent).EventId)
    (shape : (serviceGraph setup .concurrent).outputLayout selected = .binding owner payload)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, selected⟩)
    (selectedInside : low ≤ selected.val ∧
      selected.val < low + (earlier.append (.commit name owner fresh guard later)).length)
    (selectedRank : selected.val - low = earlier.length)
    (unsent : ∀ message ∈ (nativeApplication).outputs (control.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, selected⟩)
    (profile : SourceProgram.BehavioralProfile
      (earlier.prepend (.commit name owner fresh guard (later.prepend suffix))))
    (entry : SourceProgram.Config Player L Γ) (reference : DecisionView owner Ξ) :
    let current := earlier.tailProfile (.commit name owner fresh guard (later.prepend suffix))
      profile
    let before := earlier.prefixLaw (.commit name owner fresh guard (later.prepend suffix))
      profile entry
    let complete := before.bind fun config =>
      ((SourceProgram.CommitPrefix.commit name owner fresh guard later).prefixLaw suffix
        current config)
    let prior := complete.map (SourceProgram.Config.view owner)
    let observed := (later.entryView owner reference).back true
    reference ∈ prior.support →
    issuedLedger setup implementation (earlier.append (.commit name owner fresh guard later)) low
      control (low + (earlier.append (.commit name owner fresh guard later)).length)
      owner reference →
    (fiberPosterior prior (fun word => decide (issuedLedger setup implementation
      (earlier.append (.commit name owner fresh guard later)) low control
      (low + (earlier.append (.commit name owner fresh guard later)).length) owner word)) true).map
      ((earlier.append (.commit name owner fresh guard later)).wordAction owner earlier.length) =
      (SourceProgram.commitKernel current observed).map (fun result =>
        some (OwnAction.commit owner name payload result)) := by
  intro current before complete prior observed supported retained
  let beforeView := fun word : DecisionView owner Ξ => (later.entryView owner word).back true
  have possible : observed ∈ (before.map (SourceProgram.Config.view owner)).support := by
    have projected : observed ∈ (prior.map beforeView).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨reference, supported, rfl⟩
    have projection : prior.map beforeView = before.map (SourceProgram.Config.view owner) := by
      simpa only [prior, complete, before, current, beforeView,
        SourceProgram.CommitPrefix.prepend, SourceProgram.CommitPrefix.entryView, decide_true] using
        earlier.prefixLaw_split_entryView
          (.commit name owner fresh guard later) suffix profile entry owner
    exact projection ▸ projected
  have same : fiberPosterior prior (fun word => decide (issuedLedger setup implementation
      (earlier.append (.commit name owner fresh guard later)) low control
      (low + (earlier.append (.commit name owner fresh guard later)).length) owner word)) true =
      fiberPosterior prior beforeView observed := by
    apply fiberPosterior_eq_of_support_fiber
    intro word drawn
    rw [decide_eq_true_eq,
      issuedLedger_iff_prefix_at_request setup implementation
        (earlier.append (.commit name owner fresh guard later)) suffix embedding low rank actions
        trace phase installed phaseLow phaseHigh owner selected payload shape request
        selectedInside unsent reference word retained, selectedRank]
    have compared := earlier.prefixLaw_split_entryView_iff_wordActions
      (.commit name owner fresh guard later) suffix profile entry owner word reference
      drawn supported
    simpa only [SourceProgram.CommitPrefix.entryView, decide_true, beforeView, observed] using
      compared.symm
  rw [same]
  exact earlier.prefixLaw_owned_word_conditional fresh guard later suffix profile entry
    observed possible

open Classical in
/-- The actual foreign issued rectangle conditions only foreign owner words.
Each retained owner marginal keeps its original chronological dependence.
The unused focal ordinary marginal is left unconditioned. -/
theorem issuedLedger_foreign_product
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (profile : SourceProgram.BehavioralProfile (block.prepend suffix))
    (entry : SourceProgram.Config Player L Γ) (low high : Nat)
    (control : (nativeApplication).Control) (focal : Player)
    (present : ∃ final ∈ (block.prefixLaw suffix profile entry).support,
      ∀ owner, owner ≠ focal →
        issuedLedger setup implementation block low control high owner (final.view owner)) :
    fiberPosterior
      ((block.prefixLaw suffix profile entry).map (fun final owner => final.view owner))
      (fun views => decide (∀ owner, owner ≠ focal →
        issuedLedger setup implementation block low control high owner (views owner))) true =
      independentProduct (fun owner => fiberPosterior
        ((block.prefixLaw suffix profile entry).map (SourceProgram.Config.view owner))
        (fun word => decide (owner ≠ focal →
          issuedLedger setup implementation block low control high owner word)) true) := by
  let laws := fun owner =>
    (block.prefixLaw suffix profile entry).map (SourceProgram.Config.view owner)
  let restriction := fun owner => {word | owner ≠ focal →
    issuedLedger setup implementation block low control high owner word}
  have coordinate (owner : Player) : ∃ word ∈ restriction owner, word ∈ (laws owner).support := by
    obtain ⟨final, supported, retained⟩ := present
    exact ⟨final.view owner, retained owner,
      (PMF.mem_support_map_iff _ _ _).mpr ⟨final, supported, rfl⟩⟩
  have rectangle : ∃ views ∈ Set.pi Set.univ restriction,
      views ∈ (independentProduct laws).support := by
    obtain ⟨final, supported, retained⟩ := present
    refine ⟨fun owner => final.view owner, fun owner _ => retained owner, ?_⟩
    rw [← block.prefixLaw_views_product suffix profile entry]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, supported, rfl⟩
  have marginal (owner : Player) :
      fiberPosterior (laws owner) (fun word => decide (owner ≠ focal →
        issuedLedger setup implementation block low control high owner word)) true =
        (laws owner).filter (restriction owner) (coordinate owner) := by
    have meets : ∃ word ∈ {word | decide (owner ≠ focal →
        issuedLedger setup implementation block low control high owner word) = true},
        word ∈ (laws owner).support := by
      simpa only [Set.mem_ofPred_eq, decide_eq_true_eq, restriction] using coordinate owner
    simpa only [decide_eq_true_eq] using fiberPosterior_eq_filter (laws owner)
      (fun word => decide (owner ≠ focal →
        issuedLedger setup implementation block low control high owner word)) meets
  have total : fiberPosterior (independentProduct laws)
      (fun views => decide (∀ owner, owner ≠ focal →
        issuedLedger setup implementation block low control high owner (views owner))) true =
        (independentProduct laws).filter (Set.pi Set.univ restriction) rectangle := by
    have meets : ∃ views ∈ {views | decide (∀ owner, owner ≠ focal →
        issuedLedger setup implementation block low control high owner (views owner)) = true},
        views ∈ (independentProduct laws).support := by
      obtain ⟨views, belongs, supported⟩ := rectangle
      exact ⟨views, by
        simp only [Set.mem_ofPred_eq, decide_eq_true_eq]
        exact fun owner => belongs owner (Set.mem_univ owner), supported⟩
    have same : {views | decide (∀ owner, owner ≠ focal →
        issuedLedger setup implementation block low control high owner (views owner)) = true} =
        Set.pi Set.univ restriction := by
      ext views
      simp only [Set.mem_ofPred_eq, decide_eq_true_eq, Set.mem_pi, Set.mem_univ,
        forall_true_left, restriction]
    rw [fiberPosterior_eq_filter _ _ meets]
    simp only [same]
  rw [block.prefixLaw_views_product suffix profile entry]
  change fiberPosterior (independentProduct laws) _ true = independentProduct
    (fun owner => fiberPosterior (laws owner) _ true)
  rw [total]
  simp_rw [marginal]
  exact filter_independentProduct laws restriction coordinate

open Classical in
/-- The next ready foreign row under the complete foreign issued cylinder
uses its chronological owner kernel. Other owners' restrictions do not alter
that kernel, and the focal ordinary word remains unrestricted. -/
theorem issuedLedger_foreign_owned_word_conditional
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
    (earlier : SourceProgram.CommitPrefix Γ O Δ P)
    (later : SourceProgram.CommitPrefix ((name, .commitment owner payload) :: Δ)
      (insert name P) Ξ Q) (suffix : SourceProgram Player L Ξ Q)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      ((earlier.append (.commit name owner fresh guard later)).prepend suffix)) (low : Nat)
    (rank : ∀ index, (embedding.event index).val = low + index.val)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction ((earlier.append (.commit name owner fresh guard later)).prepend suffix)
        index (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    {control : (nativeApplication).Control} (trace : (nativeProtocol).Trace (some control))
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (installed : control.execution.application.phases.head? = some phase)
    (phaseLow : phase.low = low)
    (phaseHigh : phase.high = low + (earlier.append (.commit name owner fresh guard later)).length)
    (selected : (serviceGraph setup .concurrent).EventId)
    (shape : (serviceGraph setup .concurrent).outputLayout selected = .binding owner payload)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, selected⟩)
    (selectedInside : low ≤ selected.val ∧
      selected.val < low + (earlier.append (.commit name owner fresh guard later)).length)
    (selectedRank : selected.val - low = earlier.length)
    (unsent : ∀ message ∈ (nativeApplication).outputs (control.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, selected⟩)
    (profile : SourceProgram.BehavioralProfile
      (earlier.prepend (.commit name owner fresh guard (later.prepend suffix))))
    (entry : SourceProgram.Config Player L Γ) (reference : DecisionView owner Ξ)
    (focal : Player) (foreign : owner ≠ focal) :
    let block := earlier.append (.commit name owner fresh guard later)
    let current := earlier.tailProfile (.commit name owner fresh guard (later.prepend suffix))
      profile
    let before := earlier.prefixLaw (.commit name owner fresh guard (later.prepend suffix))
      profile entry
    let complete := before.bind fun config =>
      ((SourceProgram.CommitPrefix.commit name owner fresh guard later).prefixLaw suffix
        current config)
    let prior := complete.map (SourceProgram.Config.view owner)
    let observed := (later.entryView owner reference).back true
    reference ∈ prior.support →
    issuedLedger setup implementation block low control (low + block.length) owner reference →
    (∃ final ∈ complete.support, ∀ other, other ≠ focal →
      issuedLedger setup implementation block low control (low + block.length)
        other (final.view other)) →
    (fiberPosterior complete (fun final => decide (∀ other, other ≠ focal →
      issuedLedger setup implementation block low control (low + block.length)
        other (final.view other))) true).map
          (fun final => block.wordAction owner earlier.length (final.view owner)) =
      (SourceProgram.commitKernel current observed).map (fun result =>
        some (OwnAction.commit owner name payload result)) := by
  intro block current before complete prior observed supported retained present
  let fullProfile := cast (congrArg SourceProgram.BehavioralProfile
    (earlier.prepend_append (.commit name owner fresh guard later) suffix).symm) profile
  have fullLaw : block.prefixLaw suffix fullProfile entry = complete := by
    simpa only [block, fullProfile, complete, before, current,
      SourceProgram.CommitPrefix.prepend, cast_cast, cast_eq] using
      earlier.prefixLaw_append (.commit name owner fresh guard later) suffix fullProfile entry
  have fullPresent : ∃ final ∈ (block.prefixLaw suffix fullProfile entry).support,
      ∀ other, other ≠ focal → issuedLedger setup implementation block low control
        (low + block.length) other (final.view other) := by
    rwa [fullLaw]
  have product := issuedLedger_foreign_product setup implementation block suffix fullProfile
    entry low (low + block.length) control focal fullPresent
  rw [fullLaw] at product
  let read := fun final : SourceProgram.Config Player L Ξ => fun other => final.view other
  let test := fun views : ∀ other, DecisionView other Ξ => decide (∀ other, other ≠ focal →
    issuedLedger setup implementation block low control (low + block.length) other (views other))
  have possible : true ∈ (complete.map (test ∘ read)).support := by
    obtain ⟨final, member, ledger⟩ := present
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, member, by
      simpa only [test, read, Function.comp_def, decide_eq_true_eq] using ledger⟩
  have mapped := congrArg (PMF.map (fun views : ∀ other, DecisionView other Ξ => views owner))
    (map_fiberPosterior_readout complete read test true possible)
  rw [PMF.map_comp] at mapped
  have ownerPosterior :
      (fiberPosterior complete (fun final => decide (∀ other, other ≠ focal →
        issuedLedger setup implementation block low control (low + block.length)
          other (final.view other))) true).map (SourceProgram.Config.view owner) =
      fiberPosterior prior (fun word => decide (issuedLedger setup implementation block low
        control (low + block.length) owner word)) true := by
    change (fiberPosterior complete (test ∘ read) true).map
      ((fun views : ∀ other, DecisionView other Ξ => views owner) ∘ read) = _
    rw [mapped]
    rw [product, independentProduct_map_eval]
    apply fiberPosterior_eq_of_support_fiber
    intro word _member
    rw [decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨fun ledger => ledger foreign, fun ledger _ => ledger⟩
  have actionPosterior := congrArg (PMF.map (block.wordAction owner earlier.length)) ownerPosterior
  rw [PMF.map_comp] at actionPosterior
  exact actionPosterior.trans (issuedLedger_owned_word_conditional setup implementation fresh
    guard earlier later suffix embedding low rank actions trace phase installed phaseLow phaseHigh
    selected shape request selectedInside selectedRank unsent profile entry reference supported
      retained)

open Classical in
/-- Ordinary complete foreign owner words with the original issued cylinder.
The source entry is pulled from the target itself, without a posterior-support gate. -/
def ordinaryForeignJoint (operational : implementation.Operational) (who : Player)
    (history : (nativeProtocol).History) (target : setup.proposalRecoveryProtocol.History) :
    PMF (SourceProgram.History Player L × Bool) := by
  cases history with
  | mk state trace =>
    cases state with
    | none => exact PMF.pure (fun _ => [], true)
    | some control =>
      let checkpoint := (checkpointSelection setup implementation operational trace).val.checkpoint
      let pulled := target.state.bind fun current =>
        residualEntry? checkpoint.residual.tail checkpoint.residual.lift current.point
      exact pulled.elim (PMF.pure (fun _ => [], false)) fun entry => by
        by_cases committing : ProtocolState.atCommit checkpoint.residual.tail
            (ProtocolState.entry checkpoint.residual.tail entry) = true
        · let block := SourceProgram.commitPhase checkpoint.residual.tail
          let embedding := cast (congrArg (fun program => OutputEmbedding
            (inputLayout setup.context) (outputLayout setup.program) program)
              block.reconstruct.symm) checkpoint.embedding
          let wholeViews := fun owner
              (view : ProtocolView owner (block.block.prepend block.suffix)) =>
            checkpoint.views.view owner
              (cast (congrArg (ProtocolView owner) block.reconstruct) view)
          let profile := ordinaryBlockProfile setup .concurrent implementation.plan values
            block.block block.suffix
            embedding wholeViews
            (control.execution.application.entry.excluded,
              control.execution.application.generation, control.execution.application.attempt.phase)
            control.execution.application.publicView
            (PhaseProposal.sourceArchive control.execution.network.inputs)
          exact (block.block.prefixLaw block.suffix profile entry).map fun final =>
            ((fun owner => if owner = who then [] else final.history owner),
              decide (∀ owner, owner ≠ who →
                issuedLedger setup implementation block.block
                  control.execution.application.attempt.phase control
                  (control.execution.application.attempt.phase + block.block.length)
                  owner (final.view owner)))
        · exact PMF.pure (fun _ => [], true)

/-- Original whole-tape posterior at the actual observed environment prefix. -/
def prefixTapeLaw (history : (nativeProtocol).History) :
    PMF (ReservedEpoch.Tape Player implementation.tapeLength) :=
  match history.state with
  | none => implementation.prior
  | some control =>
    ((nativeApplication).schedulerMixture implementation.prior
      (ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime))).posterior
      control.execution.environmentRecall

open Classical in
/-- The actual unnormalized native reach, original tape, source posterior and
issued-word joint. Zero cylinders contribute zero before any normalization. -/
def annotatedPrefixWeight (operational : implementation.Operational)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (history : (nativeProtocol).History)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target : setup.proposalRecoveryProtocol.History) (word : SourceProgram.History Player L) :
    ℝ≥0∞ :=
  let joint := ordinaryForeignJoint setup values implementation operational who history target
  ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).historyReachWeight
       nativeProfile history * prefixTapeLaw setup implementation history tape *
    if (∀ owner, owner ≠ who →
        ¬ EventGraphRuntime.PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
          implementation.leaks implementation.bounds nativeInitial implementation.horizon
          implementation.scheduler owner history) ∧
        history.state.elim True (fun control =>
          who ∉ control.execution.application.current.excluded) then
      setup.proposalRecoveryClosedLaw sourceProfile who
        (canonicalSource setup implementation operational history) target *
        if (joint.map Prod.snd) true = 0 then 0 else
          ((fiberPosterior joint Prod.snd true).map Prod.fst) word
    else 0

open Classical in
theorem prescribed_source_history_positive
    (scale sourceBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (badPositive : 0 < sourceBad.val) (badBelow : sourceBad.val < 1)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (prescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (history : setup.proposalRecoveryProtocol.History) :
    0 < setup.proposalRecoveryModel.historyReachWeight sourceProfile history := by
  classical
  let ordinary := setup.proposalRecoveryNormalizedTrembledProfile
    scale.val scale.property.1 scale.property.2
    sourceBad.val sourceBad.property.1 sourceBad.property.2
    scale.val scale.property.1 scale.property.2 values
  have full : ∀ owner (site : setup.proposalRecoveryModel.InformationSite owner)
      (choice : setup.proposalRecoveryModel.Choice owner site.1),
      choice ∈ (ordinary owner site.1).support := by
    intro owner site choice
    change choice ∈ (PMF.map (setup.proposalRecoveryComponentChoice owner site.1).symm
      (setup.proposalRecoveryComponentTrembledLaw owner
        (setup.proposalRecoveryQuery owner site.1)
        scale.val scale.property.1 scale.property.2
        sourceBad.val sourceBad.property.1 sourceBad.property.2
        scale.val scale.property.1 scale.property.2
        (values owner (setup.proposalRecoveryQuery owner site.1)))).support
    refine (PMF.mem_support_map_iff _ _ _).mpr
      ⟨setup.proposalRecoveryComponentChoice owner site.1 choice, ?_,
        (setup.proposalRecoveryComponentChoice owner site.1).symm_apply_apply choice⟩
    exact setup.proposalRecoveryComponentTrembledLaw_fullSupport owner _
      scale.val scalePositive scaleBelow sourceBad.val badPositive badBelow
      scale.val scalePositive scaleBelow _ (fullValues owner _) _
  have positive := setup.proposalRecoveryModel.historyReachWeight_pos_of_fullSupport
    ordinary full history
  have same := setup.proposalRecoveryModel.runBehavioralFrom_congr
    (first := sourceProfile) (second := ordinary) history.trace.length
    setup.proposalRecoveryProtocol.initHistory
    (fun reached _ running owner => prescribed owner reached running)
  change 0 < setup.proposalRecoveryModel.runBehavioralFrom sourceProfile history.trace.length
    setup.proposalRecoveryProtocol.initHistory history
  rw [same]
  exact positive

/-- A positive actual annotation has a genuine closed source tag and an
issued-word cylinder. Reach support excludes the posterior's fallback branch. -/
theorem annotatedPrefixWeight_support (operational : implementation.Operational)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player) (history : (nativeProtocol).History)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (target : setup.proposalRecoveryProtocol.History) (word : SourceProgram.History Player L)
    (canonicalSupported : setup.proposalRecoveryModel.historyReachWeight sourceProfile
      (canonicalSource setup implementation operational history) ≠ 0)
    (positive : annotatedPrefixWeight setup values implementation operational sourceProfile
      nativeProfile who history tape target word ≠ 0) :
    setup.proposalRecoveryClosedKey who target = setup.proposalRecoveryClosedKey who
        (canonicalSource setup implementation operational history) ∧
      setup.proposalRecoveryModel.historyReachWeight sourceProfile target ≠ 0 ∧
      (word, true) ∈ (ordinaryForeignJoint setup values implementation operational
        who history target).support := by
  classical
  let canonical := canonicalSource setup implementation operational history
  let joint := ordinaryForeignJoint setup values implementation operational who history target
  have mass : setup.proposalRecoveryClosedMass sourceProfile who canonical ≠ 0 := by
    apply (PMF.mem_support_iff _ _).mp
    apply (PMF.mem_support_map_iff _ _ _).mpr
    refine ⟨canonical, ?_, rfl⟩
    exact (PMF.mem_support_iff _ _).mpr canonicalSupported
  unfold annotatedPrefixWeight at positive
  dsimp only at positive
  have factors := (mul_ne_zero_iff.mp positive).2
  split at factors
  · have tagged := (mul_ne_zero_iff.mp factors).1
    have issued := (mul_ne_zero_iff.mp factors).2
    have label := (setup.proposalRecoveryClosedLaw_support sourceProfile who canonical target
      mass).mp ((PMF.mem_support_iff _ _).mpr tagged)
    refine ⟨label.1, label.2, ?_⟩
    change (if (joint.map Prod.snd) true = 0 then 0 else
      ((fiberPosterior joint Prod.snd true).map Prod.fst) word) ≠ 0 at issued
    by_cases empty : (joint.map Prod.snd) true = 0
    · rw [ite_eq_left empty] at issued
      exact False.elim (issued rfl)
    · rw [ite_eq_right empty] at issued
      obtain ⟨pair, member, first⟩ := (PMF.mem_support_map_iff _ _ _).mp
        ((PMF.mem_support_iff _ _).mpr issued)
      rw [fiberPosterior_support _ _ _ ((PMF.mem_support_iff _ _).mpr empty)] at member
      have pairEq : pair = (word, true) := Prod.ext first member.1
      exact pairEq ▸ member.2
  · simp only [ne_eq, not_true_eq_false] at factors

open Classical in
/-- The literal public, focal and service projection at a raw prefix. -/
def mechanicalProjection (who : Player) (state : (nativeProtocol).State) :=
  state.map fun control =>
    (control.remaining, control.actor, control.execution.application.publicView,
      control.execution.network.publicView, control.execution.receipts,
      control.execution.observe nativeApplication who,
      (fun owner serial => decide
        (control.execution.application.current.native.candidates.lookup
          (owner, .prepared serial) = .fresh)),
      control.execution.environmentRecall, control.execution.recall who)

/-- Every raw step remains represented, including silent callbacks. -/
def mechanicalWord (who : Player) : ∀ {state : (nativeProtocol).State},
    (nativeProtocol).Trace state → List (Set.range (mechanicalProjection setup implementation who))
  | _, .start => [⟨mechanicalProjection setup implementation who none, none, rfl⟩]
  | target, .extend prior _ _ _ => mechanicalWord who prior ++
      [⟨mechanicalProjection setup implementation who target, target, rfl⟩]

theorem mechanicalWord_last (who : Player) {state : (nativeProtocol).State}
    (trace : (nativeProtocol).Trace state) :
    (mechanicalWord setup implementation who trace).getLast? =
      some ⟨mechanicalProjection setup implementation who state, state, rfl⟩ := by
  cases trace with
  | start => rfl
  | extend prior joint legal realized =>
      rw [mechanicalWord, List.getLast?_append_of_ne_nil _ (by simp),
        List.getLast?_singleton]

theorem mechanicalWord_ownPlay (who : Player)
    (left right : (nativeApplication).Control)
    (first : (nativeProtocol).Trace (some left))
    (second : (nativeProtocol).Trace (some right))
    (same : mechanicalWord setup implementation who first =
      mechanicalWord setup implementation who second) :
    ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).ownPlay who first =
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).ownPlay who second := by
  have last := congrArg List.getLast? same
  rw [mechanicalWord_last, mechanicalWord_last] at last
  have projected := congrArg Subtype.val (Option.some.inj last)
  change some (_, _, _, _, _, _, _, _, left.execution.recall who) =
    some (_, _, _, _, _, _, _, _, right.execution.recall who) at projected
  have recalled : left.execution.recall who = right.execution.recall who :=
    congrArg (fun row => row.2.2.2.2.2.2.2.2) (Option.some.inj projected)
  rw [HiddenSwap.phase_trace_ownPlay implementation.bounds nativeInitial implementation.horizon
      implementation.scheduler left first who,
    HiddenSwap.phase_trace_ownPlay implementation.bounds nativeInitial implementation.horizon
      implementation.scheduler right second who, recalled]

/-- A retained mechanical prefix together with the original whole tape. -/
def MechanicalIndex (who : Player) :=
  Set.range (fun history : (nativeProtocol).History =>
    mechanicalWord setup implementation who history.trace) ×
      ReservedEpoch.Tape Player implementation.tapeLength

open Classical in
/-- The accepting word after one genuinely available proper current SEND.
Its representative is immaterial on ready support by binding-alias invariance. -/
def bindingAdmissionBit (who : Player) (event : (serviceGraph setup .concurrent).EventId)
    (history : (nativeProtocol).History)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength) : Bool :=
  match history.state with
  | none => false
  | some control =>
    if offered : ∃ material : WitnessedSubmission (serviceGraph setup .concurrent),
        (⟨some material⟩ : (nativeApplication).Action) ∈
          (nativeMenu).actions who (control.execution.recall who)
            (control.execution.observe nativeApplication who) ∧
        ∃ (payload : L.Ty) (value : L.Val payload) (serial : Nat),
          (serviceGraph setup .concurrent).outputLayout event = .binding who payload ∧
          material.call.packet = .commitment event (who, .prepared serial) ∧
          PhaseProposal.bindingPreparation material = some ⟨payload, value⟩ then
      let sent := control.execution.respond nativeApplication who
        ⟨some (Classical.choose offered)⟩
      decide (∃ phase ∈ control.execution.application.phases.head?,
        phase.kind = .commitment ∧ ∀ named ∈ phase.events, ∀ owner,
          (serviceGraph setup .concurrent).actor? named = some owner →
          owner ∉ control.execution.application.entry.excluded →
          ReservedEpoch.ownedAcceptanceWord implementation.runtime implementation.leaks
            tape sent owner named)
    else false

open Classical in
/-- Push the one original annotated joint through the actual h-dependent
static cut and causal block. Qualification stays inside the native-history sum. -/
def annotatedForcedBlockWeight (operational : implementation.Operational)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player)
    (site : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (index : MechanicalIndex setup implementation who)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty) (value : L.Val payload)
    (cut completed : setup.proposalRecoveryProtocol.History) : ℝ≥0∞ :=
  ∑' history : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationHistory who site.1,
    if mechanicalWord setup implementation who history.val.trace = index.1.val then
      ∑' entry : setup.proposalRecoveryProtocol.History,
        ∑' word : SourceProgram.History Player L,
          annotatedPrefixWeight setup values implementation operational sourceProfile nativeProfile
              who history.val index.2 entry word *
            (if bindingAdmissionBit setup implementation who event history.val index.2
              then 1 else 0) *
            sourceForcedBlockJoint setup values implementation who history.val event payload
              entry word value (cut, completed)
    else 0

open Classical in
private theorem annotatedForcedBlockWeight_anchor
    (operational : implementation.Operational)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player)
    (site : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (index : MechanicalIndex setup implementation who)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty) (value : L.Val payload)
    (cut completed : setup.proposalRecoveryProtocol.History)
    (positive : annotatedForcedBlockWeight setup values implementation operational sourceProfile
      nativeProfile who site index event payload value cut completed ≠ 0) :
    ∃ history : ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).InformationHistory who site.1,
      mechanicalWord setup implementation who history.val.trace = index.1.val ∧
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).historyReachWeight nativeProfile history.val ≠ 0 ∧
      prefixTapeLaw setup implementation history.val index.2 ≠ 0 ∧
      (∀ owner, owner ≠ who →
        ¬ EventGraphRuntime.PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
          implementation.leaks implementation.bounds nativeInitial implementation.horizon
          implementation.scheduler owner history.val) ∧
      history.val.state.elim True (fun control =>
        who ∉ control.execution.application.current.excluded) ∧
      bindingAdmissionBit setup implementation who event history.val index.2 = true := by
  classical
  by_contra absent
  apply positive
  unfold annotatedForcedBlockWeight
  apply ENNReal.tsum_eq_zero.mpr
  intro history
  by_cases same : mechanicalWord setup implementation who history.val.trace = index.1.val
  · rw [ite_eq_left same]
    apply ENNReal.tsum_eq_zero.mpr
    intro entry
    apply ENNReal.tsum_eq_zero.mpr
    intro word
    by_contra nonzero
    have first := (mul_ne_zero_iff.mp nonzero).1
    have prefixWeight := (mul_ne_zero_iff.mp first).1
    have gate := (mul_ne_zero_iff.mp first).2
    have admitted : bindingAdmissionBit setup implementation who event history.val index.2 =
        true := by
      by_contra failed
      exact gate (ite_eq_right failed)
    unfold annotatedPrefixWeight at prefixWeight
    dsimp only at prefixWeight
    have initial := (mul_ne_zero_iff.mp prefixWeight).1
    have kept := (mul_ne_zero_iff.mp prefixWeight).2
    split at kept
    · rename_i good
      exact absent ⟨history, same, (mul_ne_zero_iff.mp initial).1,
        (mul_ne_zero_iff.mp initial).2, good.1, good.2, admitted⟩
    · exact kept rfl
  · exact ite_eq_right same

open Classical in
/-- Qualification mass before selecting a proper value or a utility. -/
def qualifiedPrefixMass
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player)
    (site : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (event : (serviceGraph setup .concurrent).EventId) : ℝ≥0∞ :=
  ∑' history : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationHistory who site.1,
    ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).historyReachWeight
         nativeProfile history.val *
      if (∀ owner, owner ≠ who →
          ¬ EventGraphRuntime.PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
            implementation.leaks implementation.bounds nativeInitial implementation.horizon
            implementation.scheduler owner history.val) ∧
          history.val.state.elim True (fun control =>
            who ∉ control.execution.application.current.excluded) then
        ∑' tape : ReservedEpoch.Tape Player implementation.tapeLength,
          prefixTapeLaw setup implementation history.val tape *
            if bindingAdmissionBit setup implementation who event history.val tape then 1 else 0
      else 0

/-- Positive qualification retains an actual supported prefix and its original
tape, before a source word or a proper focal value is selected. -/
theorem qualifiedPrefixMass_anchor
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player)
    (site : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (event : (serviceGraph setup .concurrent).EventId)
    (positive : 0 < qualifiedPrefixMass setup implementation nativeProfile who site event) :
    ∃ history : ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).InformationHistory who site.1,
      ∃ tape : ReservedEpoch.Tape Player implementation.tapeLength,
        ((nativeMenu).information nativeInitial implementation.horizon
          implementation.scheduler).historyReachWeight nativeProfile history.val ≠ 0 ∧
        prefixTapeLaw setup implementation history.val tape ≠ 0 ∧
        (∀ owner, owner ≠ who →
          ¬ EventGraphRuntime.PhaseProposal.GeneratedUnusableBindingHistory
            implementation.runtime implementation.leaks implementation.bounds nativeInitial
            implementation.horizon implementation.scheduler owner history.val) ∧
        history.val.state.elim True (fun control =>
          who ∉ control.execution.application.current.excluded) ∧
        bindingAdmissionBit setup implementation who event history.val tape = true := by
  classical
  by_contra absent
  have zero : qualifiedPrefixMass setup implementation nativeProfile who site event = 0 := by
    unfold qualifiedPrefixMass
    apply ENNReal.tsum_eq_zero.mpr
    intro history
    by_cases reached : ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).historyReachWeight nativeProfile history.val = 0
    · rw [reached, zero_mul]
    · split_ifs with good
      · suffices empty : (∑' tape : ReservedEpoch.Tape Player implementation.tapeLength,
            prefixTapeLaw setup implementation history.val tape *
              if bindingAdmissionBit setup implementation who event history.val tape
                then 1 else 0) = 0 by rw [empty, mul_zero]
        apply ENNReal.tsum_eq_zero.mpr
        intro tape
        by_cases supported : prefixTapeLaw setup implementation history.val tape = 0
        · rw [supported, zero_mul]
        · by_cases admitted : bindingAdmissionBit setup implementation who event history.val tape
            = true
          · exact False.elim (absent ⟨history, tape, reached, supported, good.1, good.2,
              admitted⟩)
          · have rejected : bindingAdmissionBit setup implementation who event history.val tape
                = false := Bool.eq_false_iff.mpr admitted
            simp only [rejected, Bool.false_eq_true, ↓reduceIte, mul_zero]
      · exact mul_zero _
  exact positive.ne' zero

omit [Fintype Player] in
theorem pulled_entry_history
    (control : (nativeApplication).Control)
    (checkpoint : RecoverySourceCheckpoint setup .concurrent control.execution.application)
    (point : ProtocolState setup.program)
    (entry : SourceProgram.Config Player L checkpoint.residual.context)
    (pulled : residualEntry? checkpoint.residual.tail checkpoint.residual.lift point = some entry) :
    ProtocolState.history setup.program point = entry.history := by
  have pointEq := (residualEntry?_eq_some_iff checkpoint.origin point entry).mp pulled
  rw [← pointEq, checkpoint.history, ProtocolState.history_entry]

omit [Fintype Player] in
theorem ordinaryBlockWord_drop
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (profile : SourceProgram.BehavioralProfile (block.prepend suffix))
    (entry : SourceProgram.Config Player L Γ) (owner : Player)
    (finished : SourceProgram.Config Player L Δ)
    (supported : finished ∈ (block.prefixLaw suffix profile entry).support) :
    (finished.history owner).drop (entry.history owner).length =
      (List.range block.length).filterMap (fun index =>
        block.wordAction owner index (finished.view owner)) := by
  rw [block.prefixLaw_wordAction_history suffix profile entry owner finished supported]
  simp


private def mechanicalForeignPolicy (rates : PhaseProposalRates) (owner : Player) :
    (nativeApplication).Policy :=
  phasePolicyDispatch setup .concurrent implementation.runtime implementation.leaks
    (fun owner event payload binding =>
      PhaseCount.phaseOpeningPolicy implementation.runtime implementation.leaks
        implementation.bounds owner event payload binding
        (fun _ _ => mix rates.waiting.val rates.waiting.property.1 rates.waiting.property.2
          (PMF.pure false) (PMF.pure true)))
    (fun owner event payload _binding past view =>
      mix rates.waiting.val rates.waiting.property.1 rates.waiting.property.2
        (PMF.pure ⟨none⟩)
        (PhaseCount.bindingResultEncoder implementation.runtime implementation.leaks
          implementation.bounds owner event payload (fun _ _ => PMF.pure .failure)
          rates.slots.val rates.slots.property.1 rates.slots.property.2 past view)) owner

/-- Packet and fresh-slot atom, with no ordinary value or alias probability. -/
def foreignMechanicalAtom (rates : PhaseProposalRates)
    (execution : (nativeApplication).Execution) (owner : Player)
    (response : (nativeApplication).Action) : ℝ≥0∞ :=
  let packet := fun action : (nativeApplication).Action =>
    action.transmission.map fun material =>
      (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
        (execution.recall owner) (execution.observe nativeApplication owner) material).payload
  let atom := ((mechanicalForeignPolicy setup implementation rates owner
    (execution.recall owner) (execution.observe nativeApplication owner)).map packet)
      (packet response)
  atom * match response.transmission with
    | none => 1
    | some material => match material.call.packet with
      | .commitment .. => ENNReal.ofReal (1 - rates.badPreparation.val)
      | _ => 1


private theorem binding_encoder_class_atom (rates : PhaseProposalRates)
    (owner : Player) (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (results : List (nativeApplication).PlayerEntry → (nativeApplication).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (value : L.Val payload) (packet : Option (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (sent : packet ≠ none) :
    let packetOf := fun response : (nativeApplication).Action => response.transmission.map
      (fun material => (PhaseCount.localEnvelope implementation.runtime implementation.leaks
        owner past view material).payload)
    let observe := fun response : (nativeApplication).Action =>
      (response.transmission.bind PhaseProposal.bindingPreparation, packetOf response)
    let encode := fun law => mix rates.waiting.val rates.waiting.property.1
      rates.waiting.property.2 (PMF.pure ⟨none⟩)
      (PhaseCount.bindingResultEncoder implementation.runtime implementation.leaks
        implementation.bounds owner event payload law rates.slots.val rates.slots.property.1
          rates.slots.property.2 past view)
    ((encode results).map observe) (some (⟨payload, value⟩ : Raw L), packet) =
      ((encode (fun _ _ => PMF.pure .failure)).map packetOf) packet *
        results past view (.success value) := by
  classical
  intro packetOf observe encode
  let failure := fun (_ : List (nativeApplication).PlayerEntry)
    (_ : (nativeApplication).PlayerView) => (PMF.pure .failure : PMF (PublicationResult
      (L.Val payload)))
  have silence : ((PMF.pure (⟨none⟩ : (nativeApplication).Action)).map observe)
      (some (⟨payload, value⟩ : Raw L), packet) =
      ((PMF.pure (⟨none⟩ : (nativeApplication).Action)).map packetOf) packet *
        results past view (.success value) := by
    simp [PMF.pure_map, observe, packetOf, sent]
  have fixed (serial : Nat) :
      (((results past view).map (phaseBindingResponse implementation.runtime implementation.leaks
        owner event payload · serial)).map observe) (some (⟨payload, value⟩ : Raw L), packet) =
      (((failure past view).map (phaseBindingResponse implementation.runtime implementation.leaks
        owner event payload · serial)).map packetOf) packet *
          results past view (.success value) := by
    let encoded := phaseBindingResponse implementation.runtime implementation.leaks
      owner event payload
    have output : setup.eventGraph.outputLayout event = .binding owner payload := binding
    have observed (result : PublicationResult (L.Val payload)) :
        observe (encoded result serial) =
          ((match result with
            | .failure => none | .success drawn => some (⟨payload, drawn⟩ : Raw L)),
            packetOf (encoded .failure serial)) := by
      apply Prod.ext
      · cases result <;>
          simp [observe, encoded, phaseBindingResponse, PhaseProposal.bindingPreparation, output]
      · exact PhaseCount.phaseBindingResponse_localPacket implementation.runtime
          implementation.leaks owner event payload past view result .failure serial
    have tested (result : PublicationResult (L.Val payload)) :
        (some (⟨payload, value⟩ : Raw L), packet) = observe (encoded result serial) ↔
          result = .success value ∧ packet = packetOf (encoded .failure serial) := by
      rw [observed]
      cases result <;> simp [Raw.mk.injEq, eq_comm]
    rw [PMF.map_comp, PMF.map_apply]
    simp only [Function.comp_apply]
    dsimp only [encoded] at tested
    rw [tsum_eq_single (.success value)]
    · rw [PMF.map_comp]
      simp only [tested, failure, PMF.pure_map, PMF.pure_apply, true_and, Function.comp_apply]
      split_ifs <;> simp
    · intro other different
      simp only [tested, different, false_and, ite_false]
  have slots :
      ((PhaseCount.phaseBindingSlotPolicy implementation.runtime implementation.leaks
        implementation.bounds owner event payload results past view).map observe)
          (some (⟨payload, value⟩ : Raw L), packet) =
      ((PhaseCount.phaseBindingSlotPolicy implementation.runtime implementation.leaks
        implementation.bounds owner event payload failure past view).map packetOf) packet *
          results past view (.success value) := by
    unfold PhaseCount.phaseBindingSlotPolicy
    split
    · rw [PMF.map_bind, PMF.map_bind, PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro serial
      rw [fixed]
      exact (mul_assoc _ _ _).symm
    · exact silence
  have canonical :
      ((PhaseCount.phaseBindingPolicy implementation.runtime implementation.leaks
        implementation.bounds owner event payload results past view).map observe)
          (some (⟨payload, value⟩ : Raw L), packet) =
      ((PhaseCount.phaseBindingPolicy implementation.runtime implementation.leaks
        implementation.bounds owner event payload failure past view).map packetOf) packet *
          results past view (.success value) := by
    unfold PhaseCount.phaseBindingPolicy
    split
    · exact silence
    · split
      · exact fixed _
      · exact silence
  dsimp only [encode]
  rw [mix_map, mix_map, mix_apply, mix_apply, silence]
  unfold PhaseCount.bindingResultEncoder
  rw [mix_map, mix_map, mix_apply, mix_apply, slots, canonical]
  ring

/-- At the actual counted callback a proper foreign binding separates its
mechanical packet, ordinary typed draw and input-specific raw alias atom. -/
theorem foreign_binding_response_atom
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (remaining : Nat) (owner : Player) (execution : (nativeApplication).Execution)
    (trace : (nativeProtocol).Trace (some ⟨remaining, some owner, execution⟩))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (key : setup.ProposalRecoveryComponent owner)
    (queried : phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
      implementation.plan owner event (execution.recall owner)
        (execution.observe nativeApplication owner) = some key)
    (response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds
      owner (execution.recall owner) (execution.observe nativeApplication owner))
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (transmitted : response.val.transmission = some material)
    (value : L.Val payload)
    (prepared : PhaseProposal.bindingPreparation material = some (⟨payload, value⟩ : Raw L))
    (serial : Nat) (packet : material.call.packet = .commitment event (owner, .prepared serial)) :
    phaseProposalBaseClasses setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner (execution.recall owner)
          (execution.observe nativeApplication owner)
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner) response) =
      foreignMechanicalAtom setup implementation rates execution owner response.val *
        ((values owner key).map (fun choice => phaseRecoveryDomainValue setup .concurrent event
          owner payload binding choice.val.val)) value ∧
    phaseProposalReferenceResponses setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner (execution.recall owner)
          (execution.observe nativeApplication owner) response =
      foreignMechanicalAtom setup implementation rates execution owner response.val *
        ((values owner key).map (fun choice => phaseRecoveryDomainValue setup .concurrent event
          owner payload binding choice.val.val)) value *
        (PMF.splitKernel
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner))
          (PhaseProposal.canonicalResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner))
          (PhaseProposal.project_canonicalResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner))
          rates.aliases.val rates.aliases.property.1 rates.aliases.property.2
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner) response)) response := by
  classical
  let past := execution.recall owner
  let view := execution.observe nativeApplication owner
  let packetOf := fun action : (nativeApplication).Action => action.transmission.map
    (fun material => (PhaseCount.localEnvelope implementation.runtime implementation.leaks
      owner past view material).payload)
  let observe := fun action : (nativeApplication).Action =>
    (action.transmission.bind PhaseProposal.bindingPreparation, packetOf action)
  let results := phaseProposalBindingResults setup .concurrent implementation.runtime
    implementation.leaks implementation.plan values rates owner event payload binding
  let encoded := fun law => mix rates.waiting.val rates.waiting.property.1
    rates.waiting.property.2 (PMF.pure (⟨none⟩ : (nativeApplication).Action))
    (PhaseCount.bindingResultEncoder implementation.runtime implementation.leaks
      implementation.bounds owner event payload law rates.slots.val rates.slots.property.1
        rates.slots.property.2 past view)
  have initial : (setup.initialLaw.map encodeInputs).map
      (PhaseRuntimeState.initial implementation.plan) = nativeInitial := by
    rw [PMF.map_comp]
    rfl
  obtain ⟨_draw, native⟩ := phaseNativeInvariant_history implementation.runtime implementation.leaks
    implementation.plan (setup.initialLaw.map encodeInputs) implementation.horizon
      implementation.scheduler (control := ⟨remaining, some owner, execution⟩) (by
        rw [initial]
        exact (nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler
          trace)
  have base : phaseProposalBasePolicy setup .concurrent implementation.runtime implementation.leaks
      implementation.bounds implementation.plan values rates owner past view = encoded results := by
    unfold phaseProposalBasePolicy
    rw [phasePolicyDispatch_binding setup .concurrent implementation.runtime implementation.leaks
      _ _ execution native owner event payload binding request]
  have mechanical : mechanicalForeignPolicy setup implementation rates owner past view =
      encoded (fun _ _ => PMF.pure .failure) := by
    unfold mechanicalForeignPolicy
    rw [phasePolicyDispatch_binding setup .concurrent implementation.runtime implementation.leaks
      _ _ execution native owner event payload binding request]
  have classLaw :
      (phaseProposalBaseClasses setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner past view).map Subtype.val =
      (phaseProposalBasePolicy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner past view).map observe := by
    rw [phaseProposalBaseClasses, PMF.map_comp,
      ← phaseProposalBaseResponses_map_val setup .concurrent implementation.runtime
        implementation.leaks implementation.bounds implementation.plan values rates owner past view,
      PMF.map_comp]
    rfl
  have classAtom : phaseProposalBaseClasses setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values rates owner past view
        (PhaseProposal.projectResponse implementation.runtime implementation.leaks
          implementation.bounds owner past view response) =
      ((encoded (fun _ _ => PMF.pure .failure)).map packetOf) (packetOf response.val) *
        results past view (.success value) := by
    rw [← pmf_map_apply_of_injective _ Subtype.val_injective
      (PhaseProposal.projectResponse implementation.runtime implementation.leaks
        implementation.bounds owner past view response), classLaw, base]
    change ((encoded results).map observe) (observe response.val) = _
    have selected : observe response.val =
        (some (⟨payload, value⟩ : Raw L), packetOf response.val) := by
      simp only [observe, transmitted, Option.bind_some, prepared]
    rw [selected]
    exact binding_encoder_class_atom setup implementation rates owner event payload binding
      past view
      results value (packetOf response.val) (by simp [packetOf, transmitted])
  have proper : results past view (.success value) =
      ENNReal.ofReal (1 - rates.badPreparation.val) *
        ((values owner key).map (fun choice => phaseRecoveryDomainValue setup .concurrent event
          owner payload binding choice.val.val)) value := by
    dsimp only [results, phaseProposalBindingResults]
    rw [queried, mix_apply]
    have mapped : ((values owner key).map (fun choice => PublicationResult.success
        (phaseRecoveryDomainValue setup .concurrent event owner payload binding choice.val.val)))
          (.success value) =
        ((values owner key).map (fun choice => phaseRecoveryDomainValue setup .concurrent event
          owner payload binding choice.val.val)) value := by
      have composed := congrArg (fun law : PMF (PublicationResult (L.Val payload)) =>
        law (.success value)) (PMF.map_comp
          (fun choice : setup.CommitRecoveryValueChoice owner key.1 =>
            phaseRecoveryDomainValue setup .concurrent event owner payload binding choice.val.val)
          (values owner key) PublicationResult.success)
      exact composed.symm.trans (pmf_map_apply_of_injective _
        (fun _ _ same => PublicationResult.success.inj same) value)
    rw [mapped]
    simp
  have properClass : phaseProposalBaseClasses setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values rates owner past view
        (PhaseProposal.projectResponse implementation.runtime implementation.leaks
          implementation.bounds owner past view response) =
      foreignMechanicalAtom setup implementation rates execution owner response.val *
        ((values owner key).map (fun choice => phaseRecoveryDomainValue setup .concurrent event
          owner payload binding choice.val.val)) value := by
    rw [classAtom, proper]
    change _ = (((mechanicalForeignPolicy setup implementation rates owner past view).map packetOf)
      (packetOf response.val) *
        (match response.val.transmission with
        | none => 1
        | some material => match material.call.packet with
          | .commitment .. => ENNReal.ofReal (1 - rates.badPreparation.val)
          | _ => 1)) * _
    rw [mechanical, transmitted]
    dsimp only
    rw [packet]
    ring
  refine ⟨properClass, ?_⟩
  unfold phaseProposalReferenceResponses PhaseProposal.splitResponseLaw
  rw [phaseProposalReferenceClasses_eq_of_counted setup .concurrent implementation.runtime
    implementation.leaks implementation.bounds implementation.plan operational.completePending
    operational.outputValues operational.maximalPhases values fullValues rates waitPositive
    waitBelow
    slotPositive badPositive badBelow implementation.horizon implementation.scheduler remaining
    owner
    execution trace]
  rw [bind_apply_of_unique_branch _ _ response
    (PhaseProposal.projectResponse implementation.runtime implementation.leaks implementation.bounds
      owner past view response) (fun chosen _ supported =>
        (PMF.splitKernel_supported _ _ _ _ _ _ chosen response supported).symm)]
  rw [properClass]

def mechanicalStepAtom (rates : PhaseProposalRates) (who : Player)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (before after : (nativeProtocol).State)
      (joint : Player → Option (nativeApplication).Action) :
    ℝ≥0∞ :=
  match before with
  | none => 1
  | some control => match control.actor with
    | some owner =>
      if owner = who then 1 else
        match joint owner with
        | none => 0
        | some response => foreignMechanicalAtom setup implementation rates
            control.execution owner response
    | none =>
      if control.remaining = 0 then 1 else
        match after with
        | none => 0
        | some later => match later.execution.environmentRecall.getLast? with
          | none => 0
          | some recorded =>
            ReservedEpoch.family implementation.runtime implementation.leaks
              (ReservedEpoch.packetCapacity implementation.runtime) tape
              control.execution.environmentRecall
              (control.execution.observeEnvironment nativeApplication) recorded.command

/-- Product of original fixed-tape command atoms and foreign mechanical atoms.
Initializer and Nature probabilities remain in the source transition mass. -/
def mechanicalPathAtom (rates : PhaseProposalRates) (who : Player)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength) :
    ∀ {state : (nativeProtocol).State}, (nativeProtocol).Trace state → ℝ≥0∞
  | _, .start => 1
  | after, @Trace.extend _ _ before _ prior joint _ _ =>
      mechanicalPathAtom rates who tape prior *
        mechanicalStepAtom setup implementation rates who tape before after joint

/-- Equal mechanical states retain the actual environment input and the whole
environment command recall, as well as the remaining horizon and actor. -/
theorem mechanicalProjection_environment (who : Player)
    (first second : (nativeApplication).Control)
    (same : mechanicalProjection setup implementation who (some first) =
      mechanicalProjection setup implementation who (some second)) :
    first.remaining = second.remaining ∧ first.actor = second.actor ∧
      first.execution.observeEnvironment nativeApplication =
        second.execution.observeEnvironment nativeApplication ∧
      first.execution.environmentRecall = second.execution.environmentRecall := by
  simp only [mechanicalProjection, Option.map_some, Option.some.injEq, Prod.mk.injEq] at same
  obtain ⟨remaining, actor, application, network, receipts, _focal, _fresh, environmentRecallEq,
    _own⟩ := same
  refine ⟨remaining, actor, ?_, environmentRecallEq⟩
  change (⟨first.execution.network.publicView, first.execution.application.publicView,
    first.execution.receipts⟩ : (nativeApplication).EnvironmentView) = _
  rw [network, application, receipts]
  rfl

/-- A reserved command reads only the original tape and mechanical input.
This equality holds pointwise, before evaluating any command atom. -/
theorem mechanicalProjection_tape_family (who : Player)
    (first second : (nativeApplication).Control)
    (same : mechanicalProjection setup implementation who (some first) =
      mechanicalProjection setup implementation who (some second))
    (tape : ReservedEpoch.Tape Player implementation.tapeLength) :
    ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) tape
        first.execution.environmentRecall (first.execution.observeEnvironment nativeApplication) =
      ReservedEpoch.family implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) tape
        second.execution.environmentRecall (second.execution.observeEnvironment
          nativeApplication) := by
  obtain ⟨_remaining, _actor, view, environmentRecallEq⟩ := mechanicalProjection_environment
    setup implementation
    who first second same
  rw [view, environmentRecallEq]

/-- Consecutive mechanical states identify the actual signed response packet.
The public input increment records silence or the single appended envelope;
private raw aliases and unchosen opening packets are absent from this equality. -/
theorem mechanicalProjection_response_packet (who owner : Player)
    (first second : (nativeApplication).Control)
    (firstTrace : (nativeProtocol).Trace (some first))
    (secondTrace : (nativeProtocol).Trace (some second))
    (firstResponse secondResponse : (nativeApplication).Action)
    (same : mechanicalProjection setup implementation who (some first) =
      mechanicalProjection setup implementation who (some second))
    (next : mechanicalProjection setup implementation who
        (some ⟨first.remaining, none,
          first.execution.respond nativeApplication owner firstResponse⟩) =
      mechanicalProjection setup implementation who
        (some ⟨second.remaining, none,
          second.execution.respond nativeApplication owner secondResponse⟩)) :
    firstResponse.transmission.map (fun material =>
        (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
          (first.execution.recall owner) (first.execution.observe nativeApplication owner)
          material).payload) =
      secondResponse.transmission.map (fun material =>
        (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
          (second.execution.recall owner) (second.execution.observe nativeApplication owner)
          material).payload) := by
  have firstRecall := PhaseCount.countRecall_history implementation.runtime implementation.leaks
    ((nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler
      firstTrace)
  have secondRecall := PhaseCount.countRecall_history implementation.runtime implementation.leaks
    ((nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler
      secondTrace)
  have inputs (execution : (nativeApplication).Execution)
      (counted : PhaseCount.CountRecall implementation.runtime implementation.leaks execution)
      (response : (nativeApplication).Action) :
      (execution.respond nativeApplication owner response).network.inputs =
        List.append (α := Message Player (nativeApplication).Payload)
          execution.network.inputs ((response.transmission.map fun material =>
            PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
              (execution.recall owner) (execution.observe nativeApplication owner)
                material).toList : List (Message Player (nativeApplication).Payload)) := by
    cases response with
    | mk transmission =>
        cases transmission with
        | none =>
            simp only [ReactiveApplication.Execution.respond, Option.map_none, Option.toList_none]
            exact (List.append_nil _).symm
        | some material =>
            simp only [Option.map_some, Option.toList_some]
            rw [PhaseCount.localEnvelope_eq_of_recall implementation.runtime implementation.leaks
              execution counted.1 counted.2.1 owner material]
            rfl
  have beforeInputs := congrArg (fun view : (nativeApplication).EnvironmentView =>
    view.network.inputs) (mechanicalProjection_environment setup implementation who first second
      same).2.2.1
  have afterInputs := congrArg (fun view : (nativeApplication).EnvironmentView =>
    view.network.inputs) (mechanicalProjection_environment setup implementation who
      ⟨first.remaining, none, first.execution.respond nativeApplication owner firstResponse⟩
      ⟨second.remaining, none, second.execution.respond nativeApplication owner secondResponse⟩
        next).2.2.1
  change (first.execution.respond nativeApplication owner firstResponse).network.inputs =
    (second.execution.respond nativeApplication owner secondResponse).network.inputs at afterInputs
  change first.execution.network.inputs = second.execution.network.inputs at beforeInputs
  rw [inputs first.execution firstRecall, inputs second.execution secondRecall,
    beforeInputs] at afterInputs
  have words := List.append_cancel_left afterInputs
  have packets : firstResponse.transmission.map (fun material =>
      PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
        (first.execution.recall owner) (first.execution.observe nativeApplication owner) material) =
      secondResponse.transmission.map (fun material =>
      PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
        (second.execution.recall owner) (second.execution.observe nativeApplication owner)
          material) := by
    simpa only [Option.head?_toList] using congrArg List.head? words
  simpa only [Option.map_map, Function.comp_def] using
    congrArg (Option.map Message.payload) packets

omit [Fintype Player] in
/-- Evaluating a supported opening packet keeps exactly the waiting or sending
coin atom. An unchosen truthful opening may contain a different private value. -/
theorem opening_packet_atom (waiting : Set.Icc (0 : ℝ) 1)
    (alternative : CommitAttemptPacket (serviceGraph setup .concurrent))
    (packet : Option (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (supported : (mix waiting.val waiting.property.1 waiting.property.2
      (PMF.pure none) (PMF.pure (some alternative))) packet ≠ 0) :
    (mix waiting.val waiting.property.1 waiting.property.2
      (PMF.pure none) (PMF.pure (some alternative))) packet =
        if packet.isNone then ENNReal.ofReal waiting.val else ENNReal.ofReal (1 - waiting.val) := by
  classical
  cases packet with
  | none => simp [mix_apply, PMF.pure_apply]
  | some packet =>
      have same : packet = alternative := by
        by_contra distinct
        apply supported
        simp [mix_apply, PMF.pure_apply, distinct]
      subst packet
      simp [mix_apply, PMF.pure_apply]

omit [Fintype Player] in
/-- Opening atoms agree at the actual packet across two supported callbacks,
even when their other truthful opening packets differ. -/
theorem opening_packet_atom_eq (waiting : Set.Icc (0 : ℝ) 1)
    (first second : CommitAttemptPacket (serviceGraph setup .concurrent))
    (packet : Option (CommitAttemptPacket (serviceGraph setup .concurrent)))
    (firstSupported : (mix waiting.val waiting.property.1 waiting.property.2
      (PMF.pure none) (PMF.pure (some first))) packet ≠ 0)
    (secondSupported : (mix waiting.val waiting.property.1 waiting.property.2
      (PMF.pure none) (PMF.pure (some second))) packet ≠ 0) :
    (mix waiting.val waiting.property.1 waiting.property.2
      (PMF.pure none) (PMF.pure (some first))) packet =
      (mix waiting.val waiting.property.1 waiting.property.2
      (PMF.pure none) (PMF.pure (some second))) packet := by
  rw [opening_packet_atom setup waiting first packet firstSupported,
    opening_packet_atom setup waiting second packet secondSupported]

/-- The actual fixed-tape environmental row atom is determined by consecutive
mechanical projections. It retains the literal recorded command. -/
theorem mechanicalStepAtom_environment (rates : PhaseProposalRates) (who : Player)
    (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    (first second : (nativeApplication).Control)
    (idle : first.actor = none)
    (firstAfter secondAfter : (nativeProtocol).State)
    (firstJoint secondJoint : Player → Option (nativeApplication).Action)
    (same : mechanicalProjection setup implementation who (some first) =
      mechanicalProjection setup implementation who (some second))
    (next : mechanicalProjection setup implementation who firstAfter =
      mechanicalProjection setup implementation who secondAfter) :
    mechanicalStepAtom setup implementation rates who tape (some first) firstAfter firstJoint =
      mechanicalStepAtom setup implementation rates who tape (some second) secondAfter
        secondJoint := by
  obtain ⟨remaining, actors, _views, _recall⟩ := mechanicalProjection_environment setup
    implementation
    who first second same
  have secondIdle : second.actor = none := actors.symm.trans idle
  have law := mechanicalProjection_tape_family setup implementation who first second same tape
  simp only [mechanicalStepAtom, idle, secondIdle]
  rw [remaining]
  by_cases exhausted : second.remaining = 0
  · simp only [exhausted, ↓reduceIte]
  · simp only [exhausted, ↓reduceIte]
    cases firstAfter with
    | none =>
        cases secondAfter with
        | none => rfl
        | some later => simp only [mechanicalProjection, Option.map_none, Option.map_some,
            reduceCtorEq] at next
    | some later =>
        cases secondAfter with
        | none => simp only [mechanicalProjection, Option.map_none, Option.map_some,
            reduceCtorEq] at next
        | some other =>
            have recalled := (mechanicalProjection_environment setup implementation who later other
              next).2.2.2
            dsimp only
            rw [recalled, law]

private theorem mechanicalForeignPolicy_covered (rates : PhaseProposalRates)
    (owner : Player) (past : List (nativeApplication).PlayerEntry)
    (view : (nativeApplication).PlayerView) (response : (nativeApplication).Action)
    (supported : response ∈
      (mechanicalForeignPolicy setup implementation rates owner past view).support) :
    response ∈ PhaseCount.onePacketActions implementation.runtime implementation.leaks
      implementation.bounds owner past view := by
  unfold mechanicalForeignPolicy at supported
  refine phasePolicyDispatch_covered setup .concurrent implementation.runtime implementation.leaks
    implementation.bounds _ ?_ _ ?_ owner past view response supported
  · intro actor event payload binding before observed action offered
    exact PhaseCount.phaseOpeningPolicy_covered implementation.runtime implementation.leaks
      implementation.bounds actor event payload binding _ before observed action offered
  · intro actor event payload _binding before observed action offered
    rcases support_mix_subset _ _ _ _ _ offered with silent | sending
    · cases (PMF.mem_support_pure_iff _ _).mp silent
      exact PhaseCount.silence_onePacket implementation.runtime implementation.leaks
        implementation.bounds actor before observed
    · exact PhaseCount.bindingResultEncoder_covered implementation.runtime implementation.leaks
        implementation.bounds actor event payload _ rates.slots.val rates.slots.property.1
          rates.slots.property.2 before observed action sending

theorem mechanicalForeignPolicy_packet_eq_base (rates : PhaseProposalRates)
    (owner : Player) (past : List (nativeApplication).PlayerEntry)
    (view : (nativeApplication).PlayerView) :
    (mechanicalForeignPolicy setup implementation rates owner past view).map
        (fun response => response.transmission.map fun material =>
          (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
            past view material).payload) =
      (phaseProposalBasePolicy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner past view).map
        (fun response => response.transmission.map fun material =>
          (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
            past view material).payload) := by
  classical
  unfold mechanicalForeignPolicy phaseProposalBasePolicy phasePolicyDispatch
  cases selected : requestedEvent setup .concurrent owner view.application.2 with
  | none => rfl
  | some event =>
      cases node : nodeView (serviceGraph setup .concurrent) event with
      | bind actor payload binding code =>
          simp only [eventPolicyDispatch, node]
          split
          · rename_i owned
            subst actor
            rw [mix_map, mix_map,
              PhaseCount.bindingResultEncoder_packet_congr implementation.runtime
                implementation.leaks implementation.bounds]
          · rfl
      | resolve actor payload binding checks output code =>
          simp only [eventPolicyDispatch, node]
      | sample payload law output code =>
          simp only [eventPolicyDispatch, node]

theorem mechanicalForeignPolicy_packet_supported
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (remaining : Nat) (owner : Player) (execution : (nativeApplication).Execution)
    (trace : (nativeProtocol).Trace (some ⟨remaining, some owner, execution⟩))
    (response : (nativeApplication).Action)
    (available : response ∈ PhaseCount.onePacketActions implementation.runtime
      implementation.leaks implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner)) :
    ((mechanicalForeignPolicy setup implementation rates owner (execution.recall owner)
      (execution.observe nativeApplication owner)).map
        (fun action => action.transmission.map fun material =>
          (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
            (execution.recall owner) (execution.observe nativeApplication owner) material).payload))
      (response.transmission.map fun material =>
        (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
          (execution.recall owner) (execution.observe nativeApplication owner)
            material).payload) ≠ 0 := by
  classical
  rw [mechanicalForeignPolicy_packet_eq_base setup values implementation]
  let chosen : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner) := ⟨response, available⟩
  have full := phaseProposalBaseClasses_fullSupport_of_counted setup .concurrent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan
    operational.completePending operational.outputValues operational.maximalPhases values
    fullValues rates waitPositive waitBelow slotPositive badPositive badBelow
    implementation.horizon implementation.scheduler remaining owner execution trace
  have selected := full (PhaseProposal.projectResponse implementation.runtime implementation.leaks
    implementation.bounds owner (execution.recall owner)
      (execution.observe nativeApplication owner) chosen)
  have projected :
      (PhaseProposal.projectResponse implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner) chosen).val.2 ∈
      ((phaseProposalBaseClasses setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner (execution.recall owner)
          (execution.observe nativeApplication owner)).map (fun choice => choice.val.2)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨_, selected, rfl⟩
  have marginal :
      (phaseProposalBaseClasses setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner (execution.recall owner)
          (execution.observe nativeApplication owner)).map (fun choice => choice.val.2) =
      (phaseProposalBasePolicy setup .concurrent implementation.runtime implementation.leaks
        implementation.bounds implementation.plan values rates owner (execution.recall owner)
          (execution.observe nativeApplication owner)).map
        (fun action => action.transmission.map fun material =>
          (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
            (execution.recall owner) (execution.observe nativeApplication owner)
              material).payload) := by
    rw [phaseProposalBaseClasses, PMF.map_comp,
      ← phaseProposalBaseResponses_map_val setup .concurrent implementation.runtime
        implementation.leaks implementation.bounds implementation.plan values rates owner
          (execution.recall owner) (execution.observe nativeApplication owner), PMF.map_comp]
    rfl
  rw [marginal] at projected
  exact (PMF.mem_support_iff _ _).mp projected

/-- Equal mechanical inputs retain the public request, every owner's submitted
word, and the physical fresh-slot predicates. -/
theorem mechanicalProjection_foreign_input (who owner : Player)
    (first second : (nativeApplication).Control)
    (firstTrace : (nativeProtocol).Trace (some first))
    (secondTrace : (nativeProtocol).Trace (some second))
    (same : mechanicalProjection setup implementation who (some first) =
      mechanicalProjection setup implementation who (some second)) :
    first.execution.application.publicView = second.execution.application.publicView ∧
      (nativeApplication).outputs (first.execution.recall owner) =
        (nativeApplication).outputs (second.execution.recall owner) ∧
      (∀ serial,
        first.execution.application.current.native.candidates.lookup (owner, .prepared serial) =
          .fresh ↔
        second.execution.application.current.native.candidates.lookup (owner, .prepared serial) =
          .fresh) := by
  have projection := same
  simp only [mechanicalProjection, Option.map_some, Option.some.injEq, Prod.mk.injEq] at projection
  obtain ⟨_remaining, _actor, application, network, _receipts, _focal, fresh, _recall, _own⟩ :=
    projection
  refine ⟨application, ?_, ?_⟩
  · rw [← (nativeApplication).history_inputRecall nativeInitial implementation.horizon
        implementation.scheduler ((nativeMenu).toRawTrace nativeInitial implementation.horizon
          implementation.scheduler firstTrace) owner,
      ← (nativeApplication).history_inputRecall nativeInitial implementation.horizon
        implementation.scheduler ((nativeMenu).toRawTrace nativeInitial implementation.horizon
          implementation.scheduler secondTrace) owner]
    exact congrArg (fun view : MessageNetwork.PublicView Player
      (CommitAttemptPacket (serviceGraph setup .concurrent)) =>
        view.inputs.filter fun message => decide (message.sender = owner)) network
  · intro serial
    exact decide_eq_decide.mp (congrFun (congrFun fresh owner) serial)

private theorem mechanical_binding_packet_law_eq
    (operational : implementation.Operational) (rates : PhaseProposalRates)
    (who owner : Player) (first second : (nativeApplication).Control)
    (firstTrace : (nativeProtocol).Trace (some first))
    (secondTrace : (nativeProtocol).Trace (some second))
    (firstActive : first.actor = some owner) (_secondActive : second.actor = some owner)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (firstRequest : first.execution.application.SeedRequest owner
      ⟨first.execution.application.attempt, event⟩)
    (secondRequest : second.execution.application.SeedRequest owner
      ⟨second.execution.application.attempt, event⟩)
    (firstUnsent : ∀ message ∈ (nativeApplication).outputs (first.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨first.execution.application.attempt, event⟩)
    (secondUnsent : ∀ message ∈ (nativeApplication).outputs (second.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨second.execution.application.attempt, event⟩)
    (same : mechanicalProjection setup implementation who (some first) =
      mechanicalProjection setup implementation who (some second)) :
    (PhaseCount.bindingResultEncoder implementation.runtime implementation.leaks
      implementation.bounds owner event payload (fun _ _ => PMF.pure .failure)
      rates.slots.val rates.slots.property.1 rates.slots.property.2
      (first.execution.recall owner) (first.execution.observe nativeApplication owner)).map
        (fun response => response.transmission.map fun material =>
          (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
            (first.execution.recall owner)
              (first.execution.observe nativeApplication owner) material).payload) =
    (PhaseCount.bindingResultEncoder implementation.runtime implementation.leaks
      implementation.bounds owner event payload (fun _ _ => PMF.pure .failure)
      rates.slots.val rates.slots.property.1 rates.slots.property.2
      (second.execution.recall owner) (second.execution.observe nativeApplication owner)).map
        (fun response => response.transmission.map fun material =>
          (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
            (second.execution.recall owner)
              (second.execution.observe nativeApplication owner) material).payload) := by
  classical
  let inputs := setup.initialLaw.map encodeInputs
  have initial : inputs.map (PhaseRuntimeState.initial implementation.plan) = nativeInitial := by
    rw [PMF.map_comp]; rfl
  obtain ⟨publicEq, _outputs, fresh⟩ := mechanicalProjection_foreign_input setup implementation
    who owner first second firstTrace secondTrace same
  have boundedValues := operational.outputValues event
  rw [binding] at boundedValues
  have firstSlots := PhaseCount.phaseBindingSlots_eq_fresh_of_history implementation.runtime
    implementation.leaks implementation.bounds nativeMenu implementation.plan inputs
    implementation.horizon implementation.scheduler first (initial ▸ firstTrace)
    owner event payload binding firstRequest firstUnsent boundedValues
  have secondSlots := PhaseCount.phaseBindingSlots_eq_fresh_of_history implementation.runtime
    implementation.leaks implementation.bounds nativeMenu implementation.plan inputs
    implementation.horizon implementation.scheduler second (initial ▸ secondTrace)
    owner event payload binding secondRequest secondUnsent boundedValues
  have slots : PhaseCount.phaseBindingSlots implementation.runtime implementation.leaks
      implementation.bounds owner event payload (first.execution.recall owner)
        (first.execution.observe nativeApplication owner) =
    PhaseCount.phaseBindingSlots implementation.runtime implementation.leaks
      implementation.bounds owner event payload (second.execution.recall owner)
        (second.execution.observe nativeApplication owner) := by
    rw [firstSlots, secondSlots]
    exact Finset.filter_congr fun serial _ => fresh serial
  have packet (serial : Nat) :
      (phaseBindingResponse implementation.runtime implementation.leaks owner event payload
        .failure serial).transmission.map (fun material =>
          (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
            (first.execution.recall owner)
              (first.execution.observe nativeApplication owner) material).payload) =
      (phaseBindingResponse implementation.runtime implementation.leaks owner event payload
        .failure serial).transmission.map (fun material =>
          (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
            (second.execution.recall owner)
              (second.execution.observe nativeApplication owner) material).payload) := by
    change some (⟨first.execution.application.publicView.attempt,
        PhaseCount.maskPacket first.execution.application.publicView
          ⟨.commitment event (owner, .prepared serial), none,
            first.execution.application.publicView.native.tokenFor
              (.commitment event (owner, .prepared serial))⟩⟩ :
                CommitAttemptPacket (serviceGraph setup .concurrent)) = _
    rw [publicEq]
    rfl
  have slotLaw :
      (PhaseCount.phaseBindingSlotPolicy implementation.runtime implementation.leaks
        implementation.bounds owner event payload (fun _ _ => PMF.pure .failure)
        (first.execution.recall owner) (first.execution.observe nativeApplication owner)).map
        (fun response => response.transmission.map fun material =>
          (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
            (first.execution.recall owner)
              (first.execution.observe nativeApplication owner) material).payload) =
      (PhaseCount.phaseBindingSlotPolicy implementation.runtime implementation.leaks
        implementation.bounds owner event payload (fun _ _ => PMF.pure .failure)
        (second.execution.recall owner) (second.execution.observe nativeApplication owner)).map
        (fun response => response.transmission.map fun material =>
          (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
            (second.execution.recall owner)
              (second.execution.observe nativeApplication owner) material).payload) := by
    unfold PhaseCount.phaseBindingSlotPolicy
    rw [slots]
    split
    · rw [PMF.map_bind, PMF.map_bind]
      apply bind_congr_on_support
      intro serial _
      simp only [PMF.pure_map]
      rw [packet]
    · simp only [PMF.pure_map, Option.map_none]
  have allocator := reactiveFreshSlot_congr
    (first.execution.observe nativeApplication owner).application.1
    (second.execution.observe nativeApplication owner).application.1 fresh
  have firstSelected := PhaseCandidates.reactiveFreshSlot_lt_horizon implementation.runtime
    implementation.leaks implementation.plan inputs implementation.horizon implementation.scheduler
    first ((nativeMenu).toRawTrace _ _ _ (initial ▸ firstTrace)) owner firstActive
  have canonicalLaw :
      (PhaseCount.phaseBindingPolicy implementation.runtime implementation.leaks
        implementation.bounds owner event payload (fun _ _ => PMF.pure .failure)
        (first.execution.recall owner) (first.execution.observe nativeApplication owner)).map
        (fun response => response.transmission.map fun material =>
          (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
            (first.execution.recall owner)
              (first.execution.observe nativeApplication owner) material).payload) =
      (PhaseCount.phaseBindingPolicy implementation.runtime implementation.leaks
        implementation.bounds owner event payload (fun _ _ => PMF.pure .failure)
        (second.execution.recall owner) (second.execution.observe nativeApplication owner)).map
        (fun response => response.transmission.map fun material =>
          (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
            (second.execution.recall owner)
              (second.execution.observe nativeApplication owner) material).payload) := by
    obtain ⟨serial, _bounded, selected⟩ := firstSelected
    have secondSelected : reactiveFreshSlot
        (second.execution.observe nativeApplication owner).application.1 = some serial :=
      allocator.symm.trans selected
    have firstMember : serial ∈ PhaseCount.phaseBindingSlots implementation.runtime
        implementation.leaks implementation.bounds owner event payload
        (first.execution.recall owner) (first.execution.observe nativeApplication owner) := by
      rw [firstSlots]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (_bounded.trans_le operational.candidateReserve),
        reactiveFreshSlot_spec _ serial selected⟩
    have secondMember := slots ▸ firstMember
    have firstCovered := (Finset.mem_filter.mp firstMember).2.2
    have secondCovered := (Finset.mem_filter.mp secondMember).2.2
    unfold PhaseCount.phaseBindingPolicy
    simp only [selected, secondSelected, ite_eq_left firstCovered,
      ite_eq_left secondCovered, PMF.pure_map]
    rw [packet]
  unfold PhaseCount.bindingResultEncoder
  rw [mix_map, mix_map, slotLaw, canonicalLaw]

private theorem ready_opening_binding_value
    (operational : implementation.Operational)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control)) (owner : Player)
    (good : ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
      implementation.leaks implementation.bounds nativeInitial implementation.horizon
        implementation.scheduler owner ⟨some control, trace⟩)
    (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup .concurrent).layout (.binding owner payload))
    (candidate : Handle (serviceGraph setup .concurrent))
    (accepted : control.execution.application.current.native.accepted binding.field =
      some candidate) :
    ∃ value : L.Val payload, binding.get?
      control.execution.application.current.native.config.store = some (.success value) := by
  classical
  obtain ⟨theta, drawn, native, _source⟩ := checkpointSelection_initializer setup implementation
    operational control trace
  cases field : binding.field with
  | inl input =>
      exact input_binding_value setup .concurrent operational.wellFormed theta drawn
        control.execution.application.current.native.config.store
        (fun input => by
          rw [EventGraph.Config.store_input, native.active.reachable.inputs_eq])
        owner payload binding input field
  | inr prior =>
      have typed : (serviceGraph setup .concurrent).outputLayout prior = .binding owner payload
        := by
        have typed := binding.layout_eq
        rw [field] at typed
        exact typed
      obtain ⟨value, successful⟩ := accepted_snapshot_value_of_no_generated_unusable setup
        implementation control trace control.execution.application.current.native (Or.inl rfl)
          owner good prior payload typed candidate (field ▸ accepted)
      have bindings := phaseBindingRecord_history implementation.runtime implementation.leaks
        implementation.plan (setup.initialLaw.map encodeInputs) implementation.horizon
        implementation.scheduler (by
          rw [PMF.map_comp]
          exact (nativeMenu).toRawTrace nativeInitial implementation.horizon
            implementation.scheduler trace)
      have present := binding.get?_isSome _
        (bindings.active.accepted_present binding.field candidate accepted)
      obtain ⟨result, stored⟩ := Option.isSome_iff_exists.mp present
      have meaning := bindings.active.binding_value binding result stored
      rw [accepted, Option.elim_some, successful] at meaning
      exact ⟨value, stored.trans (congrArg some meaning)⟩

private theorem mechanicalForeignAtom_eq
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (who owner : Player) (firstRemaining secondRemaining : Nat)
    (first second : (nativeApplication).Execution)
    (firstTrace : (nativeProtocol).Trace (some ⟨firstRemaining, some owner, first⟩))
    (secondTrace : (nativeProtocol).Trace (some ⟨secondRemaining, some owner, second⟩))
    (firstGood : ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
      implementation.leaks implementation.bounds nativeInitial implementation.horizon
        implementation.scheduler owner ⟨_, firstTrace⟩)
    (secondGood : ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
      implementation.leaks implementation.bounds nativeInitial implementation.horizon
        implementation.scheduler owner ⟨_, secondTrace⟩)
    (firstResponse secondResponse : (nativeApplication).Action)
    (firstAvailable : firstResponse ∈ PhaseCount.onePacketActions implementation.runtime
      implementation.leaks implementation.bounds owner (first.recall owner)
        (first.observe nativeApplication owner))
    (secondAvailable : secondResponse ∈ PhaseCount.onePacketActions implementation.runtime
      implementation.leaks implementation.bounds owner (second.recall owner)
        (second.observe nativeApplication owner))
    (same : mechanicalProjection setup implementation who
        (some ⟨firstRemaining, some owner, first⟩) =
      mechanicalProjection setup implementation who (some ⟨secondRemaining, some owner, second⟩))
    (packetEq : firstResponse.transmission.map (fun material =>
        (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
          (first.recall owner) (first.observe nativeApplication owner) material).payload) =
      secondResponse.transmission.map (fun material =>
        (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
          (second.recall owner) (second.observe nativeApplication owner) material).payload)) :
    foreignMechanicalAtom setup implementation rates first owner firstResponse =
      foreignMechanicalAtom setup implementation rates second owner secondResponse := by
  classical
  let inputs := setup.initialLaw.map encodeInputs
  have initial : inputs.map (PhaseRuntimeState.initial implementation.plan) = nativeInitial := by
    rw [PMF.map_comp]; rfl
  obtain ⟨publicEq, outputs, _fresh⟩ := mechanicalProjection_foreign_input setup implementation
    who owner _ _ firstTrace secondTrace same
  obtain ⟨_theta, _drawn, firstNative, _source⟩ := checkpointSelection_initializer setup
    implementation operational _ firstTrace
  obtain ⟨_theta, _drawn, secondNative, _source⟩ := checkpointSelection_initializer setup
    implementation operational _ secondTrace
  let firstPacket := fun response : (nativeApplication).Action =>
    response.transmission.map fun material =>
      (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
        (first.recall owner) (first.observe nativeApplication owner) material).payload
  let secondPacket := fun response : (nativeApplication).Action =>
    response.transmission.map fun material =>
      (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
        (second.recall owner) (second.observe nativeApplication owner) material).payload
  have firstSupported := mechanicalForeignPolicy_packet_supported setup values implementation
    operational fullValues rates waitPositive waitBelow slotPositive badPositive badBelow
    firstRemaining owner first firstTrace firstResponse firstAvailable
  have secondSupported := mechanicalForeignPolicy_packet_supported setup values implementation
    operational fullValues rates waitPositive waitBelow slotPositive badPositive badBelow
    secondRemaining owner second secondTrace secondResponse secondAvailable
  have silent (execution : (nativeApplication).Execution)
      (singleton : PhaseCount.onePacketActions implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner) = {⟨none⟩}) :
      mechanicalForeignPolicy setup implementation rates owner (execution.recall owner)
        (execution.observe nativeApplication owner) = PMF.pure ⟨none⟩ := by
    apply pmf_eq_pure_of_support_subset_singleton
    intro response supported
    exact Finset.mem_singleton.mp (singleton ▸ mechanicalForeignPolicy_covered setup
      implementation rates owner _ _ response supported)
  have silenceAtom
      (firstSilent : mechanicalForeignPolicy setup implementation rates owner
        (first.recall owner) (first.observe nativeApplication owner) = PMF.pure ⟨none⟩)
      (secondSilent : mechanicalForeignPolicy setup implementation rates owner
        (second.recall owner) (second.observe nativeApplication owner) = PMF.pure ⟨none⟩) :
      ((mechanicalForeignPolicy setup implementation rates owner (first.recall owner)
        (first.observe nativeApplication owner)).map firstPacket) (firstPacket firstResponse) =
      ((mechanicalForeignPolicy setup implementation rates owner (second.recall owner)
        (second.observe nativeApplication owner)).map secondPacket) (secondPacket
          secondResponse) := by
    rw [firstSilent, secondSilent, PMF.pure_map, PMF.pure_map]
    change (PMF.pure (none : Option (CommitAttemptPacket (serviceGraph setup .concurrent))))
        (firstPacket firstResponse) =
      (PMF.pure (none : Option (CommitAttemptPacket (serviceGraph setup .concurrent))))
        (secondPacket secondResponse)
    exact congrArg (fun packet =>
      (PMF.pure (none : Option (CommitAttemptPacket (serviceGraph setup .concurrent)))) packet)
        (show firstPacket firstResponse = secondPacket secondResponse from packetEq)
  have packetAtom :
      ((mechanicalForeignPolicy setup implementation rates owner (first.recall owner)
        (first.observe nativeApplication owner)).map firstPacket) (firstPacket firstResponse) =
      ((mechanicalForeignPolicy setup implementation rates owner (second.recall owner)
        (second.observe nativeApplication owner)).map secondPacket) (secondPacket
          secondResponse) := by
    by_cases absent : ∀ coordinate, ¬ first.application.SeedRequest owner coordinate
    · have secondAbsent : ∀ coordinate, ¬ second.application.SeedRequest owner coordinate := by
        intro coordinate requested
        apply absent coordinate
        apply (first.application.requests_publicView firstNative owner coordinate).mp
        rw [publicEq]
        exact (second.application.requests_publicView secondNative owner coordinate).mpr requested
      have firstSingleton := PhaseCount.onePacketActions_eq_singleton_of_no_request
        implementation.runtime implementation.leaks implementation.bounds implementation.plan
        inputs implementation.horizon implementation.scheduler firstRemaining owner first
        (initial ▸ firstTrace) absent
      have secondSingleton := PhaseCount.onePacketActions_eq_singleton_of_no_request
        implementation.runtime implementation.leaks implementation.bounds implementation.plan
        inputs implementation.horizon implementation.scheduler secondRemaining owner second
        (initial ▸ secondTrace) secondAbsent
      exact silenceAtom (silent first firstSingleton) (silent second secondSingleton)
    obtain ⟨coordinate, requested⟩ := not_forall.mp absent
    have firstRequest := not_not.mp requested
    rcases coordinate with ⟨attempt, event⟩
    have actual := firstRequest.1
    change attempt = first.application.attempt at actual
    subst attempt
    have attemptEq : first.application.attempt = second.application.attempt :=
      congrArg PhasePublicView.attempt publicEq
    have secondRequest : second.application.SeedRequest owner
        ⟨second.application.attempt, event⟩ := by
      apply (second.application.requests_publicView secondNative owner _).mp
      rw [← attemptEq, ← publicEq]
      exact (first.application.requests_publicView firstNative owner _).mpr firstRequest
    by_cases unsent : ∀ message ∈ (nativeApplication).outputs (first.recall owner),
        PhaseCount.event? message.payload ≠ some ⟨first.application.attempt, event⟩
    · have secondUnsent : ∀ message ∈ (nativeApplication).outputs (second.recall owner),
          PhaseCount.event? message.payload ≠ some ⟨second.application.attempt, event⟩ := by
        rw [← outputs, ← attemptEq]
        exact unsent
      cases node : nodeView (serviceGraph setup .concurrent) event with
      | bind actor payload binding code =>
          have owned : actor = owner := Option.some.inj
            (((serviceGraph setup .concurrent).actor?_of_outputLayout_binding binding).symm.trans
              firstRequest.2.2.2.1)
          subst actor
          have firstLaw : mechanicalForeignPolicy setup implementation rates owner
              (first.recall owner) (first.observe nativeApplication owner) =
            mix rates.waiting.val rates.waiting.property.1 rates.waiting.property.2
              (PMF.pure ⟨none⟩)
              (PhaseCount.bindingResultEncoder implementation.runtime implementation.leaks
                implementation.bounds owner event payload (fun _ _ => PMF.pure .failure)
                  rates.slots.val rates.slots.property.1 rates.slots.property.2
                    (first.recall owner) (first.observe nativeApplication owner)) := by
            unfold mechanicalForeignPolicy
            exact phasePolicyDispatch_binding setup .concurrent implementation.runtime
              implementation.leaks _ _ first firstNative owner event payload binding firstRequest
          have secondLaw : mechanicalForeignPolicy setup implementation rates owner
              (second.recall owner) (second.observe nativeApplication owner) =
            mix rates.waiting.val rates.waiting.property.1 rates.waiting.property.2
              (PMF.pure ⟨none⟩)
              (PhaseCount.bindingResultEncoder implementation.runtime implementation.leaks
                implementation.bounds owner event payload (fun _ _ => PMF.pure .failure)
                  rates.slots.val rates.slots.property.1 rates.slots.property.2
                    (second.recall owner) (second.observe nativeApplication owner)) := by
            unfold mechanicalForeignPolicy
            exact phasePolicyDispatch_binding setup .concurrent implementation.runtime
              implementation.leaks _ _ second secondNative owner event payload binding secondRequest
          rw [firstLaw, secondLaw, mix_map, mix_map]
          have encoder := mechanical_binding_packet_law_eq setup implementation operational rates
            who owner _ _ firstTrace secondTrace rfl rfl event payload binding firstRequest
              secondRequest unsent secondUnsent same
          rw [encoder]
          have silenceEq : (PMF.pure (⟨none⟩ : (nativeApplication).Action)).map firstPacket =
              (PMF.pure (⟨none⟩ : (nativeApplication).Action)).map secondPacket := by
            rw [PMF.pure_map, PMF.pure_map]
            rfl
          rw [silenceEq,
            show firstPacket firstResponse = secondPacket secondResponse from packetEq]
      | resolve actor payload binding checks output code =>
          have owned : actor = owner := by
            have actorEq := firstRequest.2.2.2.1
            change (((serviceGraph setup .concurrent).nodes event).actor) = _ at actorEq
            rw [← EventCode.actor_cast output ((serviceGraph setup .concurrent).nodes event),
              code] at actorEq
            exact Option.some.inj actorEq
          subst actor
          let opens := fun (_ : List (nativeApplication).PlayerEntry)
              (_ : (nativeApplication).PlayerView) =>
            mix rates.waiting.val rates.waiting.property.1 rates.waiting.property.2
              (PMF.pure false) (PMF.pure true)
          have firstOpening : mechanicalForeignPolicy setup implementation rates owner
              (first.recall owner) (first.observe nativeApplication owner) =
            PhaseCount.phaseOpeningPolicy implementation.runtime implementation.leaks
              implementation.bounds owner event payload binding opens
                (first.recall owner) (first.observe nativeApplication owner) := by
            unfold mechanicalForeignPolicy
            exact phasePolicyDispatch_opening setup .concurrent implementation.runtime
              implementation.leaks _ _ first firstNative owner event payload binding checks output
                code firstRequest
          have secondOpening : mechanicalForeignPolicy setup implementation rates owner
              (second.recall owner) (second.observe nativeApplication owner) =
            PhaseCount.phaseOpeningPolicy implementation.runtime implementation.leaks
              implementation.bounds owner event payload binding opens
                (second.recall owner) (second.observe nativeApplication owner) := by
            unfold mechanicalForeignPolicy
            exact phasePolicyDispatch_opening setup .concurrent implementation.runtime
              implementation.leaks _ _ second secondNative owner event payload binding checks output
                code secondRequest
          cases accepted : first.application.current.native.accepted binding.field with
          | none =>
              have secondAccepted : second.application.current.native.accepted binding.field =
                  none := by
                have projected := congrArg (fun view => view.native.accepted binding.field) publicEq
                exact projected.symm.trans accepted
              have firstSilent : mechanicalForeignPolicy setup implementation rates owner
                  (first.recall owner) (first.observe nativeApplication owner) = PMF.pure ⟨none⟩
                    := by
                rw [firstOpening]
                unfold PhaseCount.phaseOpeningPolicy
                have observedAccepted :
                    (first.observe nativeApplication owner).application.1.publicView.accepted
                      binding.field = none := accepted
                rw [observedAccepted]
                cases stored : binding.get?
                    (first.observe nativeApplication owner).application.1.observation.store with
                | none => rfl
                | some result => cases result <;> rfl
              have secondSilent : mechanicalForeignPolicy setup implementation rates owner
                  (second.recall owner) (second.observe nativeApplication owner) = PMF.pure
                    ⟨none⟩ := by
                rw [secondOpening]
                unfold PhaseCount.phaseOpeningPolicy
                have observedAccepted :
                    (second.observe nativeApplication owner).application.1.publicView.accepted
                      binding.field = none := secondAccepted
                rw [observedAccepted]
                cases stored : binding.get?
                    (second.observe nativeApplication owner).application.1.observation.store with
                | none => rfl
                | some result => cases result <;> rfl
              exact silenceAtom firstSilent secondSilent
          | some candidate =>
              have secondAccepted : second.application.current.native.accepted binding.field =
                  some candidate := by
                have projected := congrArg (fun view => view.native.accepted binding.field) publicEq
                exact projected.symm.trans accepted
              obtain ⟨firstValue, firstStored⟩ := ready_opening_binding_value setup implementation
                operational _ firstTrace owner firstGood payload binding candidate accepted
              obtain ⟨secondValue, secondStored⟩ := ready_opening_binding_value setup implementation
                operational _ secondTrace owner secondGood payload binding candidate secondAccepted
              obtain ⟨firstCandidate, _firstAccepted, firstOpened⟩ :=
                PhaseCount.phaseOpeningPolicy_of_history implementation.runtime implementation.leaks
                  implementation.bounds implementation.plan inputs implementation.horizon
                  implementation.scheduler (initial ▸ firstTrace) owner event payload binding checks
                  output code node firstRequest unsent firstValue firstStored
                  (by
                    have bounded := operational.outputValues event
                    rw [output] at bounded
                    exact bounded firstValue) opens
              obtain ⟨secondCandidate, _secondAccepted', secondOpened⟩ :=
                PhaseCount.phaseOpeningPolicy_of_history implementation.runtime implementation.leaks
                  implementation.bounds implementation.plan inputs implementation.horizon
                  implementation.scheduler (initial ▸ secondTrace) owner event payload binding
                    checks
                  output code node secondRequest secondUnsent secondValue secondStored
                  (by
                    have bounded := operational.outputValues event
                    rw [output] at bounded
                    exact bounded secondValue) opens
              have firstMixture :
                  (opens (first.recall owner) (first.observe nativeApplication owner)).map
                    (fun disclose => firstPacket (if disclose then
                      PhaseCount.phaseOpeningResponse implementation.runtime implementation.leaks
                        event firstCandidate ⟨payload, firstValue⟩ else ⟨none⟩)) =
                  mix rates.waiting.val rates.waiting.property.1 rates.waiting.property.2
                    (PMF.pure none) (PMF.pure (firstPacket
                      (PhaseCount.phaseOpeningResponse implementation.runtime implementation.leaks
                        event firstCandidate ⟨payload, firstValue⟩))) := by
                simp only [opens, mix_map, PMF.pure_map, Bool.false_eq_true, ↓reduceIte]
                rfl
              have secondMixture :
                  (opens (second.recall owner) (second.observe nativeApplication owner)).map
                    (fun disclose => secondPacket (if disclose then
                      PhaseCount.phaseOpeningResponse implementation.runtime implementation.leaks
                        event secondCandidate ⟨payload, secondValue⟩ else ⟨none⟩)) =
                  mix rates.waiting.val rates.waiting.property.1 rates.waiting.property.2
                    (PMF.pure none) (PMF.pure (secondPacket
                      (PhaseCount.phaseOpeningResponse implementation.runtime implementation.leaks
                        event secondCandidate ⟨payload, secondValue⟩))) := by
                simp only [opens, mix_map, PMF.pure_map, Bool.false_eq_true, ↓reduceIte]
                rfl
              have firstMarginal :
                  (mechanicalForeignPolicy setup implementation rates owner
                    (first.recall owner) (first.observe nativeApplication owner)).map firstPacket =
                  mix rates.waiting.val rates.waiting.property.1 rates.waiting.property.2
                    (PMF.pure none) (PMF.pure (firstPacket
                      (PhaseCount.phaseOpeningResponse implementation.runtime implementation.leaks
                        event firstCandidate ⟨payload, firstValue⟩))) := by
                rw [firstOpening, firstOpened, PMF.map_comp]
                simpa only [Function.comp_def] using firstMixture
              have secondMarginal :
                  (mechanicalForeignPolicy setup implementation rates owner
                    (second.recall owner) (second.observe nativeApplication owner)).map
                      secondPacket =
                  mix rates.waiting.val rates.waiting.property.1 rates.waiting.property.2
                    (PMF.pure none) (PMF.pure (secondPacket
                      (PhaseCount.phaseOpeningResponse implementation.runtime implementation.leaks
                        event secondCandidate ⟨payload, secondValue⟩))) := by
                rw [secondOpening, secondOpened, PMF.map_comp]
                simpa only [Function.comp_def] using secondMixture
              change ((mechanicalForeignPolicy setup implementation rates owner
                (first.recall owner) (first.observe nativeApplication owner)).map firstPacket)
                  (firstPacket firstResponse) ≠ 0 at firstSupported
              change ((mechanicalForeignPolicy setup implementation rates owner
                (second.recall owner) (second.observe nativeApplication owner)).map secondPacket)
                  (secondPacket secondResponse) ≠ 0 at secondSupported
              rw [firstMarginal] at firstSupported ⊢
              rw [secondMarginal] at secondSupported ⊢
              have packets : firstPacket firstResponse = secondPacket secondResponse := packetEq
              rw [packets] at firstSupported ⊢
              exact opening_packet_atom_eq setup rates.waiting _ _ _ firstSupported secondSupported
      | sample payload law output code =>
          have actorEq := firstRequest.2.2.2.1
          change (((serviceGraph setup .concurrent).nodes event).actor) = _ at actorEq
          rw [← EventCode.actor_cast output ((serviceGraph setup .concurrent).nodes event),
            code] at actorEq
          cases actorEq
    · have singleton (remaining : Nat) (execution : (nativeApplication).Execution)
          (trace : (nativeProtocol).Trace (some ⟨remaining, some owner, execution⟩))
          (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
          (spent : ¬ ∀ message ∈ (nativeApplication).outputs (execution.recall owner),
            PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩) :
          PhaseCount.onePacketActions implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner) = {⟨none⟩} := by
        push Not at spent
        obtain ⟨message, output, named⟩ := spent
        have recalled := (nativeApplication).history_inputRecall nativeInitial
          implementation.horizon
          implementation.scheduler ((nativeMenu).toRawTrace _ _ _ trace) owner
        have owned : message.sender = owner := by
          rw [← recalled] at output
          exact of_decide_eq_true (List.mem_filter.mp output).2
        have fields : message.payload.attempt = execution.application.attempt ∧
            message.payload.packet.call.event? (serviceGraph setup .concurrent) = some event := by
          unfold PhaseCount.event? at named
          obtain ⟨actual, identified, paired⟩ := Option.map_eq_some_iff.mp named
          have sameAttempt := congrArg CommitAttemptEvent.attempt paired
          have sameEvent := congrArg CommitAttemptEvent.event paired
          exact ⟨sameAttempt, identified.trans (congrArg some sameEvent)⟩
        exact PhaseCount.onePacketActions_eq_singleton_of_sent implementation.runtime
          implementation.leaks implementation.bounds implementation.plan
          (serviceGraph_revealRelaxedOrdered setup .concurrent) inputs implementation.horizon
          implementation.scheduler remaining owner execution (initial ▸ trace)
          ⟨execution.application.attempt, event⟩ request
          ⟨message, output, by
            simpa only [PhaseSeedScheduler.ownPacket, decide_eq_true_eq] using
              (And.intro owned fields)⟩
      have secondSpent : ¬ ∀ message ∈ (nativeApplication).outputs (second.recall owner),
          PhaseCount.event? message.payload ≠ some ⟨second.application.attempt, event⟩ := by
        rw [← outputs, ← attemptEq]
        exact unsent
      have firstSingleton := singleton firstRemaining first firstTrace firstRequest unsent
      have secondSingleton := singleton secondRemaining second secondTrace secondRequest secondSpent
      exact silenceAtom (silent first firstSingleton) (silent second secondSingleton)
  have factor : (match firstResponse.transmission with
      | none => (1 : ℝ≥0∞)
      | some material => match material.call.packet with
        | .commitment .. => ENNReal.ofReal (1 - rates.badPreparation.val) | _ => 1) =
    (match secondResponse.transmission with
      | none => (1 : ℝ≥0∞)
      | some material => match material.call.packet with
        | .commitment .. => ENNReal.ofReal (1 - rates.badPreparation.val) | _ => 1) := by
    have calls := congrArg (Option.map fun packet => packet.packet.call) packetEq
    have read (execution : (nativeApplication).Execution) (material : WitnessedSubmission
        (serviceGraph setup .concurrent)) :
        (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
          (execution.recall owner) (execution.observe nativeApplication owner)
            material).payload.packet.call =
          material.call.packet := by
      simp only [PhaseCount.localEnvelope, PhaseCount.maskPacket]
      split <;> split <;> rfl
    simp only [Option.map_map, Function.comp_def, read] at calls
    let multiplier : Option (Payload (serviceGraph setup .concurrent)) → ℝ≥0∞
      | none => 1
      | some (.commitment ..) => ENNReal.ofReal (1 - rates.badPreparation.val)
      | some _ => 1
    have normalized (response : (nativeApplication).Action) :
        (match response.transmission with
          | none => (1 : ℝ≥0∞)
          | some material => match material.call.packet with
            | .commitment .. => ENNReal.ofReal (1 - rates.badPreparation.val) | _ => 1) =
        multiplier (response.transmission.map (fun material => material.call.packet)) := by
      cases response.transmission with
      | none => rfl
      | some material =>
          cases packet : material.call.packet <;>
            simp only [Option.map_some, multiplier, packet]
    rw [normalized, normalized]
    exact congrArg multiplier calls
  exact congrArg₂ (· * ·) packetAtom factor

private theorem no_generated_of_tracePrefix (owner : Player)
    {before after : (nativeProtocol).State}
    {prior : (nativeProtocol).Trace before} {trace : (nativeProtocol).Trace after}
    (retained : TracePrefix prior trace)
    (good : ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
      implementation.leaks implementation.bounds nativeInitial implementation.horizon
        implementation.scheduler owner ⟨after, trace⟩) :
    ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
      implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
        ⟨before, prior⟩ := by
  rintro ⟨record, member, unusable⟩
  apply good
  exact ⟨record, (((nativeMenu).information nativeInitial implementation.horizon
    implementation.scheduler).ownPlay_isSuffix_of_reachesWithin owner
      retained.reachesWithin).subset member, unusable⟩

private theorem mechanicalStepAtom_eq_of_projection
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (who : Player) (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    {firstBefore secondBefore firstAfter secondAfter : (nativeProtocol).State}
    (first : (nativeProtocol).Trace firstBefore)
    (second : (nativeProtocol).Trace secondBefore)
    (firstJoint secondJoint : Player → Option (nativeApplication).Action)
    (firstLegal : (nativeProtocol).Legal firstBefore firstJoint)
    (secondLegal : (nativeProtocol).Legal secondBefore secondJoint)
    (firstRealized : firstAfter ∈ ((nativeProtocol).step firstBefore
      ⟨firstJoint, firstLegal⟩).support)
    (secondRealized : secondAfter ∈ ((nativeProtocol).step secondBefore
      ⟨secondJoint, secondLegal⟩).support)
    (firstGood : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨firstBefore, first⟩)
    (secondGood : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨secondBefore, second⟩)
    (same : mechanicalProjection setup implementation who firstBefore =
      mechanicalProjection setup implementation who secondBefore)
    (next : mechanicalProjection setup implementation who firstAfter =
      mechanicalProjection setup implementation who secondAfter) :
    mechanicalStepAtom setup implementation rates who tape firstBefore firstAfter firstJoint =
      mechanicalStepAtom setup implementation rates who tape secondBefore secondAfter
        secondJoint := by
  cases firstBefore with
  | none =>
      cases secondBefore with
      | none => rfl
      | some second => simp only [mechanicalProjection, Option.map_none, Option.map_some,
          reduceCtorEq] at same
  | some firstControl =>
      cases secondBefore with
      | none => simp only [mechanicalProjection, Option.map_none, Option.map_some,
          reduceCtorEq] at same
      | some secondControl =>
          obtain ⟨_remaining, actors, _view, _recall⟩ := mechanicalProjection_environment setup
            implementation who firstControl secondControl same
          rcases firstControl with ⟨firstRemaining, firstActor, firstExecution⟩
          rcases secondControl with ⟨secondRemaining, secondActor, secondExecution⟩
          change firstActor = secondActor at actors
          subst secondActor
          cases firstActor with
          | none =>
              exact mechanicalStepAtom_environment setup implementation rates who tape
                _ _ rfl _ _ firstJoint secondJoint same next
          | some owner =>
              by_cases focal : owner = who
              · simp only [mechanicalStepAtom, focal, ↓reduceIte]
              · have firstChosenLegal := firstLegal.2 owner
                have secondChosenLegal := secondLegal.2 owner
                cases firstChosen : firstJoint owner with
                | none =>
                    rw [firstChosen] at firstChosenLegal
                    exact (firstChosenLegal rfl).elim
                | some firstResponse =>
                    cases secondChosen : secondJoint owner with
                    | none =>
                        rw [secondChosen] at secondChosenLegal
                        exact (secondChosenLegal rfl).elim
                    | some secondResponse =>
                        rw [firstChosen] at firstChosenLegal
                        rw [secondChosen] at secondChosenLegal
                        change firstAfter ∈ (PMF.pure (some ⟨firstRemaining, none,
                          firstExecution.respond nativeApplication owner
                            ((firstJoint owner).getD ⟨none⟩)⟩)).support at firstRealized
                        change secondAfter ∈ (PMF.pure (some ⟨secondRemaining, none,
                          secondExecution.respond nativeApplication owner
                            ((secondJoint owner).getD ⟨none⟩)⟩)).support at secondRealized
                        rw [firstChosen, Option.getD_some] at firstRealized
                        rw [secondChosen, Option.getD_some] at secondRealized
                        have firstAfterEq := (PMF.mem_support_pure_iff _ _).mp firstRealized
                        have secondAfterEq := (PMF.mem_support_pure_iff _ _).mp secondRealized
                        rw [firstAfterEq, secondAfterEq] at next
                        have packets := mechanicalProjection_response_packet setup implementation
                          who owner _ _ first second firstResponse secondResponse same next
                        simp only [mechanicalStepAtom, focal, ↓reduceIte, firstChosen, secondChosen]
                        exact mechanicalForeignAtom_eq setup values implementation operational
                          fullValues rates waitPositive waitBelow slotPositive badPositive badBelow
                          who owner firstRemaining secondRemaining firstExecution secondExecution
                          first second (firstGood owner focal) (secondGood owner focal)
                          firstResponse secondResponse firstChosenLegal.2 secondChosenLegal.2
                          same packets

theorem mechanicalWord_length (who : Player)
    {state : (nativeProtocol).State} (trace : (nativeProtocol).Trace state) :
    (mechanicalWord setup implementation who trace).length = trace.length + 1 := by
  induction trace with
  | start => rfl
  | extend prior joint legal realized ih =>
      simp only [mechanicalWord, List.length_append, List.length_singleton, Trace.length, ih]

/-- Chronological mechanical atoms depend only on the retained mechanical word
at genuine foreign-good histories. Private preparation and alias atoms are absent. -/
theorem mechanicalPathAtom_eq_of_word
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
    (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
    (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
    (who : Player) (tape : ReservedEpoch.Tape Player implementation.tapeLength)
    {firstState secondState : (nativeProtocol).State}
    (first : (nativeProtocol).Trace firstState)
    (second : (nativeProtocol).Trace secondState)
    (firstGood : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨firstState, first⟩)
    (secondGood : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨secondState, second⟩)
    (same : mechanicalWord setup implementation who first =
      mechanicalWord setup implementation who second) :
    mechanicalPathAtom setup implementation rates who tape first =
      mechanicalPathAtom setup implementation rates who tape second := by
  induction first generalizing secondState with
  | start =>
      cases second with
      | start => rfl
      | extend prior joint legal realized =>
          have length := congrArg List.length same
          simp only [mechanicalWord_length, Trace.length] at length
          omega
  | @extend before after prior joint legal realized ih =>
      cases second with
      | start =>
          have length := congrArg List.length same
          simp only [mechanicalWord_length, Trace.length] at length
          omega
      | @extend otherBefore otherAfter other otherJoint otherLegal otherRealized =>
          have length := congrArg List.length same
          simp only [mechanicalWord_length, Trace.length] at length
          have prefixLength : (mechanicalWord setup implementation who prior).length =
              (mechanicalWord setup implementation who other).length := by
            simp only [mechanicalWord_length]
            omega
          simp only [mechanicalWord] at same
          obtain ⟨samePrior, sameAfter⟩ := List.append_inj same prefixLength
          have projectedAfter := congrArg Subtype.val (List.singleton_inj.mp sameAfter)
          have last := congrArg List.getLast? samePrior
          rw [mechanicalWord_last, mechanicalWord_last] at last
          have projectedBefore := congrArg Subtype.val (Option.some.inj last)
          have priorGood : ∀ owner, owner ≠ who →
              ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
                implementation.leaks implementation.bounds nativeInitial implementation.horizon
                  implementation.scheduler owner ⟨before, prior⟩ := by
            intro owner foreign
            exact no_generated_of_tracePrefix setup implementation owner
              (TracePrefix.extend .refl joint legal realized) (firstGood owner foreign)
          have otherGood : ∀ owner, owner ≠ who →
              ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
                implementation.leaks implementation.bounds nativeInitial implementation.horizon
                  implementation.scheduler owner ⟨otherBefore, other⟩ := by
            intro owner foreign
            exact no_generated_of_tracePrefix setup implementation owner
              (TracePrefix.extend .refl otherJoint otherLegal otherRealized) (secondGood owner
                foreign)
          rw [mechanicalPathAtom, mechanicalPathAtom,
            ih other priorGood otherGood samePrior]
          congr 1
          exact mechanicalStepAtom_eq_of_projection setup values implementation operational
            fullValues rates waitPositive waitBelow slotPositive badPositive badBelow who tape
            prior other joint otherJoint legal otherLegal realized otherRealized priorGood otherGood
            projectedBefore projectedAfter

open Classical in
/-- Explicit original tape, focal own-play, and mechanical atom product.
A supported qualified mechanical anchor selects the product, never a mass quotient. -/
def mechanicalCoefficient (rates : PhaseProposalRates)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (who : Player)
    (site : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (event : (serviceGraph setup .concurrent).EventId)
    (index : MechanicalIndex setup implementation who) : ℝ≥0∞ :=
  if present : ∃ history : ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).InformationHistory who site.1,
      mechanicalWord setup implementation who history.val.trace = index.1.val ∧
      ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).historyReachWeight
         nativeProfile history.val ≠ 0 ∧
      prefixTapeLaw setup implementation history.val index.2 ≠ 0 ∧
      (∀ owner, owner ≠ who →
        ¬ EventGraphRuntime.PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
          implementation.leaks implementation.bounds nativeInitial implementation.horizon
          implementation.scheduler owner history.val) ∧
      history.val.state.elim True (fun control =>
        who ∉ control.execution.application.current.excluded) ∧
      bindingAdmissionBit setup implementation who event history.val index.2 = true then
    let history := (Classical.choose present).val
    implementation.prior index.2 *
      ENNReal.ofReal (((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).ownPlayReachProbability (nativeProfile who)
          (((nativeMenu).information nativeInitial implementation.horizon
            implementation.scheduler).ownPlay who history.trace)) *
      mechanicalPathAtom setup implementation rates who index.2 history.trace
  else 0

/-- The literal original-tape coefficient evaluates at every positive qualified
anchor with the same retained mechanical word. -/
theorem mechanicalCoefficient_eq_of_anchor
    (operational : implementation.Operational)
    (scale nativeBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (nativeBadPositive : 0 < nativeBad.val) (nativeBadBelow : nativeBad.val < 1)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (nativePrescribed : nativeProfile = phaseProposalReferenceStrategy setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
      nativeInitial implementation.horizon implementation.scheduler values
      ⟨nativeBad, scale, scale, scale⟩)
    (who : Player)
    (site : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (event : (serviceGraph setup .concurrent).EventId)
    (index : MechanicalIndex setup implementation who)
    (history : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationHistory who site.1)
    (sameWord : mechanicalWord setup implementation who history.val.trace = index.1.val)
    (reached : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).historyReachWeight nativeProfile history.val ≠ 0)
    (tapeSupported : prefixTapeLaw setup implementation history.val index.2 ≠ 0)
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          history.val)
    (alive : history.val.state.elim True (fun control =>
      who ∉ control.execution.application.current.excluded))
    (admitted : bindingAdmissionBit setup implementation who event history.val index.2 = true) :
    mechanicalCoefficient setup implementation ⟨nativeBad, scale, scale, scale⟩ nativeProfile
        who site event index =
      implementation.prior index.2 *
        ENNReal.ofReal (((nativeMenu).information nativeInitial implementation.horizon
          implementation.scheduler).ownPlayReachProbability (nativeProfile who)
            (((nativeMenu).information nativeInitial implementation.horizon
              implementation.scheduler).ownPlay who history.val.trace)) *
        mechanicalPathAtom setup implementation ⟨nativeBad, scale, scale, scale⟩ who index.2
          history.val.trace := by
  classical
  subst nativeProfile
  have present : ∃ anchor : ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).InformationHistory who site.1,
      mechanicalWord setup implementation who anchor.val.trace = index.1.val ∧
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).historyReachWeight
          (phaseProposalReferenceStrategy setup .concurrent implementation.runtime
            implementation.leaks implementation.bounds implementation.plan nativeInitial
              implementation.horizon implementation.scheduler values
                ⟨nativeBad, scale, scale, scale⟩) anchor.val ≠ 0 ∧
      prefixTapeLaw setup implementation anchor.val index.2 ≠ 0 ∧
      (∀ owner, owner ≠ who →
        ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
          implementation.leaks implementation.bounds nativeInitial implementation.horizon
            implementation.scheduler owner anchor.val) ∧
      anchor.val.state.elim True (fun control =>
        who ∉ control.execution.application.current.excluded) ∧
      bindingAdmissionBit setup implementation who event anchor.val index.2 = true :=
    ⟨history, sameWord, reached, tapeSupported, foreign, alive, admitted⟩
  unfold mechanicalCoefficient
  rw [dite_eq_left present]
  let anchor := Classical.choose present
  obtain ⟨anchorWord, _anchorReach, _anchorTape, anchorForeign, _anchorAlive, anchorAdmitted⟩ :=
    Classical.choose_spec present
  have words : mechanicalWord setup implementation who anchor.val.trace =
      mechanicalWord setup implementation who history.val.trace := anchorWord.trans sameWord.symm
  have path := mechanicalPathAtom_eq_of_word setup values implementation operational fullValues
    ⟨nativeBad, scale, scale, scale⟩ scalePositive scaleBelow scalePositive nativeBadPositive
      nativeBadBelow who index.2 anchor.val.trace history.val.trace anchorForeign foreign words
  change bindingAdmissionBit setup implementation who event anchor.val index.2 = true
    at anchorAdmitted
  have own : ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).ownPlay who anchor.val.trace =
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).ownPlay who history.val.trace := by
    rcases anchor with ⟨⟨anchorState, anchorTrace⟩, _anchorInfo⟩
    rcases history with ⟨⟨historyState, historyTrace⟩, _historyInfo⟩
    cases anchorState with
    | none => simp only [bindingAdmissionBit, Bool.false_eq_true] at anchorAdmitted
    | some first =>
        cases historyState with
        | none => simp only [bindingAdmissionBit, Bool.false_eq_true] at admitted
        | some second =>
            exact mechanicalWord_ownPlay setup implementation who first second anchorTrace
              historyTrace words
  change _ * _ * mechanicalPathAtom setup implementation
    ⟨nativeBad, scale, scale, scale⟩ who index.2 anchor.val.trace = _
  rw [path, own]

/-- Exclusions not accounted for by the public archived/current omission footprint. -/
def foreignBindingFailureFootprint (view : (nativeApplication).PlayerView) : Finset Player :=
  view.application.2.excluded \
    ((view.application.2.retired.map fun record =>
        record.2.sourceFailureFootprint.2).foldr (fun first rest => first ∪ rest) ∅ ∪
      view.application.2.native.sourceFailureFootprint.1 view.application.2.attempt.phase)

/-- The actual ready, unsent binding domain, with its existing failure tests. -/
structure CleanUnsentBinding (who : Player)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty) : Prop where
  binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload
  request : PhaseRuntimeState.requests view.application.2 who
    ⟨view.application.2.attempt, event⟩
  unsent : ∀ message ∈ (nativeApplication).outputs past,
    PhaseCount.event? message.payload ≠ some ⟨view.application.2.attempt, event⟩
  noSaved : ¬ phaseProposalSavedBindingFailure setup .concurrent implementation.runtime
    implementation.leaks who event view
  noCurrent : ¬ phaseProposalCurrentBindingFailure setup .concurrent implementation.runtime
    implementation.leaks who event view
  noForeignFailure : ¬ (foreignBindingFailureFootprint setup implementation view).Nonempty

/-- At a clean live callback the saved and current exclusion masks agree.
The saved mask is read from its actual archived failure footprint. -/
theorem CleanUnsentBinding.excluded_eq
    {who : Player} {event : (serviceGraph setup .concurrent).EventId} {payload : L.Ty}
    (control : (nativeApplication).Control)
    (witness : RecoverySourceWitness setup .concurrent implementation.plan
      control.execution.application)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (phase : RuntimePhase (serviceGraph setup .concurrent))
    (installed : control.execution.application.phases.head? = some phase) :
    control.execution.application.current.excluded =
      control.execution.application.entry.excluded := by
  obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp installed
  have saved : control.execution.application.entry.excluded =
      PhaseRuntimeState.archivedFailureOwners control.execution.application.retired ∪
        control.execution.application.current.native.failureOwnersBefore
          control.execution.application.attempt.phase :=
    PhaseRuntimeState.saved_excluded_eq_public_failures witness.exclusions witness.failures
      witness.receipts.exclusion.frontier phase rest phases
  apply Finset.Subset.antisymm
  · intro owner excluded
    by_contra absent
    apply clean.noForeignFailure
    change (control.execution.application.publicView.excluded \
      ((control.execution.application.publicView.retired.map fun record =>
        record.2.sourceFailureFootprint.2).foldr (fun first rest => first ∪ rest) ∅ ∪
        control.execution.application.publicView.native.sourceFailureFootprint.1
          control.execution.application.publicView.attempt.phase)).Nonempty
    simpa only [PhaseRuntimeState.publicView, State.sourceFailureFootprint_read,
      PhaseRuntimeState.sourceRecordFailures_sourceControlRecords,
      PhaseRuntimeState.archivedFailureOwners, List.map_map, Function.comp_def,
      State.sourceFailureFootprint, List.foldr_map, saved] using
        (show (control.execution.application.current.excluded \
          control.execution.application.entry.excluded).Nonempty from
            ⟨owner, Finset.mem_sdiff.mpr ⟨excluded, absent⟩⟩)
  · exact witness.exclusions.coverage.inherited

/-- The actual fresh commitment entry, retaining the selected chronological
checkpoint and its ordinary source cursor. -/
structure NativeBindingEntry
    (operational : implementation.Operational)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId) where
  phase : RuntimePhase (serviceGraph setup .concurrent)
  installed : control.execution.application.phases.head? = some phase
  commitment : phase.kind = .commitment
  inside : event ∈ phase.events
  entry : (nativeApplication).Control
  entryTrace : (nativeProtocol).Trace (some entry)
  retained : TracePrefix entryTrace trace
  sameAttempt : entry.execution.application.attempt = control.execution.application.attempt
  entryInstalled : entry.execution.application.phases.head? = some phase
  idle : entry.actor = none
  entryExcluded : entry.execution.application.entry.excluded =
    entry.execution.application.current.excluded
  excluded : control.execution.application.current.excluded =
    entry.execution.application.current.excluded
  fresh : ∀ owner, ∀ record ∈ entry.execution.recall owner,
    record.beforeView.application.2.attempt ≠ entry.execution.application.attempt
  witness : RecoverySourceWitness setup .concurrent implementation.plan entry.execution.application
  archived : witness.checkpoint.ArchivedProposals entry.execution.network.inputs
  targetContext : SourceCtx Player L
  targetNames : Finset VarId
  block : SourceProgram.CommitPrefix witness.checkpoint.residual.context
    witness.checkpoint.residual.names targetContext targetNames
  suffix : SourceProgram Player L targetContext targetNames
  cursor : PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime
    implementation.leaks implementation.plan entry phase block suffix
  size : block.length = phase.high - phase.low
  offset : cursor.offset = phase.low
  source : cursor.source = witness.checkpoint.source
  config : cursor.config = entry.execution.application.current.native.config
  cursorHistory : (⟨some cursor.current, cursor.trace⟩ : setup.proposalRecoveryProtocol.History) =
    ⟨_, setup.proposalRecoveryLiftTrace
      (nativeArchiveLabels setup (PhaseProposal.sourceArchive entry.execution.network.inputs))
      witness.checkpoint.trace⟩
  canonicalHistory : (⟨some cursor.current, cursor.trace⟩ :
    setup.proposalRecoveryProtocol.History) =
    canonicalSource setup implementation operational ⟨some control, trace⟩
  archiveEq : PhaseProposal.sourceArchive control.execution.network.inputs =
    PhaseProposal.sourceArchive entry.execution.network.inputs
  refs : cursor.refs = witness.checkpoint.refs
  reconstruct : block.prepend suffix = witness.checkpoint.residual.tail
  embedding : cursor.embedding = cast (congrArg (fun program => OutputEmbedding
    (inputLayout setup.context) (outputLayout setup.program) program) reconstruct.symm)
      witness.checkpoint.embedding
  lift : ∀ point, cursor.lift point = witness.checkpoint.residual.lift
    (cast (congrArg SourceProgram.ProtocolState reconstruct) point)
  boundary : IsCommitBoundary suffix
  views : ∀ owner view, cursor.views.view owner view = witness.checkpoint.views.view owner
    (cast (congrArg (ProtocolView owner) reconstruct) view)
  selected : ∃ saved : entry.execution.application.entry = control.execution.application.entry,
    witness.checkpoint =
      (checkpointSelection setup implementation operational trace).val.checkpoint.transfer saved
        (congrArg CommitAttemptId.generation sameAttempt)
        (congrArg CommitAttemptId.phase sameAttempt)

/-- A clean actual callback has the same selected source entry as its first
fresh installed commitment prefix, independently of historical policies. -/
theorem qualified_binding_entry
    (operational : implementation.Operational)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨some control, trace⟩) :
    Nonempty (NativeBindingEntry setup implementation operational control trace who
      event) := by
  classical
  let initial := (setup.initialLaw.map encodeInputs).map
    (PhaseRuntimeState.initial implementation.plan)
  have initialEq : initial = nativeInitial := PMF.map_comp _ _ _
  let counted : ((nativeMenu).protocol initial implementation.horizon
      implementation.scheduler).Trace (some control) := initialEq.symm ▸ trace
  let selected := (checkpointSelection setup implementation operational trace).val
  have raw := (nativeMenu).toRawTrace initial implementation.horizon implementation.scheduler
    counted
  obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history implementation.runtime implementation.leaks
    implementation.plan (setup.initialLaw.map encodeInputs) implementation.horizon
      implementation.scheduler raw
  have request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩ :=
    (control.execution.application.requests_publicView valid who _).mp clean.request
  obtain ⟨phase, rest, phases, commitment, inside⟩ := phase_ready_binding_phase
    implementation.runtime implementation.leaks implementation.plan
      (serviceGraph_revealRelaxedOrdered setup .concurrent) operational.maximalPhases
      (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler raw
        who event payload clean.binding request.2.2.1
  have installed : control.execution.application.phases.head? = some phase := by
    simp only [phases, List.head?_cons]
  have equalExcluded := CleanUnsentBinding.excluded_eq setup implementation control selected
    clean phase installed
  have proper := selected.bindingsHoldValues_of_no_saved_failure_and_foreign_good setup .concurrent
    operational.wellFormed implementation.runtime implementation.leaks implementation.bounds
      implementation.plan operational.maximalPhases implementation.horizon implementation.scheduler
      control counted who event payload clean.binding request clean.noSaved
      (fun owner different _active => by
        intro generated
        exact foreign owner different
          ((generated_initializer setup implementation initialEq.symm trace owner).mp generated))
  obtain ⟨entry, entryCounted, _entryWitness, retainedCounted, sameAttempt, entryInstalled, idle,
      entryExcluded, _entryArchived, fresh⟩ := phaseProposal_binding_entry_checkpoint setup
    .concurrent implementation.runtime implementation.leaks implementation.bounds
      implementation.plan
      operational.maximalPhases implementation.horizon implementation.scheduler control counted
      phase installed
  let entryTrace : (nativeProtocol).Trace (some entry) := initialEq ▸ entryCounted
  have retained : TracePrefix entryTrace trace := by
    have kept := tracePrefix_initializer setup implementation initialEq retainedCounted
    have inverse : initialEq ▸ counted = trace :=
      trace_initializer_inverse setup implementation initialEq trace
    exact inverse ▸ kept
  obtain ⟨witness, archived, historyEq, saved, represented⟩ :=
    checkpointSelection_at_entry setup implementation operational entry control entryTrace trace
      retained sameAttempt
  have excluded : control.execution.application.current.excluded =
      entry.execution.application.current.excluded :=
    equalExcluded.trans ((congrArg (·.excluded) saved.symm).trans entryExcluded)
  have entryProper : ∀ owner, owner ∉ entry.execution.application.current.excluded →
      witness.checkpoint.source.BindingsHoldValues owner := by
    intro owner active
    rw [represented]
    intro name domain cell
    exact proper owner (by simpa only [excluded] using active) cell
  obtain ⟨Δ, P, block, suffix, cursor, size, sourceEq, configEq, cursorHistory, refsEq,
      reconstruct, embeddingEq, liftEq, viewsEq, boundary⟩ :=
        witness.ordinary_installed_binding_cursor setup
    .concurrent implementation.runtime implementation.leaks implementation.bounds
      implementation.plan
      operational.maximalPhases implementation.horizon implementation.scheduler entry entryCounted
      phase entryInstalled commitment entryExcluded fresh archived entryProper
  have offset : cursor.offset = phase.low := by
    have lower := cursor.compiled.countEq
    have phaseLow : entry.execution.application.attempt.phase = phase.low := by
      obtain ⟨tail, installedEq⟩ := List.head?_eq_some_iff.mp entryInstalled
      simp only [PhaseRuntimeState.attempt, installedEq, List.head?_cons, Option.map_some,
        Option.getD_some]
    have counts := witness.checkpoint.compiled.countEq
    have sameCount : eventCount (block.prepend suffix) =
        eventCount witness.checkpoint.residual.tail := congrArg eventCount reconstruct
    omega
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state member
    obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp member
    exact PhaseRuntimeState.initial_ordered implementation.plan draw
  have ordered := (phaseApplication_seedOrder implementation.runtime implementation.leaks).history
    initial implementation.horizon implementation.scheduler initialized
      ((nativeMenu).toRawTrace initial implementation.horizon implementation.scheduler entryCounted)
  have scope (middle : (nativeApplication).Control)
      (prior : ((nativeMenu).protocol initial implementation.horizon
        implementation.scheduler).Trace (some middle))
      (after : TracePrefix entryCounted prior) (before : TracePrefix prior counted)
      (_shorter : prior.length < counted.length) :
      middle.execution.application.attempt = entry.execution.application.attempt := by
    have lower := phase_attempt_progress_of_prefix implementation.runtime implementation.leaks
      nativeMenu initial initialized implementation.horizon implementation.scheduler entry middle
        entryCounted prior after ordered
    have middleOrdered := (phaseApplication_seedOrder implementation.runtime
      implementation.leaks).history
      initial implementation.horizon implementation.scheduler initialized
        ((nativeMenu).toRawTrace initial implementation.horizon implementation.scheduler prior)
    have upper := phase_attempt_progress_of_prefix implementation.runtime implementation.leaks
      nativeMenu initial initialized implementation.horizon implementation.scheduler middle control
        prior counted before middleOrdered
    have generation := congrArg CommitAttemptId.generation sameAttempt
    have phaseRank := congrArg CommitAttemptId.phase sameAttempt
    cases first : middle.execution.application.attempt with
    | mk firstPhase firstGeneration =>
      cases second : entry.execution.application.attempt with
      | mk secondPhase secondGeneration =>
        simp only [first, second] at lower upper generation phaseRank ⊢
        congr 1 <;> omega
  obtain ⟨ending, endingEq, archiveEq⟩ := PhaseProposal.phase_commitment_prefix_sourceArchive
    implementation.runtime implementation.leaks implementation.bounds implementation.plan
      (serviceGraph_revealRelaxedOrdered setup .concurrent) (setup.initialLaw.map encodeInputs)
      implementation.horizon implementation.scheduler entry entryCounted phase
      (Option.mem_def.mpr entryInstalled) commitment counted retainedCounted scope
  cases Option.some.inj endingEq
  have lifted := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    (⟨history.state, setup.proposalRecoveryLiftTrace
      (nativeArchiveLabels setup (PhaseProposal.sourceArchive control.execution.network.inputs))
      history.trace⟩ : setup.proposalRecoveryProtocol.History)) historyEq
  have canonicalHistory : (⟨some cursor.current, cursor.trace⟩ :
      setup.proposalRecoveryProtocol.History) =
      canonicalSource setup implementation operational ⟨some control, trace⟩ := by
    rw [cursorHistory]
    simpa only [canonicalSource, selected, archiveEq] using lifted
  exact ⟨⟨phase, installed, commitment, inside, entry, entryTrace, retained, sameAttempt,
    entryInstalled, idle, entryExcluded, excluded, fresh, witness, archived, Δ, P, block, suffix,
    cursor, size, offset, sourceEq, configEq, cursorHistory, canonicalHistory, archiveEq,
      refsEq, reconstruct,
    embeddingEq, liftEq, boundary, viewsEq, saved, represented⟩⟩

/-- The signed frontier at the current callback retains the physical store,
the saved public metadata and every already issued commitment. -/
theorem NativeBindingEntry.callback_frame
    (operational : implementation.Operational)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId)
    (entry : NativeBindingEntry setup implementation operational control trace who event) :
    PhaseProposalBindingCallbackFrame setup .concurrent implementation.runtime
      implementation.leaks entry.entry.execution entry.phase control.execution
        (phaseProposalEmissionFrontier setup .concurrent implementation.runtime
          implementation.leaks entry.entry.execution entry.phase entry.entryTrace.length
            entry.entry.execution.application.current.native.config nativeInitial
              implementation.horizon implementation.scheduler
                ((nativeMenu).toRawTrace nativeInitial implementation.horizon
                  implementation.scheduler trace)) control.actor := by
  let initial := (setup.initialLaw.map encodeInputs).map
    (PhaseRuntimeState.initial implementation.plan)
  have initialEq : initial = nativeInitial := PMF.map_comp _ _ _
  let counted : ((nativeMenu).protocol initial implementation.horizon
    implementation.scheduler).Trace (some control) := initialEq.symm ▸ trace
  let earlier : ((nativeMenu).protocol initial implementation.horizon
    implementation.scheduler).Trace (some entry.entry) := initialEq.symm ▸ entry.entryTrace
  obtain ⟨_empty, emissions, origins⟩ := phaseProposal_fresh_entry_binding_origins setup
    .concurrent implementation.runtime implementation.leaks implementation.bounds
      implementation.plan
      (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
      entry.entry earlier entry.phase entry.entryInstalled entry.commitment entry.fresh
  have frame := phaseProposalEmissionFrontier_callback_frame setup .concurrent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan
      (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
      operational.completePending operational.maximalPhases entry.entry earlier entry.phase
      entry.entryInstalled entry.commitment entry.entryExcluded origins emissions control counted
      (tracePrefix_initializer setup implementation initialEq.symm entry.retained)
      entry.sameAttempt.symm entry.excluded
  have frontierEq := emissionFrontier_initializer setup implementation initialEq.symm
    entry.entryTrace trace entry.entry.execution entry.phase
      entry.entry.execution.application.current.native.config
  exact frontierEq ▸ frame

/-- The frozen ordinary source cursor can be read at the actual callback.
The graph configuration and source prefix stay fixed; its control, address
and archive readouts are transported along the same native attempt. -/
def NativeBindingEntry.decision_cursor
    (operational : implementation.Operational)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId)
    (entry : NativeBindingEntry setup implementation operational control trace who event) :
    PhaseProposalOrdinarySourceCursor setup .concurrent implementation.runtime implementation.leaks
      implementation.plan control entry.phase entry.block entry.suffix := by
  have frame := entry.callback_frame setup implementation operational control trace who event
  have phase : control.execution.application.attempt.phase =
      entry.entry.execution.application.attempt.phase :=
    congrArg CommitAttemptId.phase entry.sameAttempt.symm
  have generation : control.execution.application.attempt.generation =
      entry.entry.execution.application.attempt.generation :=
    congrArg CommitAttemptId.generation entry.sameAttempt.symm
  have retired : control.execution.application.publicView.retired =
      entry.entry.execution.application.publicView.retired :=
    congrArg (List.map (fun row : RetiredCommitAttempt (serviceGraph setup .concurrent) =>
      (row.attempt, row.state.publicView))) frame.retired
  have addresses := PhasePublicView.sourcePublicAddressWord_eq_of_prefix implementation.plan
    control.execution.application.publicView entry.entry.execution.application.publicView
      entry.sameAttempt.symm retired frame.failures entry.cursor.offset
  refine { entry.cursor with
    excluded := entry.cursor.excluded.trans entry.excluded.symm
    entryExcluded := entry.cursor.entryExcluded.trans entry.excluded.symm
    low := phase ▸ entry.cursor.low
    controls := ?_
    addresses := ?_
    proposals := ?_ }
  · intro positive
    rw [entry.cursor.controls positive]
    have failures := frame.failures control.execution.application.attempt.phase le_rfl
    rw [phase] at failures
    simp only [PhaseRuntimeState.publicView]
    rw [frame.retired, phase, generation, failures]
  · intro positive owner
    rw [entry.cursor.addresses positive owner, addresses]
  · intro owner active
    exact (entry.cursor.proposals owner active).trans entry.archiveEq.symm

/-- The ordinary entry retains its selected single supported initializer and
the same immutable physical input draw. -/
theorem NativeBindingEntry.initializer
    (operational : implementation.Operational)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId)
    (entry : NativeBindingEntry setup implementation operational control trace who event) :
    ∃ (theta : State L setup.context) (drawn : theta ∈ setup.initialLaw.support),
      control.execution.application.current.native.config.inputs = encodeInputs theta ∧
      ∃ (initial : CommitRecoveryState setup.program)
        (first : setup.proposalRecoveryProtocol.Trace (some initial)),
        (⟨some initial, first⟩ : setup.proposalRecoveryProtocol.History) =
          ⟨_, setup.proposalRecoveryLiftTrace
            (nativeArchiveLabels setup (PhaseProposal.sourceArchive
              entry.entry.execution.network.inputs))
            (RecoverySourceCheckpoint.initialized setup .concurrent implementation.plan
              theta drawn).trace⟩ ∧ TracePrefix first entry.cursor.trace := by
  obtain ⟨theta, drawn, native, kept⟩ := checkpointSelection_initializer setup implementation
    operational control trace
  obtain ⟨saved, represented⟩ := entry.selected
  have same : (⟨_, entry.witness.checkpoint.trace⟩ : setup.commitRecoveryProtocol.History) =
      ⟨_, (checkpointSelection setup implementation operational trace).val.checkpoint.trace⟩ := by
    rw [represented]
    exact RecoverySourceCheckpoint.transfer_history _ _ _ _
  let labels := nativeArchiveLabels setup
    (PhaseProposal.sourceArchive entry.entry.execution.network.inputs)
  have lifted := setup.proposalRecoveryLiftTrace_prefix labels kept
  have source := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    (⟨history.state, setup.proposalRecoveryLiftTrace labels history.trace⟩ :
      setup.proposalRecoveryProtocol.History)) same
  have retained := lifted.reachesWithin
  rw [← source, ← entry.cursorHistory] at retained
  exact ⟨theta, drawn, native.active.reachable.inputs_eq, _, _, rfl, retained.tracePrefix⟩

/-- Every active field in the actual emitted frontier is proper at a clean
callback. Pending foreign fields retain their original signed preparations. -/
theorem NativeBindingEntry.frontier_proper
    (operational : implementation.Operational)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨some control, trace⟩)
    (entry : NativeBindingEntry setup implementation operational control trace who event) :
    let frontier := phaseProposalEmissionFrontier setup .concurrent implementation.runtime
      implementation.leaks entry.entry.execution entry.phase entry.entryTrace.length
        entry.entry.execution.application.current.native.config nativeInitial implementation.horizon
          implementation.scheduler ((nativeMenu).toRawTrace nativeInitial implementation.horizon
            implementation.scheduler trace)
    ∀ named ∈ entry.phase.events,
      ∀ owner ∉ entry.entry.execution.application.current.excluded,
      ∀ domain (binding : (serviceGraph setup .concurrent).outputLayout named =
        .binding owner domain),
      ∀ result, (⟨.inr named, binding⟩ : FieldRef (graphLayout setup.program)
        (.binding owner domain)).get? frontier.store = some result →
          ∃ value, result = PublicationResult.success value := by
  classical
  intro frontier named inside owner active domain binding result stored
  let initial := (setup.initialLaw.map encodeInputs).map
    (PhaseRuntimeState.initial implementation.plan)
  have initialEq : initial = nativeInitial := PMF.map_comp _ _ _
  let counted : ((nativeMenu).protocol initial implementation.horizon
      implementation.scheduler).Trace (some control) := initialEq.symm ▸ trace
  let entryTrace : ((nativeMenu).protocol initial implementation.horizon
      implementation.scheduler).Trace (some entry.entry) := initialEq.symm ▸ entry.entryTrace
  have retained : TracePrefix entryTrace counted := by
    exact tracePrefix_initializer setup implementation initialEq.symm entry.retained
  obtain ⟨_noInputs, initialEmissions, origins⟩ := phaseProposal_fresh_entry_binding_origins setup
    .concurrent implementation.runtime implementation.leaks implementation.bounds
      implementation.plan
      (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
      entry.entry entryTrace entry.phase entry.entryInstalled entry.commitment entry.fresh
  have frame := phaseProposalEmissionFrontier_callback_frame setup .concurrent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan
      (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
      operational.completePending operational.maximalPhases entry.entry entryTrace entry.phase
      entry.entryInstalled entry.commitment entry.entryExcluded origins initialEmissions control
      counted retained entry.sameAttempt.symm entry.excluded
  have emissions : PhaseProposalEmittedBindings implementation.runtime implementation.leaks
      control.execution entry.phase frontier := by
    have frontierEq := emissionFrontier_initializer setup implementation initialEq.symm
      entry.entryTrace trace entry.entry.execution entry.phase
        entry.entry.execution.application.current.native.config
    rw [frontierEq] at frame
    exact frame.emissions
  have completed : named ∈ frontier.cut.completed :=
    (frontier.output_available named).mp (by
      have isSome_read {kind : EventField Player L}
          (ref : FieldRef (graphLayout setup.program) kind) :
          (ref.get? frontier.store).isSome = (frontier.store ref.field).isSome := by
        rcases ref with ⟨field, shape⟩
        cases shape
        rfl
      have present := congrArg Option.isSome stored
      rw [isSome_read] at present
      change (frontier.outputs named).isSome = true at present
      exact present)
  have actor := (serviceGraph setup .concurrent).actor?_of_outputLayout_binding binding
  rcases phaseProposalEmissionFrontier_origin setup .concurrent implementation.runtime
      implementation.leaks entry.entry.execution entry.phase entry.entryTrace.length
      entry.entry.execution.application.current.native.config nativeInitial implementation.horizon
        implementation.scheduler named
        ((nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler
          trace)
        completed with old | inherited | sent
  · rcases origins named old with below | ⟨other, excluded, acted⟩
    · have bounds := (entry.phase.mem_events named).mp inside
      omega
    · have same : other = owner := Option.some.inj (acted.symm.trans actor)
      exact (active (same ▸ excluded)).elim
  · obtain ⟨other, excluded, acted⟩ := inherited
    have same : other = owner := Option.some.inj (acted.symm.trans actor)
    exact (active (same ▸ excluded)).elim
  · obtain ⟨before, after, prior, joint, legal, realized, kept, _later, sent⟩ := sent
    obtain ⟨sender, acted, remaining, execution, state, attempt, response, material, candidate,
      selected, transmitted, packet⟩ := sent
    subst before
    change after ∈ (PMF.pure (some ⟨remaining, none,
      execution.respond nativeApplication sender ((joint sender).getD ⟨none⟩)⟩)).support at realized
    rw [selected, Option.getD_some] at realized
    cases (PMF.mem_support_pure_iff _ _).mp realized
    let message := (execution.network.submit sender ((nativeApplication).packet
      ((nativeApplication).submit execution.application sender material) sender
        (execution.network.known sender) material)).1
    have responseEq : response = ⟨some material⟩ := by
      cases response
      cases transmitted
      rfl
    have output : message ∈ (nativeApplication).outputs
        ((execution.respond nativeApplication sender response).recall sender) := by
      simp [responseEq, ReactiveApplication.Execution.respond, MessageNetwork.submit,
        ReactiveApplication.outputs, message]
    have recalled := (nativeApplication).reaches_recall_prefix nativeInitial implementation.horizon
      implementation.scheduler kept.reachesWithin
        ⟨remaining, none, execution.respond nativeApplication sender response⟩ control rfl rfl
          sender
    have laterOutput : message ∈ (nativeApplication).outputs (control.execution.recall sender) := by
      obtain ⟨record, member, emitted⟩ := List.mem_filterMap.mp output
      exact List.mem_filterMap.mpr ⟨record, recalled.subset member, emitted⟩
    have member : message ∈ control.execution.network.inputs := by
      rw [← (nativeApplication).history_inputRecall nativeInitial implementation.horizon
        implementation.scheduler
          ((nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler
            trace) sender] at laterOutput
      exact (List.mem_filter.mp laterOutput).1
    have call : message.payload.packet.call = .commitment named candidate := by
      change ((execution.application.submit sender material).emit sender
        (execution.network.known sender) material).packet.call = _
      rw [phase_emit_call, packet]
    have sameNamespace : message.payload.attempt = control.execution.application.attempt :=
      attempt.trans entry.sameAttempt
    obtain ⟨serial, opening, evidence, record, slot, _senderEq, recorded, emitted, declared,
        _fresh, recordAttempt, meaning⟩ := issued_binding_record setup implementation control
      trace owner named domain binding candidate message member call
    have prepared : ∃ value : L.Val domain,
        opening.bind (fun raw => raw.as? domain) = some value := by
      by_cases own : owner = who
      · have bindingWho : (serviceGraph setup .concurrent).outputLayout named =
            .binding who domain := by simpa only [own] using binding
        have recordedWho : record ∈ control.execution.recall who := by
          simpa only [own] using recorded
        have declaredWho : record.action =
            ⟨some ⟨⟨.commitment named (who, .prepared serial), opening⟩, evidence⟩⟩ := by
          simpa only [own] using declared
        obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp entry.installed
        have raw := (nativeMenu).toRawTrace initial implementation.horizon implementation.scheduler
          counted
        obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history implementation.runtime
          implementation.leaks implementation.plan (setup.initialLaw.map encodeInputs)
            implementation.horizon implementation.scheduler raw
        have request := (control.execution.application.requests_publicView valid who _).mp
          clean.request
        exact phaseProposal_recalled_current_binding_preparation_value setup .concurrent
          implementation.runtime implementation.leaks implementation.bounds implementation.plan
            operational.maximalPhases implementation.horizon implementation.scheduler control
              counted
            (checkpointSelection setup implementation operational trace).val entry.phase rest phases
            entry.commitment who event payload clean.binding request clean.unsent clean.noCurrent
            named inside domain bindingWho serial opening evidence record recordedWho declaredWho
            (recordAttempt.trans sameNamespace)
      · exact phaseProposal_recalled_binding_preparation_value implementation.runtime
          implementation.leaks implementation.bounds nativeInitial implementation.horizon
            implementation.scheduler control trace owner (foreign owner own) named domain binding
            serial opening evidence record recorded declared
    obtain ⟨value, decoded⟩ := prepared
    have field := emissions message member sameNamespace named inside candidate call owner domain
      binding
    rw [meaning, decoded, Option.elim_some] at field
    exact ⟨value, Option.some.inj (stored.symm.trans field)⟩

/-- The actual issued cylinder has one supported complete source/graph pair.
Every field in the emitted frontier is retained in that same graph outcome. -/
theorem NativeBindingEntry.supported_completion
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨some control, trace⟩)
    (entry : NativeBindingEntry setup implementation operational control trace who event) :
    let frontier := phaseProposalEmissionFrontier setup .concurrent implementation.runtime
      implementation.leaks entry.entry.execution entry.phase entry.entryTrace.length
        entry.entry.execution.application.current.native.config nativeInitial implementation.horizon
          implementation.scheduler ((nativeMenu).toRawTrace nativeInitial implementation.horizon
            implementation.scheduler trace)
    ∃ (completed : setup.proposalRecoveryProtocol.History)
      (key : (serviceGraph setup .concurrent).SemanticKey),
      PhaseProposalOrdinarySourceBlockResult setup .concurrent entry.block entry.suffix
        entry.cursor.refs entry.cursor.embedding entry.cursor.lift entry.cursor.source
          entry.cursor.current entry.cursor.trace (completed, key) ∧
      completed ∈ (setup.proposalRecoveryModel.runBehavioralFrom
        (sourceUnflaggedStrategy setup values) entry.block.length
          ⟨some entry.cursor.current, entry.cursor.trace⟩).support ∧
      key ∈ ((serviceGraph setup .concurrent).canonicalContinuation
        (phaseProposalBindingPotentialProfile setup .concurrent implementation.runtime
          implementation.leaks implementation.plan entry.entry.execution entry.phase values)
        entry.cursor.config).support ∧
      ∀ field value, frontier.store field = some value → key.2.1 field = some value := by
  classical
  intro frontier
  let initial := (setup.initialLaw.map encodeInputs).map
    (PhaseRuntimeState.initial implementation.plan)
  have initialEq : initial = nativeInitial := PMF.map_comp _ _ _
  let counted : ((nativeMenu).protocol initial implementation.horizon
      implementation.scheduler).Trace (some control) := initialEq.symm ▸ trace
  let entryTrace : ((nativeMenu).protocol initial implementation.horizon
      implementation.scheduler).Trace (some entry.entry) := initialEq.symm ▸ entry.entryTrace
  have retained : TracePrefix entryTrace counted := by
    exact tracePrefix_initializer setup implementation initialEq.symm entry.retained
  have proper := NativeBindingEntry.frontier_proper setup implementation operational
    control trace who event payload clean foreign entry
  have frontierEq := emissionFrontier_initializer setup implementation initialEq.symm
    entry.entryTrace trace entry.entry.execution entry.phase
      entry.entry.execution.application.current.native.config
  obtain ⟨present, posterior⟩ := emitted_frontier_conditional setup .concurrent
    implementation.runtime implementation.leaks implementation.bounds implementation.plan values
      operational.completePending operational.maximalPhases fullValues implementation.horizon
      implementation.scheduler entry.entry entryTrace entry.phase entry.entryInstalled
      entry.commitment entry.entryExcluded entry.fresh control counted retained
      entry.sameAttempt.symm entry.excluded (frontierEq.symm ▸ proper)
  rw [frontierEq] at posterior
  let profile := phaseProposalBindingPotentialProfile setup .concurrent implementation.runtime
    implementation.leaks implementation.plan entry.entry.execution entry.phase values
  obtain ⟨key, atFrontier⟩ := ((serviceGraph setup .concurrent).canonicalContinuation profile
    frontier).support_nonempty
  have original : key ∈ ((serviceGraph setup .concurrent).canonicalContinuation profile
      entry.cursor.config).support := by
    rw [entry.config]
    have conditioned := atFrontier
    rw [show (serviceGraph setup .concurrent).canonicalContinuation profile frontier = _
      from posterior] at conditioned
    exact (mem_support_fiberPosterior present conditioned).2
  obtain ⟨joint, sourceMarginal, graphMarginal, supported, _fill⟩ :=
    phaseProposalBindingPotentialProfile_source_block_coupling setup .concurrent
      implementation.runtime implementation.leaks implementation.plan initial implementation.horizon
        implementation.scheduler entry.entry
          ((nativeMenu).toRawTrace initial implementation.horizon implementation.scheduler
            entryTrace)
          entry.phase values entry.block entry.suffix entry.cursor
  have jointKey : key ∈ (joint.map Prod.snd).support := by
    rw [graphMarginal]
    exact original
  obtain ⟨pair, member, keyEq⟩ := (PMF.mem_support_map_iff ..).mp jointKey
  have sourceSupport : pair.1 ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) entry.block.length
        ⟨some entry.cursor.current, entry.cursor.trace⟩).support := by
    have selected : pair.1 ∈ (joint.map Prod.fst).support :=
      (PMF.mem_support_map_iff ..).mpr ⟨pair, member, rfl⟩
    rw [sourceMarginal] at selected
    exact selected
  refine ⟨pair.1, key, keyEq ▸ supported pair member, sourceSupport, original, ?_⟩
  obtain ⟨final, reached, rfl⟩ := (PMF.mem_support_map_iff ..).mp atFrontier
  exact runPlan_retains_store _ _ frontier final reached

/-- The selected ordinary completion has a literal before-event source prefix
at the requested static rank, including the zero-offset case. -/
theorem NativeBindingEntry.before_event
    (operational : implementation.Operational)
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (entry : NativeBindingEntry setup implementation operational control trace who event)
    (completed : setup.proposalRecoveryProtocol.History)
    (key : (serviceGraph setup .concurrent).SemanticKey)
    (result : PhaseProposalOrdinarySourceBlockResult setup .concurrent entry.block entry.suffix
      entry.cursor.refs entry.cursor.embedding entry.cursor.lift entry.cursor.source
        entry.cursor.current entry.cursor.trace (completed, key))
    (supported : completed ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (sourceUnflaggedStrategy setup values) entry.block.length
        ⟨some entry.cursor.current, entry.cursor.trace⟩).support) :
    ∃ (current : CommitRecoveryState setup.program)
      (prior : setup.proposalRecoveryProtocol.Trace (some current)),
      TracePrefix entry.cursor.trace prior ∧ TracePrefix prior completed.trace ∧
      prior.length = entry.cursor.trace.length + (event.val - entry.phase.low) ∧
      instructionCount setup.program - ProtocolState.remaining setup.program current.point =
        event.val ∧
      ProtocolState.actor setup.program current.point = some who ∧
      ProtocolState.atCommit setup.program current.point = true ∧ who ∉ current.excluded := by
  have bounds := (entry.phase.mem_events event).mp entry.inside
  have positive : 0 < entry.block.length := by
    have size := entry.size
    omega
  have startRank : instructionCount setup.program -
      ProtocolState.remaining setup.program entry.cursor.current.point = entry.phase.low := by
    rw [entry.cursor.point, entry.cursor.origin.remaining_lift, ProtocolState.remaining_entry]
    have count := entry.cursor.compiled.countEq
    rw [eventCount_eq_instructionCount, eventCount_eq_instructionCount] at count
    rw [entry.offset] at count
    omega
  have startEnd : instructionCount setup.program -
      ProtocolState.commitEnd setup.program entry.cursor.current.saved = entry.phase.high := by
    rw [entry.cursor.savedEnd positive]
    have count := entry.cursor.compiled.countEq
    rw [eventCount_eq_instructionCount, eventCount_eq_instructionCount,
      entry.block.instructionCount_prepend] at count
    rw [entry.offset] at count
    have size := entry.size
    omega
  have startCommit : ProtocolState.atCommit setup.program entry.cursor.current.point = true := by
    rw [entry.cursor.point, entry.cursor.origin.atCommit_lift]
    have commits : ∀ {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
        (block : SourceProgram.CommitPrefix Γ O Δ P)
        (suffix : SourceProgram Player L Δ P) (config : SourceProgram.Config Player L Γ),
        0 < block.length → ProtocolState.atCommit (block.prepend suffix)
          (ProtocolState.entry (block.prepend suffix) config) = true := by
      intro Γ Δ O P block
      cases block with
      | nil => intro suffix config impossible; cases Nat.not_lt_zero _ impossible
      | commit => intro suffix config _; rfl
    exact commits entry.block entry.suffix entry.cursor.source positive
  have retained := (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin
    (sourceUnflaggedStrategy setup values) entry.block.length
      ⟨some entry.cursor.current, entry.cursor.trace⟩ completed supported).tracePrefix
  obtain ⟨finished, last, lastTrace, attempt, finalEq, _point, finalExcluded, _generation,
      _live, _agreement, words, _labels⟩ := result
  change completed = ⟨some last, lastTrace⟩ at finalEq
  have length : attempt.joints.length = entry.block.length := attempt.joints_length
  have instructions : setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace completed.trace) =
      attempt.joints.reverse ++
        setup.recoveryJointRecall (setup.proposalRecoveryEraseTrace entry.cursor.trace) := by
    rw [finalEq]
    exact words
  obtain ⟨current, next, prior, joint, legal, moved, rowKept, depth, _joint,
      _saved, _generation, rank⟩ := source_commit_chunk_at_rank setup entry.cursor.current
    entry.cursor.trace startCommit completed retained attempt.joints instructions
      (event.val - entry.phase.low) (by rw [length]; have size := entry.size; omega)
      event.val (by omega) (by omega)
  have priorKept : TracePrefix prior completed.trace :=
    (TracePrefix.extend .refl joint legal moved).trans rowKept
  have past : TracePrefix entry.cursor.trace prior :=
    (retained.reachesWithin.ancestor_comparable priorKept.reachesWithin
      (by
        change entry.cursor.trace.length ≤ prior.length
        rw [depth]
        omega)).tracePrefix
  obtain ⟨committing, acting, _decode⟩ := source_binding_at_rank setup.program current.point
    event who payload clean.binding rank.symm
  have activeStart : who ∉ entry.cursor.current.excluded := by
    rw [entry.cursor.excluded, ← entry.excluded]
    exact clean.request.2.2.2.2
  have active : who ∉ current.excluded := by
    have monotone := setup.commitRecovery_public_excluded_of_reaches
      (setup.proposalRecoveryEraseTrace_prefix priorKept).reachesWithin
    rw [finalEq] at monotone
    change current.excluded ⊆ last.excluded at monotone
    intro excluded
    exact activeStart (finalExcluded ▸ monotone excluded)
  exact ⟨current, prior, past, priorKept, depth, rank, acting, committing, active⟩

/-- A clean callback admits one canonical before-event cut obtained from one
complete supported source/graph word. The same word retains the entire physical
store and every current emitted field, including static-later fields. -/
def NativeBindingEntry.canonicalCut
    (operational : implementation.Operational)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (control : (nativeApplication).Control)
    (trace : (nativeProtocol).Trace (some control))
    (who : Player) (acting : control.actor = some who)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨some control, trace⟩)
    (entry : NativeBindingEntry setup implementation operational control trace who event) :
    PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values implementation.horizon
        implementation.scheduler control (sourceCutTrace setup implementation trace) who event := by
  classical
  have initialEq : ((setup.initialLaw.map encodeInputs).map
      (PhaseRuntimeState.initial implementation.plan)) = nativeInitial := PMF.map_comp _ _ _
  let frontier := phaseProposalEmissionFrontier setup .concurrent implementation.runtime
    implementation.leaks entry.entry.execution entry.phase entry.entryTrace.length
      entry.entry.execution.application.current.native.config nativeInitial implementation.horizon
        implementation.scheduler ((nativeMenu).toRawTrace nativeInitial implementation.horizon
          implementation.scheduler trace)
  let completion := entry.supported_completion setup values implementation operational fullValues
    control trace who event payload clean foreign
  let completed := Classical.choose completion
  let key := Classical.choose (Classical.choose_spec completion)
  have completionFields := Classical.choose_spec (Classical.choose_spec completion)
  have result := completionFields.1
  have supported := completionFields.2.1
  have graphSupported := completionFields.2.2.1
  have retained := completionFields.2.2.2
  let cutExists := entry.before_event setup values implementation operational control trace who
    event payload clean completed key result supported
  let current := Classical.choose cutExists
  let prior := Classical.choose (Classical.choose_spec cutExists)
  have cutFields := Classical.choose_spec (Classical.choose_spec cutExists)
  have past := cutFields.1
  have future := cutFields.2.1
  have clock := cutFields.2.2.1
  have rank := cutFields.2.2.2.1
  have actor := cutFields.2.2.2.2.1
  have atCommit := cutFields.2.2.2.2.2.1
  have survives := cutFields.2.2.2.2.2.2
  let initializerExists := entry.initializer setup implementation operational control trace who
    event
  let theta := Classical.choose initializerExists
  have drawn : theta ∈ setup.initialLaw.support :=
    Classical.choose (Classical.choose_spec initializerExists)
  have initializerFields := Classical.choose_spec (Classical.choose_spec initializerExists)
  have original := initializerFields.1
  let initial := Classical.choose initializerFields.2
  let first := Classical.choose (Classical.choose_spec initializerFields.2)
  have initializedFields := Classical.choose_spec (Classical.choose_spec initializerFields.2)
  have initialized := initializedFields.1
  have sourceRetained := initializedFields.2
  have frame := entry.callback_frame setup implementation operational control trace who event
  have request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩ := by
    let initialLaw := (setup.initialLaw.map encodeInputs).map
      (PhaseRuntimeState.initial implementation.plan)
    have initialEq : initialLaw = nativeInitial := PMF.map_comp _ _ _
    obtain ⟨_draw, native⟩ := phaseNativeInvariant_history implementation.runtime
      implementation.leaks
      implementation.plan (setup.initialLaw.map encodeInputs) implementation.horizon
      implementation.scheduler ((nativeMenu).toRawTrace initialLaw implementation.horizon
        implementation.scheduler (initialEq.symm ▸ trace))
    exact (control.execution.application.requests_publicView native who _).mp clean.request
  have lockedStore : ∀ field value,
      control.execution.application.current.native.config.store field = some value →
        key.2.1 field = some value := by
    intro field value stored
    apply retained field value
    cases field with
    | inl input =>
        change some (frontier.inputs input) = some value
        rw [← frame.inputs]
        exact stored
    | inr declared =>
        have settled : declared ∈
          control.execution.application.current.native.config.cut.completed :=
          (control.execution.application.current.native.config.output_available declared).mp
            (Option.isSome_iff_exists.mpr ⟨value, stored⟩)
        exact (frame.agreement declared settled).symm.trans stored
  have lockedEmissions : ∀ owner, owner ∉ entry.cursor.current.excluded →
      ∀ record ∈ control.execution.recall owner,
      record.beforeView.application.2.attempt = control.execution.application.attempt →
      ∀ message, record.emitted = some message →
      ∀ (declared : (serviceGraph setup .concurrent).EventId) (domain : L.Ty)
        (output : (serviceGraph setup .concurrent).outputLayout declared = .binding owner domain)
        (value : L.Val domain),
      PhaseCount.event? message.payload =
        some ⟨control.execution.application.attempt, declared⟩ →
      record.action.transmission.bind PhaseProposal.bindingPreparation = some ⟨domain, value⟩ →
      (⟨.inr declared, output⟩ : FieldRef (graphLayout setup.program)
        (.binding owner domain)).get? key.2.1 = some (.success value) := by
    intro owner active record recorded attempt message emitted declared domain output value
      named prepared
    let raw := (nativeMenu).toRawTrace nativeInitial implementation.horizon
      implementation.scheduler trace
    cases transmitted : record.action.transmission with
    | none => simp only [transmitted, Option.bind_none, reduceCtorEq] at prepared
    | some material =>
        obtain ⟨actual, sent, _sender, call⟩ := PhaseCount.recalled_submission_emitted
          implementation.runtime implementation.leaks nativeInitial implementation.horizon
            implementation.scheduler raw owner record recorded material transmitted
        have actualEq : actual = message := Option.some.inj (sent.symm.trans emitted)
        subst actual
        have member : message ∈ control.execution.network.inputs := by
          have authored : message ∈ (nativeApplication).outputs (control.execution.recall owner) :=
            List.mem_filterMap.mpr ⟨record, recorded, emitted⟩
          rw [← (nativeApplication).history_inputRecall nativeInitial implementation.horizon
            implementation.scheduler raw owner] at authored
          exact (List.mem_filter.mp authored).1
        have sameNamespace : message.payload.attempt = control.execution.application.attempt :=
          (phase_recalled_emission_attempt implementation.runtime implementation.leaks
            nativeInitial implementation.horizon implementation.scheduler raw owner record
              recorded message emitted).trans attempt
        cases packet : material.call.packet with
        | malformed =>
            simp only [transmitted, Option.bind_some, PhaseProposal.bindingPreparation, packet,
              reduceCtorEq] at prepared
        | opening =>
            simp only [transmitted, Option.bind_some, PhaseProposal.bindingPreparation, packet,
              reduceCtorEq] at prepared
        | commitment actual candidate =>
            have namedEq : actual = declared := by
              change (message.payload.packet.call.event? _).map _ = _ at named
              rw [call, packet] at named
              exact congrArg CommitAttemptEvent.event (Option.some.inj named)
            subst actual
            have inside : declared ∈ entry.phase.events := by
              obtain ⟨callback, callbackTrace, kept, _acting, viewed, requested⟩ :=
                phase_recorded_binding_request implementation.runtime implementation.leaks
                  implementation.bounds implementation.plan (setup.initialLaw.map encodeInputs)
                  implementation.horizon (serviceGraph_revealRelaxedOrdered setup .concurrent)
                  implementation.scheduler (initialEq.symm ▸ trace) owner record recorded
                    material transmitted declared candidate packet
              let nativeCallbackTrace : (nativeProtocol).Trace (some callback) :=
                initialEq ▸ callbackTrace
              have nativeKept : TracePrefix nativeCallbackTrace trace := by
                have transferred := tracePrefix_initializer setup implementation initialEq kept
                have inverse : initialEq ▸ (initialEq.symm ▸ trace) = trace :=
                  trace_initializer_inverse setup implementation initialEq trace
                exact inverse ▸ transferred
              have initialOrdered : ∀ state ∈ (nativeInitial).support, state.Ordered := by
                intro state supported
                obtain ⟨draw, _, rfl⟩ := (PMF.mem_support_map_iff ..).mp supported
                exact PhaseRuntimeState.initial_ordered implementation.plan (encodeInputs draw)
              have ordered := (phaseApplication_seedOrder implementation.runtime
                implementation.leaks).history
                nativeInitial implementation.horizon implementation.scheduler initialOrdered
                  ((nativeMenu).toRawTrace nativeInitial implementation.horizon
                    implementation.scheduler nativeCallbackTrace)
              have metadata := phase_attempt_metadata_of_prefix implementation.runtime
                implementation.leaks nativeMenu nativeInitial initialOrdered implementation.horizon
                  implementation.scheduler callback control nativeCallbackTrace trace nativeKept
                    ordered
                    (by
                      rw [viewed] at attempt
                      exact attempt)
              obtain ⟨issuedPhase, installed, member⟩ := requested.2.1
              have phaseEq : issuedPhase = entry.phase := by
                apply Option.some.inj
                exact (Option.mem_def.mp installed).symm.trans
                  ((congrArg (fun phases => phases.head?) (congrArg Prod.fst metadata)).trans
                    entry.installed)
              exact phaseEq ▸ member
            have field := frame.emissions message member sameNamespace declared inside candidate
              (call.trans packet) owner domain output
            obtain ⟨serial, opening, evidence, actualRecord, slot, _sender, actualRecorded,
                actualEmitted, actualDeclared, _fresh, _attempt, meaning⟩ :=
              issued_binding_record setup implementation control trace owner declared domain output
                candidate message member (call.trans packet)
            have recordsEq : actualRecord = record := recorded_emission_unique setup implementation
              trace owner actualRecord record actualRecorded recorded message
                actualEmitted emitted
            subst actualRecord
            have decoded : opening.bind (fun raw => raw.as? domain) = some value := by
              rw [actualDeclared] at prepared
              simp only [Option.bind_some, PhaseProposal.bindingPreparation, output,
                Option.map_eq_some_iff, Raw.mk.injEq] at prepared
              obtain ⟨draw, decoded, _samePayload, sameValue⟩ := prepared
              exact (eq_of_heq sameValue) ▸ decoded
            rw [meaning, decoded, Option.elim_some] at field
            exact (FieldRef.get?_preserved _ frontier.store key.2.1 retained _ field)
  exact {
    active := acting
    request := request
    unsent := clean.unsent
    payload := payload
    binding := clean.binding
    phase := entry.phase
    installed := entry.installed
    commitment := entry.commitment
    inside := entry.inside
    entry := entry.entry
    entryTrace := sourceCutTrace setup implementation entry.entryTrace
    nativeRetained := by
      have initialEq : ((setup.initialLaw.map encodeInputs).map
          (PhaseRuntimeState.initial implementation.plan)) = nativeInitial := PMF.map_comp _ _ _
      exact tracePrefix_initializer setup implementation initialEq.symm entry.retained
    sameAttempt := entry.sameAttempt
    entryInstalled := entry.entryInstalled
    entryIdle := entry.idle
    entryExcluded := entry.entryExcluded
    fresh := entry.fresh
    witness := entry.witness
    archived := entry.archived
    targetContext := entry.targetContext
    targetNames := entry.targetNames
    block := entry.block
    suffix := entry.suffix
    cursor := entry.cursor
    size := entry.size
    offset := entry.offset
    source := entry.source
    config := entry.config
    cursorHistory := entry.cursorHistory
    refs := entry.refs
    reconstruct := entry.reconstruct
    embedding := entry.embedding
    lift := entry.lift
    theta := theta
    thetaSupported := drawn
    originalInputs := original
    initializer := initial
    initializerTrace := first
    initialized := initialized
    sourceRetained := sourceRetained
    completed := completed
    key := key
    blockResult := result
    sourceSupported := supported
    graphSupported := graphSupported
    lockedStore := lockedStore
    lockedEmissions := lockedEmissions
    current := current
    trace := prior
    past := past
    future := future
    clock := clock
    rank := rank
    actor := actor
    atCommit := atCommit
    survives := survives }

omit [Fintype Player] in
private theorem generated_preparation_iff_joint_word (owner : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    setup.GeneratedPreparationHistory owner ⟨state, trace⟩ ↔
      ∃ joint ∈ setup.proposalRecoveryJointRecall trace,
        ProposalRecoveryMove.GeneratedPreparationFailure (joint owner) := by
  induction trace with
  | start => simp [Setup.GeneratedPreparationHistory, Setup.proposalRecoveryJointRecall,
      InfoSignals.ownPlay]
  | extend prior joint legal moved ih =>
      unfold Setup.GeneratedPreparationHistory at ih ⊢
      rw [InfoSignals.ownPlay_extend]
      cases selected : joint owner with
      | none =>
          simpa only [Setup.proposalRecoveryJointRecall, selected,
            ProposalRecoveryMove.GeneratedPreparationFailure, Option.elim_none,
            List.mem_cons, exists_eq_or_imp, false_or] using ih
      | some move =>
          simpa only [Setup.proposalRecoveryJointRecall, selected, List.mem_cons,
            exists_eq_or_imp] using (or_congr Iff.rfl ih)

/-- Ordinary completion introduces no unusable generated preparation. The
whole earlier source word, including canceled focal actions, stays literal. -/
theorem PhaseProposalCanonicalBindingCut.foreignGood
    (operational : implementation.Operational)
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId)
    (_entry : NativeBindingEntry setup implementation operational control trace who event)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values implementation.horizon
        implementation.scheduler control (sourceCutTrace setup implementation trace) who event)
    (same : (⟨some cut.cursor.current, cut.cursor.trace⟩ :
        setup.proposalRecoveryProtocol.History) =
      canonicalSource setup implementation operational ⟨some control, trace⟩)
    (foreign : ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler owner
          ⟨some control, trace⟩) :
    setup.proposalRecoveryForeignGood who ⟨some cut.current, cut.trace⟩ := by
  have good := canonicalSource_foreignGood setup implementation operational who
    ⟨some control, trace⟩ foreign
  rw [← same] at good
  obtain ⟨_finished, last, lastTrace, attempt, final, _point, _excluded, _entry, _generation,
      _word, labels, proper⟩ := proposalRecovery_ordinary_commit_block_support setup values
    cut.block cut.suffix cut.cursor.lift cut.cursor.origin cut.cursor.source cut.cursor.current
      cut.cursor.trace cut.cursor.point (cut.cursor.excluded.trans cut.cursor.entryExcluded.symm)
      cut.completed cut.sourceSupported
  apply source_good_prefix setup who cut.trace cut.completed.trace cut.future
  intro owner different generated
  rw [generated_preparation_iff_joint_word] at generated
  obtain ⟨joint, member, failed⟩ := generated
  rw [final, labels] at member
  rcases List.mem_append.mp member with fresh | earlier
  · obtain ⟨raw, rawMember, sameJoint⟩ := List.mem_map.mp fresh
    rw [← sameJoint] at failed
    cases selected : raw owner with
    | none => simp only [selected, Option.map_none,
        ProposalRecoveryMove.GeneratedPreparationFailure, Option.elim_none] at failed
    | some move =>
        have noFailure := (proper raw (List.mem_reverse.mp rawMember) owner move selected).2
        exact noFailure (ProposalRecoveryMove.generatedPreparationFailure_flags _ (by
          simpa only [selected, Option.map_some] using failed)).2
  · exact good owner different ((generated_preparation_iff_joint_word setup owner
      cut.cursor.trace).mpr ⟨joint, earlier, failed⟩)

/-- The canonical cut's source query is the actual physical decision query.
The classifier supplies ordinary current bindings, while readback retains the
complete public address word and original proposal archive. -/
theorem PhaseProposalCanonicalBindingCut.query
    (operational : implementation.Operational)
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who (control.execution.recall who)
      (control.execution.observe nativeApplication who) event payload)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values implementation.horizon
        implementation.scheduler control (sourceCutTrace setup implementation trace) who event) :
    phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
      implementation.plan who event (control.execution.recall who)
        (control.execution.observe nativeApplication who) =
      some (setup.proposalRecoveryQuery who (setup.proposalRecoveryModel.infoOf who cut.trace))
        := by
  let initial := (setup.initialLaw.map encodeInputs).map
    (PhaseRuntimeState.initial implementation.plan)
  have initialEq : initial = nativeInitial := PMF.map_comp _ _ _
  let counted : ((nativeMenu).protocol initial implementation.horizon
    implementation.scheduler).Trace (some control) := initialEq.symm ▸ trace
  let raw := (nativeMenu).toRawTrace initial implementation.horizon implementation.scheduler counted
  have readback := cut.source_view
  have ordinary : ProtocolState.BindingsHoldValues who setup.program cut.current.point := by
    rcases (setup.commitRecovery_bindingsHoldValues_or_failedBinding operational.wellFormed
      (setup.proposalRecoveryEraseTrace cut.trace) who cut.current rfl).2 with proper | failed
    · exact proper
    · exact False.elim (clean.noCurrent
        ((phaseProposalCurrentBindingFailure_iff_of_readback setup .concurrent
          implementation.runtime
          implementation.leaks who event _ cut.current.point readback).mpr failed))
  rw [phaseSurvivingSourceView?_observed_of_history setup .concurrent implementation.runtime
    implementation.leaks implementation.plan (setup.initialLaw.map encodeInputs)
      implementation.horizon implementation.scheduler raw who event] at readback
  have erased := congrArg (Option.map (ProtocolView.eraseHistory who setup.program)) readback
  rw [← decodeEventView?_eraseHistory, Option.map_some] at erased
  have typed : phaseVirtualSourceView? setup .concurrent implementation.runtime implementation.leaks
      who event (control.execution.observe nativeApplication who) =
        some (ProtocolView.virtualBindings who (setup.context.map Prod.fst).toFinset setup.program
          (ProtocolState.observe who setup.program cut.current.point)) := by
    unfold phaseVirtualSourceView?
    have ownerView : (control.execution.observe nativeApplication who).application.1.who = who
      := rfl
    rw [dite_eq_left ownerView]
    change (decodeEventView? setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program).ref who event
      ((serviceGraph setup .concurrent).playerStore who
        control.execution.application.current.native.config.store) []).map
        (ProtocolView.virtualBindings who (setup.context.map Prod.fst).toFinset setup.program) = _
    rw [erased, Option.map_some, ProtocolView.virtualBindings_eraseHistory]
  obtain ⟨controlRead, addresses, proposals⟩ := cut.native_readback
  let witness := (checkpointSelection setup implementation operational trace).val
  obtain ⟨rest, installed⟩ := List.head?_eq_some_iff.mp cut.installed
  have saved := PhaseRuntimeState.saved_excluded_eq_public_failures witness.exclusions
    witness.failures witness.receipts.exclusion.frontier cut.phase rest installed
  have first : control.execution.application.entry.excluded =
      ((control.execution.application.publicView.retired.map fun record =>
        record.2.sourceFailureFootprint.2).foldr (fun first last => first ∪ last) ∅ ∪
        control.execution.application.current.native.publicView.sourceFailureFootprint.1
          control.execution.application.attempt.phase) := by
    simp only [PhaseRuntimeState.publicView, State.sourceFailureFootprint_read,
      List.map_map, Function.comp_def,
      State.sourceFailureFootprint, List.foldr_map]
    exact saved
  have queried := ordinary_source_query_readback setup who cut.current cut.trace cut.survives
    ordinary
  rw [controlRead, first, addresses, proposals,
    ← PhaseRuntimeState.sourcePublicAddressWord_read implementation.plan] at queried
  unfold phaseProposalQuery? phaseVirtualSourceQuery?
  rw [typed, Option.map_some, Option.map_some]
  rw [PhaseProposal.observedSourceArchive_eq_submitted implementation.runtime implementation.leaks
    operational.completePending initial implementation.horizon implementation.scheduler control raw
      who cut.active]
  exact congrArg some queried

/-- At a genuine decoded source binding, successful typed payloads have one
legal ordinary enriched encoding. The entire unflagged source law is the
original domain table mapped through that encoding. -/
theorem PhaseProposalCanonicalBindingCut.binding_encoder
    (control : (nativeApplication).Control) (trace : (nativeProtocol).Trace (some control))
    (who : Player) (event : (serviceGraph setup .concurrent).EventId)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values implementation.horizon
        implementation.scheduler control (sourceCutTrace setup implementation trace) who event) :
    ∃ encode : L.Val cut.payload → setup.proposalRecoveryModel.Choice who
        (setup.proposalRecoveryModel.infoOf who cut.trace),
      (∀ value, phaseRecoveryBindingData setup .concurrent event who cut.payload cut.binding
        ((encode value).val.map (·.semantic)) = (.success value, false)) ∧
      sourceUnflaggedStrategy setup values who
        (setup.proposalRecoveryModel.infoOf who cut.trace) =
        (values who (setup.proposalRecoveryQuery who
          (setup.proposalRecoveryModel.infoOf who cut.trace))).map (fun sampled =>
            encode (phaseRecoveryDomainValue setup .concurrent event who cut.payload cut.binding
              sampled.val.val)) := by
  classical
  let info := setup.proposalRecoveryModel.infoOf who cut.trace
  let key := setup.proposalRecoveryQuery who info
  let initial := (setup.initialLaw.map encodeInputs).map
    (PhaseRuntimeState.initial implementation.plan)
  have initialEq : initial = nativeInitial := PMF.map_comp _ _ _
  let raw := (nativeMenu).toRawTrace initial implementation.horizon implementation.scheduler
    (initialEq.symm ▸ trace)
  have decoded := cut.source_view
  rw [phaseSurvivingSourceView?_observed_of_history setup .concurrent implementation.runtime
    implementation.leaks implementation.plan (setup.initialLaw.map encodeInputs)
      implementation.horizon implementation.scheduler raw who event] at decoded
  let actions (value : L.Val cut.payload) := decodeEventView_binding_value setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program).ref who event _ _ _ decoded who cut.payload cut.binding value
  let encode (value : L.Val cut.payload) : setup.proposalRecoveryModel.Choice who info :=
    ⟨some (ProposalRecoveryMove.ordinary ⟨(actions value).choose, false⟩), by
      apply (setup.proposalRecoveryModel.menu_adequate who cut.trace _).mpr
      exact ⟨⟨cut.actor, cut.survives⟩,
        ⟨(actions value).choose_spec.2.1, by simp [ProtocolState.atCommit_observe, cut.atCommit]⟩,
        ProposalRecoveryMove.ordinary_valid _⟩⟩
  have encoded (value : L.Val cut.payload) :
      phaseRecoveryBindingData setup .concurrent event who cut.payload cut.binding
        ((encode value).val.map (·.semantic)) = (.success value, false) := by
    have action := encodeEventAction?_decodeEventAction_eq_some setup.program event _ _
      (actions value).choose_spec.1
    simp only [encode, Option.map_some, ProposalRecoveryMove.ordinary, phaseRecoveryBindingData,
      Option.elim_some, Bool.false_eq_true, ↓reduceIte, Option.bind_some, action,
      Option.map_some, Option.getD_some, cast_cast, cast_eq]
  let lift (sampled : setup.CommitRecoveryValueChoice who key.1) :
      setup.proposalRecoveryModel.Choice who info :=
    (setup.proposalRecoveryComponentChoice who info).symm
      (setup.proposalRecoveryComponentLabelChoice who key false sampled.val)
  have lifted (sampled : setup.CommitRecoveryValueChoice who key.1) :
      (lift sampled).val = sampled.val.val.map ProposalRecoveryMove.ordinary := by
    change sampled.val.val.map (fun move => ProposalRecoveryMove.label move false) = _
    simp only [ProposalRecoveryMove.label_false]
  have same (sampled : setup.CommitRecoveryValueChoice who key.1) :
      lift sampled = encode (phaseRecoveryDomainValue setup .concurrent event who cut.payload
        cut.binding sampled.val.val) := by
    have legal := (setup.proposalRecoveryMenu_adequate who cut.trace (lift sampled).val).mp
      (lift sampled).property
    rw [lifted] at legal
    cases chosen : sampled.val.val with
    | none =>
        rw [chosen, Option.map_none] at legal
        exact (legal ⟨cut.actor, cut.survives⟩).elim
    | some move =>
        rw [chosen, Option.map_some] at legal
        have proper := sampled.property move chosen
        obtain ⟨graphAction, action⟩ := (source_binding_at_rank setup.program cut.current.point
          event who cut.payload cut.binding cut.rank.symm).2.2 move.action legal.2.1.1
        have encoding := encodeEventAction?_decodeEventAction_eq_some setup.program event
          graphAction move.action action
        have successful : cast (congrArg EventField.Action cut.binding) graphAction ≠ .failure := by
          intro failed
          exact proper.2 ((decodeEventAction_binding_failure_iff setup.program event who
            cut.payload cut.binding graphAction move.action action).mp failed)
        cases result : cast (congrArg EventField.Action cut.binding) graphAction with
        | failure => exact (successful result).elim
        | success value =>
            have data : phaseRecoveryBindingData setup .concurrent event who cut.payload
                cut.binding sampled.val.val = (.success value, false) := by
              simp only [chosen, phaseRecoveryBindingData, Option.elim_some, proper.1,
                Bool.false_eq_true, ↓reduceIte, Option.bind_some, encoding, Option.map_some,
                Option.getD_some, result]
            have domain : phaseRecoveryDomainValue setup .concurrent event who cut.payload
                cut.binding sampled.val.val = value := by
              unfold phaseRecoveryDomainValue
              rw [data]
            have graphEq : graphAction = cast (congrArg EventField.Action cut.binding.symm)
                (.success value) := by
              rw [← result]
              simp only [cast_cast, cast_eq]
            have actionEq : move.action = (actions value).choose :=
              Option.some.inj (action.symm.trans (graphEq ▸ (actions value).choose_spec.1))
            apply Subtype.ext
            have domainAt : phaseRecoveryDomainValue setup .concurrent event who cut.payload
                cut.binding (some move) = value := by
              simpa only [chosen] using domain
            rw [lifted, domainAt, chosen, Option.map_some]
            change some (ProposalRecoveryMove.ordinary move) =
              some (ProposalRecoveryMove.ordinary ⟨(actions value).choose, false⟩)
            cases move with
            | mk action missing =>
                dsimp only at proper actionEq
                cases proper.1
                cases actionEq
                rfl
  refine ⟨encode, encoded, ?_⟩
  have ordinary : sourceUnflaggedStrategy setup values who info =
      (values who key).map lift := by
    unfold sourceUnflaggedStrategy Setup.proposalRecoveryNormalizedTrembledProfile
      Setup.proposalRecoveryPrescribedProfile Setup.proposalRecoveryComponentTrembledLaw
      Setup.commitRecoveryValueTremble
    simp only [mix_zero, ite_self, PMF.pure_map]
    change (((values who key).map Subtype.val).map
      (fun choice => setup.proposalRecoveryComponentLabelChoice who key false choice)).map
        (setup.proposalRecoveryComponentChoice who info).symm = (values who key).map lift
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  rw [ordinary]
  apply congrArg (fun transform => (values who key).map transform)
  funext sampled
  exact same sampled

/-- A source witness tied to the actual before-action cuts at one native information site. -/
structure QualifiedBindingSource
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (who : Player)
    (nativeSite : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding who payload) where
  site : setup.proposalRecoveryModel.InformationSite who
  encode : L.Val payload → setup.proposalRecoveryModel.Choice who site.1
  anchor : setup.proposalRecoveryProtocol.History
  anchorInfo : setup.proposalRecoveryModel.infoOf who anchor.trace = site.1
  anchorGood : setup.proposalRecoveryForeignGood who anchor
  anchorReach : 0 < setup.proposalRecoveryModel.historyReachWeight sourceProfile anchor
  query : phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
      implementation.plan who event past view =
    some (setup.proposalRecoveryQuery who site.1)
  encoded : ∀ value, phaseRecoveryBindingData setup .concurrent event who payload binding
    ((encode value).val.map (fun move => move.semantic)) = (.success value, false)
  ordinary : sourceUnflaggedStrategy setup values who site.1 =
    (values who (setup.proposalRecoveryQuery who site.1)).map (fun sampled =>
      encode (phaseRecoveryDomainValue setup .concurrent event who payload binding sampled.val.val))
  actualCut : ∀ (control : (nativeApplication).Control)
    (trace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).Trace (some control))
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
      implementation.horizon implementation.scheduler control trace who event),
    ((nativeMenu).information
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.horizon implementation.scheduler).infoOf who trace = nativeSite.1 →
    setup.proposalRecoveryModel.infoOf who cut.trace = site.1

theorem qualified_source_site
    (operational : implementation.Operational)
    (scale sourceBad nativeBad : Set.Icc (0 : ℝ) 1)
    (scalePositive : 0 < scale.val) (scaleBelow : scale.val < 1)
    (sourceBadPositive : 0 < sourceBad.val) (sourceBadBelow : sourceBad.val < 1)
    (nativeBadPositive : 0 < nativeBad.val) (nativeBadBelow : nativeBad.val < 1)
    (fullValues : ∀ owner key, FullSupport (values owner key))
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (nativeProfile : ∀ owner,
      ((nativeMenu).information nativeInitial implementation.horizon
        implementation.scheduler).BehavioralPolicy owner)
    (sourcePrescribed : ∀ owner (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      sourceProfile owner (setup.proposalRecoveryModel.infoOf owner history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values owner
            (setup.proposalRecoveryModel.infoOf owner history.trace))
    (nativePrescribed : nativeProfile = phaseProposalReferenceStrategy setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
      nativeInitial implementation.horizon implementation.scheduler values
      ⟨nativeBad, scale, scale, scale⟩)
    (who : Player)
    (site : ((nativeMenu).information nativeInitial implementation.horizon
      implementation.scheduler).InformationSite who)
    (past : List (nativeApplication).PlayerEntry) (view : (nativeApplication).PlayerView)
    (siteEq : site.1 = some (past, view))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (clean : CleanUnsentBinding setup implementation who past view event payload)
    (qualified : 0 < qualifiedPrefixMass setup implementation nativeProfile who site event) :
    Nonempty (QualifiedBindingSource setup values implementation sourceProfile who site past view
      event payload clean.binding) := by
  classical
  have _nativeStrict := And.intro nativeBadPositive nativeBadBelow
  have _nativeProfile := nativePrescribed
  obtain ⟨history, tape, reached, tapeSupport, foreign, alive, admitted⟩ :=
    qualifiedPrefixMass_anchor setup implementation nativeProfile who site event qualified
  rcases history with ⟨⟨state, trace⟩, information⟩
  cases state with
  | none => simp only [bindingAdmissionBit, Bool.false_eq_true] at admitted
  | some control =>
      change ((nativeMenu).signals nativeInitial implementation.horizon
        implementation.scheduler).infoOf who trace = site.1 at information
      have observed := information.trans siteEq
      change ((nativeMenu).signals nativeInitial implementation.horizon
        implementation.scheduler).infoOf who trace = some (past, view) at observed
      rw [(nativeMenu).info nativeInitial implementation.horizon implementation.scheduler who trace]
        at observed
      have acting : control.actor = some who := by
        by_contra inactive
        simp only [ReactiveApplication.observe, inactive, ↓reduceIte, reduceCtorEq] at observed
      have input : (control.execution.recall who, control.execution.observe nativeApplication who) =
          (past, view) := by
        apply Option.some.inj
        simpa only [ReactiveApplication.observe, acting, ↓reduceIte] using observed
      have recalled : control.execution.recall who = past := congrArg Prod.fst input
      have viewed : control.execution.observe nativeApplication who = view := congrArg Prod.snd
        input
      have nativeClean : CleanUnsentBinding setup implementation who (control.execution.recall who)
          (control.execution.observe nativeApplication who) event payload := by
        simpa only [recalled, viewed] using clean
      obtain ⟨entry⟩ := qualified_binding_entry setup implementation operational control
        trace
        who event payload nativeClean foreign
      let cut := entry.canonicalCut setup values implementation
        operational fullValues control trace who acting event payload nativeClean foreign
      have canonical : (⟨some cut.cursor.current, cut.cursor.trace⟩ :
          setup.proposalRecoveryProtocol.History) =
          canonicalSource setup implementation operational ⟨some control, trace⟩ :=
        entry.canonicalHistory
      obtain ⟨encode, encoded, ordinary⟩ :=
        PhaseProposalCanonicalBindingCut.binding_encoder setup values implementation
          control trace who event cut
      have inhabited : Nonempty (L.Val cut.payload) := by
        change Nonempty (L.Val payload)
        change bindingAdmissionBit setup implementation who event ⟨some control, trace⟩ tape = true
          at admitted
        dsimp only [bindingAdmissionBit] at admitted
        split at admitted
        next offered =>
          obtain ⟨_material, _offered, domain, value, _serial, binding, _packet, _prepared⟩ :=
            offered
          have same := (EventField.binding.inj (nativeClean.binding.symm.trans binding)).2
          exact ⟨same.symm ▸ value⟩
        next absent => simp only [Bool.false_eq_true] at admitted
      let value := Classical.choice inhabited
      have decision : setup.proposalRecoveryModel.IsDecisionInfo who
          (setup.proposalRecoveryModel.infoOf who cut.trace) := by
        refine ⟨⟨⟨some cut.current, cut.trace⟩, rfl⟩, ?_, ?_⟩
        · intro terminal
          have none := ProtocolState.terminal_actor_none who setup.program cut.current.point
            terminal
          rw [ProtocolState.actor_observe_eq, cut.actor] at none
          cases none
        · cases chosen : (encode value).val with
          | none =>
              have inactive := (setup.proposalRecoveryMenu_adequate who cut.trace _).mp
                (encode value).property
              rw [chosen] at inactive
              exact (inactive ⟨cut.actor, cut.survives⟩).elim
          | some move => exact ⟨move, chosen ▸ (encode value).property⟩
      let sourceSite : setup.proposalRecoveryModel.InformationSite who :=
        ⟨setup.proposalRecoveryModel.infoOf who cut.trace, decision⟩
      have query := PhaseProposalCanonicalBindingCut.query setup values implementation operational
        control trace who event cut.payload nativeClean cut
      have good := PhaseProposalCanonicalBindingCut.foreignGood setup values implementation
        operational control trace who event entry cut canonical foreign
      have positive := prescribed_source_history_positive setup values scale sourceBad scalePositive
        scaleBelow sourceBadPositive sourceBadBelow fullValues sourceProfile sourcePrescribed
          ⟨some cut.current, cut.trace⟩
      refine ⟨{
        site := sourceSite
        encode := encode
        anchor := ⟨some cut.current, cut.trace⟩
        anchorInfo := rfl
        anchorGood := good
        anchorReach := positive
        query := by simpa only [recalled, viewed] using query
        encoded := encoded
        ordinary := ordinary
        actualCut := ?_ }⟩
      intro other otherTrace otherCut sameInfo
      have anchorInfo : ((nativeMenu).information
          ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
          implementation.horizon implementation.scheduler).infoOf who
          (sourceCutTrace setup implementation trace) = site.1 := by
        change ((nativeMenu).signals
          ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
          implementation.horizon implementation.scheduler).infoOf who
            (sourceCutTrace setup implementation trace) = site.1
        rw [(nativeMenu).info]
        have direct := information
        rw [(nativeMenu).info] at direct
        exact direct
      have sameNative : ((nativeMenu).information
          ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
          implementation.horizon implementation.scheduler).infoOf who otherTrace =
          ((nativeMenu).information
          ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
          implementation.horizon implementation.scheduler).infoOf who
            (sourceCutTrace setup implementation trace) := sameInfo.trans anchorInfo.symm
      exact otherCut.info_eq_of_information cut operational.completePending sameNative


end NativeCheckpoint
end Vegas.PhaseProposalQualifiedBinding
