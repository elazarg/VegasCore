/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalCanonicalSourceBlock
import Vegas.Game.PhaseProposalBindingWord
import Vegas.Compile.CommitPrefixWordReadout

/-! # Original ordinary instructions read from their completed typed source fields -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO)
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- Completed references retain every entry cell of the actual typed attempt.
The result applies equally to active actions and automatic excluded slots. -/
theorem commitBlockRefs_agrees_entry (block : SourceProgram.CommitPrefix Γ O Δ P) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
        (block.prepend suffix)) (refs : ContextRefs (graphLayout whole) Γ)
      (store : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ)
      (excluded : Finset Player) (finished : SourceProgram.Config Player L Δ)
      (after : Finset Player) (_attempt : block.Attempt entry excluded finished after),
      (commitBlockRefs whole block suffix embedding refs).Agrees finished.state store →
        refs.Agrees entry.state store := by
  induction block with
  | nil =>
      intro suffix embedding refs store entry excluded finished after attempt agreement
      cases attempt
      exact agreement
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      intro suffix embedding refs store entry excluded finished after attempt agreement
      let zero : Fin (eventCount
          ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix)) :=
        ⟨0, by simp only [SourceProgram.CommitPrefix.prepend, eventCount]; omega⟩
      let field : FieldRef (graphLayout whole) (.binding owner payload) :=
        ⟨.inr (embedding.event zero), by
          change outputLayout whole (embedding.event zero) = .binding owner payload
          simpa only [zero, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
            Fin.cases_zero]
            using embedding.layout_eq zero⟩
      let tailEmbedding := embedding.tail (rest.prepend suffix)
        (by simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      let tailRefs := refs.cons (name := name) (cell := .commitment owner payload) field
      cases attempt with
      | active active choice missed valid later =>
          have middle : tailRefs.Agrees (commitSuccessor name guard entry choice).state store :=
            ih suffix tailEmbedding tailRefs store _ _ finished after later agreement
          intro readName cell selected
          exact middle (.there selected)
      | excluded inactive later =>
          have middle : tailRefs.Agrees (automaticCommit name owner payload entry).state store :=
            ih suffix tailEmbedding tailRefs store _ _ finished after later agreement
          intro readName cell selected
          exact middle (.there selected)

/-- The current binding readout is exactly the actual ordinary instruction
word. The filler may have any old hidden state or history: the addressed
readout uses the completed immutable binding cells, while excluded owners
retain literal automatic NONE instructions. -/
theorem phaseProposalBindingWord_of_ordinary_attempt (block : SourceProgram.CommitPrefix Γ O Δ P) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
        (block.prepend suffix)) (refs : ContextRefs (graphLayout whole) Γ)
      (store : Store (graphLayout whole)) (entry filler : SourceProgram.Config Player L Γ)
      (excluded : Finset Player) (finished : SourceProgram.Config Player L Δ)
      (after : Finset Player) (attempt : block.Attempt entry excluded finished after),
      after = excluded →
      (commitBlockRefs whole block suffix embedding refs).Agrees finished.state store →
        phaseProposalBindingWord whole block suffix embedding excluded store filler =
          attempt.joints := by
  induction block with
  | nil =>
      intro suffix embedding refs store entry filler excluded finished after attempt unchanged
        agreement
      cases unchanged
      cases attempt
      rfl
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      intro suffix embedding refs store entry filler excluded finished after attempt unchanged
        agreement
      cases unchanged
      let zero : Fin (eventCount
          ((SourceProgram.CommitPrefix.commit name owner fresh guard rest).prepend suffix)) :=
        ⟨0, by simp only [SourceProgram.CommitPrefix.prepend, eventCount]; omega⟩
      let field : FieldRef (graphLayout whole) (.binding owner payload) :=
        ⟨.inr (embedding.event zero), by
          change outputLayout whole (embedding.event zero) = .binding owner payload
          simpa only [zero, SourceProgram.CommitPrefix.prepend, outputLayout, Fin.mk_zero,
            Fin.cases_zero]
            using embedding.layout_eq zero⟩
      let tailEmbedding := embedding.tail (rest.prepend suffix)
        (by simp only [SourceProgram.CommitPrefix.prepend, eventCount]) (fun _ => rfl)
      let tailRefs := refs.cons (name := name) (cell := .commitment owner payload) field
      let choice := (field.get? store).getD .failure
      let nextFiller := commitSuccessor name guard filler choice
      have wordCons : phaseProposalBindingWord whole
          (.commit name owner fresh guard rest) suffix embedding excluded store filler =
          (fun who => if who ∈ excluded then none else if owner = who then
            some ⟨OwnAction.commit owner name payload choice, false⟩ else none) ::
          phaseProposalBindingWord whole rest suffix tailEmbedding excluded store nextFiller := by
        have projected := SourceProgram.CommitPrefix.Attempt.entryView_eq rest nextFiller _
          (fillCommitPrefix_attempt whole rest suffix tailEmbedding store nextFiller) owner
        have headCell : (((rest.entryView owner
            ((fillCommitPrefix whole rest suffix tailEmbedding store
              nextFiller).view owner)).1.cells name
                (.commitment owner payload) .here).getD .failure) = choice := by
          rw [projected]
          simp only [nextFiller, commitSuccessor, Config.view, sourceObserve_commitment,
            ite_true, Option.getD_some]
          rfl
        simp only [phaseProposalBindingWord, SourceProgram.CommitPrefix.length,
          List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def]
        apply congrArg₂ List.cons
        · funext who
          by_cases inactive : who ∈ excluded
          · simp only [inactive, ↓reduceIte]
          · simp only [inactive, ↓reduceIte]
            by_cases own : owner = who
            · subst who
              simp only [SourceProgram.CommitPrefix.wordAction, ite_true]
              rw [show fillCommitPrefix whole (.commit name owner fresh guard rest) suffix
                embedding store filler =
                  fillCommitPrefix whole rest suffix tailEmbedding store nextFiller by rfl]
              rw [headCell]
              rfl
            · simp only [SourceProgram.CommitPrefix.wordAction, ite_eq_right own, Option.map_none]
        · rfl
      rw [wordCons]
      cases attempt with
      | active active result missed valid later =>
          cases missed with
          | true =>
              have inherited : owner ∈ excludeCommit excluded owner true := by
                simp only [excludeCommit, ↓reduceIte, Finset.mem_insert, true_or]
              exact (active (later.excluded_subset inherited)).elim
          | false =>
              have middle : tailRefs.Agrees (commitSuccessor name guard entry result).state
                  store := commitBlockRefs_agrees_entry whole rest suffix tailEmbedding
                tailRefs store _ _ finished excluded later agreement
              have stored : field.get? store = some result := middle HasVar.here
              have chosen : choice = result := by
                simp only [choice, stored, Option.getD_some]
              have tailWord := ih suffix tailEmbedding tailRefs store _ nextFiller excluded
                finished excluded later rfl agreement
              rw [tailWord]
              simp only [SourceProgram.CommitPrefix.Attempt.joints]
              congr 1
              funext who
              by_cases same : who = owner
              · subst who
                simp only [active, ↓reduceIte, chosen]
              · by_cases inactive : who ∈ excluded
                · simp only [inactive, ↓reduceIte, same]
                · simp only [inactive, ↓reduceIte, same, Ne.symm same]
      | excluded inactive later =>
          have tailWord := ih suffix tailEmbedding tailRefs store _ nextFiller excluded
            finished excluded later rfl agreement
          rw [tailWord]
          simp only [SourceProgram.CommitPrefix.Attempt.joints]
          congr 1
          funext who
          by_cases inherited : who ∈ excluded
          · simp only [inherited, ↓reduceIte]
          · have foreign : owner ≠ who := fun own => inherited (own ▸ inactive)
            simp only [inherited, ↓reduceIte, ite_eq_right foreign]

variable [Fintype Player]

/-- The complete frozen graph binding word has the law of the literal most
recent ordinary source instructions, starting from the same enriched history.
This projects the full history coupling; no source own history is replaced
by the auxiliary graph completion recall. -/
theorem phaseProposalBindingPotentialProfile_source_word_law
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (anchor : (phaseApplication runtime leaks).Control)
    (anchorTrace : ((phaseApplication runtime leaks).protocol
      initial horizon scheduler).Trace (some anchor))
    (phase : RuntimePhase (serviceGraph setup mode))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
      block suffix) :
    ((serviceGraph setup mode).canonicalContinuation
      (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor.execution phase
        values) cursor.config).map
          (fun key => phaseProposalBindingWord setup.program block suffix cursor.embedding
            cursor.current.excluded key.2.1 cursor.source) =
      (setup.proposalRecoveryModel.runBehavioralFrom
        (setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
        block.length ⟨some cursor.current, cursor.trace⟩).map
          (fun history => ((setup.recoveryJointRecall
            (setup.proposalRecoveryEraseTrace history.trace)).take block.length).reverse) := by
  obtain ⟨joint, first, second, supported, _prefixMarginal⟩ :=
    phaseProposalBindingPotentialProfile_source_block_coupling setup mode runtime leaks plan
      initial horizon scheduler anchor anchorTrace phase values block suffix cursor
  rw [← second, PMF.map_comp, ← first, PMF.map_comp]
  apply map_congr_on_support joint
  intro pair reached
  change phaseProposalBindingWord setup.program block suffix cursor.embedding
      cursor.current.excluded pair.2.2.1 cursor.source =
    ((setup.recoveryJointRecall
      (setup.proposalRecoveryEraseTrace pair.1.trace)).take block.length).reverse
  obtain ⟨finished, last, lastTrace, attempt, historyEq, point, excluded, generation, live,
    agreement, word, _labelledWord⟩ := supported pair reached
  have read := phaseProposalBindingWord_of_ordinary_attempt setup.program block suffix
    cursor.embedding cursor.refs pair.2.2.1 cursor.source cursor.source cursor.current.excluded
      finished last.excluded attempt excluded agreement
  rw [read, historyEq]
  change attempt.joints = ((setup.recoveryJointRecall
    (setup.proposalRecoveryEraseTrace lastTrace)).take block.length).reverse
  rw [word]
  have takeWord : (attempt.joints.reverse ++ setup.recoveryJointRecall
      (setup.proposalRecoveryEraseTrace cursor.trace)).take block.length =
        attempt.joints.reverse := by
    rw [← attempt.joints_length, ← List.length_reverse, List.take_left]
  rw [takeWord, List.reverse_reverse]


/-- The single structural owner-word law, after masking inherited excluded
rows, is exactly the actual ordinary enriched-source block law. The source
coordinate retains its original prior history; synthetic excluded actions
are used only by the structural readout. -/
theorem ordinaryBlockProfile_source_word_law
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (anchor : (phaseApplication runtime leaks).Control)
    (anchorTrace : ((phaseApplication runtime leaks).protocol
      initial horizon scheduler).Trace (some anchor))
    (phase : RuntimePhase (serviceGraph setup mode))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (cursor : PhaseProposalOrdinarySourceCursor setup mode runtime leaks plan anchor phase
      block suffix) :
    let controls : Finset Player × Nat × Nat :=
      ((anchor.execution.application.publicView.retired.map fun record =>
        record.2.sourceFailureFootprint.2).foldr (fun first last => first ∪ last) ∅ ∪
          anchor.execution.application.current.native.publicView.sourceFailureFootprint.1
            anchor.execution.application.attempt.phase,
        anchor.execution.application.attempt.generation,
        anchor.execution.application.attempt.phase)
    let typed := ordinaryBlockProfile setup mode plan values block suffix cursor.embedding
      (fun who view => cursor.views.view who view) controls
        anchor.execution.application.publicView
        (PhaseProposal.sourceArchive anchor.execution.network.inputs)
    (block.prefixLaw suffix typed cursor.source).map (fun completed =>
      (List.range block.length).map fun index who =>
        if who ∈ cursor.current.excluded then none else
          (block.wordAction who index (completed.view who)).map
            (fun action => (⟨action, false⟩ : CommitRecoveryMove Player L))) =
      (setup.proposalRecoveryModel.runBehavioralFrom
        (setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
        block.length ⟨some cursor.current, cursor.trace⟩).map
          (fun history => ((setup.recoveryJointRecall
            (setup.proposalRecoveryEraseTrace history.trace)).take block.length).reverse) := by
  classical
  intro controls typed
  obtain ⟨joint, _first, second, _supported, marginal⟩ :=
    phaseProposalBindingPotentialProfile_source_block_coupling setup mode runtime leaks plan
      initial horizon scheduler anchor anchorTrace phase values block suffix cursor
  have filled := marginal cursor.source (fun _ _ => rfl)
  change joint.map (fun pair => fillCommitPrefix setup.program block suffix cursor.embedding
    pair.2.2.1 cursor.source) = block.prefixLaw suffix typed cursor.source at filled
  rw [← filled, PMF.map_comp]
  change joint.map ((fun key => phaseProposalBindingWord setup.program block suffix
    cursor.embedding cursor.current.excluded key.2.1 cursor.source) ∘ Prod.snd) = _
  rw [← PMF.map_comp, second]
  exact phaseProposalBindingPotentialProfile_source_word_law setup mode runtime leaks plan
    initial horizon scheduler anchor anchorTrace phase values block suffix cursor

end Vegas
