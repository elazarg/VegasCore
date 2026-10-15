/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryIntendedBindingCheckpoint
import Vegas.Game.RecoveryReadyCommitInformation
import Vegas.Game.PhaseRecoveryBindingComponent
import Vegas.Compile.CommitPrefixAdmittedAction

/-! # Guard admission of the original copied source draw at a binding callback -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- At an actual ready callback, the copied auxiliary draw is an admitted original
source binding. Hidden intended completion is used only to recover its full focal
information; the result and guard prediction concern the actual filled prefix. -/
theorem phase_binding_source_choice_admitted
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (target : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source target)
    (execution : (phaseApplication runtime leaks).Execution)
    (checkpoint : RecoverySourceCheckpoint setup mode execution.application)
    {Δ : SourceCtx Player L} {P : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P))
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard next) = checkpoint.residual.tail)
    (clear : execution.application.entry.excluded = ∅)
    (stored : execution.application.StoredCheckpoint)
    (savedIntended : ProtocolState.Intended setup.program
      (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source)))
    (selected : Fin (eventCount checkpoint.residual.tail)) (atEnd : selected.val = earlier.length)
    (ready : execution.application.current.native.config.cut.Ready
      (checkpoint.embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (checkpoint.embedding.event selected) = some owner)
    (binding : (serviceGraph setup mode).outputLayout (checkpoint.embedding.event selected) =
      .binding owner payload)
    (valid : execution.application.current.native.BindingInvariant) {inputs}
    (reachable : execution.application.current.native.config.Reachable inputs)
    (retained : execution.application.HistoryCheckpoint)
    (saved : execution.application.entry.native.config.cut.IsPrefix
      execution.application.attempt.phase)
    (ownAdmitted :
      let embedding := cast (congrArg
        (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
          program) reconstruct.symm) checkpoint.embedding
      (fillCommitPrefix setup.program earlier (.commit name owner fresh guard next) embedding
        execution.application.current.native.config.store checkpoint.source).IntendedFor owner P)
    (choice : setup.commitRecoveryModel.Choice owner
      (setup.commitRecoveryClearInformation wellFormed owner
        (phaseSourceView? setup mode runtime leaks owner (checkpoint.embedding.event selected)
          (execution.observe (phaseApplication runtime leaks) owner))))
    (supported : choice ∈ (target owner (setup.commitRecoveryClearInformation wellFormed owner
      (phaseSourceView? setup mode runtime leaks owner (checkpoint.embedding.event selected)
        (execution.observe (phaseApplication runtime leaks) owner)))).support) :
    let embedding := cast (congrArg
      (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) reconstruct.symm) checkpoint.embedding
    let filled := fillCommitPrefix setup.program earlier (.commit name owner fresh guard next)
      embedding execution.application.current.native.config.store checkpoint.source
    ∃ value,
      phaseRecoveryBindingData setup mode (checkpoint.embedding.event selected) owner payload
        binding choice.1 = (.success value, false) ∧
      guard.predicts (sourceObserve owner filled.state) value = true ∧
      (commitSuccessor name guard filled (.success value)).IntendedFor owner (insert name P) := by
  have notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (checkpoint.embedding.event selected)).IsPublication := by
    rw [binding]
    simp only [EventField.IsPublication, not_false_eq_true]
  have historyAligned := checkpoint.filled_prefix_history_of_ready fresh guard next earlier
    reconstruct clear selected atEnd ready acting valid reachable retained saved
  have filledView := checkpoint.filled_prefix_view fresh guard next earlier reconstruct stored
    selected atEnd ready acting notPublication _ historyAligned
  obtain ⟨site, original, intendedView⟩ := checkpoint.intended_binding_information wellFormed
    fresh guard next earlier reconstruct clear stored savedIntended selected atEnd ready acting
      notPublication _ historyAligned ownAdmitted
  have actualInfo := (phaseSourceView?_observed setup mode runtime leaks execution owner
    (checkpoint.embedding.event selected)).trans intendedView
  have clearInfo : setup.commitRecoveryClearInformation wellFormed owner site.1 =
      setup.commitRecoveryInformation wellFormed owner site.1 := by
    rw [← original.2]
    exact setup.commitRecoveryClearInformation_intended wellFormed owner original.1
  have rawLaw : (target owner (setup.commitRecoveryClearInformation wellFormed owner
        (phaseSourceView? setup mode runtime leaks owner (checkpoint.embedding.event selected)
          (execution.observe (phaseApplication runtime leaks) owner)))).map Subtype.val =
      (source owner site.1).map (fun originalChoice =>
        CommitRecoveryMove.lift originalChoice.1) := by
    rw [actualInfo, clearInfo]
    change PMF.map _ (target owner
      ((setup.commitRecoveryRestriction wellFormed).information owner site.1)) = _
    rw [copies owner site, PMF.map_comp]
    rfl
  have sampled : choice.1 ∈ ((target owner (setup.commitRecoveryClearInformation wellFormed owner
        (phaseSourceView? setup mode runtime leaks owner (checkpoint.embedding.event selected)
          (execution.observe (phaseApplication runtime leaks) owner)))).map
            Subtype.val).support := by
    rw [PMF.support_map]
    exact ⟨choice, supported, rfl⟩
  rw [rawLaw] at sampled
  obtain ⟨originalChoice, _chosen, raw⟩ := PMF.support_map .. ▸ sampled
  obtain ⟨view, decoded⟩ := phaseSourceView?_succeeds setup mode runtime leaks execution owner
    (checkpoint.embedding.event selected) ready acting notPublication
  have siteView : site.1 = some view := actualInfo.symm.trans decoded
  have actor := (phaseSourceView?_actor setup mode runtime leaks execution owner
    (checkpoint.embedding.event selected) view decoded).trans acting
  have legal := originalChoice.2
  change setup.intendedMenu owner site.1 originalChoice.1 at legal
  have legalHere : setup.intendedMenu owner (some view) originalChoice.1 :=
    (congrArg (fun information => setup.intendedMenu owner information originalChoice.1)
      siteView) ▸ legal
  clear legal
  have legal := legalHere
  clear legalHere
  cases sourceValue : originalChoice.1 with
  | none =>
      rw [sourceValue] at legal
      exact (legal actor).elim
  | some action =>
      rw [sourceValue] at legal
      have offered := legal.2
      obtain ⟨graphAction, decodedAction⟩ := phaseSourceView?_available setup mode runtime leaks
        execution owner (checkpoint.embedding.event selected) view decoded action
          (ProtocolView.intendedAvailable_subset owner setup.program
            (CommitmentInterface.forfeiture setup.program) view offered)
      have rawChoice : choice.1 = some ⟨action, false⟩ := by
        rw [← raw]
        change CommitRecoveryMove.lift originalChoice.1 = _
        rw [sourceValue]
        rfl
      have offeredFilled := offered
      have sameView := intendedView.symm.trans filledView
      rw [siteView] at sameView
      have sameObserve := Option.some.inj sameView
      rw [sameObserve] at offeredFilled
      rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, entry, refs, registry, embedding, before,
        compiled, terminalAlignment, agrees, guards, failures, unique, ranks, actors, commits,
        owners, endpoints, automatic, histories, memories, steps, menus, readout, initialized,
        views, _savedHistory, origin⟩
      dsimp only at *
      change SourceProgram.Config Player L Γ at entry
      change ContextRefs (graphLayout setup.program) Γ at refs
      change OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program
        at embedding
      change SourceProgram.CommitPrefix Γ O Δ P at earlier
      change Fin (eventCount program) at selected
      change earlier.prepend (.commit name owner fresh guard next) = program at reconstruct
      subst program
      obtain ⟨value, result, predicts, nextAdmitted⟩ := compiledCommitPrefix_action_admitted
        setup.program fresh guard next earlier embedding refs lift origin views
          execution.application.current.native.config.store entry savedIntended ownAdmitted
            selected atEnd binding graphAction action decodedAction offeredFilled
      refine ⟨value, ?_, predicts, nextAdmitted⟩
      rw [rawChoice]
      have encoded := encodeEventAction?_decodeEventAction_eq_some setup.program
        (embedding.event selected) graphAction action decodedAction
      simp only [phaseRecoveryBindingData, Option.elim_some, Bool.false_eq_true, ↓reduceIte,
        Option.bind_some, encoded, Option.map_some, Option.getD_some, result]

end Vegas
