/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledReadyReveal
import Vegas.Game.RecoveryReadyRevealPrefix
import Vegas.Game.PhaseIntendedCheckpointHistory

/-! # Successful current publication kernels at actual clear copied histories -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Every ready current publication at a genuine clear canonical history has
a successful guarded output. The saved intended checkpoint, partial source
reveal meanings and all actual execution invariants are derived internally. -/
theorem phase_ready_publication_success
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
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (consistent : ∀ owner, (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      owner).Consistent (control.execution.recall owner))
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (publication : ((serviceGraph setup mode).outputLayout event).IsPublication) :
    ∃ payload binding checks outputEq codeEq,
      nodeView (serviceGraph setup mode) event =
        .resolve who payload binding checks outputEq codeEq ∧
      ∃ value, EventCode.resolveOutput? binding checks true
        control.execution.application.current.native.config.store = some (.success value) := by
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  have raw := menu.toRawTrace (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  obtain ⟨checkpoint, savedIntended⟩ := phase_intended_checkpoint_history setup mode runtime leaks
    bounds wellFormed source assessment copies plan maximal horizon scheduler trace clear consistent
  have exclusion := phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler raw
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler raw
  have coverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler raw
  obtain ⟨_draw, native⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    raw
  obtain ⟨phase, remaining, installed, inside⟩ :
      ∃ phase remaining, control.execution.application.phases = phase :: remaining ∧
        event ∈ phase.events := by
    obtain ⟨phase, member, inside⟩ := request.2.1
    cases installed : control.execution.application.phases with
    | nil => simp only [installed, List.head?_nil, Option.not_mem_none] at member
    | cons current remaining =>
        simp only [installed, List.head?_cons, Option.mem_some_iff] at member
        subst phase
        exact ⟨current, remaining, rfl, inside⟩
  have kind : phase.kind = .reveal := by
    have interval := (phase.mem_events event).mp inside
    have typed := phase.fields event interval.1 interval.2
    cases kind : phase.kind with
    | reveal => rfl
    | commitment =>
        rw [kind] at typed
        obtain ⟨owner, payload, binding⟩ := typed
        rw [binding] at publication
        exact publication.elim
    | sample =>
        rw [kind] at typed
        obtain ⟨payload, sampled⟩ := typed
        rw [sampled] at publication
        exact publication.elim
  obtain ⟨selected, selectedEq, reveals⟩ := checkpoint.ready_reveal_prefix exclusion.frontier phase
    remaining installed kind event inside request.2.2.1
  have atEntry := checkpoint.origin.intended_reflect _ savedIntended
  have entryConfig : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (config : SourceProgram.Config Player L Γ),
      ProtocolState.Intended program (ProtocolState.entry program config) → config.Intended O := by
    intro Γ O program config intended
    cases program with
    | ret => exact intended
    | sample => exact intended.1
    | commit => exact intended.1
    | reveal => exact intended.1
  have sourceIntended := entryConfig checkpoint.residual.tail checkpoint.source atEntry
  have agree : checkpoint.refs.Agrees checkpoint.source.state
      control.execution.application.current.native.config.store := by
    intro name cell selected
    exact (checkpoint.refs.get selected).get?_preserved _ _ stored _ (checkpoint.agrees selected)
  let prefixed := reveals selected.val (Nat.le_succ _)
  obtain ⟨final, finalIntended, finalAgree, _finalBindings, finalGuards, finalRevelations⟩ :=
    intended_reveal_prefix_present selected.val setup mode checkpoint.residual.tail prefixed
      checkpoint.refs checkpoint.registry checkpoint.embedding checkpoint.before
        control.execution.application.attempt.phase checkpoint.source checkpoint.compiled
          control.execution.application.current native.active.reachable coverage.active clear
            sourceIntended agree.present (fun selected => agree selected) checkpoint.guards
  let tail := revealTail selected.val checkpoint.residual.tail prefixed
  let refs := revealTailRefs setup selected.val checkpoint.residual.tail prefixed checkpoint.refs
    checkpoint.embedding
  let embedding := revealTailEmbedding setup selected.val checkpoint.residual.tail prefixed
    checkpoint.embedding
  let before : ContextRefsBefore refs embedding := revealTailRefsBefore selected.val
    checkpoint.residual.tail prefixed checkpoint.refs
    checkpoint.embedding checkpoint.before
  let registry : Registry tail.context := revealTailRegistry selected.val checkpoint.residual.tail
    prefixed
    checkpoint.registry
  have compiled := CompiledSuffix.revealTailMany setup selected.val checkpoint.residual.tail
    prefixed
    checkpoint.refs checkpoint.source.revelations checkpoint.registry checkpoint.embedding
      checkpoint.before control.execution.application.attempt.phase checkpoint.compiled
  rw [← finalRevelations] at compiled
  have first : RevealPrefix tail.tail 1 := RevealPrefix.revealTail_one selected.val
    checkpoint.residual.tail prefixed (reveals _ (Nat.le_refl _))
  have rank : event.val = control.execution.application.attempt.phase + selected.val := by
    rw [← selectedEq, checkpoint.compiled.rankEq]
  obtain ⟨owner, payload, binding, checks, outputEq, codeEq, node, value, resolved⟩ :=
    compiled_intended_head_reveal_success setup mode tail.tail first refs registry embedding before
      (control.execution.application.attempt.phase + selected.val) final compiled
        control.execution.application.current finalIntended finalAgree finalGuards event rank
          request.2.2.1
  have acting : (serviceGraph setup mode).actor? event = some owner :=
    (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
  have ownerEq : owner = who := Option.some.inj (acting.symm.trans request.2.2.2.1)
  subst owner
  exact ⟨payload, binding, checks, outputEq, codeEq, node, value, resolved⟩

end Vegas
