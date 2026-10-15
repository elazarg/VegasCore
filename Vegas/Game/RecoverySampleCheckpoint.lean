/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySourceBoundary
import Vegas.Game.CompiledSampleReadback
import Vegas.Pending.PhaseExclusionRecord
import Vegas.Pending.PhaseStoredCheckpoint
import Vegas.Pending.PhaseHistoryCheckpoint
import Vegas.Game.RecordedSourceHistory
import Vegas.Source.CommitRecoveryPathLift

/-! # Saved source checkpoints after actual singleton sample phases -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A completed actual sampling interval supplies its supported source draw and
advances the saved source checkpoint, retaining the one initialized setup trace. -/
theorem RecoverySourceCheckpoint.after_sample
    {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (remaining : List (RuntimePhase ((toEventGraph setup.program).withMode mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .sample)
    (exclusion : state.ExclusionRecord) (stored : state.StoredCheckpoint)
    (remembered : state.HistoryCheckpoint)
    {inputs : ((toEventGraph setup.program).withMode mode).Inputs}
    (reachable : (phase.drain state.current).native.config.Reachable inputs)
    (finished : phase.Finished (phase.drain state.current)) :
    Nonempty (RecoverySourceCheckpoint setup mode
      (⟨remaining, state.generation, phase.drain state.current, phase.drain state.current,
        state.retired⟩ : PhaseRuntimeState ((toEventGraph setup.program).withMode mode))) := by
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, terminalAligned, agrees, guards, failures, unique, ranks, actors, commits,
    owners, endpoints, automatic, histories, memories, steps, menus, readouts, trace, views,
    historyAlignment⟩
  let image := phase.drain state.current
  have low : phase.low = state.attempt.phase := by
    rw [PhaseRuntimeState.attempt, installed]
    rfl
  have singleton := phase.sample_singleton kind
  have total := compiled.countEq
  change state.attempt.phase + eventCount program = eventCount setup.program at total
  have positive : 0 < eventCount program := by
    have bounded := phase.bounded
    change phase.high ≤ eventCount setup.program at bounded
    have nonempty := phase.nonempty
    omega
  let zero : Fin (eventCount program) := ⟨0, positive⟩
  have ranked : (embedding.event zero).val = phase.low := by
    rw [compiled.rankEq]
    dsimp only [zero]
    omega
  have headSample : RuntimePhaseKind.sample.Matches (outputLayout program zero) := by
    have typed := phase.fields (embedding.event zero) (by omega)
      (by have nonempty := phase.nonempty; omega)
    rw [kind] at typed
    change RuntimePhaseKind.sample.Matches (outputLayout setup.program (embedding.event zero))
      at typed
    rw [embedding.layout_eq] at typed
    exact typed
  cases program with
  | ret payoffs => simp only [eventCount] at positive; omega
  | commit name owner fresh guard next =>
      obtain ⟨payload, impossible⟩ := headSample
      cases impossible
  | reveal published owner name fresh selected unresolved next =>
      obtain ⟨payload, impossible⟩ := headSample
      cases impossible
  | @sample _ _ name payload fresh law next =>
      let event := embedding.event zero
      have outputEq : ((toEventGraph setup.program).withMode mode).outputLayout event =
          .publicData payload := by
        change outputLayout setup.program (embedding.event zero) = _
        simpa only [zero, outputLayout, Fin.mk_zero, Fin.cases_zero] using embedding.layout_eq zero
      have codeEq : cast (congrArg (EventCode (graphLayout setup.program)) outputEq)
          ((toEventGraph setup.program).nodes event) =
            .sample payload (compilePublicDist refs law) := by
        simpa only [event, zero, compileRankedNodes, outputLayout, Fin.mk_zero, Fin.cases_zero]
          using compiled.nodeEq zero
      have ownerless : ((toEventGraph setup.program).withMode mode).actor? event = none :=
        (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
      have member : phase ∈ state.phases.head? := by
        simp only [installed, List.head?_cons, Option.mem_some_iff]
      have within := exclusion.frontier.positioned
      rw [installed] at within
      have excludedEq : image.excluded = state.entry.excluded := by
        rw [phase.drain_excluded]
        apply Finset.ext
        intro who
        rw [(exclusion.installed phase member).excluded]
        constructor
        · rintro (old | ⟨query, lower, actor, failed⟩)
          · exact old
          · have upper := within.2.2 query failed.completed
            have same : query = event := Fin.ext (by dsimp only [event]; omega)
            rw [same, ownerless] at actor
            cases actor
        · exact Or.inl
      have completed : event ∈ image.native.config.cut.completed :=
        finished ((phase.mem_events event).mpr ⟨by omega, by omega⟩)
      have entryAgree : refs.Agrees source.state image.native.config.store := by
        intro readName cell selected
        apply (refs.get selected).get?_preserved state.entry.native.config.store
          image.native.config.store
          (fun field value present => phase.drain_keepsStore state.current field value
            (stored field value present))
        exact agrees selected
      obtain ⟨sampled, supported, finalAgree, finalGuards, finalFailures, _transition⟩ :=
        completed_sample_source_successor fresh law next image.native.config reachable event
          completed outputEq refs source registry codeEq entryAgree guards failures
      let after := sampleSuccessor name source sampled
      let tailEmbedding := embedding.tail next (by simp only [eventCount]) (fun _ => rfl)
      let tailRefs := refs.cons (name := name) (cell := .publicData payload) ⟨.inr event, outputEq⟩
      have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
        intro readName cell selected later
        cases selected with
        | here =>
            change (embedding.event zero).val < (embedding.event (Fin.succ later)).val
            apply embedding.strictMono
            change 0 < later.val + 1
            omega
        | there selected => exact before selected (Fin.succ later)
      have path : Relation.ReflTransGen
          (fun earlier later : ProtocolState (.sample name fresh law next) × Finset Player =>
            ¬ ProtocolState.terminal (.sample name fresh law next) earlier.1 ∧
            ProtocolState.atCommit (.sample name fresh law next) earlier.1 = false ∧
            ∃ joint, later ∈ (ProtocolState.recoveryStep (.sample name fresh law next)
              earlier.1 earlier.2 joint).support)
          (Sum.inl source, state.entry.excluded)
          (Sum.inr (ProtocolState.entry next after), state.entry.excluded) := by
        apply Relation.ReflTransGen.single
        refine ⟨(fun impossible => impossible), rfl, (fun _ => none), ?_⟩
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨sampled, supported, rfl⟩
      let sourceInitial := setup.initialConfig setup.initialLaw.support_nonempty.choose
      have reached := CommitRecoveryState.reaches_of_lifted_nonCommit_path setup.program
        sourceInitial (.sample name fresh law next) lift ranks commits steps state.generation
        (Sum.inl source, state.entry.excluded)
        (Sum.inr (ProtocolState.entry next after), state.entry.excluded) path
      have sourceTrace := setup.recoveryTrace_of_reaches sourceInitial trace reached
      have adjacent := exclusion.frontier.adjacent
      have last := exclusion.frontier.last
      rw [installed] at adjacent last
      have address :
          (⟨remaining, state.generation, image, image, state.retired⟩ :
            PhaseRuntimeState ((toEventGraph setup.program).withMode mode)).attempt.phase =
              state.attempt.phase + 1 := by
        cases remaining with
        | nil =>
            have ending := last phase (by
              simp only [List.getLast?_singleton, Option.mem_some_iff])
            change ((toEventGraph setup.program).withMode mode).order.eventCount = _
            omega
        | cons following rest =>
            have boundary := adjacent.rel_head? (y := following) (by simp)
            change following.low = _
            omega
      refine ⟨
        { residual := ⟨_, _, next, fun point => lift (Sum.inr point)⟩
          source := after
          refs := tailRefs
          registry := registry.weaken
          embedding := tailEmbedding
          before := tailBefore
          compiled := ?_
          terminalAlignment :=
            terminalAligned.sampleTail setup.program fresh law next refs embedding
          agrees := finalAgree
          guards := finalGuards
          failures := finalFailures
          unique := by simpa only [List.map_cons] using List.nodup_cons.mpr ⟨fresh, unique⟩
          remaining := fun point => ranks (Sum.inr point)
          actor := fun point => actors (Sum.inr point)
          atCommit := fun point => commits (Sum.inr point)
          owners := fun point => owners (Sum.inr point)
          commitEnd := fun point => endpoints (Sum.inr point)
          automatic := fun point => automatic (Sum.inr point)
          history := fun point => histories (Sum.inr point)
          withHistory := fun point past => memories (Sum.inr point) past
          step := ?_
          menus := fun who point => menus who (Sum.inr point)
          readout := fun point => readouts (Sum.inr point)
          trace := by rw [excludedEq]; exact sourceTrace
          views := ProtocolViewSuffix.sampleTail setup.program fresh law next refs embedding
            lift views
          historyAlignment := ?_ }⟩
      · rw [address]
        exact compiled.sampleTail (_openNames := O) setup.program fresh law next refs
          source.revelations registry embedding before state.attempt.phase
      · intro point excluded joint
        rw [steps]
        simp only [ProtocolState.recoveryStep, Sum.elim_inr, PMF.map_comp, Function.comp_def]
      · intro clear
        have oldClear : state.entry.excluded = ∅ := excludedEq.symm.trans clear
        obtain ⟨⟨selected, action⟩, recorded, named⟩ :=
          List.mem_map.mp ((image.native.config.history_exact event).mpr completed)
        change selected = event at named
        subst selected
        have decoded : decodeEventAction setup.program event action = none := by
          rw [views.actionEq zero action]
          rfl
        have word := RecordedSourceHistory.sample setup.program mode image.native.config
          state.attempt.phase source.history ⟨event, action⟩ recorded
          (show event.val = state.attempt.phase from ranked.trans low) decoded
        have saved : state.entry.native.config.cut.IsPrefix state.attempt.phase := by
          rw [← low]
          exact within.1
        have prefixEnd : image.native.config.cut.IsPrefix (state.attempt.phase + 1) := by
          have ended := phase.finished_prefix image (phase.drain_within state.current within.2)
            finished
          rw [← low, ← singleton]
          exact ended
        exact RecordedSourceHistory.native_history setup.program mode
          state.entry.native.config image.native.config state.attempt.phase 1
          source.history source.history word reachable
          (remembered.trans (phase.drain_history_prefix state.current)) saved prefixEnd
          (historyAlignment oldClear)

end Vegas
