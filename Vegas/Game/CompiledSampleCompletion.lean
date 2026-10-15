/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledSampleReadback
import Vegas.Compile.EventGraphSuffix
import Vegas.Pending.PhaseNativeInvariant
import Vegas.Pending.PhaseExclusionRecord
import Vegas.Pending.PhaseStoredCheckpoint

/-! # Actual sampled phase completions supply legal typed source transitions -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A supported actual sampling effect reconstructs its genuine source chance
step. Samples neither add permanent exclusion nor trigger a phase-local
automatic event, including after previous commitment retries. -/
theorem sourceRecovery_of_actual_sampleCompletion
    (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
    {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: Γ) O)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (revelations : Revelations Γ) (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.sample name fresh law next)) (before : ContextRefsBefore refs embedding) (offset : Nat)
    (compiled : CompiledSuffix setup.program (.sample name fresh law next) refs revelations registry
      embedding before offset)
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (inputs : PMF ((toEventGraph setup.program).withMode mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (installed : control.execution.application.phases.head? = some phase)
    (kind : phase.kind = .sample) (low : phase.low = offset)
    (native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (supported : native ∈ (environmentStep runtime control.execution.application.current.native
      (.executeSample (embedding.event ⟨0, by simp only [eventCount]; omega⟩))).support)
    (completed : embedding.event ⟨0, by simp only [eventCount]; omega⟩ ∈
      native.config.cut.completed)
    (entry : SourceProgram.Config Player L Γ)
    (agree : refs.Agrees entry.state control.execution.application.entry.native.config.store)
    (guards : Registry.FailureExtension entry.registry registry entry.state)
    (failures : Revelations.PreservesFailures entry.revelations entry.state) :
    let event := embedding.event ⟨0, by simp only [eventCount]; omega⟩
    let raw := control.execution.application.current.environmentResult (.executeSample event) native
    phase.drain raw = raw ∧ raw.excluded = control.execution.application.entry.excluded ∧
    ∃ sampled : L.Val payload,
      sampled ∈ (L.evalDist law (sourcePublicEnv entry.state)).support ∧
      let after := sampleSuccessor name entry sampled
      (refs.cons (name := name) (cell := .publicData payload)
        ⟨.inr event, by
          change outputLayout setup.program event = .publicData payload
          simpa only [event, outputLayout, Fin.mk_zero, Fin.cases_zero] using
            embedding.layout_eq ⟨0, by simp only [eventCount]; omega⟩⟩).Agrees
        after.state native.config.store ∧
      Registry.FailureExtension after.registry registry.weaken after.state ∧
      Revelations.PreservesFailures after.revelations after.state ∧
      ∀ generation,
        (commitRecoveryProtocol (.sample name fresh law next) entry).Successor
          (CommitRecoveryState.atPoint (Sum.inr (ProtocolState.entry next after)) raw.excluded
            generation)
          (CommitRecoveryState.atPoint (Sum.inl entry)
            control.execution.application.entry.excluded generation) := by
  let state := control.execution.application
  let zero : Fin (eventCount (.sample name fresh law next)) :=
    ⟨0, by simp only [eventCount]; omega⟩
  let event := embedding.event zero
  let raw := state.current.environmentResult (.executeSample event) native
  have ranked : event.val = phase.low := by
    rw [low]
    simpa only [zero, Nat.add_zero] using compiled.rankEq zero
  have outputEq : ((toEventGraph setup.program).withMode mode).outputLayout event =
      .publicData payload := by
    change outputLayout setup.program (embedding.event zero) = .publicData payload
    simpa only [zero, outputLayout, Fin.mk_zero, Fin.cases_zero] using embedding.layout_eq zero
  have codeEq : cast (congrArg (EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) =
        .sample payload (compilePublicDist refs law) := by
    simpa only [event, zero, compileRankedNodes, outputLayout, Fin.mk_zero, Fin.cases_zero]
      using compiled.nodeEq zero
  have ownerless : ((toEventGraph setup.program).withMode mode).actor? event = none :=
    (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
  have record := phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler trace
  have member : phase ∈ state.phases.head? := by rw [installed]; exact Option.mem_some_iff.mpr rfl
  have within : state.current.native.config.cut.Within phase.low phase.high := by
    have position := record.frontier.positioned
    cases phases : state.phases with
    | nil => simp only [phases, List.head?_nil, Option.not_mem_none] at member
    | cons current remaining =>
        simp only [phases, List.head?_cons, Option.mem_some_iff] at member
        subst current
        rw [phases] at position
        exact position.2
  have singleton := phase.sample_singleton kind
  have excludedEq : state.current.excluded = state.entry.excluded := by
    apply Finset.ext
    intro who
    rw [(record.installed phase member).excluded]
    constructor
    · rintro (old | ⟨query, lower, actor, failed⟩)
      · exact old
      · have upper := within.2 query failed.completed
        have same : query = event := Fin.ext (by omega)
        rw [same, ownerless] at actor
        cases actor
    · exact Or.inl
  have rawExcluded : raw.excluded = state.entry.excluded := excludedEq
  have noAutomatic : ∀ query, ¬ (query ∈ phase.events ∧ raw.AutomaticReady query) := by
    intro query ⟨inside, eligible⟩
    have bounds := (phase.mem_events query).mp inside
    have same : query = event := Fin.ext (by omega)
    obtain ⟨who, actor, _excluded⟩ := eligible.owned
    rw [same, ownerless] at actor
    cases actor
  refine ⟨phase.drain_eq_of_clear raw noAutomatic, rawExcluded, ?_⟩
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    trace
  have nativeValid := environmentStep_invariant runtime state.current.native native
    (.executeSample event) valid.active supported
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler trace
  have afterAgree : refs.Agrees entry.state native.config.store := by
    intro readName cell source
    apply (refs.get source).get?_preserved state.entry.native.config.store _
      (fun field value present => environmentStep_store_of_some runtime state.current.native native
        (.executeSample event) supported field value (stored field value present)) _ (agree source)
  obtain ⟨sampled, sampledSupport, finalAgree, finalGuards, finalFailures, transition⟩ :=
    completed_sample_source_successor fresh law next native.config nativeValid.reachable event
      completed outputEq refs entry registry codeEq afterAgree guards failures
  refine ⟨sampled, sampledSupport, finalAgree, finalGuards, finalFailures, ?_⟩
  intro generation
  rw [← rawExcluded]
  exact transition raw.excluded generation

end Vegas
