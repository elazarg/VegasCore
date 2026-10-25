/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceAsyncStep
import Vegas.Source.Disclosure

/-! # Source residuals of native configurations

A *source residual* of a native configuration at a completed prefix is the
remaining source program and source configuration, aligned with the compiled
policy suffix from that rank, agreeing with the native store and history, and
through which the whole-program prefix decoder factors
(`Vegas.SourceResidual`, `Vegas.SourceResidual.decode`). Residuals exist at
initialization (`Vegas.SourceResidual.initial`) and survive every
configuration step, whatever action completes the ready event
(`Vegas.SourceResidual.configStep`). One scheduler round changes the
configuration by one configuration step, whatever the players
(`Vegas.round_configStep`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (profile : BehavioralProfile setup.program)

/-- A source reading of a native configuration at rank `rank`: a residual
source program and configuration whose compiled policy suffix starts at
`rank`, whose typed cells and history agree with the configuration, and
through which the whole-program prefix decoder factors. -/
structure SourceResidual (rank : Nat) (config : (graph setup).Config) : Type where
  Γ : SourceCtx Player L
  names : Finset VarId
  program : SourceProgram Player L Γ names
  residualProfile : BehavioralProfile program
  source : Config Player L Γ
  refs : ContextRefs (graph setup).layout Γ
  embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program
  refsBefore : ContextRefsBefore refs embedding
  aligned : CompiledPolicySuffix setup.program profile program residualProfile refs
    source.revelations source.registry embedding refsBefore rank
  admitted : (∀ who, (profile who).Admitted setup.program
      (CommitmentInterface.values setup.program)) →
    ∀ who, (residualProfile who).Admitted program (CommitmentInterface.values program)
  effective : (∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context)) →
    ∀ who, (residualProfile who).EffectiveDisclosures program source.registry
      source.revelations
  supports : (∀ who, (profile who).SupportsEffectiveChoices setup.program
      (CommitmentInterface.values setup.program) [] (Revelations.initial setup.context)) →
    ∀ who, (residualProfile who).SupportsEffectiveChoices program
      (CommitmentInterface.values program) source.registry source.revelations
  disclosing : (∀ who, Disclosing setup.program (profile who)) →
    ∀ who, Disclosing program (residualProfile who)
  lift : ProtocolState program → ProtocolState setup.program
  commutes : ∀ [Fintype Player] state,
    ProtocolState.behavioralStateStep setup.program profile (lift state) =
      (ProtocolState.behavioralStateStep program residualProfile state).map lift
  steps : ∀ state joint, ProtocolState.step setup.program (lift state) joint =
    (ProtocolState.step program state joint).map lift
  injective : Function.Injective lift
  transport : ∀ more store history,
    decodeSourcePrefix? setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program)) []
      (Revelations.initial setup.context) (outputRef setup.program) (rank + more) store history =
    (decodeSourcePrefix? program refs source.registry source.revelations embedding.ref
      more store history).map lift
  checkpoint : SourceCheckpoint setup source refs rank config

variable {setup profile}

/-- The residual decodes the configuration. -/
theorem SourceResidual.decode {rank : Nat} {config : (graph setup).Config}
    (residual : SourceResidual setup profile rank config) :
    sourceServicePrefix? setup rank config =
      some (residual.lift (ProtocolState.entry residual.program residual.source)) := by
  unfold sourceServicePrefix? serviceSourcePrefix?
  have read := residual.transport 0
  simp only [Nat.add_zero] at read
  rw [read, residual.checkpoint.decode residual.program residual.embedding.ref]
  rfl

variable (setup profile)

/-- Every initial configuration has the whole program as its residual. -/
def SourceResidual.initial (initial : State L setup.context) :
    SourceResidual setup profile 0
      (EventGraphRuntime.State.initial (graph := graph setup)
        (setup.eventInputs initial)).config where
  Γ := setup.context
  names := setup.obligations
  program := setup.program
  residualProfile := profile
  source := setup.initialConfig initial
  refs := ContextRefs.initial setup.context (outputLayout setup.program)
  embedding := outputEmbedding setup.program
  refsBefore := initialRefsBefore setup.program
  aligned := CompiledPolicySuffix.whole setup.program profile
  admitted := fun admitted => admitted
  effective := fun effective => effective
  supports := fun supported => supported
  disclosing := fun disclosing => disclosing
  lift := id
  commutes := fun state => by simp only [id_eq, PMF.map_id]
  steps := fun state joint => by simp only [id_eq, PMF.map_id]
  injective := Function.injective_id
  transport := fun more store history => by
    simp only [Nat.zero_add, Option.map_id_fun]
    rfl
  checkpoint := SourceCheckpoint.initial setup initial

variable {setup profile}

/-- A native state carrying a given configuration, used to apply the checkpoint
successor lemmas, which read only the configuration. -/
def configState (config : (graph setup).Config) : EventGraphRuntime.State (graph setup) :=
  { EventGraphRuntime.State.initial (graph := graph setup) config.inputs with config := config }

/-- A fixed native completion preserves its typed source residual and its
exact source-step atom. The successor witness supplies the same decoder and
policy transport as the reached residual, including failed disclosures. -/
theorem SourceResidual.step_mass {rank : Nat} {before : (graph setup).Config}
    (residual : SourceResidual setup profile rank before)
    (event : (graph setup).EventId) (ready : before.cut.Ready event)
    (action : (graph setup).Action event) (after : (graph setup).Config)
    (member : after ∈ (before.step event ready action).support) :
    ∃ next : SourceResidual setup profile (rank + 1) after,
      next.lift (ProtocolState.entry next.program next.source) ∈
        (ProtocolState.step setup.program
          (residual.lift (ProtocolState.entry residual.program residual.source))
          (fun _ => decodeEventAction setup.program event action)).support ∧
      (ProtocolState.step setup.program
          (residual.lift (ProtocolState.entry residual.program residual.source))
          (fun _ => decodeEventAction setup.program event action))
        (next.lift (ProtocolState.entry next.program next.source)) =
          (before.step event ready action) after := by
  obtain ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore, aligned,
    admitted, effective, supports, disclosing, lift, commutes, steps, injective, transport,
    checkpoint⟩ := residual
  have atEvent := (ready_iff_rank setup before rank checkpoint.ordered event).mp ready
  have counted := aligned.graphSuffix.countEq
  change rank + eventCount program = (graph setup).order.eventCount at counted
  cases program with
  | ret payoffs =>
      have := event.isLt
      simp only [eventCount] at counted
      omega
  | @sample Γ openNames name payload fresh distribution next =>
      let index : Fin (eventCount (.sample name fresh distribution next)) :=
        ⟨0, by simp [eventCount]⟩
      have atRank : (embedding.event index).val = rank := by
        simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
      have same : event = embedding.event index := Fin.ext (atEvent.trans atRank.symm)
      subst same
      have outputEq : (graph setup).outputLayout (embedding.event index) =
          .publicData payload := by
        change outputLayout setup.program (embedding.event index) = _
        simpa [index, outputLayout, eventCount] using embedding.layout_eq index
      have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes (embedding.event index)) =
            .sample payload (compilePublicDist refs distribution) := by
        change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
          ((toEventGraph setup.program).nodes (embedding.event index)) = _
        simpa [index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
      have decoded : decodeEventAction setup.program (embedding.event index)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit) = none := by
        have lookup := aligned.actionEq index
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
        simpa [index, outputEq, decodeEventAction] using lookup
      obtain ⟨marker, rfl⟩ : ∃ marker : PUnit,
          action = cast (congrArg EventGraph.EventField.Action outputEq.symm) marker :=
        ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
      cases marker
      have graphLaw := sample_step before _ ready outputEq refs distribution codeEq source.state
        checkpoint.agrees
      rw [graphLaw, PMF.support_map] at member
      obtain ⟨value, drawn, rfl⟩ := member
      let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
      let tailRefs : ContextRefs (graphLayout setup.program)
          ((name, .publicData payload) :: Γ) := refs.cons ⟨.inr (embedding.event index), outputEq⟩
      have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
        exact refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl
      have tailAligned : CompiledPolicySuffix setup.program profile next
          (afterSample residualProfile) tailRefs (sampleSuccessor name source value).revelations
          (sampleSuccessor name source value).registry tailEmbedding tailBefore (rank + 1) := by
        simpa only [sampleSuccessor, tailRefs, tailEmbedding, OutputEmbedding.ref] using
          aligned.sampleTail setup.program profile (_openNames := names)
            fresh distribution next residualProfile refs
            source.revelations source.registry embedding refsBefore rank
      refine ⟨{
        Γ := _, names := _, program := next, residualProfile := afterSample residualProfile,
        source := sampleSuccessor name source value, refs := tailRefs,
        embedding := tailEmbedding, refsBefore := tailBefore, aligned := tailAligned,
        admitted := fun whole who => admitted whole who,
        effective := fun whole who => effective whole who,
        supports := fun whole who => supports whole who,
        disclosing := fun whole who => disclosing whole who,
        lift := lift ∘ Sum.inr,
        commutes := fun state => ?_, steps := fun state joint => ?_,
        injective := injective.comp Sum.inr_injective,
        transport := fun more store history => ?_,
        checkpoint := checkpoint.sample (native := configState before) name (embedding.event index)
          atRank ready outputEq (fun ref => refsBefore ref index) decoded value }, ?_, ?_⟩
      · rw [Function.comp_apply, commutes, ProtocolState.behavioralStateStep_sample_tail,
          PMF.map_comp]
      · rw [Function.comp_apply, steps]
        change PMF.map lift ((ProtocolState.step next state joint).map Sum.inr) = _
        rw [PMF.map_comp]
      · rw [show rank + 1 + more = rank + (more + 1) by omega, transport,
          decodeSourcePrefix?_sample, Option.map_map]
        rfl
      · rw [steps, PMF.support_map, decoded]
        refine ⟨Sum.inr (ProtocolState.entry next (sampleSuccessor name source value)), ?_, rfl⟩
        change _ ∈ ((L.evalDist distribution (sourcePublicEnv source.state)).map fun drawn =>
          Sum.inr (ProtocolState.entry next (sampleSuccessor name source drawn))).support
        rw [PMF.support_map]
        exact ⟨value, drawn, rfl⟩
      · rw [steps, decoded, graphLaw]
        change (((L.evalDist distribution (sourcePublicEnv source.state)).map fun drawn =>
            Sum.inr (ProtocolState.entry next (sampleSuccessor name source drawn))).map lift)
              (lift (Sum.inr (ProtocolState.entry next (sampleSuccessor name source value)))) = _
        rw [PMF.map_comp]
        have sourceInjective : Function.Injective
            (lift ∘ fun drawn : L.Val payload =>
              (Sum.inr (ProtocolState.entry next (sampleSuccessor name source drawn)) :
                ProtocolState (.sample name fresh distribution next))) := by
          intro first second equal
          have entries := ProtocolState.entry_injective next
            (Sum.inr_injective (injective equal))
          exact congrArg (fun config : Config Player L ((name, .publicData payload) :: Γ) =>
            config.state.get .here) entries
        have graphInjective : Function.Injective fun drawn : L.Val payload =>
            before.complete (embedding.event index) ready
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
              (cast (congrArg EventGraph.EventField.Value outputEq.symm) drawn) := by
          intro first second equal
          have outputs := congrArg (fun config : (graph setup).Config =>
            config.outputs (embedding.event index)) equal
          simp only [EventGraph.Config.complete, Function.update_self, Option.some.injEq] at outputs
          exact (cast_inj _).mp outputs
        exact (pmf_map_apply_of_injective _ sourceInjective value).trans
          (pmf_map_apply_of_injective _ graphInjective value).symm
  | @commit Γ openNames name owner payload fresh guard next =>
      let index : Fin (eventCount (.commit name owner fresh guard next)) :=
        ⟨0, by simp [eventCount]⟩
      have atRank : (embedding.event index).val = rank := by
        simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
      have same : event = embedding.event index := Fin.ext (atEvent.trans atRank.symm)
      subst same
      have outputEq : (graph setup).outputLayout (embedding.event index) =
          .binding owner payload := by
        change outputLayout setup.program (embedding.event index) = _
        simpa [index, outputLayout, eventCount] using embedding.layout_eq index
      have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes (embedding.event index)) = .bind owner payload := by
        change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
          ((toEventGraph setup.program).nodes (embedding.event index)) = _
        simpa [index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
      obtain ⟨choice, rfl⟩ : ∃ choice : PublicationResult (L.Val payload),
          action = cast (congrArg EventGraph.EventField.Action outputEq.symm) choice :=
        ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
      have decoded : decodeEventAction setup.program (embedding.event index)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice) =
            some (.commit owner name payload choice) := by
        have lookup := aligned.actionEq index
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
        simpa [index, outputEq, decodeEventAction] using lookup
      rw [commit_step before _ ready outputEq codeEq choice, PMF.mem_support_pure_iff] at member
      subst member
      let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
      let tailRefs : ContextRefs (graphLayout setup.program)
          ((name, .commitment owner payload) :: Γ) :=
        refs.cons ⟨.inr (embedding.event index), outputEq⟩
      have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
        exact refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl
      have tailAligned : CompiledPolicySuffix setup.program profile next
          (afterCommit residualProfile) tailRefs
          (commitSuccessor name guard source choice).revelations
          (commitSuccessor name guard source choice).registry
          tailEmbedding tailBefore (rank + 1) := by
        simpa only [commitSuccessor, tailRefs, tailEmbedding, OutputEmbedding.ref] using
          aligned.commitTail setup.program profile fresh guard next residualProfile refs
            source.revelations source.registry embedding refsBefore rank
      refine ⟨{
        Γ := _, names := _, program := next, residualProfile := afterCommit residualProfile,
        source := commitSuccessor name guard source choice, refs := tailRefs,
        embedding := tailEmbedding, refsBefore := tailBefore, aligned := tailAligned,
        admitted := fun whole who => (admitted whole who).2,
        effective := fun whole who => effective whole who,
        supports := fun whole who => (supports whole who).2,
        disclosing := fun whole who => disclosing whole who,
        lift := lift ∘ Sum.inr,
        commutes := fun state => ?_, steps := fun state joint => ?_,
        injective := injective.comp Sum.inr_injective,
        transport := fun more store history => ?_,
        checkpoint := checkpoint.commit (native := configState before) name guard
          (embedding.event index) atRank ready outputEq (fun ref => refsBefore ref index)
          choice decoded }, ?_, ?_⟩
      · rw [Function.comp_apply, commutes, ProtocolState.behavioralStateStep_commit_tail,
          PMF.map_comp]
      · rw [Function.comp_apply, steps]
        change PMF.map lift ((ProtocolState.step next state joint).map Sum.inr) = _
        rw [PMF.map_comp]
      · rw [show rank + 1 + more = rank + (more + 1) by omega, transport,
          decodeSourcePrefix?_commit, Option.map_map]
        rfl
      · rw [steps, PMF.support_map, decoded]
        refine ⟨Sum.inr (ProtocolState.entry next (commitSuccessor name guard source choice)),
          ?_, rfl⟩
        change _ ∈ (PMF.pure (Sum.inr (ProtocolState.entry next (commitSuccessor name guard source
          (OwnAction.binding owner name payload
            (some (OwnAction.commit owner name payload choice))))))).support
        rw [OwnAction.binding_commit, PMF.mem_support_pure_iff]
      · rw [steps, decoded, commit_step before _ ready outputEq codeEq choice]
        simp only [ProtocolState.step, ProtocolState.entry, Function.comp_apply, Sum.elim_inl,
          OwnAction.binding_commit,
          PMF.pure_map, PMF.pure_apply_self]
  | @reveal Γ openNames published owner name payload fresh selected unresolved next =>
      let index : Fin (eventCount
          (.reveal published owner name fresh selected unresolved next)) :=
        ⟨0, by simp [eventCount]⟩
      have atRank : (embedding.event index).val = rank := by
        simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
      have same : event = embedding.event index := Fin.ext (atEvent.trans atRank.symm)
      subst same
      have outputEq : (graph setup).outputLayout (embedding.event index) =
          .publication payload := by
        change outputLayout setup.program (embedding.event index) = _
        simpa [index, outputLayout, eventCount] using embedding.layout_eq index
      let checks := compileChecks (published := published) refs
        source.registry source.revelations selected
      have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes (embedding.event index)) =
            .resolve owner payload (refs.get selected) checks := by
        change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
          ((toEventGraph setup.program).nodes (embedding.event index)) = _
        simpa [index, compileRankedNodes, checks] using aligned.graphSuffix.nodeEq index
      obtain ⟨disclose, rfl⟩ : ∃ disclose : Bool,
          action = cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose :=
        ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
      have decoded : decodeEventAction setup.program (embedding.event index)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
            some (.reveal owner name disclose) := by
        have lookup := aligned.actionEq index
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
        simpa [index, outputEq, decodeEventAction] using lookup
      rw [before.step_eq_map_of_code _ ready outputEq _ codeEq disclose
        (PMF.pure (disclosureResult published selected source disclose))
        (compileResolve_eval? refs source.registry source.revelations source.state
          before.store checkpoint.agrees selected disclose),
        PMF.pure_map, PMF.mem_support_pure_iff] at member
      subst member
      let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
      let tailRefs : ContextRefs (graphLayout setup.program)
          ((published, .publication payload) :: Γ) :=
        refs.cons ⟨.inr (embedding.event index), outputEq⟩
      have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
        exact refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl
      have tailAligned : CompiledPolicySuffix setup.program profile next
          (afterReveal residualProfile) tailRefs
          (revealSuccessor published selected source disclose).revelations
          (revealSuccessor published selected source disclose).registry
          tailEmbedding tailBefore (rank + 1) := by
        simpa only [revealSuccessor, tailRefs, tailEmbedding, OutputEmbedding.ref] using
          aligned.revealTail setup.program profile fresh selected unresolved next
            residualProfile refs source.revelations source.registry embedding refsBefore rank
      refine ⟨{
        Γ := _, names := _, program := next, residualProfile := afterReveal residualProfile,
        source := revealSuccessor published selected source disclose, refs := tailRefs,
        embedding := tailEmbedding, refsBefore := tailBefore, aligned := tailAligned,
        admitted := fun whole who => admitted whole who,
        effective := fun whole who => (effective whole who).2,
        supports := fun whole who => (supports whole who).2,
        disclosing := fun whole who => (disclosing whole who).2,
        lift := lift ∘ Sum.inr,
        commutes := fun state => ?_, steps := fun state joint => ?_,
        injective := injective.comp Sum.inr_injective,
        transport := fun more store history => ?_,
        checkpoint := checkpoint.reveal (native := configState before) published selected
          (embedding.event index) atRank ready outputEq (fun ref => refsBefore ref index)
          disclose decoded }, ?_, ?_⟩
      · rw [Function.comp_apply, commutes, ProtocolState.behavioralStateStep_reveal_tail,
          PMF.map_comp]
      · rw [Function.comp_apply, steps]
        change PMF.map lift ((ProtocolState.step next state joint).map Sum.inr) = _
        rw [PMF.map_comp]
      · rw [show rank + 1 + more = rank + (more + 1) by omega, transport,
          decodeSourcePrefix?_reveal, Option.map_map]
        rfl
      · rw [steps, PMF.support_map, decoded]
        exact ⟨_, (PMF.mem_support_pure_iff _ _).mpr rfl, rfl⟩
      · rw [steps, decoded, before.step_eq_map_of_code _ ready outputEq _ codeEq disclose
          (PMF.pure (disclosureResult published selected source disclose))
          (compileResolve_eval? refs source.registry source.revelations source.state
            before.store checkpoint.agrees selected disclose)]
        simp only [ProtocolState.step, ProtocolState.entry, Function.comp_apply, Sum.elim_inl,
          OwnAction.disclosure,
          PMF.pure_map, PMF.pure_apply_self]

/-- Completing the ready event with any action keeps a residual, one rank
later, whose source point is reached from the previous one by the source step
of the decoded action. -/
theorem SourceResidual.step {rank : Nat} {before : (graph setup).Config}
    (residual : SourceResidual setup profile rank before)
    (event : (graph setup).EventId) (ready : before.cut.Ready event)
    (action : (graph setup).Action event) (after : (graph setup).Config)
    (member : after ∈ (before.step event ready action).support) :
    ∃ next : SourceResidual setup profile (rank + 1) after,
      next.lift (ProtocolState.entry next.program next.source) ∈
        (ProtocolState.step setup.program
          (residual.lift (ProtocolState.entry residual.program residual.source))
          (fun _ => decodeEventAction setup.program event action)).support := by
  obtain ⟨next, reached, _mass⟩ := residual.step_mass event ready action after member
  exact ⟨next, reached⟩

/-- A configuration step keeps a residual, at whichever prefix the step
reaches. -/
theorem SourceResidual.configStep {rank : Nat} {before after : (graph setup).Config}
    (residual : SourceResidual setup profile rank before)
    (step : ConfigStep setup before after) (next : Nat) (ordered : after.cut.IsPrefix next) :
    Nonempty (SourceResidual setup profile next after) := by
  rcases step with same | ⟨event, ready, action, member⟩
  · subst same
    rw [isPrefix_unique ordered residual.checkpoint.ordered]
    exact ⟨residual⟩
  · have advanced : after.cut.IsPrefix (rank + 1) := by
      rw [before.step_cut event ready action after member]
      exact residual.checkpoint.ordered.complete_at event ready
        ((ready_iff_rank setup before rank residual.checkpoint.ordered event).mp ready)
    rw [isPrefix_unique ordered advanced]
    obtain ⟨next, _⟩ := residual.step event ready action after member
    exact ⟨next⟩

variable (setup)

section Generic

variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- One scheduler round changes the configuration by one configuration step:
the scheduler's command steps the graph and a response keeps the
configuration. -/
theorem round_configStep
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy)
    (execution next : (serviceApplication setup mode deadline leaks).Execution)
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).round scheduler players
        execution).support) :
    ConfigStep setup execution.application.config next.application.config := by
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have step := environmentStep_configStep setup leaks execution middle command moved
  change next ∈ (app.resume players (command.actor? app) middle).support at resumed
  have kept : next.application.config = middle.application.config := by
    cases actor : command.actor? app with
    | none =>
        rw [actor] at resumed
        simp only [ReactiveApplication.resume, PMF.mem_support_pure_iff] at resumed
        subst resumed
        rfl
    | some who =>
        rw [actor] at resumed
        change next ∈ (app.invoke players who middle).support at resumed
        rw [ReactiveApplication.invoke, PMF.support_map] at resumed
        obtain ⟨response, _, rfl⟩ := resumed
        exact ((serviceRuntime setup mode deadline).reactive_respond_application leaks middle who
                response).1
  rw [kept]
  exact step

end Generic

variable {setup}

end Vegas
