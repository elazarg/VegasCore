/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstBindingTraffic
import Vegas.Game.SourceServiceDecoderSlice

/-! # A binding phase on one whole-source decoder slice

One compiler-aligned commitment slice is fixed before integrating the seeds. The
prior carrier keeps an arbitrary parameter beside the actual effective source
prefix. The real stopped binding law advances that carrier and the same full
traffic, with auxiliary noise depending only on the whole source observation.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A real binding phase propagates a whole-source-view traffic factor
through one static compiler slice. The boundary and typed checkpoint are the
previous prefix's actual induction resources. The next source draw and whole
endpoint decoder are derived from the runtime first protected binding decision. -/
theorem sourceServiceFirstTurn_binding_prefix_factorization [Fintype Player]
    {Seed Parameter : Type*} (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon turns : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (wholeProfile : BehavioralProfile setup.program)
    {Γ : SourceCtx Player L} {names : Finset VarId} {payload : L.Ty}
    (name : VarId) (owner : Player) (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name names))
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (refs : ContextRefs (graph setup).layout Γ) (registry : Registry Γ)
    (revelations : Revelations Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.commit name owner fresh guard next) profile refs revelations registry
      embedding refsBefore rank)
    (lift : ProtocolState (.commit name owner fresh guard next) → ProtocolState setup.program)
    (injective : Function.Injective lift)
    (liftView : ∀ who, ProtocolView who (.commit name owner fresh guard next) →
      ProtocolView who setup.program)
    (viewed : ∀ who state, ProtocolState.observe who setup.program (lift state) =
      liftView who (ProtocolState.observe who (.commit name owner fresh guard next) state))
    (recover : ∀ who, ProtocolView who setup.program →
      Option (ProtocolView who (.commit name owner fresh guard next)))
    (recovered : ∀ who state, recover who (ProtocolState.observe who setup.program (lift state)) =
      some (ProtocolState.observe who (.commit name owner fresh guard next) state))
    (commutes : ∀ state, ProtocolState.behavioralStateStep setup.program wholeProfile
      (lift state) =
        (ProtocolState.behavioralStateStep (.commit name owner fresh guard next) profile state).map
          lift)
    (transport : ∀ more store history,
      decodeSourcePrefix? setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program)) []
        (Revelations.initial setup.context) (outputRef setup.program) (rank + more) store history =
      (decodeSourcePrefix? (.commit name owner fresh guard next) refs registry revelations
        embedding.ref more store history).map lift)
    (prior : PMF Seed) (parameter : Seed → Parameter) (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (registryEq : ∀ seed ∈ prior.support, (source seed).registry = registry)
    (revelationsEq : ∀ seed ∈ prior.support,
      ((source seed).revelations : Revelations Γ) = @revelations)
    (boundary : ∀ seed ∈ prior.support,
      CompletionBoundary setup leaks scheduler
        (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
          wholeProfile) rank (execution seed))
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (checkpoint : ∀ seed ∈ prior.support,
      SourceCheckpoint setup (source seed) refs rank (execution seed).application.config)
    (focal : Player) (noise : ProtocolView focal setup.program → PMF _)
    (factor : prior.map (fun seed =>
        ((parameter seed, lift (ProtocolState.entry (.commit name owner fresh guard next)
          (source seed))), (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map fun seed => (parameter seed,
        lift (ProtocolState.entry (.commit name owner fresh guard next) (source seed)))).bind
          fun carried => (noise (ProtocolState.observe focal setup.program carried.2)).map
            fun extra => (carried, extra)) :
    let event := embedding.event ⟨0, by simp [eventCount]⟩
    ∃ nextNoise : Option (ProtocolView focal setup.program) → PMF _,
      (∀ seed ∈ prior.support, sourceServicePrefix? setup rank
        (execution seed).application.config =
          some (lift (ProtocolState.entry (.commit name owner fresh guard next) (source seed)))) ∧
      (prior.bind fun seed =>
        ((application setup leaks).runUntilHorizon scheduler
          (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
            wholeProfile)
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map fun final =>
            ((parameter seed, sourceServicePrefix? setup (rank + 1) final.application.config),
              (runtime setup).bindingTraffic leaks focal final)) =
        ((prior.map fun seed => (parameter seed,
          lift (ProtocolState.entry (.commit name owner fresh guard next) (source seed)))).bind
            fun carried => (ProtocolState.behavioralStateStep setup.program wholeProfile
              carried.2).map fun after => (carried.1, some after)).bind fun carried =>
                (nextNoise (carried.2.map (ProtocolState.observe focal setup.program))).map
                  fun extra => (carried, extra) := by
  classical
  intro event
  let app := application setup leaks
  let players := sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
    wholeProfile
  have eventRank : event.val = rank := by
    simpa only [event, Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? (embedding.event _) = some owner
    simpa [event, eventCount, eventOwner?] using aligned.actorEq ⟨0, by simp [eventCount]⟩
  have outputEq : (graph setup).outputLayout event = .binding owner payload := by
    change outputLayout setup.program (embedding.event _) = _
    simpa [outputLayout, eventCount] using embedding.layout_eq ⟨0, by simp [eventCount]⟩
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes (embedding.event _)) = _
    simpa [compileRankedNodes, eventCount] using
      aligned.graphSuffix.nodeEq ⟨0, by simp [eventCount]⟩
  have node := nodeView_eq_bind outputEq codeEq
  let stopped := fun seed => app.runUntilHorizon scheduler players
    (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)
  let fixed := fun seed (value : PublicationResult (L.Val payload)) =>
    app.runUntilHorizon scheduler
      (decidedProfile (leaks := leaks) bound owner event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) value))
      (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)
  let typedNoise := fun view : DecisionView focal Γ => noise (liftView focal (Sum.inl view))
  let before := fun config : Config Player L Γ =>
    lift (ProtocolState.entry (.commit name owner fresh guard next) config)
  let after := fun config : Config Player L ((name, .commitment owner payload) :: Γ) =>
    lift (Sum.inr (ProtocolState.entry next config))
  have ready seed (supported : seed ∈ prior.support) :
      (execution seed).application.config.cut.Ready event :=
    (ready_iff_rank setup _ rank (boundary seed supported).ordered event).mpr eventRank
  have actualBoundary seed (supported : seed ∈ prior.support) :
      CompletionBoundary setup leaks scheduler players event.val (execution seed) := by
    simpa only [eventRank] using boundary seed supported
  have typedFactor : prior.map (fun seed => ((parameter seed, source seed),
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map fun seed => (parameter seed, source seed)).bind fun carried =>
        (typedNoise (carried.2.view focal)).map fun extra => (carried, extra) := by
    let embed := fun point : (Parameter × Config Player L Γ) ×
        (MessageNetwork Player app.Payload × List (MessageId Player × Bool) ×
          List app.EnvironmentEntry × List app.PlayerEntry × PlayerView (graph setup) ×
            PublicView (graph setup)) =>
      ((point.1.1, before point.1.2), point.2)
    apply pmf_map_injective (f := embed) (by
      intro first second equal
      obtain ⟨carriedEq, extraEq⟩ := Prod.mk.inj equal
      obtain ⟨parameterEq, sourceEq⟩ := Prod.mk.inj carriedEq
      have sourceEq := ProtocolState.entry_injective (.commit name owner fresh guard next)
        (injective sourceEq)
      exact Prod.ext (Prod.ext parameterEq sourceEq) extraEq)
    simpa only [embed, before, PMF.map_comp, PMF.map_bind, PMF.bind_map, Function.comp_def,
      viewed, ProtocolState.entry, ProtocolState.observe, Sum.elim_inl, typedNoise] using factor
  have seedAligned seed (supported : seed ∈ prior.support) :
      CompiledPolicySuffix setup.program wholeProfile (.commit name owner fresh guard next)
        profile refs (source seed).revelations (source seed).registry embedding refsBefore rank :=
      by
    rw [registryEq seed supported, revelationsEq seed supported]
    exact aligned
  have policy seed (supported : seed ∈ prior.support) (current : app.Execution)
      (same : current.application.config = (execution seed).application.config) :
      sourceServiceCanonicalPolicy setup leaks wholeProfile owner (current.recall owner)
          (current.observe app owner) =
        ((commitKernel profile ((source seed).view owner)).map
          (fun value => cast (congrArg EventGraph.EventField.Action outputEq.symm) value)).map
            (fun action => (runtime setup).canonicalServiceDecision leaks owner
              (current.recall owner) (current.observe app owner) event action) := by
    let site : BindingSource setup wholeProfile event current.application.config :=
      ⟨Γ, names, name, owner, payload, fresh, guard, next, profile, refs, source seed,
        embedding, refsBefore, (by simpa only [eventRank] using seedAligned seed supported),
        (by rw [same]; exact (checkpoint seed supported).agrees),
        (by rw [same]; exact (checkpoint seed supported).history), rfl⟩
    have currentReady : current.application.config.cut.Ready event := by
      rw [same]
      exact ready seed supported
    rw [sourceServiceCanonicalPolicy_at_event setup leaks wholeProfile owner current event
      (ownTurn?_of_ready setup current.application currentReady owned) owned]
    exact congrArg
      (PMF.map ((runtime setup).canonicalServiceDecision leaks owner (current.recall owner)
        (current.observe app owner) event)) (site.compiled_choice current)
  have decodedAction value : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) value) =
        some (.commit owner name payload value) := by
    simpa [event, eventCount, outputEq, decodeEventAction] using aligned.actionEq
      ⟨0, by simp [eventCount]⟩
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) value)
  have endpoint seed (supported : seed ∈ prior.support) (value : PublicationResult (L.Val payload))
      (final : app.Execution) (reached : final ∈ (fixed seed value).support) :
      sourceServicePrefix? setup (rank + 1) final.application.config =
        some (after (commitSuccessor name guard (source seed) value)) := by
    have completed := decided_completion contract timely event (execution seed)
      (actualBoundary seed supported) (bounded seed supported) (ready seed supported) owned
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) value)
      (by unfold EffectiveAction; rw [node]; trivial) final reached
    rw [commit_step (execution seed).application.config event (ready seed supported) outputEq
      codeEq value, PMF.mem_support_pure_iff] at completed
    rw [completed]
    have checked := (checkpoint seed supported).commit
      (native := configState (execution seed).application.config) name guard event eventRank
      (ready seed supported) outputEq (fun ref => refsBefore ref ⟨0, by simp [eventCount]⟩)
      value (decodedAction value)
    have read := checked.decode next (fun tail => embedding.ref tail.succ)
    unfold sourceServicePrefix?
    rw [transport 1, ← registryEq seed supported, ← revelationsEq seed supported,
      decodeSourcePrefix?_commit]
    let headOutput : EventGraph.FieldRef (graphLayout setup.program) (.binding owner payload) :=
      by simpa [outputLayout, eventCount] using embedding.ref ⟨0, by simp [eventCount]⟩
    have headRef : headOutput = ⟨.inr event, outputEq⟩ := by
      simp [headOutput, OutputEmbedding.ref, outputLayout, eventCount, event]
    rw [Option.map_map]
    change (decodeSourcePrefix? next (refs.cons (name := name) headOutput)
      (commitSuccessor name guard (source seed) value).registry
      (commitSuccessor name guard (source seed) value).revelations
      (fun tail => embedding.ref tail.succ) 0 _ _).map (lift ∘ Sum.inr) = _
    rw [headRef]
    exact congrArg (Option.map (lift ∘ Sum.inr)) read
  have phase seed (supported : seed ∈ prior.support) :
      (stopped seed).map (fun final =>
          ((parameter seed, sourceServicePrefix? setup (rank + 1) final.application.config),
            (runtime setup).bindingTraffic leaks focal final)) =
        (commitKernel profile ((source seed).view owner)).bind fun value =>
          (fixed seed value).map fun final =>
            ((parameter seed, some (after (commitSuccessor name guard (source seed) value))),
              (runtime setup).bindingTraffic leaks focal final) := by
    dsimp only [stopped, app, players]
    rw [sourceServiceTurnPolicy_firstTurn_phase event (execution seed)
      (actualBoundary seed supported)]
    unfold ReactiveApplication.runUntilHorizon
    rw [firstTurn_runUntil_mixture event (execution seed) (actualBoundary seed supported) owner
      owned bound turns wholeProfile _ (policy seed supported) _, PMF.map_bind, PMF.bind_map]
    apply bind_congr_on_support _
    intro value _
    apply map_congr_on_support _
    intro final reached
    exact Prod.ext (Prod.ext rfl (endpoint seed supported value final reached)) rfl
  have pairFactor : prior.map (fun seed => ((source seed, source seed, parameter seed),
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map fun seed => (source seed, source seed, parameter seed)).bind fun carried =>
        (typedNoise (carried.1.view focal)).map fun extra => (carried, extra) := by
    have paired := congrArg (PMF.map fun point =>
      ((point.1.2, point.1.2, point.1.1), point.2)) typedFactor
    simpa only [PMF.map_comp, PMF.map_bind, PMF.bind_map, Function.comp_def] using paired
  let choice := fun carried : Config Player L Γ × Config Player L Γ × Parameter =>
    commitKernel profile (carried.1.view owner)
  obtain ⟨nextTypedNoise, bindingLaw⟩ := sourceServiceFirstBinding_decided_factorization setup leaks
    name guard contract timely turns wholeProfile focal event outputEq codeEq node prior parameter
    source source execution actualBoundary bounded choice typedNoise pairFactor
  let typedLaw := (prior.map fun seed => (source seed, source seed, parameter seed)).bind
    fun carried => (choice carried).map fun value =>
      (commitSuccessor name guard carried.1 value, commitSuccessor name guard carried.2.1 value,
        carried.2.2)
  let typedJoint := typedLaw.bind fun carried =>
    (nextTypedNoise (carried.1.view focal)).map fun extra => (carried, extra)
  have typedJointFactor : typedJoint = (typedJoint.map Prod.fst).bind fun carried =>
      (nextTypedNoise (carried.1.view focal)).map fun extra => (carried, extra) := by
    have marginal : typedJoint.map Prod.fst = typedLaw := by
      simp only [typedJoint, Function.comp_def, ← PMF.bind_pure_comp,
        PMF.bind_bind, PMF.bind_const, PMF.pure_bind, PMF.bind_pure]
    rw [marginal]
  let defaultSource := source prior.support_nonempty.choose
  let defaultValue := (commitKernel profile (defaultSource.view owner)).support_nonempty.choose
  let fallback := (commitSuccessor name guard defaultSource defaultValue).view focal
  let recoverNext := fun view : Option (ProtocolView focal setup.program) =>
    (view.bind (recover focal) |>.bind Sum.getRight?).elim fallback
      (ProtocolView.entryView focal next)
  let embed := fun carried : Config Player L ((name, .commitment owner payload) :: Γ) ×
      Config Player L ((name, .commitment owner payload) :: Γ) × Parameter =>
    (carried.2.2, some (after carried.1))
  have recovers carried : recoverNext ((embed carried).2.map
      (ProtocolState.observe focal setup.program)) = carried.1.view focal := by
    simp only [embed, after, recoverNext, Option.map_some, Option.bind_some, recovered,
      ProtocolState.observe, Sum.elim_inr, Sum.getRight?_inr, Option.elim_some,
      ProtocolView.entryView_observe_entry]
  have lifted := map_observation_factor typedJoint (fun carried => carried.1.view focal)
    nextTypedNoise typedJointFactor embed
    (fun carried => carried.2.map (ProtocolState.observe focal setup.program)) recoverNext recovers
  have nativeEq : (prior.bind fun seed => (stopped seed).map (fun final =>
        ((parameter seed, sourceServicePrefix? setup (rank + 1) final.application.config),
          (runtime setup).bindingTraffic leaks focal final))) =
      typedJoint.map (fun carried => (embed carried.1, carried.2)) := by
    have mapped := congrArg (PMF.map fun carried => (embed carried.1, carried.2)) bindingLaw
    calc
      _ = prior.bind (fun seed =>
          (commitKernel profile ((source seed).view owner)).bind fun value =>
            (fixed seed value).map fun final =>
              ((parameter seed, some (after (commitSuccessor name guard (source seed) value))),
                (runtime setup).bindingTraffic leaks focal final)) :=
        bind_congr_on_support _ fun seed supported => phase seed supported
      _ = _ := by
        simpa only [typedJoint, typedLaw, embed, app, fixed, choice, PMF.map_bind,
          PMF.map_comp, Function.comp_def] using mapped
  have marginal : (typedJoint.map fun carried => (embed carried.1, carried.2)).map Prod.fst =
      (prior.map fun seed => (parameter seed, before (source seed))).bind fun carried =>
        (ProtocolState.behavioralStateStep setup.program wholeProfile carried.2).map fun state =>
          (carried.1, some state) := by
    simp only [typedJoint, typedLaw, embed, choice, Function.comp_def,
      ← PMF.bind_pure_comp, PMF.bind_bind, PMF.bind_const, PMF.pure_bind]
    apply bind_congr_on_support _
    intro seed _
    change _ = (ProtocolState.behavioralStateStep setup.program wholeProfile
      (lift (.inl (source seed)))).bind _
    rw [commutes, ProtocolState.behavioralStateStep_commit_entry, PMF.bind_map, PMF.bind_map]
    rfl
  refine ⟨fun view => nextTypedNoise (recoverNext view), ?_, ?_⟩
  · intro seed supported
    unfold sourceServicePrefix?
    have symbolic := transport 0
    simp only [Nat.add_zero] at symbolic
    rw [symbolic, ← registryEq seed supported, ← revelationsEq seed supported,
      (checkpoint seed supported).decode (.commit name owner fresh guard next) embedding.ref]
    rfl
  · rw [nativeEq]
    dsimp only at lifted
    rw [marginal] at lifted
    exact lifted

end Vegas
