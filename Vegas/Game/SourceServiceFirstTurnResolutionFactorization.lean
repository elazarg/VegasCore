/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstResolutionCoupling
import Vegas.Game.SourceServiceFirstTurnPrefix
import Vegas.Game.SourceServiceDecoderSlice

/-! # A resolution phase on one whole-source decoder slice

One compiler-aligned disclosure slice is fixed before integrating the seeds. The
prior carrier keeps an arbitrary parameter beside the actual effective source
prefix. The real stopped resolution law advances that carrier and the same full
traffic, with auxiliary noise depending only on the whole source observation.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A real resolution phase propagates a whole-source-view traffic factor
through one static compiler slice. The boundary and typed checkpoint are the
previous prefix's actual induction resources. The next source draw and whole
endpoint decoder are derived from the runtime first protected resolution decision. -/
theorem sourceServiceFirstTurn_resolution_prefix_factorization [Fintype Player]
    {Seed Parameter : Type*} (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon turns : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (wholeProfile : BehavioralProfile setup.program)
    {Γ : SourceCtx Player L} {names : Finset VarId} {payload : L.Ty}
    (published name : VarId) (owner : Player) (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ names)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (names.erase name))
    (profile : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (refs : ContextRefs (graph setup).layout Γ) (registry : Registry Γ)
    (revelations : Revelations Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.reveal published owner name fresh binding unresolved next) profile refs
        revelations registry
      embedding refsBefore rank)
    (effective : ∀ who, (profile who).EffectiveDisclosures
      (.reveal published owner name fresh binding unresolved next) registry revelations)
    (lift : ProtocolState (.reveal published owner name fresh binding unresolved next) →
      ProtocolState setup.program)
    (injective : Function.Injective lift)
    (liftView : ∀ who,
      ProtocolView who (.reveal published owner name fresh binding unresolved next) →
      ProtocolView who setup.program)
    (viewed : ∀ who state, ProtocolState.observe who setup.program (lift state) =
      liftView who (ProtocolState.observe who
        (.reveal published owner name fresh binding unresolved next) state))
    (recover : ∀ who, ProtocolView who setup.program →
      Option (ProtocolView who (.reveal published owner name fresh binding unresolved next)))
    (recovered : ∀ who state, recover who (ProtocolState.observe who setup.program (lift state)) =
      some (ProtocolState.observe who
        (.reveal published owner name fresh binding unresolved next) state))
    (commutes : ∀ state, ProtocolState.behavioralStateStep setup.program wholeProfile
      (lift state) =
        (ProtocolState.behavioralStateStep
          (.reveal published owner name fresh binding unresolved next) profile state).map
          lift)
    (transport : ∀ more store history,
      decodeSourcePrefix? setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program)) []
        (Revelations.initial setup.context) (outputRef setup.program) (rank + more) store history =
      (decodeSourcePrefix? (.reveal published owner name fresh binding unresolved next) refs
        registry revelations
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
        ((parameter seed, lift (ProtocolState.entry
          (.reveal published owner name fresh binding unresolved next)
          (source seed))), (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map fun seed => (parameter seed,
        lift (ProtocolState.entry
          (.reveal published owner name fresh binding unresolved next) (source seed)))).bind
          fun carried => (noise (ProtocolState.observe focal setup.program carried.2)).map
            fun extra => (carried, extra)) :
    let event := embedding.event ⟨0, by simp [eventCount]⟩
    ∃ nextNoise : Option (ProtocolView focal setup.program) → PMF _,
      (∀ seed ∈ prior.support, sourceServicePrefix? setup rank
        (execution seed).application.config =
          some (lift (ProtocolState.entry
            (.reveal published owner name fresh binding unresolved next) (source seed)))) ∧
      (prior.bind fun seed =>
        ((application setup leaks).runUntilHorizon scheduler
          (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
            wholeProfile)
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map fun final =>
            ((parameter seed, sourceServicePrefix? setup (rank + 1) final.application.config),
              (runtime setup).bindingTraffic leaks focal final)) =
        ((prior.map fun seed => (parameter seed,
          lift (ProtocolState.entry
          (.reveal published owner name fresh binding unresolved next) (source seed)))).bind
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
  have outputEq : (graph setup).outputLayout event = .publication payload := by
    change outputLayout setup.program (embedding.event _) = _
    simpa [outputLayout, eventCount] using embedding.layout_eq ⟨0, by simp [eventCount]⟩
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs registry revelations binding) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes (embedding.event _)) = _
    simpa [compileRankedNodes, eventCount] using
      aligned.graphSuffix.nodeEq ⟨0, by simp [eventCount]⟩
  have node := nodeView_eq_resolve outputEq codeEq
  let stopped := fun seed => app.runUntilHorizon scheduler players
    (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)
  let fixed := fun seed (value : Bool) =>
    app.runUntilHorizon scheduler
      (decidedProfile (leaks := leaks) bound owner event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) value))
      (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)
  let typedNoise := fun view : DecisionView focal Γ => noise (liftView focal (Sum.inl view))
  let before := fun config : Config Player L Γ =>
    lift (ProtocolState.entry (.reveal published owner name fresh binding unresolved next) config)
  let after := fun config : Config Player L ((published, .publication payload) :: Γ) =>
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
      have sourceEq := ProtocolState.entry_injective
        (.reveal published owner name fresh binding unresolved next)
        (injective sourceEq)
      exact Prod.ext (Prod.ext parameterEq sourceEq) extraEq)
    simpa only [embed, before, PMF.map_comp, PMF.map_bind, PMF.bind_map, Function.comp_def,
      viewed, ProtocolState.entry, ProtocolState.observe, Sum.elim_inl, typedNoise] using factor
  have seedAligned seed (supported : seed ∈ prior.support) :
      CompiledPolicySuffix setup.program wholeProfile
        (.reveal published owner name fresh binding unresolved next)
        profile refs (source seed).revelations (source seed).registry embedding refsBefore rank :=
      by
    rw [registryEq seed supported, revelationsEq seed supported]
    exact aligned
  have policy seed (supported : seed ∈ prior.support) (current : app.Execution)
      (same : current.application.config = (execution seed).application.config) :
      sourceServiceCanonicalPolicy setup leaks wholeProfile owner (current.recall owner)
          (current.observe app owner) =
        ((revealKernel profile ((source seed).view owner)).map
          (fun value => cast (congrArg EventGraph.EventField.Action outputEq.symm) value)).map
            (fun action => (runtime setup).canonicalServiceDecision leaks owner
              (current.recall owner) (current.observe app owner) event action) := by
    have law := sourceServiceCanonicalPolicy_reveal setup leaks fresh binding unresolved next
      wholeProfile profile refs (source seed) embedding refsBefore rank
      (seedAligned seed supported) current
      (by rw [same]; exact (checkpoint seed supported).agrees)
      (by rw [same]; exact (checkpoint seed supported).history)
      (by rw [same]; exact ready seed supported)
    rw [PMF.map_comp]
    exact law
  have normalizes seed (supported : seed ∈ prior.support) (value : Bool)
      (chosen : value ∈ (revealKernel profile ((source seed).view owner)).support) :
      effectiveDisclosure published binding (source seed) value = value := by
    have kept := (effective owner).1 rfl ((source seed).view owner) value chosen
    change effectiveDisclosureView published binding registry revelations
      (sourceObserve owner (source seed).state) value = value at kept
    rw [← registryEq seed supported, ← revelationsEq seed supported,
      effectiveDisclosureView_observe] at kept
    exact kept
  have decodedAction value : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) value) =
        some (.reveal owner name value) := by
    simpa [event, eventCount, outputEq, decodeEventAction] using aligned.actionEq
      ⟨0, by simp [eventCount]⟩
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) value)
  have endpoint seed (supported : seed ∈ prior.support) (value : Bool)
      (chosen : value ∈ (revealKernel profile ((source seed).view owner)).support)
      (final : app.Execution) (reached : final ∈ (fixed seed value).support) :
      sourceServicePrefix? setup (rank + 1) final.application.config =
        some (after (revealSuccessor published binding (source seed) value)) := by
    have actualCode : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
          (compileChecks (published := published) refs (source seed).registry
            (source seed).revelations binding) := by
      rw [registryEq seed supported, revelationsEq seed supported]
      exact codeEq
    have realized : EffectiveAction (execution seed).application.config event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) value) := by
      unfold EffectiveAction
      rw [nodeView_eq_resolve outputEq actualCode]
      simp only [cast_cast, cast_eq]
      intro requested
      subst value
      have kept := normalizes seed supported true chosen
      have resolved := compiled_disclosure_result published binding (source seed) refs
        (execution seed).application.config.store (checkpoint seed supported).agrees true
      rw [EventGraph.EventCode.resolveOutput?_playerStore] at resolved
      cases result : disclosureResult published binding (source seed) true with
      | failure => simp only [effectiveDisclosure, result] at kept; cases kept
      | success found => exact ⟨found, by rw [resolved, result]⟩
    have completed := decided_completion contract timely event (execution seed)
      (actualBoundary seed supported)
      (roundsFrom_turnFacts setup leaks
        (fun who => sourceServiceTurnPolicy_submitsAtTurn setup leaks _ _ _ _ who)
        _ _ (actualBoundary seed supported).supported).1
      (bounded seed supported) (ready seed supported) owned
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) value) realized final reached
    rw [(execution seed).application.config.step_eq_map_of_code event (ready seed supported)
      outputEq _ actualCode value
      (PMF.pure (disclosureResult published binding (source seed) value))
      (compileResolve_eval? refs (source seed).registry (source seed).revelations
        (source seed).state (execution seed).application.config.store
        (checkpoint seed supported).agrees binding value), PMF.pure_map,
      PMF.mem_support_pure_iff] at completed
    rw [completed]
    have checked := (checkpoint seed supported).reveal
      (native := configState (execution seed).application.config) published binding event eventRank
      (ready seed supported) outputEq (fun ref => refsBefore ref ⟨0, by simp [eventCount]⟩)
      value (decodedAction value)
    have read := checked.decode next (fun tail => embedding.ref tail.succ)
    unfold sourceServicePrefix?
    rw [transport 1, ← registryEq seed supported, ← revelationsEq seed supported]
    have localDecode := (decodeSourcePrefix?_reveal fresh binding unresolved next refs
      (source seed).registry (source seed).revelations embedding.ref 0 _ _).trans
        (congrArg (Option.map Sum.inr) read)
    exact congrArg (Option.map lift) localDecode
  have phase seed (supported : seed ∈ prior.support) :
      (stopped seed).map (fun final =>
          ((parameter seed, sourceServicePrefix? setup (rank + 1) final.application.config),
            (runtime setup).bindingTraffic leaks focal final)) =
        (revealKernel profile ((source seed).view owner)).bind fun value =>
          (fixed seed value).map fun final =>
            ((parameter seed,
              some (after (revealSuccessor published binding (source seed) value))),
              (runtime setup).bindingTraffic leaks focal final) := by
    dsimp only [stopped, app, players]
    rw [sourceServiceTurnPolicy_firstTurn_phase event (execution seed)
      (actualBoundary seed supported)]
    unfold ReactiveApplication.runUntilHorizon
    rw [firstTurn_runUntil_mixture event (execution seed) (actualBoundary seed supported) owner
      owned bound turns wholeProfile _ (policy seed supported) _, PMF.map_bind, PMF.bind_map]
    apply bind_congr_on_support _
    intro value chosen
    apply map_congr_on_support _
    intro final reached
    exact Prod.ext (Prod.ext rfl (endpoint seed supported value chosen final reached)) rfl
  have pairFactor : prior.map (fun seed => ((source seed, source seed, parameter seed),
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map fun seed => (source seed, source seed, parameter seed)).bind fun carried =>
        (typedNoise (carried.1.view focal)).map fun extra => (carried, extra) := by
    have paired := congrArg (PMF.map fun point =>
      ((point.1.2, point.1.2, point.1.1), point.2)) typedFactor
    simpa only [PMF.map_comp, PMF.map_bind, PMF.bind_map, Function.comp_def] using paired
  let choice := fun config : Config Player L Γ => revealKernel profile (config.view owner)
  have actualCode seed (supported : seed ∈ prior.support) :
      cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs (source seed).registry
          (source seed).revelations binding) := by
    rw [registryEq seed supported, revelationsEq seed supported]
    exact codeEq
  obtain ⟨nextTypedNoise, resolutionLaw⟩ :=
    sourceServiceFirstResolution_intention_factorization setup leaks published binding refs
      contract timely turns wholeProfile focal event outputEq prior parameter source source
      execution (fun seed supported => (checkpoint seed supported).agrees) actualCode
      (fun seed supported => nodeView_eq_resolve outputEq (actualCode seed supported))
      actualBoundary bounded
      choice typedNoise pairFactor
  let typedLaw := (prior.map fun seed => (source seed, source seed, parameter seed)).bind
    fun carried => (choice carried.2.1).map fun value =>
      (revealSuccessor published binding carried.1
        (effectiveDisclosure published binding carried.1 value),
        revealSuccessor published binding carried.2.1 value, carried.2.2)
  let typedJoint := typedLaw.bind fun carried =>
    (nextTypedNoise (carried.1.view focal)).map fun extra => (carried, extra)
  have typedJointFactor : typedJoint = (typedJoint.map Prod.fst).bind fun carried =>
      (nextTypedNoise (carried.1.view focal)).map fun extra => (carried, extra) := by
    have marginal : typedJoint.map Prod.fst = typedLaw := by
      simp only [typedJoint, Function.comp_def, ← PMF.bind_pure_comp,
        PMF.bind_bind, PMF.bind_const, PMF.pure_bind, PMF.bind_pure]
    rw [marginal]
  let defaultSource := source prior.support_nonempty.choose
  let defaultValue := (revealKernel profile (defaultSource.view owner)).support_nonempty.choose
  let fallback := (revealSuccessor published binding defaultSource defaultValue).view focal
  let recoverNext := fun view : Option (ProtocolView focal setup.program) =>
    (view.bind (recover focal) |>.bind Sum.getRight?).elim fallback
      (ProtocolView.entryView focal next)
  let embed := fun carried : Config Player L ((published, .publication payload) :: Γ) ×
      Config Player L ((published, .publication payload) :: Γ) × Parameter =>
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
    have mapped := congrArg (PMF.map fun carried => (embed carried.1, carried.2)) resolutionLaw
    calc
      _ = prior.bind (fun seed =>
          (revealKernel profile ((source seed).view owner)).bind fun value =>
            (fixed seed value).map fun final =>
              ((parameter seed,
                some (after (revealSuccessor published binding (source seed) value))),
                (runtime setup).bindingTraffic leaks focal final)) :=
        bind_congr_on_support _ fun seed supported => phase seed supported
      _ = _ := by
        rw [← mapped]
        simp only [choice, embed, PMF.map_bind, PMF.map_comp, Function.comp_def]
        apply bind_congr_on_support _
        intro seed supported
        apply bind_congr_on_support _
        intro value chosen
        rw [normalizes seed supported value chosen]
  have marginal : (typedJoint.map fun carried => (embed carried.1, carried.2)).map Prod.fst =
      (prior.map fun seed => (parameter seed, before (source seed))).bind fun carried =>
        (ProtocolState.behavioralStateStep setup.program wholeProfile carried.2).map fun state =>
          (carried.1, some state) := by
    simp only [typedJoint, typedLaw, embed, choice, Function.comp_def,
      ← PMF.bind_pure_comp, PMF.bind_bind, PMF.bind_const, PMF.pure_bind]
    apply bind_congr_on_support _
    intro seed supported
    change _ = (ProtocolState.behavioralStateStep setup.program wholeProfile
      (lift (.inl (source seed)))).bind _
    rw [commutes, ProtocolState.behavioralStateStep_reveal_entry, PMF.bind_map, PMF.bind_map]
    apply bind_congr_on_support _
    intro value chosen
    rw [normalizes seed supported value chosen]
    rfl
  refine ⟨fun view => nextTypedNoise (recoverNext view), ?_, ?_⟩
  · intro seed supported
    unfold sourceServicePrefix?
    have symbolic := transport 0
    simp only [Nat.add_zero] at symbolic
    rw [symbolic, ← registryEq seed supported, ← revelationsEq seed supported,
      (checkpoint seed supported).decode
        (.reveal published owner name fresh binding unresolved next) embedding.ref]
    rfl
  · rw [nativeEq]
    dsimp only at lifted
    rw [marginal] at lifted
    exact lifted

end Vegas
