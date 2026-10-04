/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceResolutionMemoryLaw
import Vegas.Game.SourceServiceResolutionIntentionFactorization
import Vegas.Pending.ReactiveBindingSchedule

/-! # Original disclosure memory and the complete actual response channel

Restoring the source normalizer's private memory preserves the prior effective
source and traffic channel. The current geometric response then carries both
source configurations: waiting preserves them, and transmission advances the
effective configuration by the emitted decision and the original configuration
by its intended decision. The native marginal is the actual protected policy.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Waiting keeps the source pair. Transmission preserves the original
intention while the effective source records the physically emitted decision. -/
def resolutionIntentionSources {Γ : SourceCtx Player L} {name : VarId}
    {owner : Player} {payload : L.Ty} (published : VarId)
    (binding : HasVar Γ name (.commitment owner payload))
    (pair : Config Player L Γ × Config Player L Γ) : Option Bool →
    (Config Player L Γ × Config Player L Γ) ⊕
      (Config Player L ((published, .publication payload) :: Γ) ×
        Config Player L ((published, .publication payload) :: Γ))
  | none => .inl pair
  | some intended => .inr
      (revealSuccessor published binding pair.1
        (effectiveDisclosure published binding pair.1 intended),
        revealSuccessor published binding pair.2 intended)

/-- The traffic channel reads the effective source view and the wait/decision
tag. It does not read the original hidden intention from the native packet. -/
def resolutionIntentionView {Γ : SourceCtx Player L} {payload : L.Ty}
    (published : VarId) (focal : Player) :
    ((Config Player L Γ × Config Player L Γ) ⊕
      (Config Player L ((published, .publication payload) :: Γ) ×
        Config Player L ((published, .publication payload) :: Γ))) →
    DecisionView focal Γ ⊕ DecisionView focal ((published, .publication payload) :: Γ)
  | .inl pair => .inl (pair.1.view focal)
  | .inr pair => .inr (pair.1.view focal)

/-- The physical wait or effective canonical packet for an original intention. -/
def resolutionIntentionResponse {Γ : SourceCtx Player L} {name : VarId}
    {owner : Player} {payload : L.Ty} (published : VarId)
    (binding : HasVar Γ name (.commitment owner payload)) (source : Config Player L Γ)
    (execution : (application setup leaks).Execution) (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publication payload) :
    Option Bool → (application setup leaks).Action
  | none => ⟨none⟩
  | some intended => (runtime setup).canonicalServiceDecision leaks owner
      (execution.recall owner) (execution.observe (application setup leaks) owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (effectiveDisclosure published binding source intended))

private theorem restoreMemory_traffic_factorization {Seed : Type*} {Γ : SourceCtx Player L}
    (owner focal : Player) (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (remember : DecisionView owner Γ → PMF (List (OwnAction Player L)))
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view focal)).map fun extra => (config, extra)) :
    let lifted := prior.bind fun seed =>
      ((source seed).restoreMemory owner remember).map fun original => (seed, original)
    lifted.map (fun point => ((source point.1, point.2),
        (runtime setup).bindingTraffic leaks focal (execution point.1))) =
      (lifted.map (fun point => (source point.1, point.2))).bind fun pair =>
        (noise (pair.1.view focal)).map fun extra => (pair, extra) := by
  intro lifted
  have restored := congrArg (PMF.bind · (fun pair =>
      (pair.1.restoreMemory owner remember).map fun original => ((pair.1, original), pair.2)))
    factor
  calc
    _ = prior.bind (fun seed => (noise ((source seed).view focal)).bind fun extra =>
        ((source seed).restoreMemory owner remember).map fun original =>
          ((source seed, original), extra)) := by
      simpa only [lifted, PMF.map_bind, PMF.map_comp, PMF.bind_map, PMF.bind_bind,
        Function.comp_def] using restored
    _ = prior.bind (fun seed => ((source seed).restoreMemory owner remember).bind fun original =>
        (noise ((source seed).view focal)).map fun extra => ((source seed, original), extra)) := by
      apply bind_congr_on_support _
      intro seed _
      exact PMF.bind_comm _ _ _
    _ = _ := by
      simp only [lifted, PMF.map_bind, PMF.bind_map, PMF.bind_bind, Function.comp_def]

private theorem resolutionIntention_factorization
    {Seed : Type*} {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (refs : ContextRefs (graph setup).layout Γ) (focal : Player)
    (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (prior : PMF Seed) (source original : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (agree : ∀ seed ∈ prior.support,
      refs.Agrees (source seed).state (execution seed).application.config.store)
    (valid : ∀ seed ∈ prior.support, (execution seed).application.BindingInvariant)
    (recalled : ∀ seed ∈ prior.support, (execution seed).InputRecall (application setup leaks))
    (codeEq : ∀ seed ∈ prior.support,
      cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
          (compileChecks (published := published) refs (source seed).registry
            (source seed).revelations binding))
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => ((source seed, original seed),
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (noise (pair.1.view focal)).map fun extra => (pair, extra))
    (choice : (Config Player L Γ × Config Player L Γ) → PMF (Option Bool)) :
    ∃ nextNoise :
        (DecisionView focal Γ ⊕ DecisionView focal ((published, .publication payload) :: Γ)) →
          PMF _,
      (prior.bind fun seed => (choice (source seed, original seed)).map fun intended =>
        (resolutionIntentionSources published binding (source seed, original seed) intended,
          (runtime setup).bindingTraffic leaks focal
            ((execution seed).respond (application setup leaks) owner
              (resolutionIntentionResponse published binding (source seed) (execution seed)
                event outputEq intended)))) =
      ((prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (choice pair).map (resolutionIntentionSources published binding pair)).bind fun pair =>
          (nextNoise (resolutionIntentionView published focal pair)).map fun extra =>
            (pair, extra) := by
  have emittable (config : Config Player L Γ) (intended : Bool) :
      effectiveDisclosure published binding config intended = false ∨
        ∃ value : L.Val payload, effectiveDisclosure published binding config intended = true ∧
          disclosureResult published binding config true = .success value := by
    cases intended with
    | false => exact Or.inl (effectiveDisclosure_false published binding config)
    | true =>
        cases result : disclosureResult published binding config true with
        | failure => exact Or.inl (by simp only [effectiveDisclosure, result])
        | success value => exact Or.inr ⟨value, by simp only [effectiveDisclosure, result], rfl⟩
  obtain ⟨nextNoise, law⟩ := exists_updated_observation_kernel_of_readout prior
    (fun seed => (source seed, original seed))
    (fun seed => (runtime setup).bindingTraffic leaks focal (execution seed))
    (fun pair => pair.1.view focal) noise factor choice
    (resolutionIntentionSources published binding) (resolutionIntentionView published focal)
    (fun seed intended => PMF.pure ((runtime setup).bindingTraffic leaks focal
      ((execution seed).respond (application setup leaks) owner
        (resolutionIntentionResponse published binding (source seed) (execution seed)
          event outputEq intended))))
    (by
      intro left _ first _ right _ second _ same
      cases first with
      | none =>
          cases second with
          | none => exact Sum.inl.inj same
          | some value => cases same
      | some first =>
          cases second with
          | none => cases same
          | some second =>
              exact reveal_view_reflects focal published binding left.1 right.1
                (effectiveDisclosure published binding left.1 first)
                (effectiveDisclosure published binding right.1 second) (Sum.inr.inj same))
    (by
      intro left leftSupport first _ right rightSupport second _ same traffic
      cases first with
      | none =>
          cases second with
          | none => exact congrArg PMF.pure ((runtime setup).bindingTraffic_silent leaks
              (execution left) (execution right) focal owner traffic ⟨none⟩ rfl)
          | some value => cases same
      | some first =>
          cases second with
          | none => cases same
          | some second =>
              exact congrArg PMF.pure (source_resolution_decision_traffic_congr setup leaks
                published binding refs (source left) (source right) (execution left)
                (execution right) (agree left leftSupport) (agree right rightSupport)
                (valid left leftSupport) (valid right rightSupport)
                (recalled left leftSupport) (recalled right rightSupport) event focal outputEq
                (codeEq left leftSupport) (codeEq right rightSupport)
                (nodeView_eq_resolve outputEq (codeEq left leftSupport))
                (nodeView_eq_resolve outputEq (codeEq right rightSupport))
                (effectiveDisclosure published binding (source left) first)
                (effectiveDisclosure published binding (source right) second)
                (emittable (source left) first) (emittable (source right) second)
                (Sum.inr.inj same) traffic))
  refine ⟨nextNoise, ?_⟩
  simpa only [PMF.pure_map, ← PMF.bind_pure_comp, PMF.pure_bind, Function.comp_def] using law

private theorem bind_resolution_mix {α β : Type*} (law : PMF α)
    (weight : ℝ) (nonneg : 0 ≤ weight) (atMost : weight ≤ 1)
    (first second : α → PMF β) :
    (law.bind fun point => mix weight nonneg atMost (first point) (second point)) =
      mix weight nonneg atMost (law.bind first) (law.bind second) := by
  have exchanged := PMF.bind_comm law
    (mix weight nonneg atMost (PMF.pure true) (PMF.pure false))
    (fun point selected => if selected then first point else second point)
  simpa only [mix_bind, PMF.pure_bind, Bool.false_eq_true, ↓reduceIte] using exchanged

variable [Fintype Player]

/-- At actual clear protected normalized resolution inputs, the original
memory lottery and geometric response preserve the effective/original source
pair and the same complete traffic channel. The only prior channel premise is
the effective source/traffic induction law; the original-memory coupling and
the actual native policy marginal follow from the source normalizer itself. -/
theorem source_async_resolution_memory_factorization
    {Seed : Type*} {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (profile : BehavioralProfile setup.program)
    (original : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (remember : DecisionView owner Γ → PMF (List (OwnAction Player L)))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (focal : Player) (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution) (remaining : Seed → Nat)
    (aligned : ∀ seed ∈ prior.support,
      CompiledPolicySuffix setup.program profile
        (.reveal published owner name fresh binding unresolved next)
        (Function.update original owner ((original owner).normalizeDisclosureFrom
          (.reveal published owner name fresh binding unresolved next)
            (source seed).registry (source seed).revelations remember))
        refs (source seed).revelations (source seed).registry embedding refsBefore
          (embedding.event ⟨0, by simp [eventCount]⟩).val)
    (agree : ∀ seed ∈ prior.support,
      refs.Agrees (source seed).state (execution seed).application.config.store)
    (history : ∀ seed ∈ prior.support, decodeHistory setup.program
      ((execution seed).application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = (source seed).history)
    (trace : ∀ seed ∈ prior.support,
      ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
        scheduler).Trace (some ⟨remaining seed, some owner, execution seed⟩))
    (clear : ∀ seed ∈ prior.support, ∀ player,
      (runtime setup).persistentServiceRisk leaks bound player ((execution seed).recall player)
        ((execution seed).observe (application setup leaks) player) = false)
    (ready : ∀ seed ∈ prior.support, (execution seed).application.config.cut.Ready
      (embedding.event ⟨0, by simp [eventCount]⟩))
    (unrecorded : ∀ seed ∈ prior.support,
      (runtime setup).eventRecorded leaks ((execution seed).recall owner)
        (embedding.event ⟨0, by simp [eventCount]⟩) = false)
    (fits : ∀ seed ∈ prior.support,
      (execution seed).application.publicView.InclusionFitsDeadline (runtime setup) bound
        (embedding.event ⟨0, by simp [eventCount]⟩))
    (weight : ℝ) (positive : 0 < weight) (below : weight < 1)
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view focal)).map fun extra => (config, extra)) :
    let program := SourceProgram.reveal published owner name fresh binding unresolved next
    let index : Fin (eventCount program) := ⟨0, by simp [program, eventCount]⟩
    let event := embedding.event index
    let outputEq : (graph setup).outputLayout event = .publication payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, program, outputLayout, eventCount] using embedding.layout_eq index
    let lifted := prior.bind fun seed =>
      ((source seed).restoreMemory owner remember).map fun old => (seed, old)
    let choice := fun pair : Config Player L Γ × Config Player L Γ =>
      mix weight positive.le below.le (PMF.pure none)
        ((revealKernel original (pair.2.view owner)).map some)
    let joint := lifted.bind fun point => (choice (source point.1, point.2)).map fun intended =>
      (resolutionIntentionSources published binding (source point.1, point.2) intended,
        (runtime setup).bindingTraffic leaks focal
          ((execution point.1).respond (application setup leaks) owner
            (resolutionIntentionResponse published binding (source point.1) (execution point.1)
              event outputEq intended)))
    ∃ nextNoise :
        (DecisionView focal Γ ⊕ DecisionView focal ((published, .publication payload) :: Γ)) →
          PMF _,
      joint = (
        ((lifted.map (fun point => (source point.1, point.2))).bind fun pair =>
          (choice pair).map (resolutionIntentionSources published binding pair)).bind fun pair =>
            (nextNoise (resolutionIntentionView published focal pair)).map fun extra =>
              (pair, extra)) ∧
      joint.map Prod.snd = prior.bind fun seed =>
        (sourceServiceTurnPolicy setup leaks bound horizon
          (geometricTiming setup horizon weight positive.le below.le) profile owner
          ((execution seed).recall owner)
          ((execution seed).observe (application setup leaks) owner)).map fun response =>
            (runtime setup).bindingTraffic leaks focal
              ((execution seed).respond (application setup leaks) owner response) := by
  intro program index event outputEq lifted choice joint
  have liftedSupport (point : Seed × Config Player L Γ) (supported : point ∈ lifted.support) :
      point.1 ∈ prior.support := by
    obtain ⟨seed, selected, produced⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
    obtain ⟨old, _memory, equal⟩ := PMF.support_map .. ▸ produced
    cases equal
    exact selected
  have codeEq (seed : Seed) (supported : seed ∈ prior.support) :
      cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
          (compileChecks (published := published) refs (source seed).registry
            (source seed).revelations binding) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes _) = _
    simpa [event, index, program, outputLayout, compileRankedNodes] using
      (aligned seed supported).graphSuffix.nodeEq index
  have rawTrace (seed : Seed) (supported : seed ∈ prior.support) :=
    (bounds.riskMenu (runtime setup) leaks bound).toRawTrace (initialLaw setup) horizon scheduler
      (trace seed supported)
  have sourcePairLaw := restoreMemory_traffic_factorization owner focal prior source execution
    remember noise factor
  obtain ⟨nextNoise, paired⟩ := resolutionIntention_factorization published binding refs focal
    event outputEq lifted (fun point => source point.1) Prod.snd (fun point => execution point.1)
    (fun point supported => agree point.1 (liftedSupport point supported))
    (fun point supported => (legalFacts setup leaks horizon scheduler _
      (rawTrace point.1 (liftedSupport point supported))).binding)
    (fun point supported => (legalFacts setup leaks horizon scheduler _
      (rawTrace point.1 (liftedSupport point supported))).inputs)
    (fun point supported => codeEq point.1 (liftedSupport point supported)) noise sourcePairLaw
    choice
  refine ⟨nextNoise, paired, ?_⟩
  simp only [joint, lifted, PMF.map_bind, PMF.map_comp, PMF.bind_map, PMF.bind_bind,
    Function.comp_def]
  apply bind_congr_on_support _
  intro seed supported
  have memory := sourceServiceDecision_clear_protected_resolution_memory setup leaks fresh
    binding unresolved next profile original remember refs (source seed) embedding refsBefore
    event.val (aligned seed supported) bounds bound (execution seed) (agree seed supported)
    (history seed supported) (trace seed supported) (clear seed supported) (ready seed supported)
    (unrecorded seed supported) (fits seed supported) weight positive below
  have marginal := congrArg (PMF.map ((runtime setup).bindingTraffic leaks focal)) memory.2
  have node := nodeView_eq_resolve outputEq (codeEq seed supported)
  have notBinding who ty output code
      (impossible : nodeView (graph setup) event = .bind who ty output code) : False := by
    rw [node] at impossible
    cases impossible
  have rendered (intended : Bool) :
      (runtime setup).canonicalServiceDecision leaks owner ((execution seed).recall owner)
          ((execution seed).observe (application setup leaks) owner) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm)
            (effectiveDisclosure published binding (source seed) intended)) =
        (runtime setup).canonicalServiceDecision leaks owner ((execution seed).recall owner)
          ((execution seed).observe (application setup leaks) owner) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) intended) := by
    rw [(runtime setup).canonicalServiceDecision_eq_of_not_bind leaks owner _ _ event _
      notBinding, (runtime setup).canonicalServiceDecision_eq_of_not_bind leaks owner _ _ event _
      notBinding]
    exact (serviceDecision_effectiveDisclosure (runtime setup) leaks published binding
      (source seed) refs (execution seed) (agree seed supported) event outputEq
        (codeEq seed supported) node intended).symm
  simp only [choice, mix_map, PMF.pure_map, PMF.map_comp, Function.comp_def,
    resolutionIntentionResponse]
  simp_rw [rendered]
  rw [bind_resolution_mix]
  simpa only [mix_map, mix_bind, PMF.map_bind, PMF.map_comp, ← PMF.bind_pure_comp,
    PMF.bind_bind, PMF.pure_bind, Function.comp_def] using marginal

end Vegas
