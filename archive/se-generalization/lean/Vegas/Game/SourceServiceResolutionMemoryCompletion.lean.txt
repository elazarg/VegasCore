/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceResolutionResponseCompletion
import Vegas.Game.SourceServiceRecordedResolutionTraffic

/-! # Original disclosure memory through the recorded completion boundary

The actual source memory lottery and geometric decision produce a tagged source
pair and native execution. Waiting remains at its post-response boundary. A
transmitting draw carries the same actual packet through delayed completion,
with the original intention retained and the effective source state realized.
The conditional channel includes full native traffic and scheduler recall.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem bind_memory_mix {α β : Type*} (law : PMF α)
    (weight : ℝ) (nonneg : 0 ≤ weight) (atMost : weight ≤ 1)
    (first second : α → PMF β) :
    (law.bind fun point => mix weight nonneg atMost (first point) (second point)) =
      mix weight nonneg atMost (law.bind first) (law.bind second) := by
  have exchanged := PMF.bind_comm law
    (mix weight nonneg atMost (PMF.pure true) (PMF.pure false))
    (fun point selected => if selected then first point else second point)
  simpa only [mix_bind, PMF.pure_bind, Bool.false_eq_true, ↓reduceIte] using exchanged

/-- The current owner's actual restored memory and original intention join the
effective typed completion and complete traffic channel. This is a local
probability kernel, not a source-belief or equilibrium transport theorem. -/
theorem source_async_resolution_memory_completion_factorization
    {Seed : Type} {Γ : SourceCtx Player L} {openNames : Finset VarId}
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
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (bounds : MessageBounds (graph setup))
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
    (initialized : ∀ seed ∈ prior.support,
      (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler
        (sourceServiceTurnPolicy setup leaks bound horizon
          (geometricTiming setup horizon weight positive.le below.le) profile)
        (some ⟨remaining seed, some owner, execution seed⟩))
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
    let players := sourceServiceTurnPolicy setup leaks bound horizon
      (geometricTiming setup horizon weight positive.le below.le) profile
    let boundary := fun current : (application setup leaks).Execution =>
      if (runtime setup).eventRecorded leaks (current.recall owner) event then
        (application setup leaks).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon current
      else PMF.pure current
    let lifted := prior.bind fun seed =>
      ((source seed).restoreMemory owner remember).map fun old => (seed, old)
    let choice := fun pair : Config Player L Γ × Config Player L Γ =>
      mix weight positive.le below.le (PMF.pure none)
        ((revealKernel original (pair.2.view owner)).map some)
    let draws := lifted.bind fun point => (choice (source point.1, point.2)).map fun intended =>
      (point, intended)
    let carrier := fun draw : (Seed × Config Player L Γ) × Option Bool =>
      resolutionIntentionSources published binding (source draw.1.1, draw.1.2) draw.2
    let responded := fun draw : (Seed × Config Player L Γ) × Option Bool =>
      (execution draw.1.1).respond (application setup leaks) owner
        (resolutionIntentionResponse published binding (source draw.1.1)
          (execution draw.1.1) event outputEq draw.2)
    let joint := draws.bind fun draw => (boundary (responded draw)).map fun final =>
      (carrier draw, final)
    ∃ nextNoise :
        (DecisionView focal Γ ⊕ DecisionView focal ((published, .publication payload) :: Γ)) →
          PMF _,
      joint.map (fun point => (point.1, (runtime setup).bindingTraffic leaks focal point.2)) =
        ((draws.map carrier).bind fun pair =>
          (nextNoise (resolutionIntentionView published focal pair)).map fun extra =>
            (pair, extra)) ∧
      joint.map Prod.snd = (prior.bind fun seed =>
        (players owner ((execution seed).recall owner)
          ((execution seed).observe (application setup leaks) owner)).bind fun response =>
            boundary ((execution seed).respond (application setup leaks) owner response)) ∧
      ∀ point ∈ joint.support,
        match point.1 with
        | .inl pair => refs.Agrees pair.1.state point.2.application.config.store ∧
            refs.Agrees pair.2.state point.2.application.config.store ∧
            decodeHistory setup.program (point.2.application.config.history.map
              (setup.eventGraph.fromModeCompletion .sequential)) = pair.1.history
        | .inr pair =>
            (refs.cons (name := published) ⟨.inr event, outputEq⟩).Agrees
              pair.1.state point.2.application.config.store ∧
            (refs.cons (name := published) ⟨.inr event, outputEq⟩).Agrees
              pair.2.state point.2.application.config.store ∧
            decodeHistory setup.program (point.2.application.config.history.map
              (setup.eventGraph.fromModeCompletion .sequential)) = pair.1.history := by
  intro program index event outputEq players boundary lifted choice draws carrier responded joint
  let app := application setup leaks
  let timing := geometricTiming setup horizon weight positive.le below.le
  have sourceCode (seed : Seed) (supported : seed ∈ prior.support) :
      cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
          (compileChecks (published := published) refs (source seed).registry
            (source seed).revelations binding) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes _) = _
    simpa [event, index, program, outputLayout, compileRankedNodes] using
      (aligned seed supported).graphSuffix.nodeEq index
  have ownerEq : (graph setup).actor? event = some owner :=
    nodeView_resolve_actor outputEq (sourceCode _ prior.support_nonempty.choose_spec)
  have latentSupport (draw : (Seed × Config Player L Γ) × Option Bool)
      (supported : draw ∈ draws.support) :
      draw.1.1 ∈ prior.support ∧
        draw.1.2 ∈ ((source draw.1.1).restoreMemory owner remember).support ∧
        draw.2 ∈ (choice (source draw.1.1, draw.1.2)).support := by
    obtain ⟨point, pointSupport, produced⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
    obtain ⟨intended, intentionSupport, equal⟩ := PMF.support_map .. ▸ produced
    cases equal
    obtain ⟨seed, seedSupport, restored⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ pointSupport)
    obtain ⟨old, memorySupport, equal⟩ := PMF.support_map .. ▸ restored
    cases equal
    exact ⟨seedSupport, memorySupport, intentionSupport⟩
  have selected (seed : Seed) (old : Config Player L Γ) (intended : Bool)
      (support : some intended ∈ (choice (source seed, old)).support) :
      intended ∈ (revealKernel original (old.view owner)).support := by
    dsimp only [choice] at support
    have chosen : some intended ∈ ((revealKernel original (old.view owner)).map some).support := by
      rw [PMF.mem_support_iff]
      intro zero
      rw [PMF.mem_support_iff, mix_apply] at support
      simp only [PMF.pure_apply, zero, mul_zero, add_zero, Option.some_ne_none,
        ↓reduceIte, ne_eq, not_true_eq_false] at support
    obtain ⟨drawn, member, same⟩ := PMF.support_map .. ▸ chosen
    cases Option.some.inj same
    exact member
  have completion (seed : Seed) (seedSupport : seed ∈ prior.support)
      (old : Config Player L Γ)
      (restored : old ∈ ((source seed).restoreMemory owner remember).support)
      (intended : Bool)
      (intentionSupport : intended ∈ (revealKernel original (old.view owner)).support) :=
    sourceServiceDecision_clear_resolution_intention_completion fresh binding unresolved next
      profile original remember refs (source seed) embedding refsBefore contract bounds
      (execution seed) (aligned seed seedSupport) (agree seed seedSupport)
      (history seed seedSupport) (trace seed seedSupport) (clear seed seedSupport)
      (ready seed seedSupport) (unrecorded seed seedSupport) (fits seed seedSupport)
      weight positive below players rfl (initialized seed seedSupport) old restored intended
      intentionSupport
  have afterRecorded (draw : (Seed × Config Player L Γ) × Option Bool)
      (support : draw ∈ draws.support) :
      (runtime setup).eventRecorded leaks ((responded draw).recall owner) event =
        draw.2.isSome := by
    obtain ⟨seedSupport, restored, choiceSupport⟩ := latentSupport draw support
    rcases draw with ⟨⟨seed, old⟩, intended⟩
    cases intended with
    | none =>
        change (runtime setup).eventRecorded leaks
          (((execution seed).respond app owner ⟨none⟩).recall owner) event = false
        rw [(runtime setup).eventRecorded_respond_other leaks (execution seed) owner owner
          ⟨none⟩ event (by intro _ impossible; cases impossible)]
        exact unrecorded seed seedSupport
    | some intended =>
        obtain ⟨_, entry, member, message, actionEq, _identity, call, _done⟩ :=
          completion seed seedSupport old restored intended
            (selected seed old intended choiceSupport)
        rcases (runtime setup).canonicalServiceDecision_cases leaks owner
            ((execution seed).recall owner) ((execution seed).observe app owner) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm)
              (effectiveDisclosure published binding (source seed) intended)) with silent | named
        · obtain ⟨material, fresh⟩ := call.fresh
          rw [actionEq] at fresh
          change ((runtime setup).canonicalServiceDecision leaks owner
            ((execution seed).recall owner) ((execution seed).observe app owner) event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm)
              (effectiveDisclosure published binding (source seed) intended))).transmission =
                some material at fresh
          rw [silent] at fresh
          cases fresh
        · exact (runtime setup).eventRecorded_respond leaks (execution seed) owner _ event named
  have afterSupport (draw : (Seed × Config Player L Γ) × Option Bool)
      (support : draw ∈ draws.support) (intended : Bool) (equal : draw.2 = some intended) :
      app.RoundSupported (initialLaw setup) horizon scheduler players
        (some ⟨remaining draw.1.1, none, responded draw⟩) := by
    obtain ⟨seedSupport, restored, choiceSupport⟩ := latentSupport draw support
    rw [equal] at choiceSupport
    apply sourceResponse_roundSupported (initialized draw.1.1 seedSupport)
    rw [equal]
    exact (completion draw.1.1 seedSupport draw.1.2 restored intended
      (selected draw.1.1 draw.1.2 intended choiceSupport)).1
  obtain ⟨afterNoise, afterFactor, _nativeTraffic⟩ :=
    source_async_resolution_memory_factorization fresh binding unresolved next profile original
      remember refs embedding refsBefore bounds bound focal prior source execution remaining
      aligned agree history trace clear ready unrecorded fits weight positive below noise factor
  have factorAfter : draws.map (fun draw =>
      (carrier draw, (runtime setup).bindingTraffic leaks focal (responded draw))) =
      (draws.map carrier).bind fun pair =>
        (afterNoise (resolutionIntentionView published focal pair)).map fun extra =>
          (pair, extra) := by
    simpa only [draws, lifted, choice, carrier, responded, PMF.map_bind, PMF.map_comp,
      PMF.bind_map, PMF.bind_bind, Function.comp_def] using
      afterFactor
  let representative := prior.support_nonempty.choose
  let checks := compileChecks (published := published) refs (source representative).registry
    (source representative).revelations binding
  have node := nodeView_eq_resolve outputEq (sourceCode representative
    prior.support_nonempty.choose_spec)
  obtain ⟨nextNoise, factorStopped⟩ := exists_updated_observation_kernel_of_readout draws carrier
    (fun draw => (runtime setup).bindingTraffic leaks focal (responded draw))
    (resolutionIntentionView published focal) afterNoise factorAfter (fun _ => PMF.pure Unit.unit)
    (fun pair _ => pair) (resolutionIntentionView published focal)
    (fun draw _ => (boundary (responded draw)).map ((runtime setup).bindingTraffic leaks focal))
    (fun _ _ _ _ _ _ _ _ same => same)
    (by
      intro left leftSupport _ _ right rightSupport _ _ sameView traffic
      cases first : left.2 with
      | none =>
          cases second : right.2 with
          | none =>
              simp only [boundary, afterRecorded left leftSupport, first,
                afterRecorded right rightSupport, second, Option.isSome_none,
                Bool.false_eq_true, ↓reduceIte, PMF.pure_map]
              exact congrArg PMF.pure traffic
          | some intended =>
              simp only [carrier, resolutionIntentionSources, first, second,
                resolutionIntentionView] at sameView
              cases sameView
      | some intended =>
          cases second : right.2 with
          | none =>
              simp only [carrier, resolutionIntentionSources, first, second,
                resolutionIntentionView] at sameView
              cases sameView
          | some other =>
              simp only [boundary, afterRecorded left leftSupport, first,
                afterRecorded right rightSupport, second, Option.isSome_some, ↓reduceIte]
              have leftBoundary := afterSupport left leftSupport intended first
              have rightBoundary := afterSupport right rightSupport other second
              have leftSupported := (latentSupport left leftSupport).1
              have rightSupported := (latentSupport right rightSupport).1
              have leftReady : (responded left).application.config.cut.Ready event := by
                rw [((runtime setup).reactive_respond_application leaks (execution left.1.1)
                  owner _).1]
                exact ready left.1.1 leftSupported
              have rightReady : (responded right).application.config.cut.Ready event := by
                rw [((runtime setup).reactive_respond_application leaks (execution right.1.1)
                  owner _).1]
                exact ready right.1.1 rightSupported
              rw [sourceServiceTurnPolicy_runUntilHorizon_of_recorded setup leaks scheduler bound
                horizon timing profile horizon (responded left) owner event leftReady ownerEq
                  (by rw [afterRecorded left leftSupport, first]; rfl),
                sourceServiceTurnPolicy_runUntilHorizon_of_recorded setup leaks scheduler bound
                  horizon timing profile horizon (responded right) owner event rightReady ownerEq
                    (by rw [afterRecorded right rightSupport, second]; rfl)]
              obtain ⟨leftTrace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler
                players _ (by
                  change (responded left).environmentRecall.length ≤ horizon
                  have budget := leftBoundary.1
                  change (responded left).environmentRecall.length + remaining left.1.1 =
                    horizon at budget
                  omega)
                  (responded left) leftBoundary.2
              obtain ⟨rightTrace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler
                players _ (by
                  change (responded right).environmentRecall.length ≤ horizon
                  have budget := rightBoundary.1
                  change (responded right).environmentRecall.length + remaining right.1.1 =
                    horizon at budget
                  omega)
                  (responded right) rightBoundary.2
              exact source_resolution_conforming_silent_runUntilHorizon setup leaks leftTrace
                rightTrace (by
                  intro entry member material message sent emitted
                  exact sourceServiceTurnPolicy_freshServiceEnvelope scheduler players owner timing
                    profile rfl _ (responded left) leftBoundary.2 entry member material sent
                      message emitted) leftReady payload (refs.get binding) checks outputEq
                        (sourceCode representative prior.support_nonempty.choose_spec) node focal
                          traffic)
  refine ⟨nextNoise, ?_, ?_, ?_⟩
  · simpa only [joint, PMF.map_bind, PMF.map_comp, PMF.pure_bind, PMF.pure_map,
      PMF.bind_pure, PMF.map_id, Function.comp_def] using factorStopped
  · have physical : draws.map responded = prior.bind fun seed =>
        (players owner ((execution seed).recall owner)
          ((execution seed).observe app owner)).map ((execution seed).respond app owner) := by
      simp only [draws, lifted, responded, PMF.map_bind, PMF.map_comp, PMF.bind_map,
        PMF.bind_bind, Function.comp_def]
      apply bind_congr_on_support _
      intro seed seedSupport
      have memory := sourceServiceDecision_clear_protected_resolution_memory setup leaks fresh
        binding unresolved next profile original remember refs (source seed) embedding refsBefore
        event.val (aligned seed seedSupport) bounds bound (execution seed) (agree seed seedSupport)
        (history seed seedSupport) (trace seed seedSupport) (clear seed seedSupport)
        (ready seed seedSupport) (unrecorded seed seedSupport) (fits seed seedSupport)
        weight positive below
      have notBind who ty output code
          (impossible : nodeView (graph setup) event = .bind who ty output code) : False := by
        rw [node] at impossible
        cases impossible
      have rendered (intended : Bool) :
          (runtime setup).canonicalServiceDecision leaks owner ((execution seed).recall owner)
              ((execution seed).observe app owner) event
              (cast (congrArg EventGraph.EventField.Action outputEq.symm)
                (effectiveDisclosure published binding (source seed) intended)) =
            (runtime setup).canonicalServiceDecision leaks owner ((execution seed).recall owner)
              ((execution seed).observe app owner) event
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) intended) := by
        rw [(runtime setup).canonicalServiceDecision_eq_of_not_bind leaks owner _ _ event _
          notBind, (runtime setup).canonicalServiceDecision_eq_of_not_bind leaks owner _ _ event _
          notBind]
        exact (serviceDecision_effectiveDisclosure (runtime setup) leaks published binding
          (source seed) refs (execution seed) (agree seed seedSupport) event outputEq
            (sourceCode seed seedSupport) (nodeView_eq_resolve outputEq
              (sourceCode seed seedSupport)) intended).symm
      simp only [choice, mix_map, PMF.pure_map, PMF.map_comp, Function.comp_def,
        resolutionIntentionResponse]
      calc
        _ = ((source seed).restoreMemory owner remember).bind (fun old =>
            mix weight positive.le below.le
              (PMF.pure ((execution seed).respond app owner ⟨none⟩))
              ((revealKernel original (old.view owner)).map fun intended =>
                (execution seed).respond app owner ((runtime setup).canonicalServiceDecision
                  leaks owner ((execution seed).recall owner) ((execution seed).observe app owner)
                    event (cast (congrArg EventGraph.EventField.Action outputEq.symm)
                      intended)))) := by
          apply bind_congr_on_support _
          intro old _
          congr 1
          apply map_congr_on_support _
          intro intended _
          exact congrArg ((execution seed).respond app owner) (rendered intended)
        _ = _ := by
          rw [bind_memory_mix]
          simpa only [mix_map, mix_bind, PMF.map_bind, PMF.map_comp, ← PMF.bind_pure_comp,
            PMF.bind_bind, PMF.pure_bind, Function.comp_def] using memory.2
    have advanced := congrArg (PMF.bind · boundary) physical
    have projection : joint.map Prod.snd = draws.bind (fun draw => boundary (responded draw)) := by
      simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
      apply bind_congr_on_support _
      intro draw _
      exact PMF.map_id _
    rw [projection]
    simpa only [PMF.bind_map, PMF.bind_bind, Function.comp_def] using advanced
  · intro point pointSupport
    obtain ⟨draw, drawn, produced⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ pointSupport)
    obtain ⟨final, finalSupport, equal⟩ := PMF.support_map .. ▸ produced
    cases equal
    obtain ⟨seedSupport, restored, choiceSupport⟩ := latentSupport draw drawn
    cases intention : draw.2 with
    | none =>
        simp only [boundary, afterRecorded draw drawn, intention, Option.isSome_none,
          Bool.false_eq_true, ↓reduceIte, PMF.mem_support_pure_iff] at finalSupport
        subst final
        simp only [carrier, resolutionIntentionSources, intention]
        rw [((runtime setup).reactive_respond_application leaks (execution draw.1.1) owner _).1]
        have equalState : draw.1.2.state = (source draw.1.1).state := by
          obtain ⟨past, _memory, same⟩ := PMF.support_map .. ▸ restored
          exact (congrArg Config.state same).symm
        rw [equalState]
        exact ⟨agree draw.1.1 seedSupport, agree draw.1.1 seedSupport,
          history draw.1.1 seedSupport⟩
    | some intended =>
        rw [intention] at choiceSupport
        have completed := completion draw.1.1 seedSupport draw.1.2 restored intended
          (selected draw.1.1 draw.1.2 intended choiceSupport)
        obtain ⟨_chosen, entry, _member, message, _action, _identity, _call, endpoints⟩ := completed
        simp only [boundary, afterRecorded draw drawn, intention, Option.isSome_some,
          ↓reduceIte] at finalSupport
        dsimp only [responded] at finalSupport
        rw [intention] at finalSupport
        obtain ⟨_retained, _accepted, _noMiss, _native, effectiveStore, originalStore,
          decoded⟩ := endpoints final finalSupport
        simp only [carrier, resolutionIntentionSources, intention]
        exact ⟨effectiveStore, originalStore, decoded⟩

end Vegas
