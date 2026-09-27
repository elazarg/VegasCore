/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTimedCheckpoint
import Vegas.Game.SourceServiceTimedSample
import Vegas.Game.SourceServiceBoundary
import Vegas.Game.SourceServicePrefixSupport
import Vegas.Game.RevealServiceRosterEvaluation
import Vegas.Source.ObservationRecall
import Vegas.Compile.EventGraphParameterReadout
import Vegas.Game.SourcePrefixKernel
import Vegas.Game.SourceServiceTimedAdmissibility

/-! # Joint source-state and traffic laws of service prefixes

The factorization uses the existing source protocol observation and the actual
native execution. Original failed disclosure intentions are restored by the
source assessment comparison; they are not inferred from the effective state
read by the native decoder.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering
open GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The actual initialized joint law factors through the original source
observation, without independence assumptions on the supplied private types.
The protocol observation explicitly recovers the typed entry view. -/
theorem sourceService_initial_prefix_factorization
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (focal : Player) :
    ∃ noise : setup.ProtocolView focal → FinDist _,
      ((initialLaw setup).map
        (ReactiveApplication.Execution.initial (application setup leaks))).map
          (fun execution =>
            (sourceServicePrefix? setup 0 execution.application.config,
              (runtime setup).bindingTraffic leaks focal execution)) =
      (setup.initialLaw.map fun initial =>
        some (ProtocolState.entry setup.program (setup.initialConfig initial))).bind fun state =>
          (noise (setup.protocolObserve focal state)).map fun extra => (state, extra) := by
  obtain ⟨sourceNoise, initialFactor⟩ := source_initial_memory_factorization setup leaks focal
  let execution := fun initial : State L setup.context =>
    ReactiveApplication.Execution.initial (application setup leaks)
      (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial))
  let traffic := fun initial => (runtime setup).bindingTraffic leaks focal (execution initial)
  have sourceFactor : setup.initialLaw.map (fun initial =>
      (setup.initialConfig initial, traffic initial)) =
      (setup.initialLaw.map setup.initialConfig).bind fun source =>
        (sourceNoise (source.view focal)).map fun extra => (source, extra) := by
    have projected := congrArg (FinDist.map fun pair => (pair.1.1, pair.2)) initialFactor
    simpa only [FinDist.map_comp, FinDist.map_bind, FinDist.bind_map, Function.comp_def,
      execution, traffic] using projected
  obtain ⟨noise, factor⟩ := ProtocolView.entry_noise_factor setup.program focal setup.initialLaw
    setup.initialConfig traffic sourceNoise sourceFactor
  refine ⟨noise, ?_⟩
  dsimp only at factor
  rw [FinDist.map_comp] at factor
  have native : (((initialLaw setup).map
      (ReactiveApplication.Execution.initial (application setup leaks))).map fun state =>
        (sourceServicePrefix? setup 0 state.application.config,
          (runtime setup).bindingTraffic leaks focal state)) =
      setup.initialLaw.map (fun initial =>
        (some (ProtocolState.entry setup.program (setup.initialConfig initial)),
          traffic initial)) := by
    simp only [initialLaw, FinDist.map_comp, Function.comp_def]
    apply FinDist.map_congr_of_eq_on_support
    intro initial _
    exact Prod.ext (sourceServicePrefix?_initial setup initial) rfl
  rw [native]
  exact factor

/-- The guarded-disclosure constructor of the joint prefix induction. Its
auxiliary kernel is derived from the actual timed service phase, including
the protected inclusion, deadline and retained native memories. The only
factorization premise is the preceding prefix's induction hypothesis. -/
theorem sourceService_reveal_prefix_factorization
    {Seed : Type} (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (prior : FinDist Seed) (initial : Seed → State L setup.context)
    (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (aligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile
      (.reveal published owner name fresh binding unresolved next) profile
      refs (source seed).revelations (source seed).registry embedding refsBefore rank)
    (boundary : ∀ seed ∈ prior.support,
      ServiceBoundary setup leaks rosters (initial seed) (source seed) refs rank (execution seed))
    (origins : ∀ seed ∈ prior.support,
      (runtime setup).ResolutionEvidenceOrigins leaks (execution seed))
    (effective : ∀ seed ∈ prior.support, (profile owner).EffectiveDisclosures
      (.reveal published owner name fresh binding unresolved next)
        (source seed).registry (source seed).revelations)
    (network : (runtime setup).NetworkPolicy leaks) (focal : Player)
    (noise : DecisionView focal Γ → FinDist _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view focal)).map fun extra => (config, extra)) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    (∀ seed ∈ prior.support, (execution seed).application.serviceGrant = some event) →
    ∃ nextNoise : Option
        (ProtocolView focal (.reveal published owner name fresh binding unresolved next)) →
          FinDist _,
      let law := prior.bind fun seed =>
        ((runtime setup).runInteractionPlan leaks
          (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
          ((rosters event).map ServiceInstruction.player ++
            (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++ [.expire event]))
          (execution seed)).map fun final =>
            (decodeSourcePrefix? (.reveal published owner name fresh binding unresolved next)
              refs (source seed).registry (source seed).revelations embedding.ref 1
              final.application.config.store (decodeHistory setup.program
                (final.application.config.history.map
                  (setup.eventGraph.fromModeCompletion .sequential))),
              (runtime setup).bindingTraffic leaks focal final)
      (law = (law.map Prod.fst).bind fun state =>
        (nextNoise (state.map (ProtocolState.observe focal
          (.reveal published owner name fresh binding unresolved next)))).map fun extra =>
            (state, extra)) ∧
      law.map Prod.fst = (prior.map source).bind fun config =>
        (revealKernel profile (config.view owner)).map fun disclose =>
          some (Sum.inr (ProtocolState.entry next
            (revealSuccessor published binding config disclose))) := by
  intro index event granted
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using
      (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using
      (aligned prior.support_nonempty.choose).actorEq index
  have outputEq : (graph setup).outputLayout event = .publication payload := by
    change outputLayout setup.program (embedding.event index) = _
    simpa [index, outputLayout, eventCount] using embedding.layout_eq index
  have codeEq (seed : Seed) :
      cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
          (compileChecks (published := published) refs (source seed).registry
            (source seed).revelations binding) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using (aligned seed).graphSuffix.nodeEq index
  have node (seed : Seed) : nodeView (graph setup) event =
      .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs (source seed).registry
          (source seed).revelations binding) outputEq (codeEq seed) := by
    cases viewed : nodeView (graph setup) event with
    | sample otherPayload law kind code => cases kind.symm.trans outputEq
    | bind other otherPayload kind code => cases kind.symm.trans outputEq
    | resolve other otherPayload otherBinding otherChecks kind code =>
        have samePayload := EventGraph.EventField.publication.inj (kind.symm.trans outputEq)
        subst otherPayload
        cases code.symm.trans (codeEq seed)
        rfl
  let choice := fun config : Config Player L Γ => revealKernel profile (config.view owner)
  let advance := revealSuccessor published binding
  let transcript := fun seed disclose => guardedDisclosureTranscript setup leaks network
    (rosters event) owner focal event (event.val + 1) (timing event owner owned)
      (execution seed) disclose
  let joint := prior.bind fun seed => (choice (source seed)).bind fun disclose =>
    (transcript seed disclose).map fun traffic => (advance (source seed) disclose, traffic)
  obtain ⟨nextNoise, nextFactor⟩ := guarded_disclosure_successor_factorization setup leaks
    published binding refs event outputEq prior source execution
    (fun seed supported => (boundary seed supported).agrees)
    (fun seed supported => (boundary seed supported).binding) codeEq node
    (fun seed supported => (boundary seed supported).ready event eventRank)
    (fun seed supported => (boundary seed supported).timely event eventRank
      (by simp only [owned, Option.isSome_some]))
    (fun seed supported => (boundary seed supported).recall)
    (fun seed supported => (boundary seed supported).serials)
    (fun seed supported => (boundary seed supported).published)
    (rosterOffset setup rosters owner event)
    (fun seed supported => (boundary seed supported).response_offset event eventRank owner)
    network (rosters event) focal (event.val + 1) (timing event owner owned) noise factor choice
    (fun seed supported disclose selected => effective_reveal_supported fresh binding unresolved
      next profile (source seed) (effective seed supported) disclose selected)
  have marginal : joint.map Prod.fst =
      (prior.map source).bind fun config => (choice config).map (advance config) := by
    simp only [joint, FinDist.map_bind, FinDist.map_comp, Function.comp_def,
      FinDist.map_const, ← FinDist.map_eq_bind, FinDist.bind_map]
  have jointFactor : joint = (joint.map Prod.fst).bind fun config =>
      (nextNoise (config.view focal)).map fun traffic => (config, traffic) := by
    rw [marginal]
    exact nextFactor
  let embed : Config Player L ((published, .publication payload) :: Γ) →
      Option (ProtocolState (.reveal published owner name fresh binding unresolved next)) :=
    fun config => some (Sum.inr (ProtocolState.entry next config))
  let recover := fun view : Option
      (ProtocolView focal (.reveal published owner name fresh binding unresolved next)) =>
    (view.bind (Sum.elim (fun _ => none) some)).elim
      ((advance (source prior.support_nonempty.choose) false).view focal)
      (ProtocolView.entryView focal next)
  have recovered (config : Config Player L ((published, .publication payload) :: Γ)) :
      recover ((embed config).map (ProtocolState.observe focal
        (.reveal published owner name fresh binding unresolved next))) = config.view focal := by
    exact ProtocolView.entryView_observe_entry focal next config
  have lifted := FinDist.map_observation_factor joint (fun config => config.view focal)
    nextNoise jointFactor embed (Option.map (ProtocolState.observe focal
      (.reveal published owner name fresh binding unresolved next))) recover recovered
  refine ⟨fun view => nextNoise (recover view), ?_⟩
  dsimp only
  have lawEq : (prior.bind fun seed =>
      ((runtime setup).runInteractionPlan leaks
        (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
        ((rosters event).map ServiceInstruction.player ++
          (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++ [.expire event]))
        (execution seed)).map fun final =>
          (decodeSourcePrefix? (.reveal published owner name fresh binding unresolved next)
            refs (source seed).registry (source seed).revelations embedding.ref 1
            final.application.config.store (decodeHistory setup.program
              (final.application.config.history.map
                (setup.eventGraph.fromModeCompletion .sequential))),
            (runtime setup).bindingTraffic leaks focal final)) =
      joint.map (fun pair => (embed pair.1, pair.2)) := by
    rw [FinDist.map_bind]
    apply FinDist.bind_congr
    intro seed supported
    have ready := (boundary seed supported).ready event eventRank
    obtain ⟨entered, activated⟩ := Option.isSome_iff_exists.mp
      (((boundary seed supported).invariant.activated_iff event).mpr
        ⟨ready, by simp only [owned, Option.isSome_some]⟩)
    have due : (runtime setup).deadline event ≤
        (execution seed).application.clock + (event.val + 1) - entered := by
      have earlier := (boundary seed supported).invariant.activated_le event entered activated
      change event.val + 1 ≤ (execution seed).application.clock + (event.val + 1) - entered
      omega
    have exactLaw := sourceServiceTimedPolicy_reveal_joint_law setup leaks rosters timing
      fresh binding unresolved next wholeProfile profile refs (source seed) embedding refsBefore
      rank (aligned seed) (execution seed) (boundary seed supported).toSourceCheckpoint
      (boundary seed supported).binding (boundary seed supported).recall (origins seed supported)
      (effective seed supported) (boundary seed supported).published
      (boundary seed supported).serials network entered (event.val + 1) focal owned
      (granted seed supported) ready ((boundary seed supported).timely event eventRank
        (by simp only [owned, Option.isSome_some])) activated due
      ((boundary seed supported).unsent owner event (Nat.le_of_eq eventRank.symm))
      ((boundary seed supported).response_offset event eventRank owner)
    simpa only [FinDist.map_bind, FinDist.map_comp, Function.comp_def,
      choice, transcript, advance, embed] using exactLaw
  rw [lawEq]
  refine ⟨lifted, ?_⟩
  rw [FinDist.map_comp]
  change joint.map (embed ∘ Prod.fst) = _
  rw [← FinDist.map_comp, marginal, FinDist.map_bind]
  simp only [FinDist.map_comp, choice, advance, embed, Function.comp_def]

/-- The binding constructor preserves the actual joint prefix factor. The
new private value is drawn by the source kernel, while shared timing and all
passive communication remain in the derived auxiliary law. -/
theorem sourceService_binding_prefix_factorization [Finite Player]
    {Seed : Type} (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name openNames))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (prior : FinDist Seed) (initial : Seed → State L setup.context)
    (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (aligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile
      (.commit name owner fresh guard next) profile refs (source seed).revelations
        (source seed).registry embedding refsBefore rank)
    (boundary : ∀ seed ∈ prior.support,
      ServiceBoundary setup leaks rosters (initial seed) (source seed) refs rank (execution seed))
    (network : (runtime setup).NetworkPolicy leaks) (focal : Player)
    (noise : DecisionView focal Γ → FinDist _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view focal)).map fun extra => (config, extra)) :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    (∀ seed ∈ prior.support, (execution seed).application.serviceGrant = some event) →
    ∃ nextNoise : Option (ProtocolView focal (.commit name owner fresh guard next)) → FinDist _,
      let law := prior.bind fun seed =>
        ((runtime setup).runInteractionPlan leaks
          (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
          ((rosters event).map ServiceInstruction.player ++
            (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++ [.expire event]))
          (execution seed)).map fun final =>
            (decodeSourcePrefix? (.commit name owner fresh guard next) refs
              (source seed).registry (source seed).revelations embedding.ref 1
              final.application.config.store (decodeHistory setup.program
                (final.application.config.history.map
                  (setup.eventGraph.fromModeCompletion .sequential))),
              (runtime setup).bindingTraffic leaks focal final)
      (law = (law.map Prod.fst).bind fun state =>
        (nextNoise (state.map (ProtocolState.observe focal
          (.commit name owner fresh guard next)))).map fun extra => (state, extra)) ∧
      law.map Prod.fst = (prior.map source).bind fun config =>
        (commitKernel profile (config.view owner)).map fun choice =>
          some (Sum.inr (ProtocolState.entry next (commitSuccessor name guard config choice))) := by
  intro index event granted
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using
      (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using
      (aligned prior.support_nonempty.choose).actorEq index
  let choice := fun config : Config Player L Γ => commitKernel profile (config.view owner)
  let advance := commitSuccessor name guard
  let transcript := fun seed result => bindingPhaseTranscript setup leaks network (rosters event)
    owner focal event payload (rosterOffset setup rosters owner event) (event.val + 1)
      ((timing event owner owned).map some) (execution seed) result
  have diagonal : prior.map (fun seed => ((source seed, source seed),
      (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, source seed))).bind fun pair =>
        (noise (pair.1.view focal)).map fun traffic => (pair, traffic) := by
    have mapped := congrArg (FinDist.map fun pair => ((pair.1, pair.1), pair.2)) factor
    simpa only [FinDist.map_comp, FinDist.map_bind, FinDist.bind_map, Function.comp_def]
      using mapped
  obtain ⟨nextNoise, nextFactor⟩ := binding_successor_memory_factorization setup leaks network
    (rosters event) name guard focal event prior source source execution
    (fun seed supported => (boundary seed supported).recall)
    (fun seed supported => (boundary seed supported).published)
    (rosterOffset setup rosters owner event) (event.val + 1)
    (fun seed supported => (boundary seed supported).response_offset event eventRank owner)
    ((timing event owner owned).map some) noise diagonal choice
  let joint := prior.bind fun seed => (choice (source seed)).bind fun result =>
    (transcript seed result).map fun traffic => (advance (source seed) result, traffic)
  have marginal : joint.map Prod.fst =
      (prior.map source).bind fun config => (choice config).map (advance config) := by
    simp only [joint, FinDist.map_bind, FinDist.map_comp, Function.comp_def,
      FinDist.map_const, ← FinDist.map_eq_bind, FinDist.bind_map]
  have jointFactor : joint = (joint.map Prod.fst).bind fun config =>
      (nextNoise (config.view focal)).map fun traffic => (config, traffic) := by
    rw [marginal]
    have projected := congrArg (FinDist.map fun pair => (pair.1.1, pair.2)) nextFactor
    simpa only [joint, transcript, advance, FinDist.map_bind, FinDist.map_comp,
      FinDist.bind_bind, FinDist.bind_map, Function.comp_def] using projected
  let embed : Config Player L ((name, .commitment owner payload) :: Γ) →
      Option (ProtocolState (.commit name owner fresh guard next)) :=
    fun config => some (Sum.inr (ProtocolState.entry next config))
  let recover := fun view : Option (ProtocolView focal (.commit name owner fresh guard next)) =>
    (view.bind (Sum.elim (fun _ => none) some)).elim
      ((advance (source prior.support_nonempty.choose) .failure).view focal)
      (ProtocolView.entryView focal next)
  have recovered (config : Config Player L ((name, .commitment owner payload) :: Γ)) :
      recover ((embed config).map (ProtocolState.observe focal
        (.commit name owner fresh guard next))) = config.view focal := by
    exact ProtocolView.entryView_observe_entry focal next config
  have lifted := FinDist.map_observation_factor joint (fun config => config.view focal)
    nextNoise jointFactor embed (Option.map (ProtocolState.observe focal
      (.commit name owner fresh guard next))) recover recovered
  refine ⟨fun view => nextNoise (recover view), ?_⟩
  dsimp only
  have lawEq : (prior.bind fun seed =>
      ((runtime setup).runInteractionPlan leaks
        (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
        ((rosters event).map ServiceInstruction.player ++
          (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++ [.expire event]))
        (execution seed)).map fun final =>
          (decodeSourcePrefix? (.commit name owner fresh guard next) refs
            (source seed).registry (source seed).revelations embedding.ref 1
            final.application.config.store (decodeHistory setup.program
              (final.application.config.history.map
                (setup.eventGraph.fromModeCompletion .sequential))),
            (runtime setup).bindingTraffic leaks focal final)) =
      joint.map (fun pair => (embed pair.1, pair.2)) := by
    rw [FinDist.map_bind]
    apply FinDist.bind_congr
    intro seed supported
    have exactLaw := sourceServiceTimedPolicy_binding_joint_law setup leaks bounds rosters timing
      fresh guard next wholeProfile profile refs (source seed) embedding refsBefore rank
      (aligned seed) (initial seed) (execution seed) (boundary seed supported) network
      (event.val + 1) focal owned (granted seed supported)
    simpa only [FinDist.map_bind, FinDist.map_comp, Function.comp_def,
      choice, transcript, advance, embed] using exactLaw
  rw [lawEq]
  refine ⟨lifted, ?_⟩
  rw [FinDist.map_comp]
  change joint.map (embed ∘ Prod.fst) = _
  rw [← FinDist.map_comp, marginal, FinDist.map_bind]
  simp only [FinDist.map_comp, choice, advance, embed, Function.comp_def]

/-- Public chance retains the actual replay-window and maintenance traffic.
Its conditional auxiliary law is derived from the sampled public value. -/
theorem sourceService_sample_prefix_factorization
    {Seed : Type} (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    {Γ : SourceCtx Player L} {openNames : Finset VarId} {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (distribution : L.DistExpr (SourcePublicCtx L Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: Γ) openNames)
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.sample name fresh distribution next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.sample name fresh distribution next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (prior : FinDist Seed) (initial : Seed → State L setup.context)
    (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (aligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile
      (.sample name fresh distribution next) profile refs (source seed).revelations
        (source seed).registry embedding refsBefore rank)
    (boundary : ∀ seed, ServiceBoundary setup leaks rosters (initial seed)
      (source seed) refs rank (execution seed))
    (network : (runtime setup).NetworkPolicy leaks) (focal : Player)
    (noise : DecisionView focal Γ → FinDist _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view focal)).map fun extra => (config, extra)) :
    let index : Fin (eventCount (.sample name fresh distribution next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    (∀ seed, (execution seed).application.serviceGrant = some event) →
    ∃ nextNoise : Option (ProtocolView focal (.sample name fresh distribution next)) → FinDist _,
      let law := prior.bind fun seed =>
        ((runtime setup).runInteractionPlan leaks
          (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
          ((rosters event).map ServiceInstruction.player ++
            (.sample event :: List.replicate (event.val + 1) .tick ++ [.expire event]))
          (execution seed)).map fun final =>
            (decodeSourcePrefix? (.sample name fresh distribution next) refs
              (source seed).registry (source seed).revelations embedding.ref 1
                final.application.config.store (decodeHistory setup.program
                  (final.application.config.history.map
                    (setup.eventGraph.fromModeCompletion .sequential))),
              (runtime setup).bindingTraffic leaks focal final)
      (law = (law.map Prod.fst).bind fun state =>
        (nextNoise (state.map (ProtocolState.observe focal
          (.sample name fresh distribution next)))).map fun extra => (state, extra)) ∧
      law.map Prod.fst = (prior.map source).bind fun config =>
        (L.evalDist distribution (sourcePublicEnv config.state)).map fun value =>
          some (Sum.inr (ProtocolState.entry next (sampleSuccessor name config value))) := by
  intro index event granted
  have eventRank : event.val = rank := by
    simpa only [event, index, Nat.add_zero] using
      (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
  have outputEq : (graph setup).outputLayout event = .publicData payload := by
    change outputLayout setup.program (embedding.event index) = _
    simpa [index, outputLayout, eventCount] using embedding.layout_eq index
  let choice := fun config : Config Player L Γ =>
    L.evalDist distribution (sourcePublicEnv config.state)
  let advance := sampleSuccessor (Player := Player) (L := L) (Γ := Γ) (payload := payload) name
  let transcript := fun seed value => samplePhaseTranscript setup leaks network (rosters event)
    (event.val + 1) focal (execution seed) event ((boundary seed).ready event eventRank)
      payload outputEq value
  have diagonal : prior.map (fun seed => ((source seed, source seed),
      (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, source seed))).bind fun pair =>
        (noise (pair.1.view focal)).map fun traffic => (pair, traffic) := by
    have mapped := congrArg (FinDist.map fun pair => ((pair.1, pair.1), pair.2)) factor
    simpa only [FinDist.map_comp, FinDist.map_bind, FinDist.bind_map, Function.comp_def]
      using mapped
  obtain ⟨nextNoise, nextFactor⟩ := sample_successor_memory_factorization setup leaks name
    focal event outputEq prior source source execution
    (fun seed => (boundary seed).ready event eventRank)
    (fun seed _ => (boundary seed).recall) network (rosters event) (event.val + 1)
    distribution noise diagonal
  let joint := prior.bind fun seed => (choice (source seed)).bind fun value =>
    (transcript seed value).map fun traffic => (advance (source seed) value, traffic)
  have marginal : joint.map Prod.fst =
      (prior.map source).bind fun config => (choice config).map (advance config) := by
    simp only [joint, FinDist.map_bind, FinDist.map_comp, Function.comp_def,
      FinDist.map_const, ← FinDist.map_eq_bind, FinDist.bind_map]
  have jointFactor : joint = (joint.map Prod.fst).bind fun config =>
      (nextNoise (config.view focal)).map fun traffic => (config, traffic) := by
    rw [marginal]
    have projected := congrArg (FinDist.map fun pair => (pair.1.1, pair.2)) nextFactor
    simpa only [joint, transcript, advance, FinDist.map_bind, FinDist.map_comp,
      FinDist.bind_bind, FinDist.bind_map, Function.comp_def] using projected
  let embed : Config Player L ((name, .publicData payload) :: Γ) →
      Option (ProtocolState (.sample name fresh distribution next)) :=
    fun config => some (Sum.inr (ProtocolState.entry next config))
  let recover := fun view : Option (ProtocolView focal (.sample name fresh distribution next)) =>
    (view.bind (Sum.elim (fun _ => none) some)).elim
      ((advance (source prior.support_nonempty.choose)
        (choice (source prior.support_nonempty.choose)).support_nonempty.choose).view focal)
      (ProtocolView.entryView focal next)
  have recovered (config : Config Player L ((name, .publicData payload) :: Γ)) :
      recover ((embed config).map (ProtocolState.observe focal
        (.sample name fresh distribution next))) = config.view focal :=
    ProtocolView.entryView_observe_entry focal next config
  have lifted := FinDist.map_observation_factor joint (fun config => config.view focal)
    nextNoise jointFactor embed (Option.map (ProtocolState.observe focal
      (.sample name fresh distribution next))) recover recovered
  refine ⟨fun view => nextNoise (recover view), ?_⟩
  dsimp only
  have lawEq : (prior.bind fun seed =>
      ((runtime setup).runInteractionPlan leaks
        (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
        ((rosters event).map ServiceInstruction.player ++
          (.sample event :: List.replicate (event.val + 1) .tick ++ [.expire event]))
        (execution seed)).map fun final =>
          (decodeSourcePrefix? (.sample name fresh distribution next) refs
            (source seed).registry (source seed).revelations embedding.ref 1
              final.application.config.store (decodeHistory setup.program
                (final.application.config.history.map
                  (setup.eventGraph.fromModeCompletion .sequential))),
            (runtime setup).bindingTraffic leaks focal final)) =
      joint.map (fun pair => (embed pair.1, pair.2)) := by
    rw [FinDist.map_bind]
    apply FinDist.bind_congr
    intro seed _
    rw [sourceServiceTimedPolicy_sample_joint_law setup leaks rosters timing fresh distribution
      next wholeProfile profile refs (source seed) embedding refsBefore rank (aligned seed)
      (execution seed) (boundary seed).toSourceCheckpoint network (event.val + 1) focal
      (granted seed) ((boundary seed).ready event eventRank)]
    rw [FinDist.bind_comm]
    simp only [transcript, samplePhaseTranscript, FinDist.map_bind, FinDist.map_comp,
      Function.comp_def, choice, advance, embed]
    rfl
  rw [lawEq]
  refine ⟨lifted, ?_⟩
  rw [FinDist.map_comp]
  change joint.map (embed ∘ Prod.fst) = _
  rw [← FinDist.map_comp, marginal, FinDist.map_bind]
  simp only [FinDist.map_comp, choice, advance, embed, Function.comp_def]

/-- A supported physical prefix supplies all operational induction facts for
its exact typed source checkpoint. The retained trace and certificate origins
are derived from admissibility; they are not assumptions about an auxiliary
channel or about the compiler's equilibrium path. -/
theorem sourceService_prefix_boundary_of_checkpoint [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ∀ event owner payload,
      (graph setup).outputLayout event = .binding owner payload → owner ∈ rosters event)
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who, (sourceServiceMenu setup leaks bounds rosters).Admissible
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who (players who))
    (rank : Nat) (within : rank ≤ eventCount setup.program)
    (execution : (application setup leaks).Execution)
    (supported : execution ∈ ((initialLaw setup).bind fun initial =>
      (runtime setup).runInteractionPlan leaks players network (rosterPlanPrefix setup rosters rank)
        (ReactiveApplication.Execution.initial (application setup leaks) initial)).support)
    {Γ : SourceCtx Player L} (source : Config Player L Γ)
    (refs : ContextRefs (graph setup).layout Γ)
    (checkpoint : SourceCheckpoint setup source refs rank execution.application.config) :
    (∃ initial ∈ setup.initialLaw.support,
      ServiceBoundary setup leaks rosters initial source refs rank execution) ∧
    (runtime setup).ResolutionEvidenceOrigins leaks execution := by
  let menu := sourceServiceMenu setup leaks bounds rosters
  have uniform := roster_restrict_prefix_support setup leaks rosters network menu players
    covered rank execution supported
  obtain ⟨initial, selected, _state, _related, _decoded, _ctx, _names, _program, _profile,
    _source, _refs, _embedding, _before, _aligned, _admitted, _lift, _stateEq, _stepEq,
    _decodeEq, _effective, _supports, boundary⟩ :=
    initialized_sourceService_prefix_support setup leaks bounds values capacity rosters
      opportunities menu.uniformResponses
      (fun who past view response chosen =>
        (menu.uniformResponses_support who past view response).mp chosen)
      network profile rank within execution uniform
  refine ⟨⟨initial, selected, boundary.withSourceCheckpoint checkpoint⟩, ?_⟩
  let prefixPlan := rosterPlanPrefix setup rosters rank
  have prefixFact := rosterPlanPrefix_isPrefix setup rosters rank
  have bound : prefixPlan.length ≤ (rosterPlan setup rosters).length := prefixFact.length_le
  have taken : (rosterPlan setup rosters).take prefixPlan.length = prefixPlan := by
    obtain ⟨rest, same⟩ := prefixFact
    rw [← same]
    exact List.take_left
  have law := roster_restrict_prefix_state setup leaks rosters network menu players covered
    prefixPlan.length bound
  rw [taken] at law
  have member : some ⟨(rosterPlan setup rosters).length - prefixPlan.length, none, execution⟩ ∈
      (((initialLaw setup).bind fun initial =>
        (runtime setup).runInteractionPlan leaks players network prefixPlan
          (ReactiveApplication.Execution.initial (application setup leaks) initial)).map
        (fun final => some ⟨(rosterPlan setup rosters).length - prefixPlan.length, none, final⟩) :
          FinDist (application setup leaks).ProtocolState).support :=
    FinDist.support_map .. ▸ ⟨execution, supported, rfl⟩
  rw [← law, FinDist.support_map] at member
  obtain ⟨history, _reached, stateEq⟩ := member
  have trace : (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨(rosterPlan setup rosters).length - prefixPlan.length, none, execution⟩) :=
    stateEq ▸ history.trace
  exact sourceService_resolutionEvidence setup leaks bounds rosters
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) _ trace

private def entryObservation (who : Player) {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (view : DecisionView who Γ) :
    ProtocolView who program :=
  match program with
  | .ret _ => view
  | .sample _ _ _ _ | .commit _ _ _ _ _ | .reveal _ _ _ _ _ _ _ => .inl view

private theorem observe_entry {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (who : Player) (source : Config Player L Γ) :
    ProtocolState.observe who program (ProtocolState.entry program source) =
      entryObservation who program (source.view who) := by
  cases program <;> rfl

private theorem entry_injective {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) :
    Function.Injective (ProtocolState.entry program) := by
  cases program <;> intro left right same <;> cases same <;> rfl

/-- The actual typed decoder determines the next source configuration. Its
joint law supplies both the source marginal and the preceding observation
factor; the ordered cut is supplied by actual retained-prefix support. -/
private theorem reconstruct_phase
    {Seed Encoded : Type} (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (focal : Player) {Γ : SourceCtx Player L}
    (refs : ContextRefs (graph setup).layout Γ) (rank : Nat)
    (registry : Seed → Registry Γ) (revelations : Seed → Revelations Γ)
    (joint : FinDist (Seed × (application setup leaks).Execution))
    (encoded : Config Player L Γ → Encoded) (injective : Function.Injective encoded)
    (decode : Seed → (application setup leaks).Execution → Option Encoded)
    (decodeEq : ∀ seed execution, decode seed execution =
      (decodeState? refs execution.application.config.store).map fun state =>
        encoded ⟨state, registry seed, revelations seed,
          decodeHistory setup.program (execution.application.config.history.map
            (setup.eventGraph.fromModeCompletion .sequential))⟩)
    (ordered : ∀ point ∈ joint.support, point.2.application.config.cut.IsPrefix rank)
    (marginal : FinDist (Config Player L Γ))
    (noise : DecisionView focal Γ → FinDist _)
    (factor : joint.map (fun point => (decode point.1 point.2,
        (runtime setup).bindingTraffic leaks focal point.2)) =
      marginal.bind fun source => (noise (source.view focal)).map fun extra =>
        (some (encoded source), extra)) :
    let nextPrior := joint.toSubtype (fun _ member => member)
    ∃ source : {point // point ∈ joint.support} → Config Player L Γ,
      (∀ point, SourceCheckpoint setup (source point) refs rank point.val.2.application.config) ∧
      (∀ point, (source point).registry = registry point.val.1) ∧
      (∀ point, @Config.revelations Player L Γ (source point) = @revelations point.val.1) ∧
      (∀ point, decode point.val.1 point.val.2 = some (encoded (source point))) ∧
      nextPrior.map source = marginal ∧
      nextPrior.map (fun point => (source point,
          (runtime setup).bindingTraffic leaks focal point.val.2)) =
        (nextPrior.map source).bind fun config =>
          (noise (config.view focal)).map fun extra => (config, extra) := by
  intro nextPrior
  let Point := {point // point ∈ joint.support}
  have available (point : Point) :
      ∃ state, decodeState? refs point.val.2.application.config.store = some state := by
    have member : (decode point.val.1 point.val.2,
        (runtime setup).bindingTraffic leaks focal point.val.2) ∈
        (joint.map fun point => (decode point.1 point.2,
          (runtime setup).bindingTraffic leaks focal point.2)).support :=
      FinDist.support_map .. ▸ ⟨point.val, point.property, rfl⟩
    rw [factor, FinDist.support_bind] at member
    obtain ⟨source, _, member⟩ := Set.mem_iUnion₂.mp member
    obtain ⟨extra, _, same⟩ := FinDist.support_map .. ▸ member
    have present := congrArg Prod.fst same
    rw [decodeEq] at present
    cases decoded : decodeState? refs point.val.2.application.config.store with
    | none => simp only [decoded, Option.map_none, reduceCtorEq] at present
    | some state => exact ⟨state, rfl⟩
  let source := fun point : Point =>
    (⟨(available point).choose, registry point.val.1, revelations point.val.1,
      decodeHistory setup.program (point.val.2.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential))⟩ : Config Player L Γ)
  have decoded (point : Point) : decode point.val.1 point.val.2 =
      some (encoded (source point)) := by
    rw [decodeEq, (available point).choose_spec]
    rfl
  have mapped : nextPrior.map (fun point => (some (encoded (source point)),
      (runtime setup).bindingTraffic leaks focal point.val.2)) =
      joint.map (fun point => (decode point.1 point.2,
        (runtime setup).bindingTraffic leaks focal point.2)) := by
    calc
      _ = nextPrior.map (fun point => (decode point.val.1 point.val.2,
          (runtime setup).bindingTraffic leaks focal point.val.2)) := by
        apply FinDist.map_congr_of_eq_on_support
        intro point _
        exact Prod.ext (decoded point).symm rfl
      _ = _ := FinDist.map_toSubtype joint (fun _ member => member)
        (fun point => (decode point.1 point.2,
          (runtime setup).bindingTraffic leaks focal point.2))
  have marginalEq : nextPrior.map source = marginal := by
    apply FinDist.map_injective (f := fun source => some (encoded source))
      (fun _ _ equal => injective (Option.some.inj equal))
    have projected := congrArg (FinDist.map Prod.fst) (mapped.trans factor)
    simpa only [FinDist.map_comp, FinDist.map_bind, Function.comp_def,
      FinDist.map_const, ← FinDist.map_eq_bind] using projected
  refine ⟨source, ?_, fun _ => rfl, fun _ => rfl, decoded, marginalEq, ?_⟩
  · intro point
    exact ⟨decodeState?_agrees refs point.val.2.application.config.store _
      (available point).choose_spec, rfl, ordered point.val point.property⟩
  · apply FinDist.map_injective (f := fun pair : Config Player L Γ × _ =>
        (some (encoded pair.1), pair.2)) (by
      intro left right same
      apply Prod.ext
      · exact injective (Option.some.inj (congrArg Prod.fst same))
      · exact (Prod.mk.inj same).2)
    simpa only [FinDist.map_comp, FinDist.map_bind, Function.comp_def, marginalEq]
      using mapped.trans factor

/-- Whole-prefix induction over the actual timed service. The source marginal
is the existing protocol kernel, and the auxiliary law depends only on its
actual source observation. Physical support is retained so that every new
typed checkpoint receives the all-policy operational invariants. -/
theorem sourceServiceTimedPolicy_prefix_joint_factorization [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ∀ event owner payload,
      (graph setup).outputLayout event = .binding owner payload → owner ∈ rosters event)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (network : (runtime setup).NetworkPolicy leaks)
    (wholeProfile : BehavioralProfile setup.program)
    (covered : ∀ who, (sourceServiceMenu setup leaks bounds rosters).Admissible
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who
      (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile who))
    (focal : Player) :
    ∀ count {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
      (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
      {Seed : Type} (prior : FinDist Seed) (source : Seed → Config Player L Γ)
      (execution : Seed → (application setup leaks).Execution),
      (∀ seed, CompiledPolicySuffix setup.program wholeProfile program profile refs
        (source seed).revelations (source seed).registry embedding refsBefore offset) →
      (∀ seed, SourceCheckpoint setup (source seed) refs offset
        (execution seed).application.config) →
      (∀ seed, execution seed ∈ ((initialLaw setup).bind fun initial =>
        (runtime setup).runInteractionPlan leaks
          (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
          (rosterPlanPrefix setup rosters offset)
          (ReactiveApplication.Execution.initial (application setup leaks) initial)).support) →
      (∀ seed who, (profile who).EffectiveDisclosures program (source seed).registry
        (source seed).revelations) →
      ∀ (noise : DecisionView focal Γ → FinDist _),
      prior.map (fun seed => (source seed,
          (runtime setup).bindingTraffic leaks focal (execution seed))) =
        (prior.map source).bind (fun config =>
          (noise (config.view focal)).map fun extra => (config, extra)) →
      count ≤ eventCount program →
      ∃ nextNoise : Option (ProtocolView focal program) → FinDist _,
        (prior.bind fun seed =>
          ((runtime setup).runInteractionPlan leaks
            (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
            (((List.finRange (eventCount program)).take count).flatMap fun index =>
              rosterBlock setup rosters (embedding.event index)) (execution seed)).map
                fun final =>
                  (decodeSourcePrefix? program refs (source seed).registry
                    (source seed).revelations embedding.ref count final.application.config.store
                    (decodeHistory setup.program (final.application.config.history.map
                      (setup.eventGraph.fromModeCompletion .sequential))),
                    (runtime setup).bindingTraffic leaks focal final)) =
          (prior.bind fun seed =>
            ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[count]
              (FinDist.pure (ProtocolState.entry program (source seed)))).map some).bind
                fun state => (nextNoise (state.map (ProtocolState.observe focal program))).map
                  fun extra => (state, extra) := by
  intro count
  induction count with
  | zero =>
      intro Γ names program profile refs embedding refsBefore offset Seed prior source execution
        _aligned checkpoint _supported _effective noise factor _within
      obtain ⟨nextNoise, nextFactor⟩ := ProtocolView.entry_noise_factor program focal prior source
        (fun seed => (runtime setup).bindingTraffic leaks focal (execution seed)) noise factor
      refine ⟨nextNoise, ?_⟩
      dsimp only at nextFactor
      simp only [List.take_zero, List.flatMap_nil, runInteractionPlan,
        FinDist.map_pure, (checkpoint _).decode program embedding.ref,
        Function.iterate_zero, id_eq, FinDist.map_pure, ← FinDist.map_eq_bind]
      simpa only [FinDist.map_comp, Function.comp_def] using nextFactor
  | succ count ih =>
      intro Γ names program profile refs embedding refsBefore offset Seed prior source execution
        aligned checkpoint supported effective noise factor within
      let app := application setup leaks
      let players := sourceServiceTimedPolicy setup leaks rosters timing wholeProfile
      let index : Fin (eventCount program) := ⟨0, by omega⟩
      let event : (graph setup).EventId := embedding.event index
      have eventRank : event.val = offset := by
        simpa only [event, index, Nat.add_zero] using
          (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
      have offsetBound : offset ≤ eventCount setup.program := by
        have counted := (aligned prior.support_nonempty.choose).graphSuffix.countEq
        omega
      have actualFacts (seed : Seed) := sourceService_prefix_boundary_of_checkpoint setup leaks
        bounds values capacity rosters opportunities network wholeProfile players covered
          offset offsetBound (execution seed) (supported seed) (source seed) refs (checkpoint seed)
      let initial := fun seed => (actualFacts seed).1.choose
      have boundary (seed : Seed) : ServiceBoundary setup leaks rosters (initial seed)
          (source seed) refs offset (execution seed) := (actualFacts seed).1.choose_spec.2
      let opportunity := fun seed => ((boundary seed).grant players network event).choose
      have opportunityFacts (seed : Seed) := ((boundary seed).grant players network
        event).choose_spec
      have grantLaw (seed : Seed) : (runtime setup).interactionStep leaks players network
          (.grant event) (execution seed) = FinDist.pure (opportunity seed) :=
        (opportunityFacts seed).2.2.2.2
      have grantEnvironment (seed : Seed) : (execution seed).environmentStep app
          (.application (.grant event)) = FinDist.pure (opportunity seed) := by
        have law := grantLaw seed
        simp only [interactionStep, interactionInstruction, FinDist.pure_bind] at law
        change ((execution seed).environmentStep app (.application (.grant event))).bind
          FinDist.pure = _ at law
        simpa only [FinDist.bind_pure] using law
      have grantOrigins (seed : Seed) :
          (runtime setup).ResolutionEvidenceOrigins leaks (opportunity seed) :=
        (runtime setup).resolutionEvidenceOrigins_environment leaks (execution seed)
          (opportunity seed) (boundary seed).binding (actualFacts seed).2
            (.application (.grant event)) (by rw [grantEnvironment]; simp)
      obtain ⟨grantNoise, grantFactor⟩ := source_maintenance_factorization setup leaks focal prior
        source (fun config => config.view focal) execution noise factor (.grant event)
          (fun _ impossible => by cases impossible)
      have opportunityFactor : prior.map (fun seed => (source seed,
          (runtime setup).bindingTraffic leaks focal (opportunity seed))) =
          (prior.map source).bind fun config =>
            (grantNoise (config.view focal)).map fun extra => (config, extra) := by
        change (prior.bind fun seed =>
          ((execution seed).environmentStep app (.application (.grant event))).map fun final =>
            (source seed, (runtime setup).bindingTraffic leaks focal final)) = _ at grantFactor
        simpa only [grantEnvironment, FinDist.map_pure, ← FinDist.map_eq_bind] using grantFactor
      have nextPhysical (seed : Seed) (final : app.Execution)
          (moved : final ∈ ((runtime setup).runInteractionPlan leaks players network
            (rosterBlock setup rosters event) (execution seed)).support) :
          final ∈ ((initialLaw setup).bind fun start =>
            (runtime setup).runInteractionPlan leaks players network
              (rosterPlanPrefix setup rosters (offset + 1))
              (ReactiveApplication.Execution.initial app start)).support := by
        obtain ⟨start, startSupport, prefixSupport⟩ :=
          Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported seed)
        rw [← eventRank, rosterPlanPrefix_succ]
        rw [FinDist.support_bind]
        apply Set.mem_iUnion₂.mpr
        refine ⟨start, startSupport, ?_⟩
        rw [runInteractionPlan_append]
        rw [FinDist.support_bind]
        apply Set.mem_iUnion₂.mpr
        exact ⟨execution seed, by simpa only [eventRank] using prefixSupport, moved⟩
      let advanced := prior.bind fun seed =>
        ((runtime setup).runInteractionPlan leaks players network
          (rosterBlock setup rosters event) (execution seed)).map fun final => (seed, final)
      let NextSeed := {point : Seed × app.Execution // point ∈ advanced.support}
      let nextPrior : FinDist NextSeed := advanced.toSubtype (fun _ member => member)
      let nextExecution := fun point : NextSeed => point.val.2
      have nextSupport (point : NextSeed) : point.val.1 ∈ prior.support ∧
          point.val.2 ∈ ((runtime setup).runInteractionPlan leaks players network
            (rosterBlock setup rosters event) (execution point.val.1)).support := by
        rcases point with ⟨⟨seed, final⟩, member⟩
        change seed ∈ prior.support ∧ final ∈ _
        change (seed, final) ∈ (prior.bind fun seed =>
          ((runtime setup).runInteractionPlan leaks players network
            (rosterBlock setup rosters event) (execution seed)).map fun final =>
              (seed, final)).support at member
        rw [FinDist.support_bind] at member
        obtain ⟨seed, selected, moved⟩ := Set.mem_iUnion₂.mp member
        rw [FinDist.support_map] at moved
        obtain ⟨final, moved, same⟩ := moved
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
        exact ⟨selected, moved⟩
      have nextReached (point : NextSeed) :
          nextExecution point ∈ ((initialLaw setup).bind fun start =>
            (runtime setup).runInteractionPlan leaks players network
              (rosterPlanPrefix setup rosters (offset + 1))
              (ReactiveApplication.Execution.initial app start)).support :=
        nextPhysical point.val.1 point.val.2 (nextSupport point).2
      have nextOrdered (point : Seed × app.Execution) (member : point ∈ advanced.support) :
          point.2.application.config.cut.IsPrefix (offset + 1) := by
        have uniform := roster_restrict_prefix_support setup leaks rosters network
          (sourceServiceMenu setup leaks bounds rosters) players covered (offset + 1) point.2
            (nextReached ⟨point, member⟩)
        obtain ⟨_start, _selected, _state, _related, _decoded, _ctx, _names, _program, _profile,
          _source, _refs, _embedding, _before, _aligned, _admitted, _lift, _stateEq, _stepEq,
          _decodeEq, _effective, _supports, result⟩ :=
          initialized_sourceService_prefix_support setup leaks bounds values capacity rosters
            opportunities (sourceServiceMenu setup leaks bounds rosters).uniformResponses
            (fun who past view response chosen =>
              ((sourceServiceMenu setup leaks bounds rosters).uniformResponses_support
                who past view response).mp chosen)
            network wholeProfile (offset + 1) (by
              have strict : event.val < eventCount setup.program := event.isLt
              omega) point.2 uniform
        exact result.ordered
      have finishStep {Δ : SourceCtx Player L} {tailNames : Finset VarId}
          (tail : SourceProgram Player L Δ tailNames) (tailProfile : BehavioralProfile tail)
          (tailRefs : ContextRefs (graphLayout setup.program) Δ)
          (tailEmbedding : OutputEmbedding (inputLayout setup.context)
            (outputLayout setup.program) tail)
          (tailBefore : ContextRefsBefore tailRefs tailEmbedding)
          (nextSource : NextSeed → Config Player L Δ)
          (nextAligned : ∀ point, CompiledPolicySuffix setup.program wholeProfile tail tailProfile
            tailRefs (nextSource point).revelations (nextSource point).registry
              tailEmbedding tailBefore (offset + 1))
          (nextCheckpoint : ∀ point, SourceCheckpoint setup (nextSource point) tailRefs
            (offset + 1) (nextExecution point).application.config)
          (nextEffective : ∀ point who, (tailProfile who).EffectiveDisclosures tail
            (nextSource point).registry (nextSource point).revelations)
          (nextNoise : DecisionView focal Δ → FinDist _)
          (nextFactor : nextPrior.map (fun point => (nextSource point,
              (runtime setup).bindingTraffic leaks focal (nextExecution point))) =
            (nextPrior.map nextSource).bind fun config =>
              (nextNoise (config.view focal)).map fun extra => (config, extra))
          (stepSource : Config Player L Γ → FinDist (Config Player L Δ))
          (nextMarginal : nextPrior.map nextSource = (prior.map source).bind stepSource)
          (lift : ProtocolState tail → ProtocolState program)
          (recover : Option (ProtocolView focal program) → Option (ProtocolView focal tail))
          (recovers : ∀ state : Option (ProtocolState tail),
            recover ((state.map lift).map (ProtocolState.observe focal program)) =
              state.map (ProtocolState.observe focal tail))
          (decodeLater : ∀ point : NextSeed, ∀ final : app.Execution,
            decodeSourcePrefix? program refs (source point.val.1).registry
              (source point.val.1).revelations embedding.ref (count + 1)
                final.application.config.store (decodeHistory setup.program
                  (final.application.config.history.map
                    (setup.eventGraph.fromModeCompletion .sequential))) =
            (decodeSourcePrefix? tail tailRefs (nextSource point).registry
              (nextSource point).revelations tailEmbedding.ref count
                final.application.config.store (decodeHistory setup.program
                  (final.application.config.history.map
                    (setup.eventGraph.fromModeCompletion .sequential)))).map lift)
          (kernel : ∀ config,
            ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[count + 1]
              (FinDist.pure (ProtocolState.entry program config))) =
            ((stepSource config).bind fun next =>
              ((fun law => law.bind (ProtocolState.behavioralStateStep tail tailProfile))^[count]
                (FinDist.pure (ProtocolState.entry tail next)))).map lift)
          (planEq : (((List.finRange (eventCount program)).take (count + 1)).flatMap
            fun index => rosterBlock setup rosters (embedding.event index)) =
            rosterBlock setup rosters event ++
              (((List.finRange (eventCount tail)).take count).flatMap fun index =>
                rosterBlock setup rosters (tailEmbedding.event index)))
          (withinTail : count ≤ eventCount tail) :
          ∃ nextNoise : Option (ProtocolView focal program) → FinDist _,
            (prior.bind fun seed =>
              ((runtime setup).runInteractionPlan leaks players network
                (((List.finRange (eventCount program)).take (count + 1)).flatMap fun index =>
                  rosterBlock setup rosters (embedding.event index)) (execution seed)).map
                    fun final =>
                      (decodeSourcePrefix? program refs (source seed).registry
                        (source seed).revelations embedding.ref (count + 1)
                          final.application.config.store (decodeHistory setup.program
                            (final.application.config.history.map
                              (setup.eventGraph.fromModeCompletion .sequential))),
                        (runtime setup).bindingTraffic leaks focal final)) =
              (prior.bind fun seed =>
                ((fun law => law.bind (ProtocolState.behavioralStateStep program
                  profile))^[count + 1]
                  (FinDist.pure (ProtocolState.entry program (source seed)))).map some).bind
                    fun state => (nextNoise (state.map (ProtocolState.observe focal program))).map
                      fun extra => (state, extra) := by
        obtain ⟨tailNoise, tailLaw⟩ := ih tail tailProfile tailRefs tailEmbedding tailBefore
          (offset + 1) nextPrior nextSource nextExecution nextAligned nextCheckpoint nextReached
          nextEffective nextNoise nextFactor withinTail
        let remainingPlan := ((List.finRange (eventCount tail)).take count).flatMap fun index =>
          rosterBlock setup rosters (tailEmbedding.event index)
        let tailJoint := nextPrior.bind fun point =>
          ((runtime setup).runInteractionPlan leaks players network remainingPlan
            (nextExecution point)).map fun final =>
              (decodeSourcePrefix? tail tailRefs (nextSource point).registry
                (nextSource point).revelations tailEmbedding.ref count
                  final.application.config.store
                  (decodeHistory setup.program (final.application.config.history.map
                    (setup.eventGraph.fromModeCompletion .sequential))),
                (runtime setup).bindingTraffic leaks focal final)
        let tailSource := nextPrior.bind fun point =>
          ((fun law => law.bind (ProtocolState.behavioralStateStep tail tailProfile))^[count]
            (FinDist.pure (ProtocolState.entry tail (nextSource point)))).map some
        have tailMarginal : tailJoint.map Prod.fst = tailSource := by
          have projected := congrArg (FinDist.map Prod.fst) tailLaw
          simp only [FinDist.map_bind, FinDist.map_comp, Function.comp_def,
            FinDist.map_const, FinDist.bind_pure] at projected
          simpa only [tailJoint, tailSource, FinDist.map_bind, FinDist.map_comp,
            Function.comp_def] using projected
        have tailFactor : tailJoint = (tailJoint.map Prod.fst).bind fun state =>
            (tailNoise (state.map (ProtocolState.observe focal tail))).map fun extra =>
              (state, extra) := by
          rw [tailMarginal]
          exact tailLaw
        have lifted := FinDist.map_observation_factor tailJoint
          (Option.map (ProtocolState.observe focal tail)) tailNoise tailFactor
          (Option.map lift) (Option.map (ProtocolState.observe focal program)) recover recovers
        refine ⟨fun view => tailNoise (recover view), ?_⟩
        have nativeEq : (prior.bind fun seed =>
            ((runtime setup).runInteractionPlan leaks players network
              (((List.finRange (eventCount program)).take (count + 1)).flatMap fun index =>
                rosterBlock setup rosters (embedding.event index)) (execution seed)).map
                  fun final =>
                    (decodeSourcePrefix? program refs (source seed).registry
                      (source seed).revelations embedding.ref (count + 1)
                        final.application.config.store (decodeHistory setup.program
                          (final.application.config.history.map
                            (setup.eventGraph.fromModeCompletion .sequential))),
                      (runtime setup).bindingTraffic leaks focal final)) =
            tailJoint.map (fun pair => (pair.1.map lift, pair.2)) := by
          rw [planEq]
          let continuePoint := fun point : Seed × app.Execution =>
            ((runtime setup).runInteractionPlan leaks players network remainingPlan point.2).map
              fun final =>
                (decodeSourcePrefix? program refs (source point.1).registry
                  (source point.1).revelations embedding.ref (count + 1)
                    final.application.config.store (decodeHistory setup.program
                      (final.application.config.history.map
                        (setup.eventGraph.fromModeCompletion .sequential))),
                  (runtime setup).bindingTraffic leaks focal final)
          calc
            _ = advanced.bind continuePoint := by
              simp only [advanced, continuePoint, FinDist.bind_bind, FinDist.bind_map,
                runInteractionPlan_append, FinDist.map_bind, remainingPlan]
            _ = nextPrior.bind (fun point => continuePoint point.val) := by
              rw [← FinDist.bind_map Subtype.val nextPrior continuePoint,
                FinDist.map_val_toSubtype]
            _ = _ := by
              simp only [tailJoint, FinDist.map_bind, FinDist.map_comp, Function.comp_def]
              apply FinDist.bind_congr
              intro point _
              apply FinDist.map_congr_of_eq_on_support
              intro final _
              exact Prod.ext (decodeLater point final) rfl
        have sourceEq : tailSource.map (Option.map lift) =
            prior.bind fun seed =>
              ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[count + 1]
                (FinDist.pure (ProtocolState.entry program (source seed)))).map some := by
          simp only [tailSource, FinDist.map_bind, FinDist.map_comp, Option.map_some,
            Function.comp_def]
          let continuation := fun config : Config Player L Δ =>
            ((fun law => law.bind (ProtocolState.behavioralStateStep tail tailProfile))^[count]
              (FinDist.pure (ProtocolState.entry tail config))).map fun state => some (lift state)
          change nextPrior.bind (fun point => continuation (nextSource point)) = _
          rw [← FinDist.bind_map nextSource nextPrior continuation, nextMarginal,
            FinDist.bind_bind, FinDist.bind_map]
          apply FinDist.bind_congr
          intro seed _
          rw [kernel, FinDist.map_comp, FinDist.map_bind]
          rfl
        have marginalEq : (tailJoint.map (fun pair => (pair.1.map lift, pair.2))).map
            Prod.fst = prior.bind (fun seed =>
              ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[count + 1]
                (FinDist.pure (ProtocolState.entry program (source seed)))).map some) := by
          rw [FinDist.map_comp]
          change tailJoint.map (Option.map lift ∘ Prod.fst) = _
          rw [← FinDist.map_comp, tailMarginal]
          exact sourceEq
        rw [nativeEq]
        simpa only [marginalEq] using lifted
      cases program with
      | ret payoffs => simp only [eventCount] at within; omega
      | @sample Γ names name payload fresh distribution next =>
          have remaining : count ≤ eventCount next := by
            simpa only [eventCount, Nat.succ_le_succ_iff] using within
          have chance : (graph setup).actor? event = none := by
            change (toEventGraph setup.program).actor? event = none
            simpa [event, index, eventOwner?, eventCount] using
              (aligned prior.support_nonempty.choose).actorEq index
          have outputEq : (graph setup).outputLayout event = .publicData payload := by
            change outputLayout setup.program event = _
            simpa [event, index, outputLayout, eventCount] using embedding.layout_eq index
          let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
          let tailRefs : ContextRefs (graphLayout setup.program)
              ((name, .publicData payload) :: Γ) := refs.cons ⟨.inr event, outputEq⟩
          have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
            intro readName cell ref rest
            cases ref with
            | here =>
                change (embedding.event index).val < (embedding.event rest.succ).val
                exact embedding.strictMono (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _))
            | there ref => exact refsBefore ref rest.succ
          obtain ⟨phaseNoise, phaseFactor, phaseMarginal⟩ :=
            sourceService_sample_prefix_factorization setup leaks rosters timing fresh
              distribution next wholeProfile profile refs embedding refsBefore offset prior initial
              source opportunity aligned (fun seed => (opportunityFacts seed).1)
              network focal grantNoise opportunityFactor
                (fun seed => (opportunityFacts seed).2.1)
          let nextRegistry : Seed → Registry ((name, .publicData payload) :: Γ) :=
            fun seed => (source seed).registry.weaken
          let nextRevelations := fun seed =>
            (Revelations.weaken (source seed).revelations :
              Revelations ((name, .publicData payload) :: Γ))
          let encoded := fun config : Config Player L ((name, .publicData payload) :: Γ) =>
            (Sum.inr (ProtocolState.entry next config) :
              ProtocolState (.sample name fresh distribution next))
          let decode := fun seed (final : app.Execution) =>
            decodeSourcePrefix? (.sample name fresh distribution next) refs (source seed).registry
              (source seed).revelations embedding.ref 1 final.application.config.store
                (decodeHistory setup.program (final.application.config.history.map
                  (setup.eventGraph.fromModeCompletion .sequential)))
          let stepSource := fun config : Config Player L Γ =>
            (L.evalDist distribution (sourcePublicEnv config.state)).map (sampleSuccessor name
              config)
          let configNoise := fun view => phaseNoise (some (Sum.inr (entryObservation focal next
            view)))
          have phaseJoint : advanced.map (fun point => (decode point.1 point.2,
              (runtime setup).bindingTraffic leaks focal point.2)) =
              ((prior.map source).bind stepSource).bind fun config =>
                (configNoise (config.view focal)).map fun extra => (some (encoded config),
                  extra) := by
            have fact := phaseFactor
            rw [phaseMarginal] at fact
            simp only [advanced, FinDist.map_bind, FinDist.map_comp, Function.comp_def]
            change (prior.bind fun seed =>
              ((runtime setup).runInteractionPlan leaks players network
                (rosterBlock setup rosters event) (execution seed)).map fun final =>
                  (decode seed final, (runtime setup).bindingTraffic leaks focal final)) = _
            have block (seed : Seed) : (runtime setup).runInteractionPlan leaks players network
                (rosterBlock setup rosters event) (execution seed) =
                (runtime setup).runInteractionPlan leaks players network
                  ((rosters event).map ServiceInstruction.player ++
                    (.sample event :: List.replicate (event.val + 1) .tick ++
                      [.expire event])) (opportunity seed) := by
              simp only [rosterBlock, chance]
              change ((runtime setup).interactionStep leaks players network (.grant event)
                (execution seed)).bind _ = _
              rw [grantLaw, FinDist.pure_bind]
              change (runtime setup).runInteractionPlan leaks players network
                (((rosters event).map ServiceInstruction.player ++ [.sample event]) ++
                  List.replicate (event.val + 1) .tick ++ [.expire event]) (opportunity seed) = _
              congr 1
              simp only [List.append_assoc, List.singleton_append]
            simp only [block]
            simpa only [stepSource, configNoise, encoded, decode, FinDist.bind_bind,
              FinDist.bind_map, Option.map_some, ProtocolState.observe, Sum.elim_inr,
              observe_entry] using fact
          obtain ⟨nextSource, nextCheckpoint, nextRegistryEq, nextRevelationsEq, _nextRead,
            nextMarginal, nextFactor⟩ := reconstruct_phase setup leaks focal tailRefs (offset + 1)
              nextRegistry nextRevelations advanced encoded
              (Sum.inr_injective.comp (entry_injective next)) decode (by
                intro seed final
                simp only [decode, decodeSourcePrefix?,
                  Option.map_map, Function.comp_def]
                rfl) nextOrdered ((prior.map source).bind stepSource) configNoise phaseJoint
          have nextAligned (point : NextSeed) : CompiledPolicySuffix setup.program wholeProfile next
              (afterSample profile) tailRefs (nextSource point).revelations
              (nextSource point).registry tailEmbedding tailBefore (offset + 1) := by
            rw [nextRegistryEq, nextRevelationsEq]
            simpa only [nextRegistry, nextRevelations, sampleSuccessor, tailRefs, tailEmbedding,
              OutputEmbedding.ref] using
              (aligned point.val.1).sampleTail setup.program wholeProfile (_openNames := names)
                fresh distribution next profile refs (source point.val.1).revelations
                  (source point.val.1).registry embedding refsBefore offset
          have nextEffective (point : NextSeed) (who : Player) :
              ((afterSample profile) who).EffectiveDisclosures next (nextSource point).registry
                (nextSource point).revelations := by
            rw [nextRegistryEq, nextRevelationsEq]
            exact effective point.val.1 who
          refine finishStep next (afterSample profile) tailRefs tailEmbedding tailBefore nextSource
            nextAligned nextCheckpoint nextEffective configNoise nextFactor stepSource nextMarginal
            Sum.inr (fun view => view.bind (Sum.elim (fun _ => none) some)) ?_ ?_ ?_ ?_ remaining
          · intro state
            cases state <;> rfl
          · intro point final
            rw [nextRegistryEq, nextRevelationsEq, decodeSourcePrefix?_sample]
            rfl
          · intro config
            rw [ProtocolState.behavioralStatePrefix_sample]
            simp only [stepSource, FinDist.bind_map, FinDist.map_bind]
          · simp only [eventCount, List.finRange_succ, List.take_succ_cons, ← List.map_take,
              List.flatMap_cons, List.flatMap_map]
            rfl
      | @commit Γ names name owner payload fresh guard next =>
          have remaining : count ≤ eventCount next := by
            simpa only [eventCount, Nat.succ_le_succ_iff] using within
          have owned : (graph setup).actor? event = some owner := by
            change (toEventGraph setup.program).actor? event = some owner
            simpa [event, index, eventOwner?, eventCount] using
              (aligned prior.support_nonempty.choose).actorEq index
          have outputEq : (graph setup).outputLayout event = .binding owner payload := by
            change outputLayout setup.program event = _
            simpa [event, index, outputLayout, eventCount] using embedding.layout_eq index
          let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
          let tailRefs : ContextRefs (graphLayout setup.program)
              ((name, .commitment owner payload) :: Γ) := refs.cons ⟨.inr event, outputEq⟩
          have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
            intro readName cell ref rest
            cases ref with
            | here =>
                change (embedding.event index).val < (embedding.event rest.succ).val
                exact embedding.strictMono (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _))
            | there ref => exact refsBefore ref rest.succ
          obtain ⟨phaseNoise, phaseFactor, phaseMarginal⟩ :=
            sourceService_binding_prefix_factorization setup leaks bounds rosters timing fresh
              guard next wholeProfile profile refs embedding refsBefore offset prior initial
              source opportunity aligned (fun seed _ => (opportunityFacts seed).1)
              network focal grantNoise opportunityFactor
                (fun seed _ => (opportunityFacts seed).2.1)
          let nextRegistry := fun seed => (commitSuccessor name guard (source seed)
            .failure).registry
          let nextRevelations := fun seed =>
            ((commitSuccessor name guard (source seed) .failure).revelations :
              Revelations ((name, .commitment owner payload) :: Γ))
          let encoded := fun config : Config Player L ((name, .commitment owner payload) :: Γ) =>
            (Sum.inr (ProtocolState.entry next config) :
              ProtocolState (.commit name owner fresh guard next))
          let decode := fun seed (final : app.Execution) =>
            decodeSourcePrefix? (.commit name owner fresh guard next) refs (source seed).registry
              (source seed).revelations embedding.ref 1 final.application.config.store
                (decodeHistory setup.program (final.application.config.history.map
                  (setup.eventGraph.fromModeCompletion .sequential)))
          let stepSource := fun config : Config Player L Γ =>
            (commitKernel profile (config.view owner)).map (commitSuccessor name guard config)
          let configNoise := fun view => phaseNoise (some (Sum.inr (entryObservation focal next
            view)))
          have phaseJoint : advanced.map (fun point => (decode point.1 point.2,
              (runtime setup).bindingTraffic leaks focal point.2)) =
              ((prior.map source).bind stepSource).bind fun config =>
                (configNoise (config.view focal)).map fun extra => (some (encoded config),
                  extra) := by
            have fact := phaseFactor
            rw [phaseMarginal] at fact
            simp only [advanced, FinDist.map_bind, FinDist.map_comp, Function.comp_def]
            change (prior.bind fun seed =>
              ((runtime setup).runInteractionPlan leaks players network
                (rosterBlock setup rosters event) (execution seed)).map fun final =>
                  (decode seed final, (runtime setup).bindingTraffic leaks focal final)) = _
            have block (seed : Seed) : (runtime setup).runInteractionPlan leaks players network
                (rosterBlock setup rosters event) (execution seed) =
                (runtime setup).runInteractionPlan leaks players network
                  ((rosters event).map ServiceInstruction.player ++
                    (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++
                      [.expire event])) (opportunity seed) := by
              rw [rosterBlock_of_owner setup rosters event owner owned]
              change ((runtime setup).interactionStep leaks players network (.grant event)
                (execution seed)).bind _ = _
              rw [grantLaw, FinDist.pure_bind]
              simp only [List.append_assoc, List.singleton_append]
              rfl
            simp only [block]
            simpa only [stepSource, configNoise, encoded, decode, FinDist.bind_bind,
              FinDist.bind_map, Option.map_some, ProtocolState.observe, Sum.elim_inr,
              observe_entry] using fact
          obtain ⟨nextSource, nextCheckpoint, nextRegistryEq, nextRevelationsEq, _nextRead,
            nextMarginal, nextFactor⟩ := reconstruct_phase setup leaks focal tailRefs (offset + 1)
              nextRegistry nextRevelations advanced encoded
              (Sum.inr_injective.comp (entry_injective next)) decode (by
                intro seed final
                simp only [decode, decodeSourcePrefix?,
                  Option.map_map, Function.comp_def]
                rfl) nextOrdered ((prior.map source).bind stepSource) configNoise phaseJoint
          have nextAligned (point : NextSeed) : CompiledPolicySuffix setup.program wholeProfile next
              (afterCommit profile) tailRefs (nextSource point).revelations
              (nextSource point).registry tailEmbedding tailBefore (offset + 1) := by
            rw [nextRegistryEq, nextRevelationsEq]
            simpa only [nextRegistry, nextRevelations, commitSuccessor, tailRefs, tailEmbedding,
              OutputEmbedding.ref] using
              (aligned point.val.1).commitTail setup.program wholeProfile fresh guard next profile
                refs (source point.val.1).revelations (source point.val.1).registry
                  embedding refsBefore offset
          have nextEffective (point : NextSeed) (who : Player) :
              ((afterCommit profile) who).EffectiveDisclosures next (nextSource point).registry
                (nextSource point).revelations := by
            rw [nextRegistryEq, nextRevelationsEq]
            exact effective point.val.1 who
          refine finishStep next (afterCommit profile) tailRefs tailEmbedding tailBefore nextSource
            nextAligned nextCheckpoint nextEffective configNoise nextFactor stepSource nextMarginal
            Sum.inr (fun view => view.bind (Sum.elim (fun _ => none) some)) ?_ ?_ ?_ ?_ remaining
          · intro state
            cases state <;> rfl
          · intro point final
            rw [nextRegistryEq, nextRevelationsEq, decodeSourcePrefix?_commit]
            rfl
          · intro config
            rw [ProtocolState.behavioralStatePrefix_commit]
            simp only [stepSource, FinDist.bind_map, FinDist.map_bind]
          · simp only [eventCount, List.finRange_succ, List.take_succ_cons, ← List.map_take,
              List.flatMap_cons, List.flatMap_map]
            rfl
      | @reveal Γ names published owner name payload fresh binding unresolved next =>
          have remaining : count ≤ eventCount next := by
            simpa only [eventCount, Nat.succ_le_succ_iff] using within
          have owned : (graph setup).actor? event = some owner := by
            change (toEventGraph setup.program).actor? event = some owner
            simpa [event, index, eventOwner?, eventCount] using
              (aligned prior.support_nonempty.choose).actorEq index
          have outputEq : (graph setup).outputLayout event = .publication payload := by
            change outputLayout setup.program event = _
            simpa [event, index, outputLayout, eventCount] using embedding.layout_eq index
          let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
          let tailRefs : ContextRefs (graphLayout setup.program)
              ((published, .publication payload) :: Γ) := refs.cons ⟨.inr event, outputEq⟩
          have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
            intro readName cell ref rest
            cases ref with
            | here =>
                change (embedding.event index).val < (embedding.event rest.succ).val
                exact embedding.strictMono (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _))
            | there ref => exact refsBefore ref rest.succ
          obtain ⟨phaseNoise, phaseFactor, phaseMarginal⟩ :=
            sourceService_reveal_prefix_factorization setup leaks rosters timing fresh
              binding unresolved next wholeProfile profile refs embedding refsBefore offset
                prior initial
              source opportunity aligned (fun seed _ => (opportunityFacts seed).1)
              (fun seed _ => grantOrigins seed) (fun seed _ => effective seed owner)
              network focal grantNoise opportunityFactor
                (fun seed _ => (opportunityFacts seed).2.1)
          let nextRegistry : Seed → Registry ((published, .publication payload) :: Γ) :=
            fun seed => (source seed).registry.weaken
          let nextRevelations := fun seed =>
            (Revelations.reveal (published := published) (source seed).revelations binding :
              Revelations ((published, .publication payload) :: Γ))
          let encoded := fun config : Config Player L ((published, .publication payload) :: Γ) =>
            (Sum.inr (ProtocolState.entry next config) :
              ProtocolState (.reveal published owner name fresh binding unresolved next))
          let decode := fun seed (final : app.Execution) =>
            decodeSourcePrefix? (.reveal published owner name fresh binding unresolved next)
              refs (source seed).registry
              (source seed).revelations embedding.ref 1 final.application.config.store
                (decodeHistory setup.program (final.application.config.history.map
                  (setup.eventGraph.fromModeCompletion .sequential)))
          let stepSource := fun config : Config Player L Γ =>
            (revealKernel profile (config.view owner)).map (revealSuccessor published binding
              config)
          let configNoise := fun view => phaseNoise (some (Sum.inr (entryObservation focal next
            view)))
          have phaseJoint : advanced.map (fun point => (decode point.1 point.2,
              (runtime setup).bindingTraffic leaks focal point.2)) =
              ((prior.map source).bind stepSource).bind fun config =>
                (configNoise (config.view focal)).map fun extra => (some (encoded config),
                  extra) := by
            have fact := phaseFactor
            rw [phaseMarginal] at fact
            simp only [advanced, FinDist.map_bind, FinDist.map_comp, Function.comp_def]
            change (prior.bind fun seed =>
              ((runtime setup).runInteractionPlan leaks players network
                (rosterBlock setup rosters event) (execution seed)).map fun final =>
                  (decode seed final, (runtime setup).bindingTraffic leaks focal final)) = _
            have block (seed : Seed) : (runtime setup).runInteractionPlan leaks players network
                (rosterBlock setup rosters event) (execution seed) =
                (runtime setup).runInteractionPlan leaks players network
                  ((rosters event).map ServiceInstruction.player ++
                    (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++
                      [.expire event])) (opportunity seed) := by
              rw [rosterBlock_of_owner setup rosters event owner owned]
              change ((runtime setup).interactionStep leaks players network (.grant event)
                (execution seed)).bind _ = _
              rw [grantLaw, FinDist.pure_bind]
              simp only [List.append_assoc, List.singleton_append]
              rfl
            simp only [block]
            simpa only [stepSource, configNoise, encoded, decode, FinDist.bind_bind,
              FinDist.bind_map, Option.map_some, ProtocolState.observe, Sum.elim_inr,
              observe_entry] using fact
          obtain ⟨nextSource, nextCheckpoint, nextRegistryEq, nextRevelationsEq, _nextRead,
            nextMarginal, nextFactor⟩ := reconstruct_phase setup leaks focal tailRefs (offset + 1)
              nextRegistry nextRevelations advanced encoded
              (Sum.inr_injective.comp (entry_injective next)) decode (by
                intro seed final
                simp only [decode, decodeSourcePrefix?,
                  Option.map_map, Function.comp_def]
                rfl) nextOrdered ((prior.map source).bind stepSource) configNoise phaseJoint
          have nextAligned (point : NextSeed) : CompiledPolicySuffix setup.program wholeProfile next
              (afterReveal profile) tailRefs (nextSource point).revelations
              (nextSource point).registry tailEmbedding tailBefore (offset + 1) := by
            rw [nextRegistryEq, nextRevelationsEq]
            simpa only [nextRegistry, nextRevelations, revealSuccessor, tailRefs, tailEmbedding,
              OutputEmbedding.ref] using
              (aligned point.val.1).revealTail (whole := setup.program) (wholeProfile :=
                wholeProfile)
                fresh binding unresolved next profile refs (source point.val.1).revelations
                  (source point.val.1).registry embedding refsBefore offset
          have nextEffective (point : NextSeed) (who : Player) :
              ((afterReveal profile) who).EffectiveDisclosures next (nextSource point).registry
                (nextSource point).revelations := by
            rw [nextRegistryEq, nextRevelationsEq]
            exact (effective point.val.1 who).2
          refine finishStep next (afterReveal profile) tailRefs tailEmbedding tailBefore nextSource
            nextAligned nextCheckpoint nextEffective configNoise nextFactor stepSource nextMarginal
            Sum.inr (fun view => view.bind (Sum.elim (fun _ => none) some)) ?_ ?_ ?_ ?_ remaining
          · intro state
            cases state <;> rfl
          · intro point final
            rw [nextRegistryEq, nextRevelationsEq, decodeSourcePrefix?_reveal]
            rfl
          · intro config
            rw [ProtocolState.behavioralStatePrefix_reveal]
            simp only [stepSource, FinDist.bind_map, FinDist.map_bind]
          · simp only [eventCount, List.finRange_succ, List.take_succ_cons, ← List.map_take,
              List.flatMap_cons, List.flatMap_map]
            rfl

/-- Every initialized timed prefix has the source protocol's state marginal,
jointly with the entire focal traffic record. The auxiliary law is derived for
arbitrary correlated initial types and every supported native timing branch. -/
theorem sourceServiceTimedPolicy_initialized_prefix_factorization [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ∀ event owner payload,
      (graph setup).outputLayout event = .binding owner payload → owner ∈ rosters event)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (covered : ∀ who, (sourceServiceMenu setup leaks bounds rosters).Admissible
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who
      (sourceServiceTimedPolicy setup leaks rosters timing profile who))
    (permitted : ∀ who, (profile who).Admitted setup.program
      (CommitmentInterface.values setup.program))
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (focal : Player) (count : Nat) (within : count ≤ eventCount setup.program) :
    let admission := CommitmentInterface.values setup.program
    let encoded := fun who => setup.toProtocolBehavioralPolicy admission who
      (profile who) (permitted who)
    ∃ noise : setup.ProtocolView focal → FinDist _,
      (((initialLaw setup).bind fun state => (runtime setup).runInteractionPlan leaks
        (sourceServiceTimedPolicy setup leaks rosters timing profile) network
        (rosterPlanPrefix setup rosters count)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).map fun final =>
          (sourceServicePrefix? setup count final.application.config,
            (runtime setup).bindingTraffic leaks focal final)) =
        (((setup.informationModel admission).runBehavioral encoded (count + 1)).map
          GameTheory.Protocol.ExecutionProtocol.History.state).bind fun state =>
            (noise (setup.protocolObserve focal state)).map fun extra => (state, extra) := by
  intro admission encoded
  let Seed := {initial // initial ∈ setup.initialLaw.support}
  let prior : FinDist Seed := setup.initialLaw.toSubtype (fun _ member => member)
  let source := fun seed : Seed => setup.initialConfig seed.val
  let execution := fun seed : Seed => ReactiveApplication.Execution.initial
    (application setup leaks) (EventGraphRuntime.State.initial (graph := graph setup)
      (setup.eventInputs seed.val))
  obtain ⟨initialNoise, initialFactor⟩ := source_initial_memory_factorization setup leaks focal
  have factor : prior.map (fun seed => (source seed,
      (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map source).bind fun config =>
        (initialNoise (config.view focal)).map fun extra => (config, extra) := by
    have projected := congrArg (FinDist.map fun pair => (pair.1.1, pair.2)) initialFactor
    dsimp only [prior, source, execution]
    rw [FinDist.map_toSubtype setup.initialLaw (fun _ member => member)
      (fun initial => (setup.initialConfig initial,
        (runtime setup).bindingTraffic leaks focal
          (ReactiveApplication.Execution.initial (application setup leaks)
            (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial))))),
      FinDist.map_toSubtype setup.initialLaw (fun _ member => member) setup.initialConfig]
    simpa only [FinDist.map_comp, FinDist.map_bind, FinDist.bind_map, Function.comp_def]
      using projected
  have initialized (seed : Seed) : execution seed ∈ ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks
        (sourceServiceTimedPolicy setup leaks rosters timing profile) network
        (rosterPlanPrefix setup rosters 0)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).support := by
    simp only [rosterPlanPrefix, List.take_zero, List.flatMap_nil, runInteractionPlan,
      ← FinDist.map_eq_bind, initialLaw, FinDist.map_comp, FinDist.support_map]
    exact ⟨seed.val, seed.property, rfl⟩
  obtain ⟨noise, law⟩ := sourceServiceTimedPolicy_prefix_joint_factorization setup leaks
    bounds values capacity rosters opportunities timing network profile covered focal count
      setup.program profile (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program) (initialRefsBefore setup.program) 0 prior source execution
      (fun _ => CompiledPolicySuffix.whole setup.program profile)
      (fun seed => SourceCheckpoint.initial setup seed.val) initialized
      (fun _ who => effective who) initialNoise factor within
  refine ⟨noise, ?_⟩
  let combined := fun initial : State L setup.context =>
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceTimedPolicy setup leaks rosters timing profile) network
      (rosterPlanPrefix setup rosters count)
      (ReactiveApplication.Execution.initial (application setup leaks)
        (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)))).map
      fun final => (sourceServicePrefix? setup count final.application.config,
        (runtime setup).bindingTraffic leaks focal final)
  let sourcePrefix := fun initial : State L setup.context =>
    ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program profile))^[count]
      (FinDist.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).map some
  have nativeLaw : prior.bind (fun seed => combined seed.val) = setup.initialLaw.bind combined := by
    rw [← FinDist.bind_map Subtype.val prior combined]
    exact congrArg (fun law => law.bind combined) (FinDist.map_val_toSubtype _ _)
  have sourceLaw : prior.bind (fun seed => sourcePrefix seed.val) =
      setup.initialLaw.bind sourcePrefix := by
    rw [← FinDist.bind_map Subtype.val prior sourcePrefix]
    exact congrArg (fun law => law.bind sourcePrefix) (FinDist.map_val_toSubtype _ _)
  change (prior.bind fun seed => combined seed.val) =
    (prior.bind fun seed => sourcePrefix seed.val).bind fun state =>
      (noise (setup.protocolObserve focal state)).map fun extra => (state, extra) at law
  rw [nativeLaw, sourceLaw] at law
  rw [setup.encoded_prefix_state]
  rw [initialLaw, FinDist.bind_map, FinDist.map_bind]
  exact law

/-- The compiler's original source policy is normalized only through the
existing private-intention reconstruction. Its concrete timed native prefix
has the conditional-state factor needed by original-assessment comparisons. -/
theorem sourceServiceTimedProfile_prefix_factorization [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ∀ event owner payload,
      (graph setup).outputLayout event = .binding owner payload → owner ∈ rosters event)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (full : ∀ event who owned, (timing event who owned).FullSupport)
    (network : (runtime setup).NetworkPolicy leaks)
    (original : BehavioralProfile setup.program)
    (permitted : ∀ who, (original who).Admitted setup.program
      (CommitmentInterface.values setup.program))
    (focal : Player) (count : Nat) (within : count ≤ eventCount setup.program) :
    let normalized := normalizeDisclosureProfile setup.program []
      (Revelations.initial setup.context) original
    let admission := CommitmentInterface.values setup.program
    let encoded := fun who => setup.toProtocolBehavioralPolicy admission who
      (normalized who) (normalized_sourceService_admitted setup original permitted who)
    ∃ noise : setup.ProtocolView focal → FinDist _,
      (((initialLaw setup).bind fun state => (runtime setup).runInteractionPlan leaks
        (sourceServiceTimedPolicy setup leaks rosters timing normalized) network
        (rosterPlanPrefix setup rosters count)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).map fun final =>
          (sourceServicePrefix? setup count final.application.config,
            (runtime setup).bindingTraffic leaks focal final)) =
        (((setup.informationModel admission).runBehavioral encoded (count + 1)).map
          GameTheory.Protocol.ExecutionProtocol.History.state).bind fun state =>
            (noise (setup.protocolObserve focal state)).map fun extra => (state, extra) := by
  intro normalized admission encoded
  have admitted := normalized_sourceService_admitted setup original permitted
  exact sourceServiceTimedPolicy_initialized_prefix_factorization setup leaks bounds values
    capacity rosters opportunities timing network normalized
    (sourceServiceTimedPolicy_admissible setup leaks bounds values initialValues capacity
      rosters opportunities network timing full normalized admitted)
    admitted (fun who => (original who).normalizeDisclosureFrom_effective setup.program []
      (Revelations.initial setup.context) (fun view => FinDist.pure view.2)) focal count within

end Vegas.SourceProgram.RevealService
