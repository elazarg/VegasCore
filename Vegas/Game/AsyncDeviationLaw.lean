/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncDeviationChoice
import Vegas.Game.SourceServiceDeviationLaw

/-! # The source law of one deviation under an arbitrary scheduler

Against the first-turn clients of a source profile, under a scheduler
satisfying the asynchronous contract, one player follows an arbitrary native
policy. Phase by phase, the decoded source state follows the source protocol in
which every other player keeps its source policy and the deviator follows a
single source behavioral policy, built event by event: in a phase of another
player's event, or of chance, the source step is the source kernel and the
deviator's traffic depends on its public effect only; in a phase of its own
event its choice is a behavioral choice of its source view. Throughout, the
deviator's native traffic factors through its source view. The deviator's
bindings may fail.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime
open GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Phases

variable {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The completion runs of a list of events in turn, each to the horizon. -/
def deviationPhases (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (horizon : Nat) :
    List (graph setup).EventId → (application setup leaks).Execution →
      PMF (application setup leaks).Execution
  | [], execution => PMF.pure execution
  | event :: rest, execution =>
      ((application setup leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
        (deviationPhases scheduler players horizon rest)

end Phases

variable [Fintype Player]

/-- **Whole-prefix induction for one deviating player under an arbitrary
scheduler.** Against the first-turn clients of a source profile, under a
scheduler satisfying the asynchronous contract, one player follows an arbitrary
native policy. Phase by phase, the decoded source state then has the law of
the source protocol in which that player follows a single source behavioral
policy, whose bindings may fail, and every other player keeps its source
policy; jointly, the deviator's native traffic depends on the source state only
through the deviator's source view. -/
theorem asyncDeviation_prefix_joint_factorization
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program)
    (who : Player) (deviation : (application setup leaks).Policy) :
    let players := deviatedTurnProfile bound turns (firstTurnTiming setup turns) wholeProfile
      who deviation
    ∀ count {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
      (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
      {Seed : Type} (prior : PMF Seed) (source : Seed → Config Player L Γ)
      (execution : Seed → (application setup leaks).Execution),
      (∀ seed, CompiledPolicySuffix setup.program wholeProfile program profile refs
        (source seed).revelations (source seed).registry embedding refsBefore offset) →
      (∀ seed, SourceCheckpoint setup (source seed) refs offset
        (execution seed).application.config) →
      (∀ seed ∈ prior.support, CompletionBoundary setup leaks scheduler players offset
        (execution seed)) →
      (∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon) →
      (∀ seed player, (profile player).EffectiveDisclosures program (source seed).registry
        (source seed).revelations) →
      ∀ (noise : DecisionView who Γ → PMF _),
      prior.map (fun seed => (source seed,
          (runtime setup).bindingTraffic leaks who (execution seed))) =
        (prior.map source).bind (fun config =>
          (noise (config.view who)).map fun extra => (config, extra)) →
      count ≤ eventCount program →
      ∃ policy : BehavioralPolicy who program,
        ∃ nextNoise : Option (ProtocolView who program) → PMF _,
          (prior.bind fun seed =>
            (deviationPhases scheduler players horizon
              (((List.finRange (eventCount program)).take count).map embedding.event)
              (execution seed)).map
                  fun final =>
                    (decodeSourcePrefix? program refs (source seed).registry
                      (source seed).revelations embedding.ref count
                        final.application.config.store
                      (decodeHistory setup.program (final.application.config.history.map
                        (setup.eventGraph.fromModeCompletion .sequential))),
                      (runtime setup).bindingTraffic leaks who final)) =
            (prior.bind fun seed =>
              ((fun law => law.bind (ProtocolState.behavioralStateStep program
                (Function.update profile who policy)))^[count]
                (PMF.pure (ProtocolState.entry program (source seed)))).map some).bind
                  fun state => (nextNoise (state.map (ProtocolState.observe who program))).map
                    fun extra => (state, extra) := by
  intro players count
  induction count with
  | zero =>
      intro Γ names program profile refs embedding refsBefore offset Seed prior source execution
        _aligned checkpoint _boundary _bounded _effective noise factor _within
      obtain ⟨nextNoise, nextFactor⟩ := ProtocolView.entry_noise_factor program who prior source
        (fun seed => (runtime setup).bindingTraffic leaks who (execution seed)) noise factor
      refine ⟨profile who, nextNoise, ?_⟩
      dsimp only at nextFactor
      simp only [List.take_zero, List.map_nil, deviationPhases,
        Function.iterate_zero, id_eq, ← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind,
        PMF.pure_bind]
      simp only [← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
        at nextFactor
      refine Eq.trans (bind_congr_on_support _ fun seed _ => ?_) nextFactor
      rw [(checkpoint seed).decode program embedding.ref]
  | succ count ih =>
      intro Γ names program profile refs embedding refsBefore offset Seed prior source execution
        aligned checkpoint boundary bounded effective noise factor within
      let app := application setup leaks
      let index : Fin (eventCount program) := ⟨0, by omega⟩
      let event : (graph setup).EventId := embedding.event index
      have eventRank : event.val = offset := by
        simpa only [event, index, Nat.add_zero] using
          (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
      have offsetBound : offset ≤ eventCount setup.program := by
        have counted := (aligned prior.support_nonempty.choose).graphSuffix.countEq
        omega
      have boundaryAt (seed : Seed) (supported : seed ∈ prior.support) :
          CompletionBoundary setup leaks scheduler players event.val (execution seed) := by
        rw [eventRank]
        exact boundary seed supported
      let advanced := prior.bind fun seed =>
        (app.runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map fun final => (seed, final)
      let NextSeed := {point : Seed × app.Execution // point ∈ advanced.support}
      let nextPrior : PMF NextSeed := pmfToSubtype advanced (fun _ member => member)
      let nextExecution := fun point : NextSeed => point.val.2
      have nextSupport (point : NextSeed) : point.val.1 ∈ prior.support ∧
          point.val.2 ∈ (app.runUntilHorizon scheduler players
            (fun final => event ∈ final.application.config.cut.completed) horizon
            (execution point.val.1)).support := by
        rcases point with ⟨⟨seed, final⟩, member⟩
        change seed ∈ prior.support ∧ final ∈ _
        change (seed, final) ∈ (prior.bind fun seed =>
          (app.runUntilHorizon scheduler players
            (fun final => event ∈ final.application.config.cut.completed) horizon
            (execution seed)).map fun final => (seed, final)).support at member
        rw [PMF.support_bind] at member
        obtain ⟨seed, selected, moved⟩ := Set.mem_iUnion₂.mp member
        rw [PMF.support_map] at moved
        obtain ⟨final, moved, same⟩ := moved
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
        exact ⟨selected, moved⟩
      have nextFacts (point : NextSeed) :
          CompletionBoundary setup leaks scheduler players (offset + 1) (nextExecution point) ∧
            (nextExecution point).environmentRecall.length ≤ horizon := by
        obtain ⟨_, _, _, nextBounded, nextBoundary⟩ := completionRun_boundary_step
          contract.completes event (execution point.val.1)
          (boundaryAt point.val.1 (nextSupport point).1) (bounded point.val.1 (nextSupport point).1)
          point.val.2 (nextSupport point).2
        rw [eventRank] at nextBoundary
        exact ⟨nextBoundary, nextBounded⟩
      have nextOrdered (point : Seed × app.Execution) (member : point ∈ advanced.support) :
          point.2.application.config.cut.IsPrefix (offset + 1) :=
        (nextFacts ⟨point, member⟩).1.ordered
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
          (nextEffective : ∀ point player, (tailProfile player).EffectiveDisclosures tail
            (nextSource point).registry (nextSource point).revelations)
          (nextNoise : DecisionView who Δ → PMF _)
          (nextFactor : nextPrior.map (fun point => (nextSource point,
              (runtime setup).bindingTraffic leaks who (nextExecution point))) =
            (nextPrior.map nextSource).bind fun config =>
              (nextNoise (config.view who)).map fun extra => (config, extra))
          (stepSource : Config Player L Γ → PMF (Config Player L Δ))
          (nextMarginal : nextPrior.map nextSource = (prior.map source).bind stepSource)
          (lift : ProtocolState tail → ProtocolState program)
          (recover : Option (ProtocolView who program) → Option (ProtocolView who tail))
          (recovers : ∀ state : Option (ProtocolState tail),
            recover ((state.map lift).map (ProtocolState.observe who program)) =
              state.map (ProtocolState.observe who tail))
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
          (build : BehavioralPolicy who tail → BehavioralPolicy who program)
          (kernel : ∀ policy config,
            ((fun law => law.bind (ProtocolState.behavioralStateStep program
              (Function.update profile who (build policy))))^[count + 1]
              (PMF.pure (ProtocolState.entry program config))) =
            ((stepSource config).bind fun next =>
              ((fun law => law.bind (ProtocolState.behavioralStateStep tail
                (Function.update tailProfile who policy)))^[count]
                (PMF.pure (ProtocolState.entry tail next)))).map lift)
          (planEq : ((List.finRange (eventCount program)).take (count + 1)).map
            embedding.event = event ::
              ((List.finRange (eventCount tail)).take count).map tailEmbedding.event)
          (withinTail : count ≤ eventCount tail) :
          ∃ policy : BehavioralPolicy who program,
            ∃ nextNoise : Option (ProtocolView who program) → PMF _,
              (prior.bind fun seed =>
                (deviationPhases scheduler players horizon
                  (((List.finRange (eventCount program)).take (count + 1)).map embedding.event)
                  (execution seed)).map
                      fun final =>
                        (decodeSourcePrefix? program refs (source seed).registry
                          (source seed).revelations embedding.ref (count + 1)
                            final.application.config.store (decodeHistory setup.program
                              (final.application.config.history.map
                                (setup.eventGraph.fromModeCompletion .sequential))),
                          (runtime setup).bindingTraffic leaks who final)) =
                (prior.bind fun seed =>
                  ((fun law => law.bind (ProtocolState.behavioralStateStep program
                    (Function.update profile who policy)))^[count + 1]
                    (PMF.pure (ProtocolState.entry program (source seed)))).map some).bind
                      fun state => (nextNoise (state.map (ProtocolState.observe who program))).map
                        fun extra => (state, extra) := by
        obtain ⟨tailPolicy, tailNoise, tailLaw⟩ := ih tail tailProfile tailRefs
          tailEmbedding tailBefore (offset + 1) nextPrior nextSource nextExecution nextAligned
          nextCheckpoint (fun point _ => (nextFacts point).1) (fun point _ => (nextFacts point).2)
          nextEffective nextNoise nextFactor withinTail
        refine ⟨build tailPolicy, ?_⟩
        let remainingPlan := ((List.finRange (eventCount tail)).take count).map
          tailEmbedding.event
        let tailJoint := nextPrior.bind fun point =>
          (deviationPhases scheduler players horizon remainingPlan
            (nextExecution point)).map fun final =>
              (decodeSourcePrefix? tail tailRefs (nextSource point).registry
                (nextSource point).revelations tailEmbedding.ref count
                  final.application.config.store
                  (decodeHistory setup.program (final.application.config.history.map
                    (setup.eventGraph.fromModeCompletion .sequential))),
                (runtime setup).bindingTraffic leaks who final)
        let tailSource := nextPrior.bind fun point =>
          ((fun law => law.bind (ProtocolState.behavioralStateStep tail
            (Function.update tailProfile who tailPolicy)))^[count]
            (PMF.pure (ProtocolState.entry tail (nextSource point)))).map some
        have tailMarginal : tailJoint.map Prod.fst = tailSource := by
          have projected := congrArg (PMF.map Prod.fst) tailLaw
          simp only [← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind, PMF.pure_bind,
            PMF.bind_const] at projected
          simpa only [tailJoint, tailSource, ← PMF.bind_pure_comp, Function.comp_def,
            PMF.bind_bind, PMF.pure_bind, PMF.bind_pure] using projected
        have tailFactor : tailJoint = (tailJoint.map Prod.fst).bind fun state =>
            (tailNoise (state.map (ProtocolState.observe who tail))).map fun extra =>
              (state, extra) := by
          rw [tailMarginal]
          exact tailLaw
        have lifted := map_observation_factor tailJoint
          (Option.map (ProtocolState.observe who tail)) tailNoise tailFactor
          (Option.map lift) (Option.map (ProtocolState.observe who program)) recover recovers
        refine ⟨fun view => tailNoise (recover view), ?_⟩
        have nativeEq : (prior.bind fun seed =>
            (deviationPhases scheduler players horizon
              (((List.finRange (eventCount program)).take (count + 1)).map embedding.event)
              (execution seed)).map
                  fun final =>
                    (decodeSourcePrefix? program refs (source seed).registry
                      (source seed).revelations embedding.ref (count + 1)
                        final.application.config.store (decodeHistory setup.program
                          (final.application.config.history.map
                            (setup.eventGraph.fromModeCompletion .sequential))),
                      (runtime setup).bindingTraffic leaks who final)) =
            tailJoint.map (fun pair => (pair.1.map lift, pair.2)) := by
          rw [planEq]
          let continuePoint := fun point : Seed × app.Execution =>
            (deviationPhases scheduler players horizon remainingPlan point.2).map
              fun final =>
                (decodeSourcePrefix? program refs (source point.1).registry
                  (source point.1).revelations embedding.ref (count + 1)
                    final.application.config.store (decodeHistory setup.program
                      (final.application.config.history.map
                        (setup.eventGraph.fromModeCompletion .sequential))),
                  (runtime setup).bindingTraffic leaks who final)
          calc
            _ = advanced.bind continuePoint := by
              simp only [advanced, continuePoint, PMF.bind_bind, PMF.bind_map,
                deviationPhases, PMF.map_bind, remainingPlan, Function.comp_def]
              rfl
            _ = nextPrior.bind (fun point => continuePoint point.val) := by
              rw [show (nextPrior.bind fun point => continuePoint point.val) =
                  (nextPrior.map Subtype.val).bind continuePoint from
                (PMF.bind_map nextPrior Subtype.val continuePoint).symm, map_val_pmfToSubtype]
            _ = _ := by
              simp only [tailJoint, PMF.map_bind, PMF.map_comp, Function.comp_def]
              apply bind_congr_on_support _
              intro point _
              apply map_congr_on_support _
              intro final _
              exact Prod.ext (decodeLater point final) rfl
        have sourceEq : tailSource.map (Option.map lift) =
            prior.bind fun seed =>
              ((fun law => law.bind (ProtocolState.behavioralStateStep program
                (Function.update profile who (build tailPolicy))))^[count + 1]
                (PMF.pure (ProtocolState.entry program (source seed)))).map some := by
          simp only [tailSource, PMF.map_bind, PMF.map_comp, Option.map_some,
            Function.comp_def]
          let continuation := fun config : Config Player L Δ =>
            ((fun law => law.bind (ProtocolState.behavioralStateStep tail
              (Function.update tailProfile who tailPolicy)))^[count]
              (PMF.pure (ProtocolState.entry tail config))).map fun state => some (lift state)
          change nextPrior.bind (fun point => continuation (nextSource point)) = _
          rw [show (nextPrior.bind fun point => continuation (nextSource point)) =
              (nextPrior.map nextSource).bind continuation from
            (PMF.bind_map nextPrior nextSource continuation).symm, nextMarginal,
            PMF.bind_bind, PMF.bind_map]
          apply bind_congr_on_support _
          intro seed _
          rw [kernel, PMF.map_comp, PMF.map_bind]
          rfl
        have marginalEq : (tailJoint.map (fun pair => (pair.1.map lift, pair.2))).map
            Prod.fst = prior.bind (fun seed =>
              ((fun law => law.bind (ProtocolState.behavioralStateStep program
                (Function.update profile who (build tailPolicy))))^[count + 1]
                (PMF.pure (ProtocolState.entry program (source seed)))).map some) := by
          rw [PMF.map_comp]
          change tailJoint.map (Option.map lift ∘ Prod.fst) = _
          rw [← PMF.map_comp, tailMarginal]
          exact sourceEq
        rw [nativeEq]
        simpa only [marginalEq] using lifted
      cases program with
      | ret payoffs => simp only [eventCount] at within; omega
      | @sample Γ names name payload fresh distribution next =>
          have remaining : count ≤ eventCount next := by
            simpa only [eventCount, Nat.succ_le_succ_iff] using within
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
          obtain ⟨configNoise, phaseJoint⟩ := asyncDeviation_sample_factorization contract turns
            wholeProfile who deviation fresh distribution next profile refs embedding refsBefore
            offset prior source execution aligned checkpoint boundary bounded noise factor
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
          have phaseJoint' : advanced.map (fun point => (decode point.1 point.2,
              (runtime setup).bindingTraffic leaks who point.2)) =
              ((prior.map source).bind stepSource).bind fun config =>
                (configNoise (config.view who)).map fun extra => (some (encoded config),
                  extra) := by
            simp only [advanced, PMF.map_bind, PMF.map_comp, Function.comp_def]
            exact phaseJoint
          obtain ⟨nextSource, nextCheckpoint, nextRegistryEq, nextRevelationsEq, _nextRead,
            nextMarginal, nextFactor⟩ := reconstruct_service_phase setup leaks who tailRefs
              (offset + 1) nextRegistry nextRevelations advanced encoded
              (Sum.inr_injective.comp (ProtocolState.entry_injective next)) decode (by
                intro seed final
                simp only [decode, decodeSourcePrefix?,
                  Option.map_map, Function.comp_def]
                rfl) nextOrdered ((prior.map source).bind stepSource) configNoise phaseJoint'
          have nextAligned (point : NextSeed) : CompiledPolicySuffix setup.program wholeProfile next
              (afterSample profile) tailRefs (nextSource point).revelations
              (nextSource point).registry tailEmbedding tailBefore (offset + 1) := by
            rw [nextRegistryEq, nextRevelationsEq]
            simpa only [nextRegistry, nextRevelations, sampleSuccessor, tailRefs, tailEmbedding,
              OutputEmbedding.ref] using
              (aligned point.val.1).sampleTail setup.program wholeProfile (_openNames := names)
                fresh distribution next profile refs (source point.val.1).revelations
                  (source point.val.1).registry embedding refsBefore offset
          have nextEffective (point : NextSeed) (player : Player) :
              ((afterSample profile) player).EffectiveDisclosures next (nextSource point).registry
                (nextSource point).revelations := by
            rw [nextRegistryEq, nextRevelationsEq]
            exact effective point.val.1 player
          refine finishStep next (afterSample profile) tailRefs tailEmbedding tailBefore nextSource
            nextAligned nextCheckpoint nextEffective configNoise
            nextFactor stepSource nextMarginal Sum.inr
            (fun view => view.bind (Sum.elim (fun _ => none) some)) ?_ ?_ (fun policy => policy)
            ?_ ?_ remaining
          · intro state
            cases state <;> rfl
          · intro point final
            rw [nextRegistryEq, nextRevelationsEq, decodeSourcePrefix?_sample]
            rfl
          · intro policy config
            rw [ProtocolState.behavioralStatePrefix_sample, afterSample_update]
            simp only [stepSource, PMF.bind_map, PMF.map_bind, Function.comp_def]
          · simp only [eventCount, List.finRange_succ, List.take_succ_cons, ← List.map_take,
              List.map_cons, List.map_map]
            rfl
      | @commit Γ names name owner payload fresh guard next =>
          have remaining : count ≤ eventCount next := by
            simpa only [eventCount, Nat.succ_le_succ_iff] using within
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
          have nextAligned (nextSource : NextSeed → Config Player L
                ((name, .commitment owner payload) :: Γ))
              (nextRegistryEq : ∀ point, (nextSource point).registry = nextRegistry point.val.1)
              (nextRevelationsEq : ∀ point, @Config.revelations Player L _ (nextSource point) =
                @nextRevelations point.val.1)
              (point : NextSeed) : CompiledPolicySuffix setup.program wholeProfile next
              (afterCommit profile) tailRefs (nextSource point).revelations
              (nextSource point).registry tailEmbedding tailBefore (offset + 1) := by
            rw [nextRegistryEq, nextRevelationsEq]
            simpa only [nextRegistry, nextRevelations, commitSuccessor, tailRefs, tailEmbedding,
              OutputEmbedding.ref] using
              (aligned point.val.1).commitTail setup.program wholeProfile fresh guard next profile
                refs (source point.val.1).revelations (source point.val.1).registry
                  embedding refsBefore offset
          have nextEffective (nextSource : NextSeed → Config Player L
                ((name, .commitment owner payload) :: Γ))
              (nextRegistryEq : ∀ point, (nextSource point).registry = nextRegistry point.val.1)
              (nextRevelationsEq : ∀ point, @Config.revelations Player L _ (nextSource point) =
                @nextRevelations point.val.1)
              (point : NextSeed) (player : Player) :
              ((afterCommit profile) player).EffectiveDisclosures next (nextSource point).registry
                (nextSource point).revelations := by
            rw [nextRegistryEq, nextRevelationsEq]
            exact effective point.val.1 player
          have planEq : ((List.finRange (eventCount (.commit name owner fresh guard next))).take
              (count + 1)).map embedding.event = event ::
                ((List.finRange (eventCount next)).take count).map tailEmbedding.event := by
            simp only [eventCount, List.finRange_succ, List.take_succ_cons, ← List.map_take,
              List.map_cons, List.map_map]
            rfl
          by_cases own : owner = who
          · subst owner
            obtain ⟨choice, configNoise, phaseJoint⟩ := asyncDeviator_binding_factorization
              contract turns wholeProfile who deviation fresh guard next profile refs embedding
              refsBefore offset prior source execution aligned checkpoint boundary bounded noise
              factor
            let stepSource := fun config : Config Player L Γ =>
              (choice (config.view who)).map (commitSuccessor name guard config)
            have phaseJoint' : advanced.map (fun point => (decode point.1 point.2,
                (runtime setup).bindingTraffic leaks who point.2)) =
                ((prior.map source).bind stepSource).bind fun config =>
                  (configNoise (config.view who)).map fun extra => (some (encoded config),
                    extra) := by
              simp only [advanced, PMF.map_bind, PMF.map_comp, Function.comp_def]
              exact phaseJoint
            obtain ⟨nextSource, nextCheckpoint, nextRegistryEq, nextRevelationsEq, _nextRead,
              nextMarginal, nextFactor⟩ := reconstruct_service_phase setup leaks who tailRefs
                (offset + 1) nextRegistry nextRevelations advanced encoded
                (Sum.inr_injective.comp (ProtocolState.entry_injective next)) decode (by
                  intro seed final
                  simp only [decode, decodeSourcePrefix?,
                    Option.map_map, Function.comp_def]
                  rfl) nextOrdered ((prior.map source).bind stepSource) configNoise phaseJoint'
            refine finishStep next (afterCommit profile) tailRefs tailEmbedding tailBefore
              nextSource (nextAligned nextSource nextRegistryEq nextRevelationsEq) nextCheckpoint
              (nextEffective nextSource nextRegistryEq nextRevelationsEq)
              configNoise nextFactor stepSource nextMarginal
              Sum.inr (fun view => view.bind (Sum.elim (fun _ => none) some)) ?_ ?_
              (fun policy => (fun _ view => choice view, policy)) ?_ planEq remaining
            · intro state
              cases state <;> rfl
            · intro point final
              rw [nextRegistryEq, nextRevelationsEq, decodeSourcePrefix?_commit]
              rfl
            · intro policy config
              rw [ProtocolState.behavioralStatePrefix_commit, afterCommit_update]
              simp only [stepSource, commitKernel, Function.update_self, PMF.bind_map,
                PMF.map_bind, Function.comp_def]
          · obtain ⟨configNoise, phaseJoint⟩ := asyncDeviation_binding_factorization contract
              timely turns wholeProfile who deviation own fresh guard next profile refs embedding
              refsBefore offset prior source execution aligned checkpoint boundary bounded noise
              factor
            let stepSource := fun config : Config Player L Γ =>
              (commitKernel profile (config.view owner)).map (commitSuccessor name guard config)
            have phaseJoint' : advanced.map (fun point => (decode point.1 point.2,
                (runtime setup).bindingTraffic leaks who point.2)) =
                ((prior.map source).bind stepSource).bind fun config =>
                  (configNoise (config.view who)).map fun extra => (some (encoded config),
                    extra) := by
              simp only [advanced, PMF.map_bind, PMF.map_comp, Function.comp_def]
              exact phaseJoint
            obtain ⟨nextSource, nextCheckpoint, nextRegistryEq, nextRevelationsEq, _nextRead,
              nextMarginal, nextFactor⟩ := reconstruct_service_phase setup leaks who tailRefs
                (offset + 1) nextRegistry nextRevelations advanced encoded
                (Sum.inr_injective.comp (ProtocolState.entry_injective next)) decode (by
                  intro seed final
                  simp only [decode, decodeSourcePrefix?,
                    Option.map_map, Function.comp_def]
                  rfl) nextOrdered ((prior.map source).bind stepSource) configNoise phaseJoint'
            refine finishStep next (afterCommit profile) tailRefs tailEmbedding tailBefore
              nextSource (nextAligned nextSource nextRegistryEq nextRevelationsEq) nextCheckpoint
              (nextEffective nextSource nextRegistryEq nextRevelationsEq)
              configNoise nextFactor stepSource nextMarginal
              Sum.inr (fun view => view.bind (Sum.elim (fun _ => none) some)) ?_ ?_
              (fun policy => ((profile who).1, policy)) ?_ planEq remaining
            · intro state
              cases state <;> rfl
            · intro point final
              rw [nextRegistryEq, nextRevelationsEq, decodeSourcePrefix?_commit]
              rfl
            · intro policy config
              rw [ProtocolState.behavioralStatePrefix_commit, afterCommit_update,
                commitKernel_update_foreign profile who own]
              simp only [stepSource, PMF.bind_map, PMF.map_bind, Function.comp_def]
      | @reveal Γ names published owner name payload fresh binding unresolved next =>
          have remaining : count ≤ eventCount next := by
            simpa only [eventCount, Nat.succ_le_succ_iff] using within
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
          have nextAligned (nextSource : NextSeed → Config Player L
                ((published, .publication payload) :: Γ))
              (nextRegistryEq : ∀ point, (nextSource point).registry = nextRegistry point.val.1)
              (nextRevelationsEq : ∀ point, @Config.revelations Player L _ (nextSource point) =
                @nextRevelations point.val.1)
              (point : NextSeed) : CompiledPolicySuffix setup.program wholeProfile next
              (afterReveal profile) tailRefs (nextSource point).revelations
              (nextSource point).registry tailEmbedding tailBefore (offset + 1) := by
            rw [nextRegistryEq, nextRevelationsEq]
            simpa only [nextRegistry, nextRevelations, revealSuccessor, tailRefs, tailEmbedding,
              OutputEmbedding.ref] using
              (aligned point.val.1).revealTail (whole := setup.program) (wholeProfile :=
                wholeProfile)
                fresh binding unresolved next profile refs (source point.val.1).revelations
                  (source point.val.1).registry embedding refsBefore offset
          have nextEffective (nextSource : NextSeed → Config Player L
                ((published, .publication payload) :: Γ))
              (nextRegistryEq : ∀ point, (nextSource point).registry = nextRegistry point.val.1)
              (nextRevelationsEq : ∀ point, @Config.revelations Player L _ (nextSource point) =
                @nextRevelations point.val.1)
              (point : NextSeed) (player : Player) :
              ((afterReveal profile) player).EffectiveDisclosures next (nextSource point).registry
                (nextSource point).revelations := by
            rw [nextRegistryEq, nextRevelationsEq]
            exact (effective point.val.1 player).2
          have planEq : ((List.finRange (eventCount
              (.reveal published owner name fresh binding unresolved next))).take
              (count + 1)).map embedding.event = event ::
                ((List.finRange (eventCount next)).take count).map tailEmbedding.event := by
            simp only [eventCount, List.finRange_succ, List.take_succ_cons, ← List.map_take,
              List.map_cons, List.map_map]
            rfl
          by_cases own : owner = who
          · subst owner
            obtain ⟨choice, configNoise, phaseJoint⟩ := asyncDeviator_reveal_factorization
              contract turns wholeProfile who deviation fresh binding unresolved next profile refs
              embedding refsBefore offset prior source execution aligned checkpoint boundary
              bounded noise factor
            let stepSource := fun config : Config Player L Γ =>
              (choice (config.view who)).map (revealSuccessor published binding config)
            have phaseJoint' : advanced.map (fun point => (decode point.1 point.2,
                (runtime setup).bindingTraffic leaks who point.2)) =
                ((prior.map source).bind stepSource).bind fun config =>
                  (configNoise (config.view who)).map fun extra => (some (encoded config),
                    extra) := by
              simp only [advanced, PMF.map_bind, PMF.map_comp, Function.comp_def]
              exact phaseJoint
            obtain ⟨nextSource, nextCheckpoint, nextRegistryEq, nextRevelationsEq, _nextRead,
              nextMarginal, nextFactor⟩ := reconstruct_service_phase setup leaks who tailRefs
                (offset + 1) nextRegistry nextRevelations advanced encoded
                (Sum.inr_injective.comp (ProtocolState.entry_injective next)) decode (by
                  intro seed final
                  simp only [decode, decodeSourcePrefix?,
                    Option.map_map, Function.comp_def]
                  rfl) nextOrdered ((prior.map source).bind stepSource) configNoise phaseJoint'
            refine finishStep next (afterReveal profile) tailRefs tailEmbedding tailBefore
              nextSource (nextAligned nextSource nextRegistryEq nextRevelationsEq) nextCheckpoint
              (nextEffective nextSource nextRegistryEq nextRevelationsEq)
              configNoise nextFactor stepSource nextMarginal
              Sum.inr (fun view => view.bind (Sum.elim (fun _ => none) some)) ?_ ?_
              (fun policy => (fun _ view => choice view, policy)) ?_ planEq remaining
            · intro state
              cases state <;> rfl
            · intro point final
              rw [nextRegistryEq, nextRevelationsEq, decodeSourcePrefix?_reveal]
              rfl
            · intro policy config
              rw [ProtocolState.behavioralStatePrefix_reveal, afterReveal_update]
              simp only [stepSource, revealKernel, Function.update_self, PMF.bind_map,
                PMF.map_bind, Function.comp_def]
          · obtain ⟨configNoise, phaseJoint⟩ := asyncDeviation_reveal_factorization contract
              timely turns wholeProfile who deviation own fresh binding unresolved next profile
              refs embedding refsBefore offset prior source execution aligned checkpoint boundary
              bounded (fun seed _ => effective seed owner) noise factor
            let stepSource := fun config : Config Player L Γ =>
              (revealKernel profile (config.view owner)).map (revealSuccessor published binding
                config)
            have phaseJoint' : advanced.map (fun point => (decode point.1 point.2,
                (runtime setup).bindingTraffic leaks who point.2)) =
                ((prior.map source).bind stepSource).bind fun config =>
                  (configNoise (config.view who)).map fun extra => (some (encoded config),
                    extra) := by
              simp only [advanced, PMF.map_bind, PMF.map_comp, Function.comp_def]
              exact phaseJoint
            obtain ⟨nextSource, nextCheckpoint, nextRegistryEq, nextRevelationsEq, _nextRead,
              nextMarginal, nextFactor⟩ := reconstruct_service_phase setup leaks who tailRefs
                (offset + 1) nextRegistry nextRevelations advanced encoded
                (Sum.inr_injective.comp (ProtocolState.entry_injective next)) decode (by
                  intro seed final
                  simp only [decode, decodeSourcePrefix?,
                    Option.map_map, Function.comp_def]
                  rfl) nextOrdered ((prior.map source).bind stepSource) configNoise phaseJoint'
            refine finishStep next (afterReveal profile) tailRefs tailEmbedding tailBefore
              nextSource (nextAligned nextSource nextRegistryEq nextRevelationsEq) nextCheckpoint
              (nextEffective nextSource nextRegistryEq nextRevelationsEq)
              configNoise nextFactor stepSource nextMarginal
              Sum.inr (fun view => view.bind (Sum.elim (fun _ => none) some)) ?_ ?_
              (fun policy => ((profile who).1, policy)) ?_ planEq remaining
            · intro state
              cases state <;> rfl
            · intro point final
              rw [nextRegistryEq, nextRevelationsEq, decodeSourcePrefix?_reveal]
              rfl
            · intro policy config
              rw [ProtocolState.behavioralStatePrefix_reveal, afterReveal_update,
                revealKernel_update_foreign profile who own]
              simp only [stepSource, PMF.bind_map, PMF.map_bind, Function.comp_def]


end Vegas
