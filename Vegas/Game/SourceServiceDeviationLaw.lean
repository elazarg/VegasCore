/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDeviationChoice

/-! # The source law of a permitted deviation

Against the timed calendar profile of a source profile, let one player follow
any policy of the permitted menu. Phase by phase, the decoded source state then
follows the source protocol in which every other player keeps its source policy
and the deviator follows a single source behavioral policy, built event by
event: in a phase of another player's event the deviator is silent and the
phase runs as under the timed profile; in a phase of its own event its choice
is a behavioral choice of its source view. Throughout, the deviator's native
traffic factors through its source view.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime
open GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Updates

variable {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {owner : Player}
  {payload : L.Ty}

private theorem afterSample_update {fresh : name ∉ Γ.map Prod.fst}
    {law : L.DistExpr (SourcePublicCtx L Γ) payload}
    {next : SourceProgram Player L ((name, .publicData payload) :: Γ) O}
    (profile : BehavioralProfile (.sample name fresh law next)) (who : Player)
    (policy : BehavioralPolicy who next) :
    afterSample (Function.update profile who policy) =
      Function.update (afterSample profile) who policy := by
  funext player
  by_cases same : player = who
  · subst player
    simp only [afterSample, Function.update_self]
  · simp only [afterSample, Function.update_of_ne same]

private theorem afterCommit_update {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O)}
    (profile : BehavioralProfile (.commit name owner fresh guard next)) (who : Player)
    (policy : BehavioralPolicy who (.commit name owner fresh guard next)) :
    afterCommit (Function.update profile who policy) =
      Function.update (afterCommit profile) who policy.2 := by
  funext player
  by_cases same : player = who
  · subst player
    simp only [afterCommit, Function.update_self]
  · simp only [afterCommit, Function.update_of_ne same]

private theorem afterReveal_update {published : VarId} {fresh : published ∉ Γ.map Prod.fst}
    {selected : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ O}
    {next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    (profile : BehavioralProfile (.reveal published owner name fresh selected unresolved next))
    (who : Player)
    (policy : BehavioralPolicy who (.reveal published owner name fresh selected unresolved next)) :
    afterReveal (Function.update profile who policy) =
      Function.update (afterReveal profile) who policy.2 := by
  funext player
  by_cases same : player = who
  · subst player
    simp only [afterReveal, Function.update_self]
  · simp only [afterReveal, Function.update_of_ne same]

private theorem commitKernel_update_foreign {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O)}
    (profile : BehavioralProfile (.commit name owner fresh guard next)) (who : Player)
    (other : owner ≠ who)
    (policy : BehavioralPolicy who (.commit name owner fresh guard next)) :
    commitKernel (Function.update profile who policy) = commitKernel profile := by
  simp only [commitKernel, Function.update_of_ne other]

private theorem revealKernel_update_foreign {published : VarId}
    {fresh : published ∉ Γ.map Prod.fst}
    {selected : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ O}
    {next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    (profile : BehavioralProfile (.reveal published owner name fresh selected unresolved next))
    (who : Player) (other : owner ≠ who)
    (policy : BehavioralPolicy who (.reveal published owner name fresh selected unresolved next)) :
    revealKernel (Function.update profile who policy) = revealKernel profile := by
  simp only [revealKernel, Function.update_of_ne other]

end Updates

variable [Fintype Player]

/-- **Whole-prefix induction for one permitted deviation.** Against the timed
calendar profile of a source profile, one player follows an arbitrary policy of
the permitted menu. The decoded source state then has the law of the source
protocol in which that player follows a single source behavioral policy,
admitted at the commitment interface, and every other player keeps its source
policy; jointly, the deviator's native traffic depends on the source state only
through the deviator's source view. -/
theorem sourceServiceDeviation_prefix_joint_factorization
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (timing : TimingLaw setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (wholeProfile : BehavioralProfile setup.program)
    (who : Player) (deviation : (application setup leaks).Policy)
    (lawful : ∀ past view response, response ∈ (deviation past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (covered : ∀ player, (sourceServiceMenu setup leaks bounds rosters).Admissible
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) player
      (Function.update (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) who
        deviation player)) :
    let players := Function.update (sourceServiceTimedPolicy setup leaks rosters timing
      wholeProfile) who deviation
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
      (∀ seed, execution seed ∈ ((initialLaw setup).bind fun initial =>
        (runtime setup).runInteractionPlan leaks players network
          (rosterPlanPrefix setup rosters offset)
          (ReactiveApplication.Execution.initial (application setup leaks) initial)).support) →
      (∀ seed player, (profile player).EffectiveDisclosures program (source seed).registry
        (source seed).revelations) →
      (∀ player, (profile player).Admitted program (CommitmentInterface.values program)) →
      ∀ (noise : DecisionView who Γ → PMF _),
      prior.map (fun seed => (source seed,
          (runtime setup).bindingTraffic leaks who (execution seed))) =
        (prior.map source).bind (fun config =>
          (noise (config.view who)).map fun extra => (config, extra)) →
      count ≤ eventCount program →
      ∃ policy : BehavioralPolicy who program,
        policy.Admitted program (CommitmentInterface.values program) ∧
        ∃ nextNoise : Option (ProtocolView who program) → PMF _,
          (prior.bind fun seed =>
            ((runtime setup).runInteractionPlan leaks players network
              (((List.finRange (eventCount program)).take count).flatMap fun index =>
                rosterBlock setup rosters (embedding.event index)) (execution seed)).map
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
        _aligned checkpoint _supported _effective admitted noise factor _within
      obtain ⟨nextNoise, nextFactor⟩ := ProtocolView.entry_noise_factor program who prior source
        (fun seed => (runtime setup).bindingTraffic leaks who (execution seed)) noise factor
      refine ⟨profile who, admitted who, nextNoise, ?_⟩
      dsimp only at nextFactor
      simp only [List.take_zero, List.flatMap_nil, runInteractionPlan,
        Function.iterate_zero, id_eq, ← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind,
        PMF.pure_bind]
      simp only [← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
        at nextFactor
      refine Eq.trans (bind_congr_on_support _ fun seed _ => ?_) nextFactor
      rw [(checkpoint seed).decode program embedding.ref]
  | succ count ih =>
      intro Γ names program profile refs embedding refsBefore offset Seed prior source execution
        aligned checkpoint supported effective admitted noise factor within
      let app := application setup leaks
      let index : Fin (eventCount program) := ⟨0, by omega⟩
      let event : (graph setup).EventId := embedding.event index
      have eventRank : event.val = offset := by
        simpa only [event, index, Nat.add_zero] using
          (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
      have offsetBound : offset ≤ eventCount setup.program := by
        have counted := (aligned prior.support_nonempty.choose).graphSuffix.countEq
        omega
      have actualFacts (seed : Seed) := sourceService_prefix_boundary_of_checkpoint setup leaks
        bounds values capacity rosters opportunities network players covered
          offset offsetBound (execution seed) (supported seed) (source seed) refs (checkpoint seed)
      let initial := fun seed => (actualFacts seed).1.choose
      have boundary (seed : Seed) : ServiceBoundary setup leaks rosters (initial seed)
          (source seed) refs offset (execution seed) := (actualFacts seed).1.choose_spec.2
      have boundaryOrigins (seed : Seed) :
          (runtime setup).ResolutionEvidenceOrigins leaks (execution seed) := (actualFacts seed).2
      have sole (seed : Seed) : (execution seed).application.publicView.SoleReady event :=
        soleReady_of_ready setup (execution seed).application
          ((boundary seed).ready event eventRank)
      have nextPhysical (seed : Seed) (final : app.Execution)
          (moved : final ∈ ((runtime setup).runInteractionPlan leaks players network
            (rosterBlock setup rosters event) (execution seed)).support) :
          final ∈ ((initialLaw setup).bind fun start =>
            (runtime setup).runInteractionPlan leaks players network
              (rosterPlanPrefix setup rosters (offset + 1))
              (ReactiveApplication.Execution.initial app start)).support := by
        obtain ⟨start, startSupport, prefixSupport⟩ :=
          Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported seed)
        rw [← eventRank, rosterPlanPrefix_succ]
        rw [PMF.support_bind]
        apply Set.mem_iUnion₂.mpr
        refine ⟨start, startSupport, ?_⟩
        rw [runInteractionPlan_append]
        rw [PMF.support_bind]
        apply Set.mem_iUnion₂.mpr
        exact ⟨execution seed, by simpa only [eventRank] using prefixSupport, moved⟩
      let advanced := prior.bind fun seed =>
        ((runtime setup).runInteractionPlan leaks players network
          (rosterBlock setup rosters event) (execution seed)).map fun final => (seed, final)
      let NextSeed := {point : Seed × app.Execution // point ∈ advanced.support}
      let nextPrior : PMF NextSeed := pmfToSubtype advanced (fun _ member => member)
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
        rw [PMF.support_bind] at member
        obtain ⟨seed, selected, moved⟩ := Set.mem_iUnion₂.mp member
        rw [PMF.support_map] at moved
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
          (nextEffective : ∀ point player, (tailProfile player).EffectiveDisclosures tail
            (nextSource point).registry (nextSource point).revelations)
          (nextAdmitted : ∀ player, (tailProfile player).Admitted tail
            (CommitmentInterface.values tail))
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
          (buildAdmitted : ∀ policy, policy.Admitted tail (CommitmentInterface.values tail) →
            (build policy).Admitted program (CommitmentInterface.values program))
          (kernel : ∀ policy config,
            ((fun law => law.bind (ProtocolState.behavioralStateStep program
              (Function.update profile who (build policy))))^[count + 1]
              (PMF.pure (ProtocolState.entry program config))) =
            ((stepSource config).bind fun next =>
              ((fun law => law.bind (ProtocolState.behavioralStateStep tail
                (Function.update tailProfile who policy)))^[count]
                (PMF.pure (ProtocolState.entry tail next)))).map lift)
          (planEq : (((List.finRange (eventCount program)).take (count + 1)).flatMap
            fun index => rosterBlock setup rosters (embedding.event index)) =
            rosterBlock setup rosters event ++
              (((List.finRange (eventCount tail)).take count).flatMap fun index =>
                rosterBlock setup rosters (tailEmbedding.event index)))
          (withinTail : count ≤ eventCount tail) :
          ∃ policy : BehavioralPolicy who program,
            policy.Admitted program (CommitmentInterface.values program) ∧
            ∃ nextNoise : Option (ProtocolView who program) → PMF _,
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
                          (runtime setup).bindingTraffic leaks who final)) =
                (prior.bind fun seed =>
                  ((fun law => law.bind (ProtocolState.behavioralStateStep program
                    (Function.update profile who policy)))^[count + 1]
                    (PMF.pure (ProtocolState.entry program (source seed)))).map some).bind
                      fun state => (nextNoise (state.map (ProtocolState.observe who program))).map
                        fun extra => (state, extra) := by
        obtain ⟨tailPolicy, tailAdmitted, tailNoise, tailLaw⟩ := ih tail tailProfile tailRefs
          tailEmbedding tailBefore (offset + 1) nextPrior nextSource nextExecution nextAligned
          nextCheckpoint nextReached nextEffective nextAdmitted nextNoise nextFactor withinTail
        refine ⟨build tailPolicy, buildAdmitted tailPolicy tailAdmitted, ?_⟩
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
            ((runtime setup).runInteractionPlan leaks players network
              (((List.finRange (eventCount program)).take (count + 1)).flatMap fun index =>
                rosterBlock setup rosters (embedding.event index)) (execution seed)).map
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
            ((runtime setup).runInteractionPlan leaks players network remainingPlan point.2).map
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
                runInteractionPlan_append, PMF.map_bind, remainingPlan, Function.comp_def]
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
              source execution aligned (fun seed => boundary seed)
              network who noise factor
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
          let configNoise := fun view => phaseNoise (some (Sum.inr
            (sourceEntryObservation who next view)))
          have phaseJoint : advanced.map (fun point => (decode point.1 point.2,
              (runtime setup).bindingTraffic leaks who point.2)) =
              ((prior.map source).bind stepSource).bind fun config =>
                (configNoise (config.view who)).map fun extra => (some (encoded config),
                  extra) := by
            have fact := phaseFactor
            rw [phaseMarginal] at fact
            simp only [advanced, PMF.map_bind, PMF.map_comp, Function.comp_def]
            have block (seed : Seed) : (runtime setup).runInteractionPlan leaks players network
                (rosterBlock setup rosters event) (execution seed) =
                (runtime setup).runInteractionPlan leaks
                  (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
                  ((rosters event).map ServiceInstruction.player ++
                    (.sample event :: List.replicate (event.val + 1) .tick ++
                      [.expire event])) (execution seed) := by
              rw [deviation_foreign_block setup leaks bounds rosters timing wholeProfile who
                deviation lawful network event (by rw [chance]; exact fun none => by cases none)
                (execution seed) (sole seed)]
              simp only [rosterBlock, chance, List.append_assoc, List.singleton_append]
            change (prior.bind fun seed =>
              ((runtime setup).runInteractionPlan leaks players network
                (rosterBlock setup rosters event) (execution seed)).map fun final =>
                  (decode seed final, (runtime setup).bindingTraffic leaks who final)) = _
            simp only [block]
            simpa only [stepSource, configNoise, encoded, decode, PMF.bind_bind,
              PMF.bind_map, Option.map_some, ProtocolState.observe, Sum.elim_inr,
              observe_entry_eq_sourceEntryObservation, Function.comp_def] using fact
          obtain ⟨nextSource, nextCheckpoint, nextRegistryEq, nextRevelationsEq, _nextRead,
            nextMarginal, nextFactor⟩ := reconstruct_service_phase setup leaks who tailRefs
              (offset + 1) nextRegistry nextRevelations advanced encoded
              (Sum.inr_injective.comp (ProtocolState.entry_injective next)) decode (by
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
          have nextEffective (point : NextSeed) (player : Player) :
              ((afterSample profile) player).EffectiveDisclosures next (nextSource point).registry
                (nextSource point).revelations := by
            rw [nextRegistryEq, nextRevelationsEq]
            exact effective point.val.1 player
          refine finishStep next (afterSample profile) tailRefs tailEmbedding tailBefore nextSource
            nextAligned nextCheckpoint nextEffective (fun player => admitted player) configNoise
            nextFactor stepSource nextMarginal Sum.inr
            (fun view => view.bind (Sum.elim (fun _ => none) some)) ?_ ?_ (fun policy => policy)
            (fun _ allowed => allowed) ?_ ?_ remaining
          · intro state
            cases state <;> rfl
          · intro point final
            rw [nextRegistryEq, nextRevelationsEq, decodeSourcePrefix?_sample]
            rfl
          · intro policy config
            rw [ProtocolState.behavioralStatePrefix_sample, afterSample_update]
            simp only [stepSource, PMF.bind_map, PMF.map_bind, Function.comp_def]
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
          have planEq : (((List.finRange (eventCount (.commit name owner fresh guard next))).take
              (count + 1)).flatMap fun index => rosterBlock setup rosters (embedding.event index)) =
              rosterBlock setup rosters event ++
                (((List.finRange (eventCount next)).take count).flatMap fun index =>
                  rosterBlock setup rosters (tailEmbedding.event index)) := by
            simp only [eventCount, List.finRange_succ, List.take_succ_cons, ← List.map_take,
              List.flatMap_cons, List.flatMap_map]
            rfl
          by_cases own : owner = who
          · subst owner
            obtain ⟨choice, choiceSupport, configNoise, phaseJoint⟩ :=
              sourceService_deviator_binding_factorization setup leaks bounds values capacity
                rosters opportunities timing wholeProfile who deviation lawful fresh guard next
                profile refs embedding refsBefore offset prior initial source execution aligned
                (fun seed _ => boundary seed) network noise factor
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
              (fun player => (admitted player).2) configNoise nextFactor stepSource nextMarginal
              Sum.inr (fun view => view.bind (Sum.elim (fun _ => none) some)) ?_ ?_
              (fun policy => (fun _ view => choice view, policy)) ?_ ?_ planEq remaining
            · intro state
              cases state <;> rfl
            · intro point final
              rw [nextRegistryEq, nextRevelationsEq, decodeSourcePrefix?_commit]
              rfl
            · intro policy allowed
              refine ⟨fun _ view result member => ?_, allowed⟩
              rcases choiceSupport view result member with fallback | ⟨value, rfl⟩
              · exact (admitted who).1 rfl view result fallback
              · exact CommitmentAdmission.admits_success _ value
            · intro policy config
              rw [ProtocolState.behavioralStatePrefix_commit, afterCommit_update]
              simp only [stepSource, commitKernel, Function.update_self, PMF.bind_map,
                PMF.map_bind, Function.comp_def]
          · obtain ⟨phaseNoise, phaseFactor, phaseMarginal⟩ :=
              sourceService_binding_prefix_factorization setup leaks bounds rosters timing fresh
                guard next wholeProfile profile refs embedding refsBefore offset prior initial
                source execution aligned (fun seed _ => boundary seed)
                network who noise factor
            let stepSource := fun config : Config Player L Γ =>
              (commitKernel profile (config.view owner)).map (commitSuccessor name guard config)
            let configNoise := fun view => phaseNoise (some (Sum.inr
              (sourceEntryObservation who next view)))
            have phaseJoint : advanced.map (fun point => (decode point.1 point.2,
                (runtime setup).bindingTraffic leaks who point.2)) =
                ((prior.map source).bind stepSource).bind fun config =>
                  (configNoise (config.view who)).map fun extra => (some (encoded config),
                    extra) := by
              have fact := phaseFactor
              rw [phaseMarginal] at fact
              simp only [advanced, PMF.map_bind, PMF.map_comp, Function.comp_def]
              have block (seed : Seed) : (runtime setup).runInteractionPlan leaks players network
                  (rosterBlock setup rosters event) (execution seed) =
                  (runtime setup).runInteractionPlan leaks
                    (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
                    ((rosters event).map ServiceInstruction.player ++
                      (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++
                        [.expire event])) (execution seed) := by
                have foreign : (graph setup).actor? event ≠ some who := by
                  rw [owned]
                  exact fun same => own (Option.some.inj same)
                rw [deviation_foreign_block setup leaks bounds rosters timing wholeProfile who
                  deviation lawful network event foreign (execution seed) (sole seed),
                  rosterBlock_of_owner setup rosters event owner owned]
                simp only [List.append_assoc, List.singleton_append]
              change (prior.bind fun seed =>
                ((runtime setup).runInteractionPlan leaks players network
                  (rosterBlock setup rosters event) (execution seed)).map fun final =>
                    (decode seed final, (runtime setup).bindingTraffic leaks who final)) = _
              simp only [block]
              simpa only [stepSource, configNoise, encoded, decode, PMF.bind_bind,
                PMF.bind_map, Option.map_some, ProtocolState.observe, Sum.elim_inr,
                observe_entry_eq_sourceEntryObservation, Function.comp_def] using fact
            obtain ⟨nextSource, nextCheckpoint, nextRegistryEq, nextRevelationsEq, _nextRead,
              nextMarginal, nextFactor⟩ := reconstruct_service_phase setup leaks who tailRefs
                (offset + 1) nextRegistry nextRevelations advanced encoded
                (Sum.inr_injective.comp (ProtocolState.entry_injective next)) decode (by
                  intro seed final
                  simp only [decode, decodeSourcePrefix?,
                    Option.map_map, Function.comp_def]
                  rfl) nextOrdered ((prior.map source).bind stepSource) configNoise phaseJoint
            refine finishStep next (afterCommit profile) tailRefs tailEmbedding tailBefore
              nextSource (nextAligned nextSource nextRegistryEq nextRevelationsEq) nextCheckpoint
              (nextEffective nextSource nextRegistryEq nextRevelationsEq)
              (fun player => (admitted player).2) configNoise nextFactor stepSource nextMarginal
              Sum.inr (fun view => view.bind (Sum.elim (fun _ => none) some)) ?_ ?_
              (fun policy => ((profile who).1, policy)) ?_ ?_ planEq remaining
            · intro state
              cases state <;> rfl
            · intro point final
              rw [nextRegistryEq, nextRevelationsEq, decodeSourcePrefix?_commit]
              rfl
            · intro policy allowed
              exact ⟨(admitted who).1, allowed⟩
            · intro policy config
              rw [ProtocolState.behavioralStatePrefix_commit, afterCommit_update,
                commitKernel_update_foreign profile who own]
              simp only [stepSource, PMF.bind_map, PMF.map_bind, Function.comp_def]
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
          have planEq : (((List.finRange (eventCount
              (.reveal published owner name fresh binding unresolved next))).take
              (count + 1)).flatMap fun index => rosterBlock setup rosters (embedding.event index)) =
              rosterBlock setup rosters event ++
                (((List.finRange (eventCount next)).take count).flatMap fun index =>
                  rosterBlock setup rosters (tailEmbedding.event index)) := by
            simp only [eventCount, List.finRange_succ, List.take_succ_cons, ← List.map_take,
              List.flatMap_cons, List.flatMap_map]
            rfl
          by_cases own : owner = who
          · subst owner
            obtain ⟨choice, configNoise, phaseJoint⟩ :=
              sourceService_deviator_reveal_factorization setup leaks bounds rosters timing
                wholeProfile who deviation lawful fresh binding unresolved next profile refs
                embedding refsBefore offset prior initial source execution aligned
                (fun seed _ => boundary seed) network noise factor
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
              (fun player => admitted player) configNoise nextFactor stepSource nextMarginal
              Sum.inr (fun view => view.bind (Sum.elim (fun _ => none) some)) ?_ ?_
              (fun policy => (fun _ view => choice view, policy)) (fun _ allowed => allowed)
              ?_ planEq remaining
            · intro state
              cases state <;> rfl
            · intro point final
              rw [nextRegistryEq, nextRevelationsEq, decodeSourcePrefix?_reveal]
              rfl
            · intro policy config
              rw [ProtocolState.behavioralStatePrefix_reveal, afterReveal_update]
              simp only [stepSource, revealKernel, Function.update_self, PMF.bind_map,
                PMF.map_bind, Function.comp_def]
          · obtain ⟨phaseNoise, phaseFactor, phaseMarginal⟩ :=
              sourceService_reveal_prefix_factorization setup leaks rosters timing fresh
                binding unresolved next wholeProfile profile refs embedding refsBefore offset
                  prior initial
                source execution aligned (fun seed _ => boundary seed)
                (fun seed _ => boundaryOrigins seed) (fun seed _ => effective seed owner)
                network who noise factor
            let stepSource := fun config : Config Player L Γ =>
              (revealKernel profile (config.view owner)).map (revealSuccessor published binding
                config)
            let configNoise := fun view => phaseNoise (some (Sum.inr
              (sourceEntryObservation who next view)))
            have phaseJoint : advanced.map (fun point => (decode point.1 point.2,
                (runtime setup).bindingTraffic leaks who point.2)) =
                ((prior.map source).bind stepSource).bind fun config =>
                  (configNoise (config.view who)).map fun extra => (some (encoded config),
                    extra) := by
              have fact := phaseFactor
              rw [phaseMarginal] at fact
              simp only [advanced, PMF.map_bind, PMF.map_comp, Function.comp_def]
              have block (seed : Seed) : (runtime setup).runInteractionPlan leaks players network
                  (rosterBlock setup rosters event) (execution seed) =
                  (runtime setup).runInteractionPlan leaks
                    (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
                    ((rosters event).map ServiceInstruction.player ++
                      (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++
                        [.expire event])) (execution seed) := by
                have foreign : (graph setup).actor? event ≠ some who := by
                  rw [owned]
                  exact fun same => own (Option.some.inj same)
                rw [deviation_foreign_block setup leaks bounds rosters timing wholeProfile who
                  deviation lawful network event foreign (execution seed) (sole seed),
                  rosterBlock_of_owner setup rosters event owner owned]
                simp only [List.append_assoc, List.singleton_append]
              change (prior.bind fun seed =>
                ((runtime setup).runInteractionPlan leaks players network
                  (rosterBlock setup rosters event) (execution seed)).map fun final =>
                    (decode seed final, (runtime setup).bindingTraffic leaks who final)) = _
              simp only [block]
              simpa only [stepSource, configNoise, encoded, decode, PMF.bind_bind,
                PMF.bind_map, Option.map_some, ProtocolState.observe, Sum.elim_inr,
                observe_entry_eq_sourceEntryObservation, Function.comp_def] using fact
            obtain ⟨nextSource, nextCheckpoint, nextRegistryEq, nextRevelationsEq, _nextRead,
              nextMarginal, nextFactor⟩ := reconstruct_service_phase setup leaks who tailRefs
                (offset + 1) nextRegistry nextRevelations advanced encoded
                (Sum.inr_injective.comp (ProtocolState.entry_injective next)) decode (by
                  intro seed final
                  simp only [decode, decodeSourcePrefix?,
                    Option.map_map, Function.comp_def]
                  rfl) nextOrdered ((prior.map source).bind stepSource) configNoise phaseJoint
            refine finishStep next (afterReveal profile) tailRefs tailEmbedding tailBefore
              nextSource (nextAligned nextSource nextRegistryEq nextRevelationsEq) nextCheckpoint
              (nextEffective nextSource nextRegistryEq nextRevelationsEq)
              (fun player => admitted player) configNoise nextFactor stepSource nextMarginal
              Sum.inr (fun view => view.bind (Sum.elim (fun _ => none) some)) ?_ ?_
              (fun policy => ((profile who).1, policy)) (fun _ allowed => allowed) ?_ planEq
              remaining
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
