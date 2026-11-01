/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.AsyncDeviationChoice
import Vegas.Game.SourceServiceAsyncStep
import Vegas.Game.SourceServiceDeviationChoice
import Vegas.Game.SourceServiceFactorization

/-! # Source realization of a physical deviation

Structural induction on source instructions carries one typed source checkpoint
and an automatic-completion path to the actual ledger configuration. Joint
successor/traffic laws retain the source information boundary; terminal source
configurations are frozen under all remaining physical rounds.
-/

noncomputable section
namespace Vegas
open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (horizon : Nat) (scheduler : (application setup runtime leaks).Scheduler)
  (players : Player → (application setup runtime leaks).Policy)
  (wholeProfile : BehavioralProfile setup.program) (who : Player)

/-- Every coupled physical continuation of a source suffix has the terminal law
of one source behavioral deviation. The simulation retains typed checkpoints,
automatic completion paths and traffic conditional on the player's source view. -/
private def SourceDeviationLaw {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat) : Prop :=
  ∀ {Seed : Type} (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (ghost : Seed → EventGraphRuntime.State (graph setup))
    (execution : Seed → (application setup runtime leaks).Execution),
    (∀ seed, CompiledPolicySuffix setup.program wholeProfile program profile refs
      (source seed).revelations (source seed).registry embedding refsBefore rank) →
    (∀ seed, SourceCheckpoint setup (source seed) refs rank (ghost seed).config) →
    (∀ seed, ∃ reached : EventGraphRuntime.State (graph setup),
      Relation.ReflTransGen EventGraphRuntime.State.AutomaticStep (ghost seed) reached ∧
        reached.config = (execution seed).application.config) →
    (∀ seed ∈ prior.support, ∃ actualRank,
      CompletionBoundary setup leaks scheduler players actualRank (execution seed)) →
    (∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon) →
    (∀ seed player, (profile player).EffectiveDisclosures program
      (source seed).registry (source seed).revelations) →
    ∀ noise : DecisionView who Γ → PMF _,
    prior.map (fun seed => (source seed, runtime.bindingTraffic leaks who (execution seed))) =
      (prior.map source).bind (fun config =>
        (noise (config.view who)).map fun traffic => (config, traffic)) →
    ∃ policy : BehavioralPolicy who program,
      (prior.bind fun seed =>
        ((application setup runtime leaks).runToHorizon scheduler players horizon
          (execution seed)).map fun final =>
            decodeConfig? setup.program program refs (source seed).revelations
              (source seed).registry embedding final.application.config.store
              final.application.config.history) =
        (prior.bind fun seed => SourceProgram.runFrom program
          (Function.update profile who policy) (source seed)).map some

/-- Terminal source configurations are frozen by subsequent physical rounds. -/
private theorem SourceDeviationLaw.terminal {Γ : SourceCtx Player L}
    (payoffs : List (Player × L.Expr (SourcePublicCtx L Γ) L.int))
    (profile : BehavioralProfile (.ret payoffs))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.ret payoffs))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat) :
    SourceDeviationLaw setup runtime leaks horizon scheduler players wholeProfile who
      (.ret payoffs) profile refs embedding refsBefore rank := by
  intro Seed prior source ghost execution aligned checkpoint lag _boundary _bounded _effective
    _noise _factor
  refine ⟨PUnit.unit, ?_⟩
  have full : rank = (graph setup).order.eventCount := by
    change rank = eventCount setup.program
    have counted := (aligned prior.support_nonempty.choose).graphSuffix.countEq
    simpa only [eventCount, Nat.add_zero] using counted
  have equal (seed : Seed) : (execution seed).application.config = (ghost seed).config := by
    obtain ⟨reached, path, ending⟩ := lag seed
    have noAuto : ∀ event, ¬ (ghost seed).AutomaticReady event := by
      intro event eligible
      have terminal : (ghost seed).config.cut.Terminal := by
        have ordered := (checkpoint seed).ordered
        rw [full] at ordered
        exact ordered.terminal
      apply eligible.1.1
      rw [terminal]
      exact Finset.mem_univ _
    have same := EventGraphRuntime.State.automatic_path_eq_of_quiescent path noAuto
    rw [same] at ending
    exact ending.symm
  rw [PMF.map_bind]
  apply bind_congr_on_support _
  intro seed _supported
  have terminal : (execution seed).application.config.cut.IsPrefix
      (graph setup).order.eventCount := by
    rw [equal seed, ← full]
    exact (checkpoint seed).ordered
  have decoded (final : (application setup runtime leaks).Execution)
      (reached : final ∈ ((application setup runtime leaks).runToHorizon scheduler players
        horizon (execution seed)).support) :
      decodeConfig? setup.program (.ret payoffs) refs (source seed).revelations
        (source seed).registry embedding final.application.config.store
        final.application.config.history = some (source seed) := by
    have unchanged := runRounds_config_terminal scheduler players _ (execution seed) final
      terminal reached
    rw [unchanged, equal seed]
    unfold decodeConfig?
    change (decodeState? refs (ghost seed).config.store).map _ = _
    rw [decodeState?_eq_some refs (source seed).state (ghost seed).config.store
      (checkpoint seed).agrees]
    simp only [Option.map_some, finalRegistry, finalRevelations,
      (checkpoint seed).history]
    change some {source seed with defaults := (ghost seed).config.defaults} = some (source seed)
    rw [(checkpoint seed).defaults]
  rw [map_congr_on_support _ (g := fun _ => some (source seed)) decoded,
    pmf_map_fun_const]
  simp only [SourceProgram.runFrom, PMF.pure_map]

private theorem automatic_stopped_boundary
    (event : (graph setup).EventId)
    (ghost caught : EventGraphRuntime.State (graph setup))
    (before after : (application setup runtime leaks).Execution)
    (ready : ghost.config.cut.Ready event)
    (lag : Relation.ReflTransGen EventGraphRuntime.State.AutomaticStep ghost caught)
    (ending : caught.config = before.application.config)
    (physical : ∃ actualRank,
      CompletionBoundary setup leaks scheduler players actualRank before)
    (bounded : before.environmentRecall.length ≤ horizon)
    (reached : after ∈ ((application setup runtime leaks).runUntilHorizon scheduler players
      (fun current => event ∈ current.application.config.cut.completed) horizon before).support)
    (completed : event ∈ after.application.config.cut.completed) :
    after.environmentRecall.length ≤ horizon ∧ ∃ actualRank,
      CompletionBoundary setup leaks scheduler players actualRank after := by
  by_cases already : event ∈ before.application.config.cut.completed
  · unfold ReactiveApplication.runUntilHorizon at reached
    rw [(application setup runtime leaks).runUntil_of_stop scheduler players _ _ before already,
      PMF.mem_support_pure_iff] at reached
    subst after
    exact ⟨bounded, physical⟩
  · have same := EventGraph.Config.Step.path_eq_of_ready_of_not_completed event
      (fun query queryReady =>
        setup.eventGraph.sequentialize_ready_unique _ queryReady ready)
      (ending ▸ already) (EventGraphRuntime.State.automatic_path_graph_steps lag)
    have equal : before.application.config = ghost.config := ending.symm.trans same
    have compiledPrefix : before.application.config.cut.IsPrefix event.val := by
      rw [equal]
      exact ⟨event.isLt.le, fun query =>
        setup.eventGraph.sequentialize_mem_completed_iff_lt_of_ready _ ready⟩
    obtain ⟨actualRank, boundary⟩ := physical
    have ranks : actualRank = event.val := boundary.ordered.unique compiledPrefix
    subst actualRank
    obtain ⟨boundedAfter, nextRank, _later, nextBoundary⟩ :=
      boundary.stopped runtime event before bounded after reached completed
    exact ⟨boundedAfter, nextRank, nextBoundary⟩

/-- A coupled successor distribution composes with its suffix's deviation law. -/
private theorem SourceDeviationLaw.finish
    {Γ Δ : SourceCtx Player L} {names tailNames : Finset VarId}
    (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (tail : SourceProgram Player L Δ tailNames) (tailProfile : BehavioralProfile tail)
    (tailRefs : ContextRefs (graphLayout setup.program) Δ)
    (tailEmbedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) tail)
    (tailBefore : ContextRefsBefore tailRefs tailEmbedding) (nextRank : Nat)
    (tailLaw : SourceDeviationLaw setup runtime leaks horizon scheduler players wholeProfile who
      tail tailProfile tailRefs tailEmbedding tailBefore nextRank)
    {Seed : Type} (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup runtime leaks).Execution)
    (staged : PMF (Seed × (application setup runtime leaks).Execution))
    (nextSource : {point // point ∈ staged.support} → Config Player L Δ)
    (nextGhost : {point // point ∈ staged.support} → EventGraphRuntime.State (graph setup))
    (nextAligned : ∀ point, CompiledPolicySuffix setup.program wholeProfile tail tailProfile
      tailRefs (nextSource point).revelations (nextSource point).registry tailEmbedding
      tailBefore nextRank)
    (nextCheckpoint : ∀ point, SourceCheckpoint setup (nextSource point) tailRefs nextRank
      (nextGhost point).config)
    (nextLag : ∀ point : {point // point ∈ staged.support},
      ∃ reached : EventGraphRuntime.State (graph setup),
        Relation.ReflTransGen EventGraphRuntime.State.AutomaticStep (nextGhost point) reached ∧
          reached.config = point.val.2.application.config)
    (nextBoundary : ∀ point : {point // point ∈ staged.support}, ∃ actualRank,
      CompletionBoundary setup leaks scheduler players actualRank point.val.2)
    (nextBounded : ∀ point : {point // point ∈ staged.support},
      point.val.2.environmentRecall.length ≤ horizon)
    (nextEffective : ∀ point player, (tailProfile player).EffectiveDisclosures tail
      (nextSource point).registry (nextSource point).revelations)
    (nextNoise : DecisionView who Δ → PMF _)
    (nextFactor :
      (pmfToSubtype staged (fun _ member => member)).map (fun point =>
        (nextSource point, runtime.bindingTraffic leaks who point.val.2)) =
      ((pmfToSubtype staged (fun _ member => member)).map nextSource).bind fun config =>
        (nextNoise (config.view who)).map fun traffic => (config, traffic))
    (stepSource : Config Player L Γ → PMF (Config Player L Δ))
    (nextMarginal : (pmfToSubtype staged (fun _ member => member)).map nextSource =
      (prior.map source).bind stepSource)
    (readResult : Config Player L tail.terminalCtx → Config Player L program.terminalCtx)
    (decodeLater : ∀ (point : {point // point ∈ staged.support})
      (final : (application setup runtime leaks).Execution),
      decodeConfig? setup.program program refs (source point.val.1).revelations
        (source point.val.1).registry embedding final.application.config.store
          final.application.config.history =
      (decodeConfig? setup.program tail tailRefs (nextSource point).revelations
        (nextSource point).registry tailEmbedding final.application.config.store
          final.application.config.history).map readResult)
    (build : BehavioralPolicy who tail → BehavioralPolicy who program)
    (sourceStep : ∀ policy config,
      SourceProgram.runFrom program (Function.update profile who (build policy)) config =
      ((stepSource config).bind fun next => SourceProgram.runFrom tail
        (Function.update tailProfile who policy) next).map readResult)
    (nativeStep :
      (prior.bind fun seed =>
        ((application setup runtime leaks).runToHorizon scheduler players horizon
          (execution seed)).map fun final => decodeConfig? setup.program program refs
            (source seed).revelations (source seed).registry embedding
            final.application.config.store final.application.config.history) =
      staged.bind fun point =>
        ((application setup runtime leaks).runToHorizon scheduler players horizon point.2).map
          fun final => decodeConfig? setup.program program refs (source point.1).revelations
            (source point.1).registry embedding final.application.config.store
            final.application.config.history) :
    ∃ policy : BehavioralPolicy who program,
      (prior.bind fun seed =>
        ((application setup runtime leaks).runToHorizon scheduler players horizon
          (execution seed)).map fun final => decodeConfig? setup.program program refs
            (source seed).revelations (source seed).registry embedding
            final.application.config.store final.application.config.history) =
        (prior.bind fun seed => SourceProgram.runFrom program
          (Function.update profile who policy) (source seed)).map some := by
  let nextPrior := pmfToSubtype staged (fun _ member => member)
  obtain ⟨policy, tailResult⟩ := tailLaw nextPrior nextSource nextGhost (fun point => point.val.2)
    nextAligned nextCheckpoint nextLag (fun point _ => nextBoundary point)
    (fun point _ => nextBounded point) nextEffective nextNoise nextFactor
  refine ⟨build policy, ?_⟩
  have nextNative : (staged.bind fun point =>
      ((application setup runtime leaks).runToHorizon scheduler players horizon point.2).map
        fun final => decodeConfig? setup.program program refs (source point.1).revelations
          (source point.1).registry embedding final.application.config.store
          final.application.config.history) =
      ((nextPrior.bind fun point =>
        ((application setup runtime leaks).runToHorizon scheduler players horizon point.val.2).map
          fun final => decodeConfig? setup.program tail tailRefs (nextSource point).revelations
            (nextSource point).registry tailEmbedding final.application.config.store
              final.application.config.history)).map (Option.map readResult) := by
    have recover := map_val_pmfToSubtype staged (fun _ member => member)
    conv_lhs => rw [← recover]
    rw [PMF.bind_map, PMF.map_bind]
    apply bind_congr_on_support _
    intro point _
    rw [PMF.map_comp]
    apply map_congr_on_support _
    intro final _
    exact decodeLater point final
  rw [nativeStep, nextNative, tailResult, PMF.map_comp]
  have pushed : (nextPrior.bind fun point => SourceProgram.runFrom tail
      (Function.update tailProfile who policy) (nextSource point)) =
      prior.bind fun seed => (stepSource (source seed)).bind fun config =>
        SourceProgram.runFrom tail (Function.update tailProfile who policy) config := by
    calc
      _ = (nextPrior.map nextSource).bind (SourceProgram.runFrom tail
          (Function.update tailProfile who policy)) := (PMF.bind_map _ _ _).symm
      _ = _ := by
        rw [nextMarginal, PMF.bind_bind, PMF.bind_map]
        rfl
  rw [pushed]
  simp only [PMF.map_bind, Option.map_some, Function.comp_def]
  apply bind_congr_on_support _
  intro seed _
  rw [sourceStep, PMF.map_comp, PMF.map_bind]
  rfl

/-- An instruction's joint successor and traffic law supplies the coupled prior
for the remaining source program. -/
private theorem SourceDeviationLaw.of_head
    {Γ Δ : SourceCtx Player L} {names tailNames : Finset VarId}
    (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (tail : SourceProgram Player L Δ tailNames) (tailProfile : BehavioralProfile tail)
    (tailRefs : ContextRefs (graphLayout setup.program) Δ)
    (tailEmbedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) tail)
    (tailBefore : ContextRefsBefore tailRefs tailEmbedding) (nextRank : Nat)
    (tailLaw : SourceDeviationLaw setup runtime leaks horizon scheduler players wholeProfile who
      tail tailProfile tailRefs tailEmbedding tailBefore nextRank)
    {Seed : Type} (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup runtime leaks).Execution)
    (phase : Seed → PMF (application setup runtime leaks).Execution)
    (advance : Seed → (application setup runtime leaks).Execution → Config Player L Δ)
    (stepSource : Config Player L Γ → PMF (Config Player L Δ))
    (nextNoise : DecisionView who Δ → PMF _)
    (joint : (prior.bind fun seed => (phase seed).map fun final =>
        (advance seed final, runtime.bindingTraffic leaks who final)) =
      ((prior.map source).bind stepSource).bind fun config =>
        (nextNoise (config.view who)).map fun traffic => (config, traffic))
    (aligned : ∀ seed final, CompiledPolicySuffix setup.program wholeProfile tail tailProfile
      tailRefs (advance seed final).revelations (advance seed final).registry
      tailEmbedding tailBefore nextRank)
    (effective : ∀ seed final player, (tailProfile player).EffectiveDisclosures tail
      (advance seed final).registry (advance seed final).revelations)
    (endpoint : ∀ seed ∈ prior.support, ∀ final ∈ (phase seed).support,
      ∃ native : EventGraphRuntime.State (graph setup),
        SourceCheckpoint setup (advance seed final) tailRefs nextRank native.config ∧
        (∃ caught : EventGraphRuntime.State (graph setup),
          Relation.ReflTransGen EventGraphRuntime.State.AutomaticStep native caught ∧
            caught.config = final.application.config) ∧
        (∃ actualRank, CompletionBoundary setup leaks scheduler players actualRank final) ∧
        final.environmentRecall.length ≤ horizon)
    (readResult : Config Player L tail.terminalCtx → Config Player L program.terminalCtx)
    (decodeLater : ∀ (seed : Seed)
      (stopped final : (application setup runtime leaks).Execution),
      decodeConfig? setup.program program refs (source seed).revelations
        (source seed).registry embedding final.application.config.store
          final.application.config.history =
      (decodeConfig? setup.program tail tailRefs (advance seed stopped).revelations
        (advance seed stopped).registry tailEmbedding final.application.config.store
          final.application.config.history).map readResult)
    (build : BehavioralPolicy who tail → BehavioralPolicy who program)
    (sourceStep : ∀ policy config,
      SourceProgram.runFrom program (Function.update profile who (build policy)) config =
      ((stepSource config).bind fun next => SourceProgram.runFrom tail
        (Function.update tailProfile who policy) next).map readResult)
    (markov : ∀ seed,
      (application setup runtime leaks).runToHorizon scheduler players horizon (execution seed) =
      (phase seed).bind
        ((application setup runtime leaks).runToHorizon scheduler players horizon)) :
    ∃ policy : BehavioralPolicy who program,
      (prior.bind fun seed =>
        ((application setup runtime leaks).runToHorizon scheduler players horizon
          (execution seed)).map fun final => decodeConfig? setup.program program refs
            (source seed).revelations (source seed).registry embedding
            final.application.config.store final.application.config.history) =
      (prior.bind fun seed => SourceProgram.runFrom program
        (Function.update profile who policy) (source seed)).map some := by
  let staged := prior.bind fun seed => (phase seed).map fun final => (seed, final)
  let Point := {point // point ∈ staged.support}
  let nextPrior := pmfToSubtype staged (fun _ member => member)
  let nextSource : Point → Config Player L Δ := fun point => advance point.val.1 point.val.2
  have supported (point : Point) : point.val.1 ∈ prior.support ∧
      point.val.2 ∈ (phase point.val.1).support := by
    have member := point.property
    change point.val ∈ (prior.bind fun seed =>
      (phase seed).map fun final => (seed, final)).support at member
    simp only [PMF.support_bind] at member
    obtain ⟨seed, present, later⟩ := Set.mem_iUnion₂.mp member
    obtain ⟨final, reached, equal⟩ := (PMF.mem_support_map_iff ..).mp later
    have parentEq : seed = point.val.1 := congrArg Prod.fst equal
    have finalEq : final = point.val.2 := congrArg Prod.snd equal
    rw [← parentEq, ← finalEq]
    exact ⟨present, reached⟩
  have witnesses (point : Point) := endpoint point.val.1 (supported point).1
    point.val.2 (supported point).2
  let nextGhost : Point → EventGraphRuntime.State (graph setup) :=
    fun point => (witnesses point).choose
  have nextJoint : nextPrior.map (fun point =>
      (nextSource point, runtime.bindingTraffic leaks who point.val.2)) =
      ((prior.map source).bind stepSource).bind fun config =>
        (nextNoise (config.view who)).map fun traffic => (config, traffic) := by
    have reduced := map_pmfToSubtype staged (fun _ member => member)
      (fun point => (advance point.1 point.2, runtime.bindingTraffic leaks who point.2))
    change _ = _ at reduced
    rw [reduced]
    simpa only [staged, PMF.map_bind, PMF.map_comp, Function.comp_def] using joint
  have nextMarginal : nextPrior.map nextSource = (prior.map source).bind stepSource := by
    have projected := congrArg (PMF.map Prod.fst) nextJoint
    simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, pmf_map_fun_const,
      PMF.bind_pure] using projected
  have nextFactor : nextPrior.map (fun point =>
      (nextSource point, runtime.bindingTraffic leaks who point.val.2)) =
      (nextPrior.map nextSource).bind fun config =>
        (nextNoise (config.view who)).map fun traffic => (config, traffic) := by
    rw [nextMarginal]
    exact nextJoint
  apply SourceDeviationLaw.finish setup runtime leaks horizon scheduler players wholeProfile who
    program profile refs embedding tail tailProfile tailRefs tailEmbedding tailBefore nextRank
    tailLaw prior source execution staged nextSource nextGhost
    (fun point => aligned point.val.1 point.val.2)
    (fun point => (witnesses point).choose_spec.1)
    (fun point => (witnesses point).choose_spec.2.1)
    (fun point => (witnesses point).choose_spec.2.2.1)
    (fun point => (witnesses point).choose_spec.2.2.2)
    (fun point => effective point.val.1 point.val.2) nextNoise nextFactor
    stepSource nextMarginal readResult
    (fun point => decodeLater point.val.1 point.val.2) build sourceStep
  simp only [staged, PMF.bind_bind, PMF.bind_map,
    Function.comp_def]
  apply bind_congr_on_support _
  intro seed _
  rw [markov seed, PMF.map_bind]

end Vegas


namespace Vegas
open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem SourceDeviationLaw.sample
    (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (horizon : Nat) (scheduler : (application setup runtime leaks).Scheduler)
    (complete : CompletesPlay runtime leaks (initialLaw setup) horizon scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (who : Player)
    (deviation : (application setup runtime leaks).Policy)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (distribution : L.DistExpr (SourcePublicCtx L Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: Γ) openNames)
    (profile : BehavioralProfile (.sample name fresh distribution next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.sample name fresh distribution next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat) :
    let index : Fin (eventCount (.sample name fresh distribution next)) :=
      ⟨0, by simp [eventCount]⟩
    let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
    let tailRefs := refs.cons (embedding.ref index)
    let tailBefore : ContextRefsBefore tailRefs tailEmbedding :=
      refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl
    let players := Function.update
      (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) who deviation
    SourceDeviationLaw setup runtime leaks horizon scheduler players wholeProfile who
      next (afterSample profile) tailRefs tailEmbedding tailBefore (rank + 1) →
    SourceDeviationLaw setup runtime leaks horizon scheduler players wholeProfile who
      (.sample name fresh distribution next) profile refs embedding refsBefore rank := by
  intro index tailEmbedding tailRefs tailBefore players tailLaw Seed prior source ghost execution
    aligned checkpoint lag boundary bounded effective noise factor
  let event := embedding.event index
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using
      (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
  have ownerless : (graph setup).actor? event = none := by
    change (toEventGraph setup.program).actor? event = none
    simpa [event, index, eventOwner?, eventCount] using
      (aligned prior.support_nonempty.choose).actorEq index
  have ready (seed : Seed) : (ghost seed).config.cut.Ready event := by
    have ordered := (checkpoint seed).ordered
    rw [← eventRank] at ordered
    exact ordered.ready event.isLt
  have actualEq (seed : Seed) : (execution seed).application.config = (ghost seed).config := by
    obtain ⟨caught, path, ending⟩ := lag seed
    have quiescent : ∀ query, ¬ (ghost seed).AutomaticReady query := by
      intro query eligible
      cases setup.eventGraph.sequentialize_ready_unique _ eligible.1 (ready seed)
      obtain ⟨owner, acting, _⟩ := eligible.owned
      rw [ownerless] at acting
      cases acting
    exact ending.symm.trans (congrArg EventGraphRuntime.State.config
      (EventGraphRuntime.State.automatic_path_eq_of_quiescent path quiescent))
  have actualCheckpoint (seed : Seed) :
      SourceCheckpoint setup (source seed) refs rank (execution seed).application.config := by
    rw [actualEq seed]
    exact checkpoint seed
  have actualBoundary (seed : Seed) (supported : seed ∈ prior.support) :
      CompletionBoundary setup leaks scheduler players rank (execution seed) := by
    obtain ⟨physicalRank, physical⟩ := boundary seed supported
    have same : physicalRank = rank := physical.ordered.unique (actualCheckpoint seed).ordered
    subst physicalRank
    exact physical
  obtain ⟨nextNoise, joint, endpoints⟩ := sourceService_chance_law runtime leaks complete bound
    turns wholeProfile who deviation fresh distribution next profile refs embedding refsBefore
    rank prior source execution aligned actualCheckpoint actualBoundary bounded noise factor
  let outputEq : (graph setup).outputLayout event = .publicData payload := by
    change outputLayout setup.program (embedding.event index) = _
    simpa [index, outputLayout, eventCount] using embedding.layout_eq index
  let pick := fun final : (application setup runtime leaks).Execution =>
    ((final.application.config.outputs event).map
      (cast (congrArg EventGraph.EventField.Value outputEq))).getD (L.someValue payload)
  let phase := fun seed => (application setup runtime leaks).runUntilHorizon scheduler players
    (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)
  let advance := fun seed final => sampleSuccessor name (source seed) (pick final)
  let stepSource := fun config : Config Player L Γ =>
    (L.evalDist distribution (sourcePublicEnv config.state)).map (sampleSuccessor name config)
  apply SourceDeviationLaw.of_head setup runtime leaks horizon scheduler players wholeProfile who
    (.sample name fresh distribution next) profile refs embedding next (afterSample profile)
    tailRefs tailEmbedding tailBefore (rank + 1) tailLaw prior source execution phase advance
    stepSource nextNoise joint (readResult := id) (build := id)
  · intro seed final
    exact CompiledPolicySuffix.sampleTail setup.program wholeProfile (_openNames := openNames)
      fresh distribution next
      profile refs (source seed).revelations (source seed).registry embedding refsBefore rank
      (aligned seed)
  · intro seed final player
    exact effective seed player
  · intro seed supported final reached
    obtain ⟨value, native, typed, drained, picked⟩ := endpoints seed supported final reached
    have completeAfter : event ∈ final.application.config.cut.completed := by
      rw [drained]
      apply EventGraph.Config.Step.path_completed_mono native.drain_graph_steps
      exact (typed.ordered.2 event).mpr (by omega)
    obtain ⟨caught, path, ending⟩ := lag seed
    obtain ⟨boundAfter, physicalAfter⟩ := automatic_stopped_boundary setup runtime leaks
      horizon scheduler players event (ghost seed) caught (execution seed) final (ready seed)
      path ending (boundary seed supported) (bounded seed supported) reached completeAfter
    refine ⟨native, ?_, ⟨native.drain, native.drain_trace, drained.symm⟩,
      physicalAfter, boundAfter⟩
    have pickEq : pick final = value := picked
    change SourceCheckpoint setup (sampleSuccessor name (source seed) (pick final))
      tailRefs (rank + 1) native.config
    rw [pickEq]
    simpa only [tailRefs, OutputEmbedding.ref, event, index] using typed
  · intro seed stopped final
    simp only [decodeConfig?, terminalRefsWith, finalRegistry, finalRevelations,
      advance, sampleSuccessor, Option.map_id]
    rfl
  · intro policy config
    simp only [stepSource, PMF.map_id, PMF.bind_map, SourceProgram.runFrom]
    rfl
  · intro seed
    exact (application setup runtime leaks).runToHorizon_eq_runUntilHorizon_bind scheduler
      players _ horizon (execution seed)

end Vegas


namespace Vegas
open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem SourceDeviationLaw.commit_owned
    (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (horizon : Nat) (scheduler : (application setup runtime leaks).Scheduler)
    (complete : CompletesPlay runtime leaks (initialLaw setup) horizon scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (who : Player)
    (deviation : (application setup runtime leaks).Policy)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ who name payload)
    (next : SourceProgram Player L ((name, .commitment who payload) :: Γ) (insert name openNames))
    (profile : BehavioralProfile (.commit name who fresh guard next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name who fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat) :
    let index : Fin (eventCount (.commit name who fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
    let tailRefs := refs.cons (embedding.ref index)
    let tailBefore : ContextRefsBefore tailRefs tailEmbedding :=
      refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl
    let players := Function.update
      (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) who deviation
    SourceDeviationLaw setup runtime leaks horizon scheduler players wholeProfile who
      next (afterCommit profile) tailRefs tailEmbedding tailBefore (rank + 1) →
    SourceDeviationLaw setup runtime leaks horizon scheduler players wholeProfile who
      (.commit name who fresh guard next) profile refs embedding refsBefore rank := by
  intro index tailEmbedding tailRefs tailBefore players tailLaw Seed prior source ghost execution
    aligned checkpoint lag boundary bounded effective noise factor
  let event := embedding.event index
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using
      (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
  have ready (seed : Seed) : (ghost seed).config.cut.Ready event := by
    have ordered := (checkpoint seed).ordered
    rw [← eventRank] at ordered
    exact ordered.ready event.isLt
  have alone : ∀ (cut : (graph setup).order.Cut) other,
      cut.Ready event → cut.Ready other → other = event := by
    intro cut other first second
    exact setup.eventGraph.sequentialize_ready_unique cut second first
  obtain ⟨kernel, nextNoise, joint, endpoints⟩ := sourceService_deviator_commit_law
    (setup := setup) (mode := .sequential) (deadline := runtime.deadline) complete bound turns
    wholeProfile who deviation fresh guard next profile refs embedding refsBefore rank alone
    prior source execution ghost aligned checkpoint (fun seed _ => lag seed) boundary bounded
    noise factor
  let pick := fun final : (application setup runtime leaks).Execution =>
    OwnAction.binding who name payload
      (((final.application.playerView who).observation.ownActions.find?
        (fun record => decide (record.event = event))).bind fun record =>
          record.decision.bind (decodeEventAction setup.program record.event))
  let phase := fun seed => (application setup runtime leaks).runUntilHorizon scheduler players
    (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)
  let advance := fun seed final => commitSuccessor name guard (source seed) (pick final)
  let stepSource := fun config : Config Player L Γ =>
    (kernel (config.view who)).map (commitSuccessor name guard config)
  let build : BehavioralPolicy who next →
      BehavioralPolicy who (.commit name who fresh guard next) :=
    fun policy => (fun _ view _ => kernel view, policy)
  apply SourceDeviationLaw.of_head setup runtime leaks horizon scheduler players wholeProfile who
    (.commit name who fresh guard next) profile refs embedding next (afterCommit profile)
    tailRefs tailEmbedding tailBefore (rank + 1) tailLaw prior source execution phase advance
    stepSource nextNoise joint (readResult := id) (build := build)
  · intro seed final
    exact CompiledPolicySuffix.commitTail setup.program wholeProfile
      (openNames := openNames) fresh guard next profile refs (source seed).revelations
      (source seed).registry embedding refsBefore rank (aligned seed)
  · intro seed final player
    exact effective seed player
  · intro seed supported final reached
    obtain ⟨choice, native, typed, nextLag, _active, picked⟩ :=
      endpoints seed supported final reached
    have completeAfter : event ∈ final.application.config.cut.completed := by
      obtain ⟨caught, path, ending⟩ := nextLag
      rw [← ending]
      apply EventGraph.Config.Step.path_completed_mono
        (EventGraphRuntime.State.automatic_path_graph_steps path)
      exact (typed.ordered.2 event).mpr (by omega)
    obtain ⟨caught, path, ending⟩ := lag seed
    obtain ⟨boundAfter, physicalAfter⟩ := automatic_stopped_boundary setup runtime leaks
      horizon scheduler players event (ghost seed) caught (execution seed) final (ready seed)
      path ending (boundary seed supported) (bounded seed supported) reached completeAfter
    refine ⟨native, ?_, nextLag, physicalAfter, boundAfter⟩
    have pickEq : pick final = choice := picked
    change SourceCheckpoint setup (commitSuccessor name guard (source seed) (pick final))
      tailRefs (rank + 1) native.config
    rw [pickEq]
    simpa only [tailRefs, OutputEmbedding.ref, event, index] using typed
  · intro seed stopped final
    simp only [decodeConfig?, terminalRefsWith, finalRegistry, finalRevelations,
      advance, commitSuccessor, Option.map_id]
    rfl
  · intro policy config
    simp only [stepSource, PMF.map_id, PMF.bind_map, Function.comp_def, SourceProgram.runFrom,
      afterCommit_update, build, commitKernel, Function.update_self]
    by_cases inactive : who ∈ config.defaulted
    · simp only [inactive, dite_true, PMF.pure_bind]
      have ignored : ∀ choice : Option (PublicationResult (L.Val payload)),
          commitSuccessor name guard config choice = commitSuccessor name guard config none := by
        intro choice
        simp only [commitSuccessor, inactive, ite_true]
      simp_rw [ignored]
      exact (PMF.bind_const _ _).symm
    · simp only [inactive, dite_false]
  · intro seed
    exact (application setup runtime leaks).runToHorizon_eq_runUntilHorizon_bind scheduler
      players _ horizon (execution seed)

private theorem SourceDeviationLaw.reveal_owned
    (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (horizon : Nat) (scheduler : (application setup runtime leaks).Scheduler)
    (complete : CompletesPlay runtime leaks (initialLaw setup) horizon scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (who : Player)
    (deviation : (application setup runtime leaks).Policy)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {payload : L.Ty} (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment who payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (openNames.erase name))
    (profile : BehavioralProfile (.reveal published who name fresh binding unresolved next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published who name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat) :
    let index : Fin (eventCount (.reveal published who name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
    let tailRefs := refs.cons (embedding.ref index)
    let tailBefore : ContextRefsBefore tailRefs tailEmbedding :=
      refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl
    let players := Function.update
      (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) who deviation
    SourceDeviationLaw setup runtime leaks horizon scheduler players wholeProfile who
      next (afterReveal profile) tailRefs tailEmbedding tailBefore (rank + 1) →
    SourceDeviationLaw setup runtime leaks horizon scheduler players wholeProfile who
      (.reveal published who name fresh binding unresolved next) profile refs embedding refsBefore
        rank := by
  intro index tailEmbedding tailRefs tailBefore players tailLaw Seed prior source ghost execution
    aligned checkpoint lag boundary bounded effective noise factor
  let event := embedding.event index
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using
      (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
  have ready (seed : Seed) : (ghost seed).config.cut.Ready event := by
    have ordered := (checkpoint seed).ordered
    rw [← eventRank] at ordered
    exact ordered.ready event.isLt
  have alone : ∀ (cut : (graph setup).order.Cut) other,
      cut.Ready event → cut.Ready other → other = event := by
    intro cut other first second
    exact setup.eventGraph.sequentialize_ready_unique cut second first
  obtain ⟨kernel, nextNoise, joint, endpoints⟩ := sourceService_deviator_reveal_law
    (setup := setup) (mode := .sequential) (deadline := runtime.deadline) complete bound turns
    wholeProfile who deviation fresh binding unresolved next profile refs embedding refsBefore rank
    alone
    prior source execution ghost aligned checkpoint (fun seed _ => lag seed) boundary bounded
    noise factor
  let pick := fun final : (application setup runtime leaks).Execution =>
    OwnAction.disclosure
      (((final.application.playerView who).observation.ownActions.find?
        (fun record => decide (record.event = event))).bind fun record =>
          record.decision.bind (decodeEventAction setup.program record.event))
  let phase := fun seed => (application setup runtime leaks).runUntilHorizon scheduler players
    (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)
  let advance := fun seed final => revealSuccessor published binding (source seed) (pick final)
  let stepSource := fun config : Config Player L Γ =>
    (kernel (config.view who)).map (revealSuccessor published binding config)
  let build : BehavioralPolicy who next →
      BehavioralPolicy who (.reveal published who name fresh binding unresolved next) :=
    fun policy => (fun _ view _ => kernel view, policy)
  apply SourceDeviationLaw.of_head setup runtime leaks horizon scheduler players wholeProfile who
    (.reveal published who name fresh binding unresolved next) profile refs embedding next
    (afterReveal profile)
    tailRefs tailEmbedding tailBefore (rank + 1) tailLaw prior source execution phase advance
    stepSource nextNoise joint (readResult := id) (build := build)
  · intro seed final
    exact CompiledPolicySuffix.revealTail setup.program wholeProfile
      (openNames := openNames) fresh binding unresolved next profile refs (source seed).revelations
      (source seed).registry embedding refsBefore rank (aligned seed)
  · intro seed final player
    exact (effective seed player).2
  · intro seed supported final reached
    obtain ⟨choice, native, typed, nextLag, _active, picked⟩ :=
      endpoints seed supported final reached
    have completeAfter : event ∈ final.application.config.cut.completed := by
      obtain ⟨caught, path, ending⟩ := nextLag
      rw [← ending]
      apply EventGraph.Config.Step.path_completed_mono
        (EventGraphRuntime.State.automatic_path_graph_steps path)
      exact (typed.ordered.2 event).mpr (by omega)
    obtain ⟨caught, path, ending⟩ := lag seed
    obtain ⟨boundAfter, physicalAfter⟩ := automatic_stopped_boundary setup runtime leaks
      horizon scheduler players event (ghost seed) caught (execution seed) final (ready seed)
      path ending (boundary seed supported) (bounded seed supported) reached completeAfter
    refine ⟨native, ?_, nextLag, physicalAfter, boundAfter⟩
    have pickEq : pick final = choice := picked
    change SourceCheckpoint setup (revealSuccessor published binding (source seed) (pick final))
      tailRefs (rank + 1) native.config
    rw [pickEq]
    simpa only [tailRefs, OutputEmbedding.ref, event, index] using typed
  · intro seed stopped final
    simp only [decodeConfig?, terminalRefsWith, finalRegistry, finalRevelations,
      advance, revealSuccessor, Option.map_id]
    rfl
  · intro policy config
    simp only [stepSource, PMF.map_id, PMF.bind_map, Function.comp_def, SourceProgram.runFrom,
      afterReveal_update, build, revealKernel, Function.update_self]
    by_cases inactive : who ∈ config.defaulted
    · simp only [inactive, dite_true, PMF.pure_bind]
      have ignored : ∀ choice : Bool,
          revealSuccessor published binding config choice =
            revealSuccessor published binding config false := by
        intro choice
        simp only [revealSuccessor, inactive, ite_true]
      simp_rw [ignored]
      exact (PMF.bind_const _ _).symm
    · simp only [inactive, dite_false]
  · intro seed
    exact (application setup runtime leaks).runToHorizon_eq_runUntilHorizon_bind scheduler
      players _ horizon (execution seed)

end Vegas


namespace Vegas
open SourceProgram GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem runFrom_commit_update_other
    {Γ : SourceCtx Player L} {names : Finset VarId}
    {name : VarId} {payload : L.Ty} {owner focal : Player}
    (different : owner ≠ focal) (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name names))
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (policy : BehavioralPolicy focal next) (config : Config Player L Γ) :
    SourceProgram.runFrom (.commit name owner fresh guard next)
      (Function.update profile focal ((profile focal).1, policy)) config =
    (((if inactive : owner ∈ config.defaulted then PMF.pure none
      else commitKernel profile (config.view owner) inactive).map
        (commitSuccessor name guard config)).bind fun after =>
          SourceProgram.runFrom next (Function.update (afterCommit profile) focal policy)
            after) := by
  have tails : afterCommit (Function.update profile focal ((profile focal).1, policy)) =
      Function.update (afterCommit profile) focal policy := by
    funext player
    by_cases same : player = focal
    · subst player
      simp only [afterCommit, Function.update_self]
    · simp only [afterCommit, Function.update_of_ne same]
  rw [SourceProgram.runFrom, tails, PMF.bind_map]
  by_cases inactive : owner ∈ config.defaulted
  · simp only [inactive, dite_true, Function.comp_def]
  · simp only [inactive, dite_false, commitKernel, Function.update_of_ne different,
      Function.comp_def]

private theorem runFrom_reveal_update_other
    {Γ : SourceCtx Player L} {names : Finset VarId}
    {name published : VarId} {payload : L.Ty} {owner focal : Player}
    (different : owner ≠ focal) (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ names)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (names.erase name))
    (profile : BehavioralProfile (.reveal published owner name fresh selected unresolved next))
    (policy : BehavioralPolicy focal next) (config : Config Player L Γ) :
    SourceProgram.runFrom (.reveal published owner name fresh selected unresolved next)
      (Function.update profile focal ((profile focal).1, policy)) config =
    (((if inactive : owner ∈ config.defaulted then PMF.pure false
      else revealKernel profile (config.view owner) inactive).map
        (revealSuccessor published selected config)).bind fun after =>
          SourceProgram.runFrom next (Function.update (afterReveal profile) focal policy)
            after) := by
  have tails : afterReveal (Function.update profile focal ((profile focal).1, policy)) =
      Function.update (afterReveal profile) focal policy := by
    funext player
    by_cases same : player = focal
    · subst player
      simp only [afterReveal, Function.update_self]
    · simp only [afterReveal, Function.update_of_ne same]
  rw [SourceProgram.runFrom, tails, PMF.bind_map]
  by_cases inactive : owner ∈ config.defaulted
  · simp only [inactive, dite_true, Function.comp_def]
  · simp only [inactive, dite_false, revealKernel, Function.update_of_ne different,
      Function.comp_def]

end Vegas


namespace Vegas
open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem SourceDeviationLaw.commit_foreign
    (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (horizon : Nat) (scheduler : (application setup runtime leaks).Scheduler)
    (delay bound : (graph setup).EventId → Nat) (turns : Nat)
    (contract : AsyncContract runtime leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely runtime delay bound)
    (wholeProfile : BehavioralProfile setup.program) (focal owner : Player)
    (deviation : (application setup runtime leaks).Policy) (foreign : owner ≠ focal)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name openNames))
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat) :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
    let tailRefs := refs.cons (embedding.ref index)
    let tailBefore : ContextRefsBefore tailRefs tailEmbedding :=
      refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl
    let players := Function.update
      (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation
    SourceDeviationLaw setup runtime leaks horizon scheduler players wholeProfile focal
      next (afterCommit profile) tailRefs tailEmbedding tailBefore (rank + 1) →
    SourceDeviationLaw setup runtime leaks horizon scheduler players wholeProfile focal
      (.commit name owner fresh guard next) profile refs embedding refsBefore rank := by
  intro index tailEmbedding tailRefs tailBefore players tailLaw Seed prior source ghost execution
    aligned checkpoint lag boundary bounded effective noise factor
  let event := embedding.event index
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using
      (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
  have ready (seed : Seed) : (ghost seed).config.cut.Ready event := by
    have ordered := (checkpoint seed).ordered
    rw [← eventRank] at ordered
    exact ordered.ready event.isLt
  obtain ⟨nextNoise, joint, endpoints⟩ := sourceService_foreign_commit_law runtime leaks
    delay bound turns contract timely wholeProfile focal owner deviation foreign fresh guard next
    profile refs embedding refsBefore rank prior source execution ghost aligned checkpoint
    (fun seed _ => lag seed) boundary bounded noise factor
  let pick := fun final : (application setup runtime leaks).Execution =>
    OwnAction.binding owner name payload
      ((final.application.config.history.find? (fun record => decide (record.event = event))).bind
        fun record => record.decision.bind (decodeEventAction setup.program record.event))
  let phase := fun seed => (application setup runtime leaks).runUntilHorizon scheduler players
    (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)
  let advance := fun seed final => commitSuccessor name guard (source seed) (pick final)
  let stepSource := fun config : Config Player L Γ =>
    (if inactive : owner ∈ config.defaulted then PMF.pure none
      else commitKernel profile (config.view owner) inactive).map
        (commitSuccessor name guard config)
  let build : BehavioralPolicy focal next →
      BehavioralPolicy focal (.commit name owner fresh guard next) :=
    fun policy => ((profile focal).1, policy)
  apply SourceDeviationLaw.of_head setup runtime leaks horizon scheduler players wholeProfile focal
    (.commit name owner fresh guard next) profile refs embedding next (afterCommit profile)
    tailRefs tailEmbedding tailBefore (rank + 1) tailLaw prior source execution phase advance
    stepSource nextNoise joint (readResult := id) (build := build)
  · intro seed final
    exact CompiledPolicySuffix.commitTail setup.program wholeProfile
      (openNames := openNames) fresh guard next profile refs (source seed).revelations
      (source seed).registry embedding refsBefore rank (aligned seed)
  · intro seed final player
    exact effective seed player
  · intro seed supported final reached
    obtain ⟨choice, native, typed, nextLag, _active, picked⟩ :=
      endpoints seed supported final reached
    have completeAfter : event ∈ final.application.config.cut.completed := by
      obtain ⟨caught, path, ending⟩ := nextLag
      rw [← ending]
      apply EventGraph.Config.Step.path_completed_mono
        (EventGraphRuntime.State.automatic_path_graph_steps path)
      exact (typed.ordered.2 event).mpr (by omega)
    obtain ⟨caught, path, ending⟩ := lag seed
    obtain ⟨boundAfter, physicalAfter⟩ := automatic_stopped_boundary setup runtime leaks
      horizon scheduler players event (ghost seed) caught (execution seed) final (ready seed)
      path ending (boundary seed supported) (bounded seed supported) reached completeAfter
    refine ⟨native, ?_, nextLag, physicalAfter, boundAfter⟩
    have pickEq : pick final = choice := picked
    change SourceCheckpoint setup (commitSuccessor name guard (source seed) (pick final))
      tailRefs (rank + 1) native.config
    rw [pickEq]
    simpa only [tailRefs, OutputEmbedding.ref, event, index] using typed
  · intro seed stopped final
    simp only [decodeConfig?, terminalRefsWith, finalRegistry, finalRevelations,
      advance, commitSuccessor, Option.map_id]
    rfl
  · intro policy config
    simpa only [stepSource, build, PMF.map_id] using
      runFrom_commit_update_other foreign fresh guard next profile policy config
  · intro seed
    exact (application setup runtime leaks).runToHorizon_eq_runUntilHorizon_bind scheduler
      players _ horizon (execution seed)

private theorem SourceDeviationLaw.reveal_foreign
    (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (horizon : Nat) (scheduler : (application setup runtime leaks).Scheduler)
    (delay bound : (graph setup).EventId → Nat) (turns : Nat)
    (contract : AsyncContract runtime leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely runtime delay bound)
    (wholeProfile : BehavioralProfile setup.program) (focal owner : Player)
    (deviation : (application setup runtime leaks).Policy) (foreign : owner ≠ focal)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {payload : L.Ty} (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (openNames.erase name))
    (profile : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
    let tailRefs := refs.cons (embedding.ref index)
    let tailBefore : ContextRefsBefore tailRefs tailEmbedding :=
      refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl
    let players := Function.update
      (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation
    SourceDeviationLaw setup runtime leaks horizon scheduler players wholeProfile focal
      next (afterReveal profile) tailRefs tailEmbedding tailBefore (rank + 1) →
    SourceDeviationLaw setup runtime leaks horizon scheduler players wholeProfile focal
      (.reveal published owner name fresh binding unresolved next) profile refs embedding refsBefore
        rank := by
  intro index tailEmbedding tailRefs tailBefore players tailLaw Seed prior source ghost execution
    aligned checkpoint lag boundary bounded effective noise factor
  let event := embedding.event index
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using
      (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
  have ready (seed : Seed) : (ghost seed).config.cut.Ready event := by
    have ordered := (checkpoint seed).ordered
    rw [← eventRank] at ordered
    exact ordered.ready event.isLt
  obtain ⟨nextNoise, joint, endpoints⟩ := sourceService_foreign_reveal_law runtime leaks
    delay bound turns contract timely wholeProfile focal owner deviation foreign fresh binding
    unresolved next profile refs embedding refsBefore rank prior source execution ghost aligned
    checkpoint (fun seed _ => lag seed) boundary bounded (fun seed _ => effective seed owner)
    noise factor
  let pick := fun final : (application setup runtime leaks).Execution =>
    OwnAction.disclosure
      ((final.application.config.history.find? (fun record => decide (record.event = event))).bind
        fun record => record.decision.bind (decodeEventAction setup.program record.event))
  let phase := fun seed => (application setup runtime leaks).runUntilHorizon scheduler players
    (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)
  let advance := fun seed final => revealSuccessor published binding (source seed) (pick final)
  let stepSource := fun config : Config Player L Γ =>
    (if inactive : owner ∈ config.defaulted then PMF.pure false
      else revealKernel profile (config.view owner) inactive).map
        (revealSuccessor published binding config)
  let build : BehavioralPolicy focal next →
      BehavioralPolicy focal (.reveal published owner name fresh binding unresolved next) :=
    fun policy => ((profile focal).1, policy)
  apply SourceDeviationLaw.of_head setup runtime leaks horizon scheduler players wholeProfile focal
    (.reveal published owner name fresh binding unresolved next) profile refs embedding next
    (afterReveal profile)
    tailRefs tailEmbedding tailBefore (rank + 1) tailLaw prior source execution phase advance
    stepSource nextNoise joint (readResult := id) (build := build)
  · intro seed final
    exact CompiledPolicySuffix.revealTail setup.program wholeProfile
      (openNames := openNames) fresh binding unresolved next profile refs (source seed).revelations
      (source seed).registry embedding refsBefore rank (aligned seed)
  · intro seed final player
    exact (effective seed player).2
  · intro seed supported final reached
    obtain ⟨choice, native, typed, nextLag, _active, picked⟩ :=
      endpoints seed supported final reached
    have completeAfter : event ∈ final.application.config.cut.completed := by
      obtain ⟨caught, path, ending⟩ := nextLag
      rw [← ending]
      apply EventGraph.Config.Step.path_completed_mono
        (EventGraphRuntime.State.automatic_path_graph_steps path)
      exact (typed.ordered.2 event).mpr (by omega)
    obtain ⟨caught, path, ending⟩ := lag seed
    obtain ⟨boundAfter, physicalAfter⟩ := automatic_stopped_boundary setup runtime leaks
      horizon scheduler players event (ghost seed) caught (execution seed) final (ready seed)
      path ending (boundary seed supported) (bounded seed supported) reached completeAfter
    refine ⟨native, ?_, nextLag, physicalAfter, boundAfter⟩
    have pickEq : pick final = choice := picked
    change SourceCheckpoint setup (revealSuccessor published binding (source seed) (pick final))
      tailRefs (rank + 1) native.config
    rw [pickEq]
    simpa only [tailRefs, OutputEmbedding.ref, event, index] using typed
  · intro seed stopped final
    simp only [decodeConfig?, terminalRefsWith, finalRegistry, finalRevelations,
      advance, revealSuccessor, Option.map_id]
    rfl
  · intro policy config
    simpa only [stepSource, build, PMF.map_id] using
      runFrom_reveal_update_other foreign fresh binding unresolved next profile policy config
  · intro seed
    exact (application setup runtime leaks).runToHorizon_eq_runUntilHorizon_bind scheduler
      players _ horizon (execution seed)

end Vegas


namespace Vegas
open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem SourceDeviationLaw.initialized
    (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (horizon : Nat) (scheduler : (application setup runtime leaks).Scheduler)
    (players : Player → (application setup runtime leaks).Policy)
    (profile : BehavioralProfile setup.program) (who : Player)
    (effective : ∀ player, (profile player).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (law : SourceDeviationLaw setup runtime leaks horizon scheduler players profile who
      setup.program profile (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program) (initialRefsBefore setup.program) 0) :
    ∃ policy : BehavioralPolicy who setup.program,
      ((application setup runtime leaks).roundsFrom (initialLaw setup) scheduler players
        horizon).map (fun final => sourceReadout setup runtime leaks
          ((application setup runtime leaks).finished final)) =
        (setup.run (Function.update profile who policy)).map some := by
  let app := application setup runtime leaks
  let ghost := fun initial => EventGraphRuntime.State.initial (graph := graph setup)
    (setup.eventInputs initial)
  let execution := fun initial => ReactiveApplication.Execution.initial app (ghost initial)
  obtain ⟨noise, factor⟩ := source_initial_traffic_factorization setup
    (deadline := runtime.deadline) leaks who
  have boundary (initial : State L setup.context) (supported : initial ∈ setup.initialLaw.support) :
      CompletionBoundary setup leaks scheduler players 0 (execution initial) := by
    refine ⟨?_, EventOrder.Cut.empty_isPrefix _, ?_⟩
    · change execution initial ∈ (app.roundsFrom (initialLaw setup) scheduler players 0).support
      unfold ReactiveApplication.roundsFrom
      simp only [ReactiveApplication.runRounds, initialLaw, serviceInitialLaw]
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨ghost initial,
        (PMF.mem_support_map_iff _ _ _).mpr ⟨initial, supported, rfl⟩,
        (PMF.mem_support_pure_iff _ _).mpr rfl⟩
    · intro event _ observer entry member
      cases member
  obtain ⟨policy, result⟩ := law setup.initialLaw Config.initial ghost execution
    (fun _ => CompiledPolicySuffix.whole setup.program profile)
    (fun initial => SourceCheckpoint.initial setup initial)
    (fun initial => ⟨ghost initial, .refl, rfl⟩)
    (fun initial supported => ⟨0, boundary initial supported⟩)
    (fun _ _ => Nat.zero_le _) (fun _ player => effective player) noise factor
  refine ⟨policy, ?_⟩
  simpa only [ReactiveApplication.roundsFrom, initialLaw, serviceInitialLaw, PMF.bind_map,
    PMF.map_bind, ReactiveApplication.runToHorizon, ReactiveApplication.Execution.initial,
    List.length_nil, Nat.sub_zero, Setup.run, SourceProgram.run, execution, ghost, app,
    Config.initial, Function.comp_def, sourceReadout, ReactiveApplication.finished,
    serviceSourceReadout_eq_decode setup .sequential runtime.deadline leaks, List.map_id]
    using result

end Vegas


namespace Vegas
open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem sourceService_deviation_law
    (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (horizon : Nat) (scheduler : (application setup runtime leaks).Scheduler)
    (delay bound : (graph setup).EventId → Nat) (turns : Nat)
    (contract : AsyncContract runtime leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely runtime delay bound)
    (wholeProfile : BehavioralProfile setup.program) (who : Player)
    (deviation : (application setup runtime leaks).Policy) :
    ∀ {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
      (refsBefore : ContextRefsBefore refs embedding) (rank : Nat),
      SourceDeviationLaw setup runtime leaks horizon scheduler
        (Function.update (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
          (firstTurnTiming setup turns) wholeProfile) who deviation)
        wholeProfile who program profile refs embedding refsBefore rank := by
  intro Γ names program
  induction program with
  | ret payoffs =>
      intro profile refs embedding refsBefore rank
      exact SourceDeviationLaw.terminal setup runtime leaks horizon scheduler _ wholeProfile who
        payoffs profile refs embedding refsBefore rank
  | sample name fresh distribution next ih =>
      intro profile refs embedding refsBefore rank
      apply SourceDeviationLaw.sample setup runtime leaks horizon scheduler contract.completes
        bound turns wholeProfile who deviation fresh distribution next profile refs embedding
        refsBefore rank
      exact ih _ _ _
        (refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl) (rank + 1)
  | commit name owner fresh guard next ih =>
      intro profile refs embedding refsBefore rank
      by_cases same : owner = who
      · subst owner
        apply SourceDeviationLaw.commit_owned setup runtime leaks horizon scheduler
          contract.completes bound turns wholeProfile who deviation fresh guard next profile
          refs embedding refsBefore rank
        exact ih _ _ _
          (refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl) (rank + 1)
      · apply SourceDeviationLaw.commit_foreign setup runtime leaks horizon scheduler delay bound
          turns contract timely wholeProfile who owner deviation same fresh guard next profile
          refs embedding refsBefore rank
        exact ih _ _ _
          (refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl) (rank + 1)
  | reveal published owner name fresh binding unresolved next ih =>
      intro profile refs embedding refsBefore rank
      by_cases same : owner = who
      · subst owner
        apply SourceDeviationLaw.reveal_owned setup runtime leaks horizon scheduler
          contract.completes bound turns wholeProfile who deviation fresh binding unresolved
          next profile refs embedding refsBefore rank
        exact ih _ _ _
          (refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl) (rank + 1)
      · apply SourceDeviationLaw.reveal_foreign setup runtime leaks horizon scheduler delay bound
          turns contract timely wholeProfile who owner deviation same fresh binding unresolved
          next profile refs embedding refsBefore rank
        exact ih _ _ _
          (refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl) (rank + 1)

/-- Against first-turn clients, every physical policy of one player has exactly
the terminal source-configuration law of one behavioral source deviation. -/
theorem sourceService_deviation_readout_law
    (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (horizon : Nat) (scheduler : (application setup runtime leaks).Scheduler)
    (delay bound : (graph setup).EventId → Nat) (turns : Nat)
    (contract : AsyncContract runtime leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely runtime delay bound)
    (profile : BehavioralProfile setup.program)
    (effective : ∀ player, (profile player).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (who : Player) (deviation : (application setup runtime leaks).Policy) :
    ∃ policy : BehavioralPolicy who setup.program,
      ((application setup runtime leaks).roundsFrom (initialLaw setup) scheduler
        (Function.update (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
          (firstTurnTiming setup turns) profile) who deviation) horizon).map
          (fun final => sourceReadout setup runtime leaks
            ((application setup runtime leaks).finished final)) =
        (setup.run (Function.update profile who policy)).map some := by
  apply SourceDeviationLaw.initialized setup runtime leaks horizon scheduler _ profile who effective
  exact sourceService_deviation_law setup runtime leaks horizon scheduler delay bound turns
    contract timely profile who deviation setup.program profile
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program) (initialRefsBefore setup.program) 0

end Vegas
