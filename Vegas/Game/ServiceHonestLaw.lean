/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncDeviationReadout

/-! # The honest law of the first-turn clients on barrier-ordered graphs

When every player follows the first-turn client of a source profile, under a
scheduler satisfying the asynchronous contract, the decoded source state has,
phase by phase, the law of the source protocol of the profile
(`Vegas.honestLaw`). A block of commitments is drawn in advance from the
owners' source kernels (`Vegas.honest_block_law`); a public event is a phase of
its own. From initialization the typed outcome has the source law of the
profile (`Vegas.firstTurn_readout_law`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Block

variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- The first-turn clients are every player drawn with nothing assigned. -/
theorem firstTurnProfile_eq_drawnPlayers (bound : (serviceGraph setup mode).EventId → Nat)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (others : Player → (serviceApplication setup mode deadline leaks).Policy) :
    serviceTurnPolicy setup mode deadline leaks bound turns (firstTurnTiming setup turns mode)
        profile =
      drawnPlayers bound turns profile (fun _ => True) others (fun _ => none) := by
  funext player
  simp only [drawnPlayers, ↓reduceIte]
  exact (assignedTurnPolicy_empty bound turns profile player).symm

/-- **The honest block.** On a reveal-relaxed graph, under the asynchronous
contract with `delay + bound < deadline`, when every player follows the
first-turn client of a source profile, the run from completion boundaries at
the start `low` of a block of bindings until the block is done decodes, through
its leading commitments, to the source law of the block in which every owner
draws from its source kernel. -/
theorem honest_block_law (relaxed : (serviceGraph setup mode).RevealRelaxedOrdered)
    {low high : Nat} (wall : BlockEnd setup mode high) {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program)
    (bindings : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val → event.val < high →
      ∃ owner payload outputEq codeEq,
        nodeView (serviceGraph setup mode) event = .bind owner payload outputEq codeEq)
    {Γ : SourceCtx Player L} {names : Finset VarId} (program : SourceProgram Player L Γ names)
    (profile : BehavioralProfile program) (count : Nat) (prefixed : CommitPrefix program count)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (refsBefore : ContextRefsBefore refs embedding) (highEq : low + count = high)
    (anyone : Player)
    {Seed : Type} (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution)
    (aligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile program profile refs
      (source seed).revelations (source seed).registry embedding refsBefore low)
    (checkpoint : ∀ seed, SourceCheckpoint setup (source seed) refs low
      (execution seed).application.config)
    (boundary : ∀ seed ∈ prior.support, CompletionBoundary setup leaks scheduler
      (serviceTurnPolicy setup mode deadline leaks bound turns (firstTurnTiming setup turns mode)
        wholeProfile) low (execution seed))
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon) :
    (prior.bind fun seed =>
      ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
        (serviceTurnPolicy setup mode deadline leaks bound turns (firstTurnTiming setup turns mode)
          wholeProfile) (BlockDone high) horizon (execution seed)).map fun final =>
        decodeSourcePrefix? program refs (source seed).registry (source seed).revelations
          embedding.ref count final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion mode)))) =
      ((prior.map source).bind fun config =>
        listChain (fun _ => True) count program profile prefixed config []).map fun config =>
          some ((commitTail count program prefixed).lift (ProtocolState.entry _ config)) := by
  let app := serviceApplication setup mode deadline leaks
  let others : Player → app.Policy := fun _ => app.silentPolicy
  have lowHigh : low ≤ high := by omega
  -- Block events are the embedded leading commitments.
  have embedded (event : (serviceGraph setup mode).EventId) (lower : low ≤ event.val)
      (upper : event.val < high) (seed : Seed) :
      ∃ index : Fin (eventCount program), index.val < count ∧ embedding.event index = event := by
    have within := prefixed.le_eventCount
    have below : event.val - low < count := by omega
    refine ⟨⟨event.val - low, Nat.lt_of_lt_of_le below within⟩, below, ?_⟩
    apply Fin.ext
    rw [(aligned seed).graphSuffix.rankEq]
    simp only
    omega
  rw [PMF.map_bind, PMF.bind_map]
  apply bind_congr_on_support _
  intro seed supported
  have start := boundary seed supported
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler _ _
    (bounded seed supported) _ start.supported
  have ownSlots (owner : Player) :
      OwnSubmissionsAtTurn setup leaks (execution seed) owner ∧
        CanonicalSlotsUsed setup leaks (execution seed) owner :=
    canonicalSlots_roundsFrom scheduler _ owner (bound := bound)
      (firstTurnTiming setup turns mode) wholeProfile rfl _ _ start.supported
  have answered := roundsFrom_activationsAnswered _ _ start.supported
  have predraw := drawnPlayers_runUntil_predraw relaxed wall contract timely turns wholeProfile
    (fun _ => True) others (execution seed) start.ordered start.untouched
    (fun owner _ => (ownSlots owner).1) answered bindings count program profile prefixed refs
    embedding refsBefore low (source seed) (aligned seed) (execution seed).application.config
    (checkpoint seed) Relation.ReflTransGen.refl le_rfl (by omega) (fun _ => none)
    (fun _ _ none => by cases none) (fun event _ lower upper => by omega) _ 0
    (by simpa only [Nat.zero_add] using trace)
  -- Every run of a draw decodes to the block's source configuration of the draw.
  have decided (picked : Assignment setup mode)
      (member : picked ∈ (assignChain setup mode (fun _ => True) count program profile prefixed
        embedding (source seed) (fun _ => none)).support)
      (final : app.Execution)
      (reached : final ∈ (app.runUntil scheduler
        (drawnPlayers bound turns wholeProfile (fun _ => True) others picked) (BlockDone high)
        (horizon - (execution seed).environmentRecall.length) (execution seed)).support) :
      decodeSourcePrefix? program refs (source seed).registry (source seed).revelations
          embedding.ref count final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion mode))) =
        some ((commitTail count program prefixed).lift (ProtocolState.entry _
          (assembleChain setup mode (fun _ => True) count program prefixed embedding
            (source seed) picked []))) := by
    have done := runUntil_blockDone_of_trace _ contract.completes high _ _ final trace reached
    have reach := runUntil_configReaches scheduler _ _ _ _ final reached
    have inside := runUntil_within (BlockEnd.sealed_relaxed relaxed wall
        (plain_of_bindings bindings))
      scheduler _ _ _ final
      (start.withinBlock lowHigh) reached
    have finalPrefix : final.application.config.cut.IsPrefix high :=
      inside.within.isPrefix wall.1 done
    rw [← assembleChain_all count program prefixed embedding (source seed) picked
      (deviatorChoices setup mode (fun _ => True) anyone count program prefixed embedding
        ((serviceGraph setup mode).playerStore anyone final.application.config.store))]
    refine blockDecode relaxed (fun _ => True) anyone (fun _ undrawn => (undrawn trivial).elim)
      wholeProfile (execution seed).application.config final.application.config reach
      start.ordered finalPrefix bindings picked ?_ count program profile prefixed refs embedding
      refsBefore low (source seed) (aligned seed) (execution seed).application.config
      (checkpoint seed) Relation.ReflTransGen.refl
      (fun completion member notStart =>
        (notStart ((execution seed).application.config.history_exact
          _ |>.mp (List.mem_map_of_mem member))).elim) le_rfl (by omega)
    intro event owner lower upper owned _
    obtain ⟨index, below, rfl⟩ := embedded event lower upper seed
    obtain ⟨action, assigned⟩ := assignChain_support_assigns (fun _ => True) count program
      profile prefixed embedding _ _ picked member index owner below owned trivial
    obtain ⟨nodeOwner, nodePayload, nodeEq, nodeCode, _⟩ := bindings _ lower upper
    have ownerIs : nodeOwner = owner := Option.some.inj
      ((nodeView_bind_actor nodeEq nodeCode).symm.trans owned)
    subst ownerIs
    have facts := binding_decision_facts nodeEq action
    have phase := DecidedEventPhase.runUntil contract timely facts.1 facts.2.1 facts.2.2.1
      (start.untouched _ lower)
      (players := drawnPlayers bound turns wholeProfile (fun _ => True) others picked)
      (by
        simp only [drawnPlayers, ↓reduceIte]
        exact assignedTurnPolicy_decidesAt bound turns wholeProfile nodeOwner picked _ action
          assigned)
      (by
        simp only [drawnPlayers, ↓reduceIte]
        exact assignedTurnPolicy_submitsAtTurn bound turns wholeProfile nodeOwner picked)
      (BlockDone high) _ 0 _ (by simpa only [Nat.zero_add] using trace)
      (DecidedEventPhase.initial bound action (start.untouched _ lower) (ownSlots nodeOwner).1
        (fun completed => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le
          ((start.ordered.2 _).mp completed) lower)))
      (ownSlots nodeOwner).1 answered final reached
    exact ⟨action, assigned, phase.binding_completed nodeEq (done _ upper)⟩
  unfold ReactiveApplication.runUntilHorizon
  rw [firstTurnProfile_eq_drawnPlayers bound turns wholeProfile others, predraw, PMF.map_bind,
    Function.comp_apply]
  calc
    _ = (assignChain setup mode (fun _ => True) count program profile prefixed embedding
          (source seed) (fun _ => none)).bind fun picked =>
          PMF.pure (some ((commitTail count program prefixed).lift (ProtocolState.entry _
            (assembleChain setup mode (fun _ => True) count program prefixed embedding
              (source seed) picked [])))) := by
      apply bind_congr_on_support _
      intro picked member
      rw [map_congr_on_support _ (g := fun _ => some ((commitTail count program prefixed).lift
        (ProtocolState.entry _ (assembleChain setup mode (fun _ => True) count program prefixed
          embedding (source seed) picked []))))
        (fun final reached => decided picked member final reached), pmf_map_fun_const]
    _ = ((assignChain setup mode (fun _ => True) count program profile prefixed embedding
          (source seed) (fun _ => none)).map fun picked => assembleChain setup mode
            (fun _ => True) count program prefixed embedding (source seed) picked []).map
          fun config => some ((commitTail count program prefixed).lift
            (ProtocolState.entry _ config)) := by
      rw [PMF.map_comp, ← PMF.bind_pure_comp]
      rfl
    _ = _ := by
      rw [assignChain_assemble (fun _ => True) count program profile prefixed embedding
        (source seed) (source seed) (fun _ => none) [] (fun _ _ => rfl)]

end Block

section Law

variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
  (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
  (players : Player → (serviceApplication setup mode deadline leaks).Policy)
  (wholeProfile : BehavioralProfile setup.program)

/-- A property of a residual profile at a registry and revelations. -/
abbrev ResidualProperty (Player : Type) [DecidableEq Player] (L : IExpr) [IExpr.ResultTypes L] :=
  ∀ {Γ : SourceCtx Player L} {names : Finset VarId} (program : SourceProgram Player L Γ names),
    BehavioralProfile program → Registry Γ → Revelations Γ → Prop

/-- Every player of the residual profile discloses only effectively. -/
def effectiveResidual : ResidualProperty Player L := fun program profile registry revelations =>
  ∀ player, (profile player).EffectiveDisclosures program registry revelations

/-- **The honest law of a residual program.** From completion boundaries at
rank `offset` that the source configurations of a seed law check, and at which
the residual profile `admits` its registry and revelations, the phases `ends`
decode to the law of the source run of the residual profile. -/
def HonestLaw [Fintype Player] (admits : ResidualProperty Player L)
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat) (ends : List Nat) : Prop :=
  ∀ {Seed : Type} (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution),
    (∀ seed, CompiledPolicySuffix setup.program wholeProfile program profile refs
      (source seed).revelations (source seed).registry embedding refsBefore offset) →
    (∀ seed, SourceCheckpoint setup (source seed) refs offset
      (execution seed).application.config) →
    (∀ seed ∈ prior.support, CompletionBoundary setup leaks scheduler players offset
      (execution seed)) →
    (∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon) →
    (∀ seed, admits program profile (source seed).registry (source seed).revelations) →
    (prior.bind fun seed =>
      (deviationPhases scheduler players horizon ends (execution seed)).map fun final =>
        decodeSourcePrefix? program refs (source seed).registry (source seed).revelations
          embedding.ref (eventCount program) final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion mode)))) =
      prior.bind fun seed =>
        ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[
          eventCount program] (PMF.pure (ProtocolState.entry program (source seed)))).map some

/-- **One honest phase, decoded.** If the run of the first phase, ending at
`high`, decodes through an injective embedding of residual entry states with
the source law of a source step kernel, and stops at completion boundaries within the
horizon, then the residual honest law gives the program's over all of its
phases. -/
theorem HonestLaw.phase [Fintype Player] (admits : ResidualProperty Player L)
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    {Δ : SourceCtx Player L} {tailNames : Finset VarId}
    (tail : SourceProgram Player L Δ tailNames) (tailProfile : BehavioralProfile tail)
    (tailRefs : ContextRefs (graphLayout setup.program) Δ)
    (tailEmbedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      tail)
    (tailBefore : ContextRefsBefore tailRefs tailEmbedding) (high : Nat) (rest : List Nat)
    (tailLaw : HonestLaw setup leaks horizon scheduler players wholeProfile admits tail
      tailProfile tailRefs tailEmbedding tailBefore high rest)
    {Seed : Type} (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution)
    (lift : ProtocolState tail → ProtocolState program)
    (injective : Function.Injective fun config : Config Player L Δ =>
      lift (ProtocolState.entry tail config))
    (nextRegistry : Seed → Registry Δ) (nextRevelations : Seed → Revelations Δ)
    (decode : Seed → (serviceApplication setup mode deadline leaks).Execution →
      Option (ProtocolState program))
    (decodeEq : ∀ seed final, decode seed final =
      (decodeState? tailRefs final.application.config.store).map fun state =>
        lift (ProtocolState.entry tail ⟨state, nextRegistry seed, nextRevelations seed,
          decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion mode))⟩))
    (stepSource : Config Player L Γ → PMF (Config Player L Δ))
    (law : (phaseJoint setup leaks horizon scheduler players high prior execution).map
        (fun point => decode point.1 point.2) =
      ((prior.map source).bind stepSource).map fun config =>
        some (lift (ProtocolState.entry tail config)))
    (nextBoundary : ∀ point :
      PhasePoint setup leaks horizon scheduler players high prior execution,
      CompletionBoundary setup leaks scheduler players high point.val.2)
    (nextBounded : ∀ point :
      PhasePoint setup leaks horizon scheduler players high prior execution,
      point.val.2.environmentRecall.length ≤ horizon)
    (nextAligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile tail tailProfile
      tailRefs (nextRevelations seed) (nextRegistry seed) tailEmbedding tailBefore high)
    (nextAdmits : ∀ seed, admits tail tailProfile (nextRegistry seed) (nextRevelations seed))
    (decodeLater : ∀ seed (final : (serviceApplication setup mode deadline leaks).Execution),
      decodeSourcePrefix? program refs (source seed).registry
        (source seed).revelations embedding.ref (eventCount program)
          final.application.config.store (decodeHistory setup.program
            (final.application.config.history.map (setup.eventGraph.fromModeCompletion mode))) =
      (decodeSourcePrefix? tail tailRefs (nextRegistry seed) (nextRevelations seed)
        tailEmbedding.ref (eventCount tail) final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion mode)))).map lift)
    (kernel : ∀ seed ∈ prior.support,
      ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[
        eventCount program] (PMF.pure (ProtocolState.entry program (source seed)))) =
      ((stepSource (source seed)).bind fun next =>
        ((fun law => law.bind (ProtocolState.behavioralStateStep tail tailProfile))^[
          eventCount tail] (PMF.pure (ProtocolState.entry tail next)))).map lift) :
    (prior.bind fun seed =>
      (deviationPhases scheduler players horizon (high :: rest) (execution seed)).map
        fun final =>
        decodeSourcePrefix? program refs (source seed).registry (source seed).revelations
          embedding.ref (eventCount program) final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion mode)))) =
      prior.bind fun seed =>
        ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[
          eventCount program] (PMF.pure (ProtocolState.entry program (source seed)))).map
          some := by
  let app := serviceApplication setup mode deadline leaks
  let advanced := phaseJoint setup leaks horizon scheduler players high prior execution
  obtain ⟨nextSource, nextCheckpoint, nextRegistryEq, nextRevelationsEq, _nextRead,
    nextMarginal⟩ := reconstruct_service_marginal setup tailRefs high nextRegistry
      nextRevelations advanced (fun config => lift (ProtocolState.entry tail config)) injective
      decode decodeEq (fun point member => (nextBoundary ⟨point, member⟩).ordered)
      ((prior.map source).bind stepSource) law
  let nextPrior := pmfToSubtype advanced (fun _ member => member)
  have tailEq := tailLaw nextPrior nextSource (fun point => point.val.2)
    (fun point => by
      rw [nextRegistryEq, nextRevelationsEq]
      exact nextAligned point.val.1)
    nextCheckpoint (fun point _ => nextBoundary point) (fun point _ => nextBounded point)
    (fun point => by
      rw [nextRegistryEq, nextRevelationsEq]
      exact nextAdmits point.val.1)
  let continuePoint := fun point : Seed × app.Execution =>
    (deviationPhases scheduler players horizon rest point.2).map fun final =>
      decodeSourcePrefix? program refs (source point.1).registry
        (source point.1).revelations embedding.ref (eventCount program)
          final.application.config.store (decodeHistory setup.program
            (final.application.config.history.map
              (setup.eventGraph.fromModeCompletion mode)))
  let continuation := fun config : Config Player L Δ =>
    ((fun law => law.bind (ProtocolState.behavioralStateStep tail tailProfile))^[
      eventCount tail] (PMF.pure (ProtocolState.entry tail config))).map
      fun state => some (lift state)
  calc
    _ = advanced.bind continuePoint := by
      simp only [advanced, continuePoint, PMF.bind_bind, PMF.bind_map,
        deviationPhases, PMF.map_bind, Function.comp_def]
    _ = nextPrior.bind (fun point => continuePoint point.val) := by
      rw [show (nextPrior.bind fun point => continuePoint point.val) =
          (nextPrior.map Subtype.val).bind continuePoint from
        (PMF.bind_map nextPrior Subtype.val continuePoint).symm, map_val_pmfToSubtype]
    _ = (nextPrior.bind fun point =>
          (deviationPhases scheduler players horizon rest point.val.2).map fun final =>
            decodeSourcePrefix? tail tailRefs (nextSource point).registry
              (nextSource point).revelations tailEmbedding.ref (eventCount tail)
              final.application.config.store (decodeHistory setup.program
                (final.application.config.history.map
                  (setup.eventGraph.fromModeCompletion mode)))).map (Option.map lift) := by
      rw [PMF.map_bind]
      apply bind_congr_on_support _
      intro point _
      rw [PMF.map_comp]
      apply map_congr_on_support _
      intro final _
      change _ = Option.map lift _
      rw [nextRegistryEq, nextRevelationsEq]
      exact decodeLater point.val.1 final
    _ = nextPrior.bind (fun point => continuation (nextSource point)) := by
      rw [tailEq, PMF.map_bind]
      apply bind_congr_on_support _
      intro point _
      rw [PMF.map_comp]
      rfl
    _ = ((prior.map source).bind stepSource).bind continuation := by
      rw [show (nextPrior.bind fun point => continuation (nextSource point)) =
          (nextPrior.map nextSource).bind continuation from
        (PMF.bind_map nextPrior nextSource continuation).symm, nextMarginal]
    _ = _ := by
      rw [PMF.bind_bind, PMF.bind_map]
      apply bind_congr_on_support _
      intro seed supported
      rw [Function.comp_apply, kernel seed supported, PMF.map_comp, PMF.map_bind]
      rfl

end Law

/-- **An honest sample.** On a reveal-relaxed graph a sample is ready alone and
decodes to its source sampling law; the honest law of the program after it gives
the program's. -/
theorem HonestLaw.sample_step [Fintype Player]
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (relaxed : (serviceGraph setup mode).RevealRelaxedOrdered)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (turns : Nat) (wholeProfile : BehavioralProfile setup.program)
    (admits : ResidualProperty Player L)
    {Γ : SourceCtx Player L} {names : Finset VarId} {name : VarId} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst} {distribution : L.DistExpr (SourcePublicCtx L Γ) payload}
    {next : SourceProgram Player L ((name, .publicData payload) :: Γ) names}
    {offset : Nat} {rest : List Nat}
    (admitsNext : ∀ (profile : BehavioralProfile (.sample name fresh distribution next))
      (registry : Registry Γ) (revelations : Revelations Γ),
      admits (.sample name fresh distribution next) profile registry revelations →
        admits next (afterSample profile) registry.weaken revelations.weaken)
    (ih : ∀ (profile : BehavioralProfile next)
      (refs : ContextRefs (graphLayout setup.program) ((name, .publicData payload) :: Γ))
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) next)
      (refsBefore : ContextRefsBefore refs embedding),
      HonestLaw setup leaks horizon scheduler
        (serviceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) wholeProfile)
        wholeProfile admits next profile refs embedding refsBefore (offset + 1) rest) :
    ∀ (profile : BehavioralProfile (.sample name fresh distribution next))
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (.sample name fresh distribution next)) (refsBefore : ContextRefsBefore refs embedding),
      HonestLaw setup leaks horizon scheduler
        (serviceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) wholeProfile)
        wholeProfile admits (.sample name fresh distribution next) profile refs embedding
        refsBefore offset ((offset + 1) :: rest) := by
  let app := serviceApplication setup mode deadline leaks
  let players := serviceTurnPolicy setup mode deadline leaks bound turns
    (firstTurnTiming setup turns mode) wholeProfile
  intro profile refs embedding refsBefore Seed prior source execution aligned checkpoint
    boundary bounded effective
  let index : Fin (eventCount (.sample name fresh distribution next)) :=
    ⟨0, by simp [eventCount]⟩
  let event : (serviceGraph setup mode).EventId := embedding.event index
  have eventRank : event.val = offset := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using
      (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
  have outputEq : (serviceGraph setup mode).outputLayout event = .publicData payload := by
    change outputLayout setup.program event = _
    simpa [event, index, outputLayout, eventCount] using embedding.layout_eq index
  have alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event := sample_alone relaxed outputEq
  have boundaryAt (seed : Seed) (supported : seed ∈ prior.support) :
      CompletionBoundary setup leaks scheduler players event.val (execution seed) := by
    rw [eventRank]
    exact boundary seed supported
  have stopEq (seed : Seed) (supported : seed ∈ prior.support) :
      app.runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed) =
        app.runUntilHorizon scheduler players (BlockDone (offset + 1)) horizon
          (execution seed) := by
    have stopped := runUntilHorizon_eventDone_eq_blockDone horizon event alone _
      (boundaryAt seed supported)
    rwa [eventRank] at stopped
  have nextFacts (point : PhasePoint setup leaks horizon scheduler players (offset + 1) prior
      execution) :
      CompletionBoundary setup leaks scheduler players (offset + 1) point.val.2 ∧
        point.val.2.environmentRecall.length ≤ horizon := by
    obtain ⟨supported, reached⟩ := phaseJoint_mem setup leaks horizon scheduler players
      point.property
    rw [← stopEq _ supported] at reached
    obtain ⟨_, _, _, nextBounded, nextBoundary⟩ := completionRun_boundary_step
      contract.completes event alone (execution point.val.1) (boundaryAt _ supported)
      (bounded _ supported) point.val.2 reached
    rw [eventRank] at nextBoundary
    exact ⟨nextBoundary, nextBounded⟩
  obtain ⟨_, marginal⟩ := sample_phase_law contract.completes players wholeProfile fresh
    distribution next profile refs embedding refsBefore offset alone prior source execution
    aligned checkpoint boundary bounded
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
  let stepSource := fun config : Config Player L Γ =>
    (L.evalDist distribution (sourcePublicEnv config.state)).map (sampleSuccessor name config)
  refine HonestLaw.phase setup leaks horizon scheduler players wholeProfile admits
    (.sample name fresh distribution next) profile refs embedding next (afterSample profile)
    tailRefs tailEmbedding tailBefore (offset + 1) rest
    (ih (afterSample profile) tailRefs tailEmbedding tailBefore) prior source execution
    Sum.inr (Sum.inr_injective.comp (ProtocolState.entry_injective next))
    (fun seed => (source seed).registry.weaken)
    (fun seed => Revelations.weaken (source seed).revelations)
    (fun seed final => decodeSourcePrefix? (.sample name fresh distribution next) refs
      (source seed).registry (source seed).revelations embedding.ref 1
      final.application.config.store (decodeHistory setup.program
        (final.application.config.history.map (setup.eventGraph.fromModeCompletion mode))))
    ?_ stepSource ?_ (fun point => (nextFacts point).1)
    (fun point => (nextFacts point).2) ?_ (fun seed => admitsNext profile _ _ (effective seed))
    ?_ ?_
  · intro seed final
    simp only [decodeSourcePrefix?, Option.map_map, Function.comp_def]
    rfl
  · refine Eq.trans ?_ (marginal.trans ?_)
    · simp only [phaseJoint, PMF.map_bind, PMF.map_comp, Function.comp_def]
      apply bind_congr_on_support _
      intro seed supported
      rw [← stopEq seed supported]
    · simp only [stepSource, PMF.map_bind, PMF.map_comp, Function.comp_def]
  · intro seed
    simpa only [sampleSuccessor, tailRefs, tailEmbedding, OutputEmbedding.ref] using
      (aligned seed).sampleTail setup.program wholeProfile (_openNames := names)
        fresh distribution next profile refs (source seed).revelations
          (source seed).registry embedding refsBefore offset
  · intro seed final
    rfl
  · intro seed _
    generalize source seed = config
    rw [show eventCount (SourceProgram.sample name fresh distribution next) =
      eventCount next + 1 from rfl, ProtocolState.behavioralStatePrefix_sample]
    simp only [stepSource, PMF.bind_map, PMF.map_bind, Function.comp_def]

/-- **An honest block of commitments.** On a reveal-relaxed graph a maximal run of
commitments is drawn in advance from the owners' source kernels; the honest law
of the program after it gives the program's. -/
theorem HonestLaw.commits_step [Fintype Player]
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (relaxed : (serviceGraph setup mode).RevealRelaxedOrdered)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (admits : ResidualProperty Player L)
    (admitsTail : ∀ {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (count : Nat)
      (prefixed : CommitPrefix program count) (profile : BehavioralProfile program)
      (registry : Registry Γ) (revelations : Revelations Γ),
      admits program profile registry revelations →
        admits (commitTail count program prefixed).tail
          (commitTailProfile count program prefixed profile)
          (commitTailRegistry count program prefixed registry)
          (commitTailRevelations count program prefixed revelations))
    {Γ : SourceCtx Player L} {names : Finset VarId} {program : SourceProgram Player L Γ names}
    {offset : Nat} {rest : List Nat} (count : Nat) (prefixed : CommitPrefix program count)
    (positive : 0 < count)
    (maximal : leadingCommits (commitTail count program prefixed).tail = 0)
    (ih : ∀ (profile : BehavioralProfile (commitTail count program prefixed).tail)
      (refs : ContextRefs (graphLayout setup.program) (commitTail count program prefixed).context)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (commitTail count program prefixed).tail)
      (refsBefore : ContextRefsBefore refs embedding),
      HonestLaw setup leaks horizon scheduler
        (serviceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) wholeProfile)
        wholeProfile admits (commitTail count program prefixed).tail profile refs embedding
        refsBefore (offset + count) rest) :
    ∀ (profile : BehavioralProfile program) (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding),
      HonestLaw setup leaks horizon scheduler
        (serviceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) wholeProfile)
        wholeProfile admits program profile refs embedding refsBefore offset
        ((offset + count) :: rest) := by
  let app := serviceApplication setup mode deadline leaks
  let players := serviceTurnPolicy setup mode deadline leaks bound turns
    (firstTurnTiming setup turns mode) wholeProfile
  intro profile refs embedding refsBefore Seed prior source execution aligned checkpoint
    boundary bounded effective
  have anyone : Player := by
    cases count with
    | zero => omega
    | succ count =>
        cases program with
        | commit _ owner _ _ _ => exact owner
        | ret _ => exact prefixed.elim
        | sample _ _ _ _ => exact prefixed.elim
        | reveal _ _ _ _ _ _ _ => exact prefixed.elim
  let tailRefs := commitTailRefs setup count program prefixed refs embedding
  let tailEmbedding := commitTailEmbedding setup count program prefixed embedding
  have tailBefore : ContextRefsBefore tailRefs tailEmbedding :=
    commitTailRefsBefore count program prefixed refs embedding refsBefore
  have tailAligned (seed : Seed) := CompiledPolicySuffix.commitTailMany wholeProfile count
    program prefixed profile refs (source seed).revelations (source seed).registry embedding
    refsBefore offset (aligned seed)
  have wall : BlockEnd setup mode (offset + count) :=
    CompiledSuffix.blockEnd maximal (tailAligned prior.support_nonempty.choose).graphSuffix
  have bindings : ∀ event : (serviceGraph setup mode).EventId, offset ≤ event.val →
      event.val < offset + count → ∃ owner payload outputEq codeEq,
        EventGraphRuntime.nodeView (serviceGraph setup mode) event =
          .bind owner payload outputEq codeEq := by
    intro event lower upper
    have within := prefixed.le_eventCount
    obtain ⟨index, below, same⟩ : ∃ index : Fin (eventCount program), index.val < count ∧
        embedding.event index = event := by
      refine ⟨⟨event.val - offset, by omega⟩, by simp only; omega, ?_⟩
      apply Fin.ext
      rw [(aligned prior.support_nonempty.choose).graphSuffix.rankEq]
      simp only
      omega
    subst same
    exact CompiledSuffix.commitPrefix_bind count program prefixed refs _ _ embedding
      refsBefore offset (aligned prior.support_nonempty.choose).graphSuffix index below
  have nextFacts (point : PhasePoint setup leaks horizon scheduler players (offset + count)
      prior execution) :
      CompletionBoundary setup leaks scheduler players (offset + count) point.val.2 ∧
        point.val.2.environmentRecall.length ≤ horizon := by
    obtain ⟨supported, reached⟩ := phaseJoint_mem setup leaks horizon scheduler players
      point.property
    have done := blockRun_completes contract.completes (offset + count)
      (execution point.val.1) (boundary _ supported) (bounded _ supported) _ reached
    obtain ⟨nextBounded, nextBoundary⟩ := blockRun_boundary (Nat.le_add_right _ _)
      (BlockEnd.sealed_relaxed relaxed wall (plain_of_bindings bindings)) wall.1
      (execution point.val.1) (boundary _ supported) (bounded _ supported) _ reached done
    exact ⟨nextBoundary, nextBounded⟩
  have block := honest_block_law relaxed wall contract timely turns
    wholeProfile bindings
    program profile count prefixed refs embedding refsBefore rfl anyone prior source execution
    aligned checkpoint boundary bounded
  refine HonestLaw.phase setup leaks horizon scheduler players wholeProfile admits
    program
    profile refs embedding (commitTail count program prefixed).tail
    (commitTailProfile count program prefixed profile) tailRefs tailEmbedding tailBefore
    (offset + count) rest (ih _ tailRefs tailEmbedding tailBefore) prior source execution
    (commitTail count program prefixed).lift
    ((commitTail_lift_injective count program prefixed).comp
      (ProtocolState.entry_injective _))
    (fun seed => commitTailRegistry count program prefixed (source seed).registry)
    (fun seed => commitTailRevelations count program prefixed (source seed).revelations)
    (fun seed final => decodeSourcePrefix? program refs (source seed).registry
      (source seed).revelations embedding.ref count final.application.config.store
      (decodeHistory setup.program (final.application.config.history.map
        (setup.eventGraph.fromModeCompletion mode))))
    (fun seed final => decodeSourcePrefix?_commitTail_entry count program prefixed refs _ _
      embedding _ _)
    (fun config => listChain (fun _ => True) count program profile prefixed config []) ?_
    (fun point => (nextFacts point).1) (fun point => (nextFacts point).2) tailAligned
    (fun seed => admitsTail program count prefixed profile _ _ (effective seed)) ?_ ?_
  · simp only [PMF.map_bind] at block
    simp only [phaseJoint, PMF.map_bind, PMF.map_comp, Function.comp_def]
    exact block
  · intro seed final
    have through := decodeSourcePrefix?_commitTail count program prefixed refs
      (source seed).registry (source seed).revelations embedding
      (eventCount (commitTail count program prefixed).tail) final.application.config.store
      (decodeHistory setup.program (final.application.config.history.map
        (setup.eventGraph.fromModeCompletion mode)))
    rw [eventCount_commitTail] at through
    exact through
  · intro seed _
    generalize source seed = config
    have chained := iterate_listChain_all count program profile prefixed
      (eventCount (commitTail count program prefixed).tail) config
    rw [eventCount_commitTail] at chained
    rw [PMF.map_bind]
    exact chained

/-- **The honest law over every phase.** On a barrier-ordered graph, under
the asynchronous contract with timely delays, when every player follows the
first-turn client of a source profile, the phases of any residual program
decode to the law of the source run of the residual profile. -/
theorem honestLaw [Fintype Player]
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (ordered : (serviceGraph setup mode).BarrierOrdered)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program)
    {Γ : SourceCtx Player L} {names : Finset VarId} {program : SourceProgram Player L Γ names}
    {offset : Nat} {ends : List Nat} (phases : PhaseEnds program offset ends) :
    ∀ (profile : BehavioralProfile program) (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding),
      HonestLaw setup leaks horizon scheduler
        (serviceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) wholeProfile)
        wholeProfile effectiveResidual program profile refs embedding refsBefore offset ends := by
  let app := serviceApplication setup mode deadline leaks
  let players := serviceTurnPolicy setup mode deadline leaks bound turns
    (firstTurnTiming setup turns mode) wholeProfile
  induction phases with
  | ret payoffs offset =>
      intro profile refs embedding refsBefore Seed prior source execution _aligned checkpoint
        _boundary _bounded _effective
      apply bind_congr_on_support _
      intro seed _
      simp only [deviationPhases, eventCount, Function.iterate_zero, id_eq, PMF.pure_map]
      rw [(checkpoint seed).decode (.ret payoffs) embedding.ref]
  | @sample Γ names name payload fresh distribution next offset rest _ ih =>
      exact HonestLaw.sample_step setup leaks ordered.revealRelaxedOrdered contract turns
        wholeProfile effectiveResidual (fun _ _ _ effective => effective) ih
  | @reveal Γ names published name owner payload fresh binding unresolved next offset rest _
      ih =>
      intro profile refs embedding refsBefore Seed prior source execution aligned checkpoint
        boundary bounded effective
      let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
        ⟨0, by simp [eventCount]⟩
      let event : (serviceGraph setup mode).EventId := embedding.event index
      have eventRank : event.val = offset := by
        simpa only [event, index, Fin.val_zero, Nat.add_zero] using
          (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
      have outputEq : (serviceGraph setup mode).outputLayout event = .publication payload := by
        change outputLayout setup.program event = _
        simpa [event, index, outputLayout, eventCount] using embedding.layout_eq index
      have alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
          cut.Ready other → other = event := fun cut other ready otherReady =>
        ordered.ready_public_unique cut (by rw [outputEq]; trivial) ready otherReady
      have boundaryAt (seed : Seed) (supported : seed ∈ prior.support) :
          CompletionBoundary setup leaks scheduler players event.val (execution seed) := by
        rw [eventRank]
        exact boundary seed supported
      have stopEq (seed : Seed) (supported : seed ∈ prior.support) :
          app.runUntilHorizon scheduler players
              (fun final => event ∈ final.application.config.cut.completed) horizon
              (execution seed) =
            app.runUntilHorizon scheduler players (BlockDone (offset + 1)) horizon
              (execution seed) := by
        have stopped := runUntilHorizon_eventDone_eq_blockDone horizon event alone _
          (boundaryAt seed supported)
        rwa [eventRank] at stopped
      have nextFacts (point : PhasePoint setup leaks horizon scheduler players (offset + 1) prior
          execution) :
          CompletionBoundary setup leaks scheduler players (offset + 1) point.val.2 ∧
            point.val.2.environmentRecall.length ≤ horizon := by
        obtain ⟨supported, reached⟩ := phaseJoint_mem setup leaks horizon scheduler players
          point.property
        rw [← stopEq _ supported] at reached
        obtain ⟨_, _, _, nextBounded, nextBoundary⟩ := completionRun_boundary_step
          contract.completes event alone (execution point.val.1) (boundaryAt _ supported)
          (bounded _ supported) point.val.2 reached
        rw [eventRank] at nextBoundary
        exact ⟨nextBoundary, nextBounded⟩
      -- The owner is honest: the honest players are the owner deviating to its own client.
      have selfDeviation : deviatedTurnProfile bound turns (firstTurnTiming setup turns mode)
          wholeProfile owner (players owner) = players := Function.update_eq_self _ _
      obtain ⟨phaseLaw, decidedDecode⟩ := reveal_phase_decided contract timely turns
        wholeProfile owner (players owner) (by rw [selfDeviation]) fresh binding unresolved next
        profile refs embedding refsBefore offset alone prior source execution aligned checkpoint
        (by rw [selfDeviation]; exact boundary) bounded (fun seed _ => effective seed owner)
      rw [selfDeviation] at phaseLaw
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
      let stepSource := fun config : Config Player L Γ =>
        (revealKernel profile (config.view owner)).map (revealSuccessor published binding config)
      refine HonestLaw.phase setup leaks horizon scheduler players wholeProfile effectiveResidual
        (.reveal published owner name fresh binding unresolved next) profile refs embedding next
        (afterReveal profile) tailRefs tailEmbedding tailBefore (offset + 1) rest
        (ih (afterReveal profile) tailRefs tailEmbedding tailBefore) prior source execution
        Sum.inr (Sum.inr_injective.comp (ProtocolState.entry_injective next))
        (fun seed => (source seed).registry.weaken)
        (fun seed => Revelations.reveal (published := published) (source seed).revelations
          binding)
        (fun seed final => decodeSourcePrefix?
          (.reveal published owner name fresh binding unresolved next) refs
          (source seed).registry (source seed).revelations embedding.ref 1
          final.application.config.store (decodeHistory setup.program
            (final.application.config.history.map (setup.eventGraph.fromModeCompletion mode))))
        ?_ stepSource ?_ (fun point => (nextFacts point).1)
        (fun point => (nextFacts point).2) ?_ (fun seed player => (effective seed player).2) ?_
        ?_
      · intro seed final
        simp only [decodeSourcePrefix?, Option.map_map, Function.comp_def]
        rfl
      · simp only [phaseJoint, PMF.map_bind, PMF.map_comp, Function.comp_def, stepSource,
          PMF.bind_map]
        apply bind_congr_on_support _
        intro seed supported
        rw [← stopEq seed supported, phaseLaw seed supported, PMF.map_bind,
          ← PMF.bind_pure_comp]
        apply bind_congr_on_support _
        intro disclose chosen
        rw [map_congr_on_support _ (g := fun _ => some (Sum.inr (ProtocolState.entry next
          (revealSuccessor published binding (source seed) disclose))))
          (fun final reached => decidedDecode seed supported disclose chosen final reached),
          pmf_map_fun_const]
        rfl
      · intro seed
        simpa only [revealSuccessor, tailRefs, tailEmbedding, OutputEmbedding.ref] using
          (aligned seed).revealTail (whole := setup.program) (wholeProfile := wholeProfile)
            fresh binding unresolved next profile refs (source seed).revelations
              (source seed).registry embedding refsBefore offset
      · intro seed final
        rfl
      · intro seed _
        generalize source seed = config
        rw [show eventCount (SourceProgram.reveal published owner name fresh binding unresolved
            next) = eventCount next + 1 from rfl, ProtocolState.behavioralStatePrefix_reveal]
        simp only [stepSource, PMF.bind_map, PMF.map_bind, Function.comp_def]
  | @block Γ names program offset rest count prefixed positive maximal _ ih =>
      exact HonestLaw.commits_step setup leaks ordered.revealRelaxedOrdered contract timely turns
        wholeProfile effectiveResidual
        (fun program count prefixed profile registry revelations effective player =>
          effective_commitTail (who := player) count program prefixed profile registry
            revelations (effective player))
        count prefixed positive maximal ih


/-- **The honest law from initialization.** When every player follows the
first-turn client of a source profile that admits the initial registry and
revelations, and the whole program has the honest law over its phases `ends`,
the phases from the initial law decode to the source protocol's state law of the
profile. -/
theorem firstTurn_initialized_law [Fintype Player]
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat} (turns : Nat)
    (profile : BehavioralProfile setup.program) (admits : ResidualProperty Player L)
    (admitted : admits setup.program profile [] (Revelations.initial setup.context))
    {ends : List Nat}
    (honest : HonestLaw setup leaks horizon scheduler
      (serviceTurnPolicy setup mode deadline leaks bound turns (firstTurnTiming setup turns mode)
        profile) profile admits setup.program profile
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program) (initialRefsBefore setup.program) 0 ends) :
    (((serviceInitialLaw setup mode).bind fun state =>
      deviationPhases scheduler (serviceTurnPolicy setup mode deadline leaks bound turns
        (firstTurnTiming setup turns mode) profile) horizon ends
        (ReactiveApplication.Execution.initial (serviceApplication setup mode deadline leaks)
          state)).map fun final =>
        serviceSourcePrefix? setup mode (eventCount setup.program) final.application.config) =
      setup.initialLaw.bind fun initial =>
        ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program profile))^[
          eventCount setup.program]
          (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).map
            some := by
  let app := serviceApplication setup mode deadline leaks
  let players := serviceTurnPolicy setup mode deadline leaks bound turns
    (firstTurnTiming setup turns mode) profile
  let Seed := {initial // initial ∈ setup.initialLaw.support}
  let prior : PMF Seed := pmfToSubtype setup.initialLaw (fun _ member => member)
  let source := fun seed : Seed => setup.initialConfig seed.val
  let execution := fun seed : Seed => ReactiveApplication.Execution.initial app
    (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
      (setup.eventInputs seed.val))
  have initialBoundary (seed : Seed) : CompletionBoundary setup leaks scheduler players 0
      (execution seed) := by
    refine ⟨?_, EventOrder.Cut.empty_isPrefix _, ?_⟩
    · change execution seed ∈ (app.roundsFrom (serviceInitialLaw setup mode) scheduler
        players 0).support
      unfold ReactiveApplication.roundsFrom
      simp only [ReactiveApplication.runRounds, serviceInitialLaw]
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨_, (PMF.mem_support_map_iff _ _ _).mpr
        ⟨seed.val, seed.property, rfl⟩, (PMF.mem_support_pure_iff _ _).mpr rfl⟩
    · intro event _ observer entry member
      cases member
  have law := honest prior source execution
    (fun _ => CompiledPolicySuffix.whole setup.program profile)
    (fun seed => SourceCheckpoint.initial setup seed.val)
    (fun seed _ => initialBoundary seed) (fun _ _ => Nat.zero_le _)
    (fun _ => admitted)
  let combined := fun initial : State L setup.context =>
    (deviationPhases scheduler players horizon ends
      (ReactiveApplication.Execution.initial app
        (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
          (setup.eventInputs initial)))).map
      fun final => serviceSourcePrefix? setup mode (eventCount setup.program)
        final.application.config
  let sourcePrefix := fun initial : State L setup.context =>
    ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program profile))^[
      eventCount setup.program]
      (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).map some
  have nativeLaw : prior.bind (fun seed => combined seed.val) =
      setup.initialLaw.bind combined := by
    refine (PMF.bind_map prior Subtype.val combined).symm.trans ?_
    exact congrArg (fun law => law.bind combined) (map_val_pmfToSubtype _ _)
  have sourceLaw : prior.bind (fun seed => sourcePrefix seed.val) =
      setup.initialLaw.bind sourcePrefix := by
    refine (PMF.bind_map prior Subtype.val sourcePrefix).symm.trans ?_
    exact congrArg (fun law => law.bind sourcePrefix) (map_val_pmfToSubtype _ _)
  change (prior.bind fun seed => combined seed.val) =
    (prior.bind fun seed => sourcePrefix seed.val) at law
  rw [nativeLaw, sourceLaw] at law
  rw [serviceInitialLaw, PMF.bind_map, PMF.map_bind]
  exact law

/-- The first-turn clients of a source profile have the typed outcome law of
the profile's source run. -/
def FirstTurnSourceLaw (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode) (deadline : (serviceGraph setup mode).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) : Prop :=
  ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
    scheduler (serviceTurnPolicy setup mode deadline leaks bound turns
      (firstTurnTiming setup turns mode) profile) horizon).map
      (fun execution => serviceSourceReadout setup mode deadline leaks
        ((serviceApplication setup mode deadline leaks).finished execution)) =
    (setup.run profile).map some

/-- **The first-turn clients have the source outcome law, from an honest law.**
When every player follows the first-turn client of a source profile that admits
the initial registry and revelations, the whole program has the honest law over
its phases `ends`, and those phases stop at the end of the graph, the typed
outcome has exactly the source law of the profile. -/
theorem firstTurn_readout_law_of_honest [Fintype Player]
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat} (turns : Nat)
    (profile : BehavioralProfile setup.program) (admits : ResidualProperty Player L)
    (admitted : admits setup.program profile [] (Revelations.initial setup.context))
    {ends : List Nat}
    (honest : HonestLaw setup leaks horizon scheduler
      (serviceTurnPolicy setup mode deadline leaks bound turns (firstTurnTiming setup turns mode)
        profile) profile admits setup.program profile
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program) (initialRefsBefore setup.program) 0 ends)
    (terminates : ∀ execution : (serviceApplication setup mode deadline leaks).Execution,
      CompletionBoundary setup leaks scheduler (serviceTurnPolicy setup mode deadline leaks bound
        turns (firstTurnTiming setup turns mode) profile) 0 execution →
      execution.environmentRecall.length ≤ horizon →
      ∀ final ∈ (deviationPhases scheduler (serviceTurnPolicy setup mode deadline leaks bound
        turns (firstTurnTiming setup turns mode) profile) horizon ends execution).support,
        CompletionBoundary setup leaks scheduler (serviceTurnPolicy setup mode deadline leaks bound
          turns (firstTurnTiming setup turns mode) profile) (eventCount setup.program) final) :
    ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
      scheduler (serviceTurnPolicy setup mode deadline leaks bound turns
        (firstTurnTiming setup turns mode) profile) horizon).map
        (fun execution => serviceSourceReadout setup mode deadline leaks
          ((serviceApplication setup mode deadline leaks).finished execution)) =
      (setup.run profile).map some := by
  classical
  let app := serviceApplication setup mode deadline leaks
  let players := serviceTurnPolicy setup mode deadline leaks bound turns
    (firstTurnTiming setup turns mode) profile
  have joint := firstTurn_initialized_law setup leaks turns profile admits admitted honest
  have physical : (app.roundsFrom (serviceInitialLaw setup mode) scheduler players horizon).map
      (fun execution => serviceSourceReadout setup mode deadline leaks (app.finished execution)) =
      ((serviceInitialLaw setup mode).bind fun state => deviationPhases scheduler players
        horizon ends (ReactiveApplication.Execution.initial app state)).map
          (fun final => serviceSourceReadout setup mode deadline leaks (app.finished final)) := by
    unfold ReactiveApplication.roundsFrom
    rw [PMF.map_bind, PMF.map_bind]
    apply bind_congr_on_support _
    intro state stateSupport
    have toHorizon : app.runRounds scheduler players horizon
        (ReactiveApplication.Execution.initial app state) =
        app.runToHorizon scheduler players horizon
          (ReactiveApplication.Execution.initial app state) := rfl
    rw [toHorizon, runToHorizon_eq_deviationPhases_bind scheduler players horizon ends,
      PMF.map_bind]
    rw [← PMF.bind_pure_comp]
    apply bind_congr_on_support _
    intro final reached
    have initialBoundary : CompletionBoundary setup leaks scheduler players 0
        (ReactiveApplication.Execution.initial app state) := by
      refine ⟨?_, ?_, ?_⟩
      · change ReactiveApplication.Execution.initial app state ∈
          (app.roundsFrom (serviceInitialLaw setup mode) scheduler players 0).support
        unfold ReactiveApplication.roundsFrom
        exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨state, stateSupport,
          (PMF.mem_support_pure_iff _ _).mpr rfl⟩
      · obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ stateSupport
        exact EventOrder.Cut.empty_isPrefix _
      · intro event _ observer entry member
        cases member
    have finalBoundary := terminates _ initialBoundary (Nat.zero_le _) final reached
    have terminal : final.application.config.cut.IsPrefix
        (serviceGraph setup mode).order.eventCount := finalBoundary.ordered
    unfold ReactiveApplication.runToHorizon
    rw [map_congr_on_support _
      (g := fun _ => serviceSourceReadout setup mode deadline leaks (app.finished final))
      (fun next moved => by
        have same := runRounds_config_terminal scheduler players _ final next terminal moved
        change serviceSourceReadout setup mode deadline leaks (some ⟨0, none, next⟩) =
          serviceSourceReadout setup mode deadline leaks (some ⟨0, none, final⟩)
        simp only [serviceSourceReadout, Option.bind_some, same]), pmf_map_fun_const]
    rfl
  rw [physical]
  have projected := congrArg (PMF.map setup.protocolReadout) joint
  simp only [PMF.map_comp, Function.comp_def, PMF.map_bind] at projected
  simp only [serviceSourcePrefix?_terminal_readout] at projected
  have admitted (player : Player) :
      (profile player).Admitted setup.program (CommitmentInterface.forfeiture setup.program) :=
    BehavioralPolicy.admitted_forfeiture setup.program _
  have encodedState := setup.encoded_prefix_state (CommitmentInterface.forfeiture setup.program)
    profile admitted (eventCount setup.program)
  have sourceLaw := setup.protocol_runBehavioral_eq (CommitmentInterface.forfeiture setup.program)
    profile admitted
  rw [InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom] at sourceLaw
  have encodedReadout := congrArg (PMF.map setup.protocolReadout) encodedState
  simp only [PMF.map_comp, Function.comp_def, PMF.map_bind] at encodedReadout
  have terminal := projected.trans (encodedReadout.symm.trans (by
    simpa only [eventCount_eq_instructionCount, InformationModel.runBehavioral] using sourceLaw))
  have readoutEq (final : app.Execution) :
      serviceSourceReadout setup mode deadline leaks (app.finished final) =
        decodeState? (terminalRefs setup.program) final.application.config.store :=
    serviceSourceReadout_eq_decode setup leaks ⟨0, none, final⟩
  simp only [readoutEq, PMF.map_bind]
  exact terminal

/-- **The first-turn clients have the source outcome law.** On a
barrier-ordered graph, under a scheduler satisfying the asynchronous contract
with timely delays, when every player follows the first-turn client of a source
profile with effective disclosures, the typed outcome has exactly the source
law of the profile. -/
theorem firstTurn_readout_law [Finite Player]
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (ordered : (serviceGraph setup mode).BarrierOrdered)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (profile : BehavioralProfile setup.program)
    (effective : ∀ player, (profile player).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context)) :
    ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
      scheduler (serviceTurnPolicy setup mode deadline leaks bound turns
        (firstTurnTiming setup turns mode) profile) horizon).map
        (fun execution => serviceSourceReadout setup mode deadline leaks
          ((serviceApplication setup mode deadline leaks).finished execution)) =
      (setup.run profile).map some := by
  have := Fintype.ofFinite Player
  obtain ⟨ends, phases⟩ := PhaseEnds.exists (eventCount setup.program) setup.program rfl 0
  exact firstTurn_readout_law_of_honest setup leaks turns profile effectiveResidual effective
    (honestLaw setup leaks ordered contract timely turns profile phases profile _ _
      (initialRefsBefore setup.program))
    (fun execution boundary bounded final reached => (PhaseEnds.boundary ordered
      contract.completes _ profile phases profile _ _ _ (outputEmbedding setup.program)
      (initialRefsBefore setup.program) (CompiledPolicySuffix.whole setup.program profile)
      execution boundary bounded final reached).1)

end Vegas
