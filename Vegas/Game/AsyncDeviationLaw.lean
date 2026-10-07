/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncDeviationChoice
import Vegas.Game.ServiceBlockLaw
import Vegas.Game.ServiceCommitTail
import Vegas.Game.SourceServicePrefixFactorization

/-! # The law of one deviation, phase by phase, on barrier-ordered graphs

Against the first-turn clients of a source profile, under a scheduler
satisfying the asynchronous contract, one player follows an arbitrary native
policy. On a barrier-ordered graph the run splits into phases
(`Vegas.PhaseEnds`): a maximal run of commitments is one phase, completed by
`Vegas.asyncDeviation_block_factorization`, and every public event is a phase
of its own, completed by the public-event factorizations. Phase by phase, the
decoded source state has the law of the source protocol in which the deviator
follows one source behavioral policy and every other player keeps its source
policy; jointly, the deviator's traffic depends on the source state only
through the deviator's source view
(`Vegas.asyncDeviation_deviationLaw`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime
open GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Phases

variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- The runs of a list of phases in turn, each until its end is done, each
within the horizon. -/
def deviationPhases (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (horizon : Nat) :
    List Nat → (serviceApplication setup mode deadline leaks).Execution →
      PMF (serviceApplication setup mode deadline leaks).Execution
  | [], execution => PMF.pure execution
  | high :: rest, execution =>
      ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler players
        (BlockDone high) horizon execution).bind (deviationPhases scheduler players horizon rest)

end Phases

/-- The number of leading commitments of a program. -/
def leadingCommits : {Γ : SourceCtx Player L} → {names : Finset VarId} →
    SourceProgram Player L Γ names → Nat
  | _, _, .commit _ _ _ _ next => leadingCommits next + 1
  | _, _, .ret _ => 0
  | _, _, .sample _ _ _ _ => 0
  | _, _, .reveal _ _ _ _ _ _ _ => 0

/-- A program's leading commitments are commitments. -/
theorem leadingCommits_prefix : ∀ {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names), CommitPrefix program (leadingCommits program)
  | _, _, .commit _ _ _ _ next => leadingCommits_prefix next
  | _, _, .ret _ => trivial
  | _, _, .sample _ _ _ _ => trivial
  | _, _, .reveal _ _ _ _ _ _ _ => trivial

/-- After all its leading commitments, a program has none left. -/
theorem leadingCommits_commitTail : ∀ {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names),
    leadingCommits (commitTail (leadingCommits program) program
      (leadingCommits_prefix program)).tail = 0
  | _, _, .commit _ _ _ _ next => leadingCommits_commitTail next
  | _, _, .ret _ => rfl
  | _, _, .sample _ _ _ _ => rfl
  | _, _, .reveal _ _ _ _ _ _ _ => rfl

/-- Leading commitments are events counted by the program. -/
theorem eventCount_commitTail : ∀ (count : Nat) {Γ : SourceCtx Player L}
    {names : Finset VarId} (program : SourceProgram Player L Γ names)
    (prefixed : CommitPrefix program count),
    count + eventCount (commitTail count program prefixed).tail = eventCount program := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed; simp [commitTail]
  | succ count ih =>
      intro Γ names program prefixed
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ next =>
          have := ih next prefixed
          simp only [commitTail, eventCount] at this ⊢
          omega

/-- **The phases of a program from a rank.** A maximal run of commitments is one
phase; every other operation is a phase of its own. Each phase is named by the
rank its end leaves completed. -/
inductive PhaseEnds : {Γ : SourceCtx Player L} → {names : Finset VarId} →
    SourceProgram Player L Γ names → Nat → List Nat → Prop
  | ret {Γ : SourceCtx Player L} (payoffs) (offset : Nat) :
      PhaseEnds (.ret (Γ := Γ) payoffs) offset []
  | sample {Γ : SourceCtx Player L} {names : Finset VarId} {name : VarId} {payload : L.Ty}
      {fresh : name ∉ Γ.map Prod.fst} {law : L.DistExpr (SourcePublicCtx L Γ) payload}
      {next : SourceProgram Player L ((name, .publicData payload) :: Γ) names}
      {offset : Nat} {rest : List Nat} :
      PhaseEnds next (offset + 1) rest →
      PhaseEnds (.sample name fresh law next) offset ((offset + 1) :: rest)
  | reveal {Γ : SourceCtx Player L} {names : Finset VarId} {published name : VarId}
      {owner : Player} {payload : L.Ty} {fresh : published ∉ Γ.map Prod.fst}
      {selected : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ names}
      {next : SourceProgram Player L ((published, .publication payload) :: Γ) (names.erase name)}
      {offset : Nat} {rest : List Nat} :
      PhaseEnds next (offset + 1) rest →
      PhaseEnds (.reveal published owner name fresh selected unresolved next) offset
        ((offset + 1) :: rest)
  | block {Γ : SourceCtx Player L} {names : Finset VarId}
      {program : SourceProgram Player L Γ names} {offset : Nat} {rest : List Nat}
      (count : Nat) (prefixed : CommitPrefix program count) (positive : 0 < count)
      (maximal : leadingCommits (commitTail count program prefixed).tail = 0) :
      PhaseEnds (commitTail count program prefixed).tail (offset + count) rest →
      PhaseEnds program offset ((offset + count) :: rest)

/-- Every program has its phases from every rank. -/
theorem PhaseEnds.exists : ∀ (size : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names), eventCount program = size →
    ∀ offset, ∃ ends, PhaseEnds program offset ends := by
  intro size
  induction size using Nat.strong_induction_on with
  | _ size ih =>
      intro Γ names program sized offset
      by_cases leading : leadingCommits program = 0
      · cases program with
        | ret payoffs => exact ⟨[], .ret payoffs offset⟩
        | sample name fresh law next =>
            obtain ⟨rest, ends⟩ := ih (eventCount next) (by simp [eventCount] at sized; omega)
              next rfl (offset + 1)
            exact ⟨_, .sample ends⟩
        | reveal published owner name fresh selected unresolved next =>
            obtain ⟨rest, ends⟩ := ih (eventCount next) (by simp [eventCount] at sized; omega)
              next rfl (offset + 1)
            exact ⟨_, .reveal ends⟩
        | commit => simp [leadingCommits] at leading
      · have counted := eventCount_commitTail (leadingCommits program) program
          (leadingCommits_prefix program)
        obtain ⟨rest, ends⟩ := ih (eventCount (commitTail (leadingCommits program) program
          (leadingCommits_prefix program)).tail) (by omega) _ rfl
          (offset + leadingCommits program)
        exact ⟨_, .block (leadingCommits program) (leadingCommits_prefix program)
          (Nat.pos_of_ne_zero leading) (leadingCommits_commitTail program) ends⟩

section Law

variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
  (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
  (players : Player → (serviceApplication setup mode deadline leaks).Policy)
  (wholeProfile : BehavioralProfile setup.program) (who : Player)

/-- **The deviation law of a residual program.** From completion boundaries at
rank `offset` that the source configurations of a seed law check, whenever the
deviator's traffic factors through its source view, the phases `ends` give
the decoded state of the residual program jointly with the deviator's traffic
the law of a source run in which the deviator follows one source policy, with
the traffic factoring through the deviator's source observation. -/
def DeviationLaw [Fintype Player] {Γ : SourceCtx Player L} {names : Finset VarId}
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
    (∀ seed player, (profile player).EffectiveDisclosures program (source seed).registry
      (source seed).revelations) →
    ∀ (noise : DecisionView who Γ → PMF _),
    prior.map (fun seed => (source seed,
        (serviceRuntime setup mode deadline).bindingTraffic leaks who (execution seed))) =
      (prior.map source).bind (fun config =>
        (noise (config.view who)).map fun extra => (config, extra)) →
    ∃ policy : BehavioralPolicy who program,
      ∃ nextNoise : Option (ProtocolView who program) → PMF _,
        (prior.bind fun seed =>
          (deviationPhases scheduler players horizon ends (execution seed)).map fun final =>
            (decodeSourcePrefix? program refs (source seed).registry (source seed).revelations
              embedding.ref (eventCount program) final.application.config.store
              (decodeHistory setup.program (final.application.config.history.map
                (setup.eventGraph.fromModeCompletion mode))),
              (serviceRuntime setup mode deadline).bindingTraffic leaks who final)) =
          (prior.bind fun seed =>
            ((fun law => law.bind (ProtocolState.behavioralStateStep program
              (Function.update profile who policy)))^[eventCount program]
              (PMF.pure (ProtocolState.entry program (source seed)))).map some).bind
            fun state => (nextNoise (state.map (ProtocolState.observe who program))).map
              fun extra => (state, extra)

/-- The points a first phase ending at `high` reaches, paired with their seeds. -/
abbrev phaseJoint {Seed : Type} (high : Nat) (prior : PMF Seed)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution) :
    PMF (Seed × (serviceApplication setup mode deadline leaks).Execution) :=
  prior.bind fun seed =>
    ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler players
      (BlockDone high) horizon (execution seed)).map fun final => (seed, final)

/-- A point a first phase ending at `high` reaches. -/
abbrev PhasePoint {Seed : Type} (high : Nat) (prior : PMF Seed)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution) : Type :=
  {point // point ∈ (phaseJoint setup leaks horizon scheduler players high prior
    execution).support}

/-- **Finishing a phase.** If the first phase of a program, ending at `high`,
reconstructs a residual configuration for every reached point, with the source
law of the phase given by a source step kernel, and the residual program has the
deviation law over the remaining phases, then the program has it over all of
its phases. -/
theorem DeviationLaw.finish [Fintype Player] {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    {Δ : SourceCtx Player L} {tailNames : Finset VarId}
    (tail : SourceProgram Player L Δ tailNames) (tailProfile : BehavioralProfile tail)
    (tailRefs : ContextRefs (graphLayout setup.program) Δ)
    (tailEmbedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      tail)
    (tailBefore : ContextRefsBefore tailRefs tailEmbedding) (high : Nat) (rest : List Nat)
    (tailLaw : DeviationLaw setup leaks horizon scheduler players wholeProfile who tail
      tailProfile tailRefs tailEmbedding tailBefore high rest)
    {Seed : Type} (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution)
    (nextSource : PhasePoint setup leaks horizon scheduler players high prior execution →
      Config Player L Δ)
    (nextAligned : ∀ point :
      PhasePoint setup leaks horizon scheduler players high prior execution,
      CompiledPolicySuffix setup.program wholeProfile tail tailProfile
      tailRefs (nextSource point).revelations (nextSource point).registry tailEmbedding tailBefore
      high)
    (nextCheckpoint : ∀ point :
      PhasePoint setup leaks horizon scheduler players high prior execution,
      SourceCheckpoint setup (nextSource point) tailRefs high
      point.val.2.application.config)
    (nextBoundary : ∀ point :
      PhasePoint setup leaks horizon scheduler players high prior execution,
      CompletionBoundary setup leaks scheduler players high point.val.2)
    (nextBounded : ∀ point :
      PhasePoint setup leaks horizon scheduler players high prior execution,
      point.val.2.environmentRecall.length ≤ horizon)
    (nextEffective : ∀ (point :
      PhasePoint setup leaks horizon scheduler players high prior execution) player,
      (tailProfile player).EffectiveDisclosures tail
      (nextSource point).registry (nextSource point).revelations)
    (nextNoise : DecisionView who Δ → PMF _)
    (nextFactor : (pmfToSubtype
        (phaseJoint setup leaks horizon scheduler players high prior execution)
        (fun _ member => member)).map (fun point => (nextSource point,
          (serviceRuntime setup mode deadline).bindingTraffic leaks who point.val.2)) =
      ((pmfToSubtype
        (phaseJoint setup leaks horizon scheduler players high prior execution)
        (fun _ member => member)).map nextSource).bind fun config =>
        (nextNoise (config.view who)).map fun extra => (config, extra))
    (stepSource : Config Player L Γ → PMF (Config Player L Δ))
    (nextMarginal : (pmfToSubtype
        (phaseJoint setup leaks horizon scheduler players high prior execution)
        (fun _ member => member)).map nextSource = (prior.map source).bind stepSource)
    (lift : ProtocolState tail → ProtocolState program)
    (recover : Option (ProtocolView who program) → Option (ProtocolView who tail))
    (recovers : ∀ state : Option (ProtocolState tail),
      recover ((state.map lift).map (ProtocolState.observe who program)) =
        state.map (ProtocolState.observe who tail))
    (decodeLater : ∀ (point : PhasePoint setup leaks horizon scheduler players high prior
        execution)
      (final : (serviceApplication setup mode deadline leaks).Execution),
      decodeSourcePrefix? program refs (source point.val.1).registry
        (source point.val.1).revelations embedding.ref (eventCount program)
          final.application.config.store (decodeHistory setup.program
            (final.application.config.history.map (setup.eventGraph.fromModeCompletion mode))) =
      (decodeSourcePrefix? tail tailRefs (nextSource point).registry
        (nextSource point).revelations tailEmbedding.ref (eventCount tail)
          final.application.config.store (decodeHistory setup.program
            (final.application.config.history.map
              (setup.eventGraph.fromModeCompletion mode)))).map lift)
    (build : BehavioralPolicy who tail → BehavioralPolicy who program)
    (kernel : ∀ policy config,
      ((fun law => law.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who (build policy))))^[eventCount program]
        (PMF.pure (ProtocolState.entry program config))) =
      ((stepSource config).bind fun next =>
        ((fun law => law.bind (ProtocolState.behavioralStateStep tail
          (Function.update tailProfile who policy)))^[eventCount tail]
          (PMF.pure (ProtocolState.entry tail next)))).map lift) :
    ∃ policy : BehavioralPolicy who program,
      ∃ nextNoise : Option (ProtocolView who program) → PMF _,
        (prior.bind fun seed =>
          (deviationPhases scheduler players horizon (high :: rest) (execution seed)).map
            fun final =>
            (decodeSourcePrefix? program refs (source seed).registry (source seed).revelations
              embedding.ref (eventCount program) final.application.config.store
              (decodeHistory setup.program (final.application.config.history.map
                (setup.eventGraph.fromModeCompletion mode))),
              (serviceRuntime setup mode deadline).bindingTraffic leaks who final)) =
          (prior.bind fun seed =>
            ((fun law => law.bind (ProtocolState.behavioralStateStep program
              (Function.update profile who policy)))^[eventCount program]
              (PMF.pure (ProtocolState.entry program (source seed)))).map some).bind
            fun state => (nextNoise (state.map (ProtocolState.observe who program))).map
              fun extra => (state, extra) := by
  let app := serviceApplication setup mode deadline leaks
  let advanced := prior.bind fun seed =>
    (app.runUntilHorizon scheduler players (BlockDone high) horizon (execution seed)).map
      fun final => (seed, final)
  let NextSeed := {point // point ∈ advanced.support}
  let nextPrior : PMF NextSeed := pmfToSubtype advanced (fun _ member => member)
  let nextExecution := fun point : NextSeed => point.val.2
  obtain ⟨tailPolicy, tailNoise, law⟩ := tailLaw nextPrior nextSource nextExecution nextAligned
    nextCheckpoint (fun point _ => nextBoundary point) (fun point _ => nextBounded point)
    nextEffective nextNoise nextFactor
  refine ⟨build tailPolicy, ?_⟩
  let tailJoint := nextPrior.bind fun point =>
    (deviationPhases scheduler players horizon rest (nextExecution point)).map fun final =>
      (decodeSourcePrefix? tail tailRefs (nextSource point).registry
        (nextSource point).revelations tailEmbedding.ref (eventCount tail)
          final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion mode))),
        (serviceRuntime setup mode deadline).bindingTraffic leaks who final)
  let tailSource := nextPrior.bind fun point =>
    ((fun law => law.bind (ProtocolState.behavioralStateStep tail
      (Function.update tailProfile who tailPolicy)))^[eventCount tail]
      (PMF.pure (ProtocolState.entry tail (nextSource point)))).map some
  have tailMarginal : tailJoint.map Prod.fst = tailSource := by
    have projected := congrArg (PMF.map Prod.fst) law
    simp only [← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind, PMF.pure_bind,
      PMF.bind_const] at projected
    simpa only [tailJoint, tailSource, ← PMF.bind_pure_comp, Function.comp_def,
      PMF.bind_bind, PMF.pure_bind, PMF.bind_pure] using projected
  have tailFactor : tailJoint = (tailJoint.map Prod.fst).bind fun state =>
      (tailNoise (state.map (ProtocolState.observe who tail))).map fun extra =>
        (state, extra) := by
    rw [tailMarginal]
    exact law
  have lifted := map_observation_factor tailJoint
    (Option.map (ProtocolState.observe who tail)) tailNoise tailFactor
    (Option.map lift) (Option.map (ProtocolState.observe who program)) recover recovers
  refine ⟨fun view => tailNoise (recover view), ?_⟩
  have nativeEq : (prior.bind fun seed =>
      (deviationPhases scheduler players horizon (high :: rest) (execution seed)).map
        fun final =>
          (decodeSourcePrefix? program refs (source seed).registry
            (source seed).revelations embedding.ref (eventCount program)
              final.application.config.store (decodeHistory setup.program
                (final.application.config.history.map
                  (setup.eventGraph.fromModeCompletion mode))),
            (serviceRuntime setup mode deadline).bindingTraffic leaks who final)) =
      tailJoint.map (fun pair => (pair.1.map lift, pair.2)) := by
    let continuePoint := fun point : Seed × app.Execution =>
      (deviationPhases scheduler players horizon rest point.2).map
        fun final =>
          (decodeSourcePrefix? program refs (source point.1).registry
            (source point.1).revelations embedding.ref (eventCount program)
              final.application.config.store (decodeHistory setup.program
                (final.application.config.history.map
                  (setup.eventGraph.fromModeCompletion mode))),
            (serviceRuntime setup mode deadline).bindingTraffic leaks who final)
    calc
      _ = advanced.bind continuePoint := by
        simp only [advanced, continuePoint, PMF.bind_bind, PMF.bind_map,
          deviationPhases, PMF.map_bind, Function.comp_def]
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
          (Function.update profile who (build tailPolicy))))^[eventCount program]
          (PMF.pure (ProtocolState.entry program (source seed)))).map some := by
    simp only [tailSource, PMF.map_bind, PMF.map_comp, Option.map_some, Function.comp_def]
    let continuation := fun config : Config Player L Δ =>
      ((fun law => law.bind (ProtocolState.behavioralStateStep tail
        (Function.update tailProfile who tailPolicy)))^[eventCount tail]
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
          (Function.update profile who (build tailPolicy))))^[eventCount program]
          (PMF.pure (ProtocolState.entry program (source seed)))).map some) := by
    rw [PMF.map_comp]
    change tailJoint.map (Option.map lift ∘ Prod.fst) = _
    rw [← PMF.map_comp, tailMarginal]
    exact sourceEq
  rw [nativeEq]
  simpa only [marginalEq] using lifted

/-- A point a first phase reaches comes from a seed of the prior and a run of
the phase. -/
theorem phaseJoint_mem {Seed : Type} {high : Nat} {prior : PMF Seed}
    {execution : Seed → (serviceApplication setup mode deadline leaks).Execution}
    {point : Seed × (serviceApplication setup mode deadline leaks).Execution}
    (member : point ∈ (phaseJoint setup leaks horizon scheduler players high prior
      execution).support) :
    point.1 ∈ prior.support ∧
      point.2 ∈ ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler players
        (BlockDone high) horizon (execution point.1)).support := by
  rcases point with ⟨seed, final⟩
  unfold phaseJoint at member
  rw [PMF.support_bind] at member
  obtain ⟨selected, chosen, moved⟩ := Set.mem_iUnion₂.mp member
  rw [PMF.support_map] at moved
  obtain ⟨reached, moved, same⟩ := moved
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact ⟨chosen, moved⟩

/-- **One phase, decoded.** If the run of the first phase, ending at `high`,
decodes through an injective embedding of residual entry states with the
source law of a source step kernel jointly with the deviator's traffic, factoring through
the deviator's residual view, and stops at completion boundaries within the
horizon, then the residual deviation law gives the program's over all of its
phases. -/
theorem DeviationLaw.phase [Fintype Player] {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    {Δ : SourceCtx Player L} {tailNames : Finset VarId}
    (tail : SourceProgram Player L Δ tailNames) (tailProfile : BehavioralProfile tail)
    (tailRefs : ContextRefs (graphLayout setup.program) Δ)
    (tailEmbedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      tail)
    (tailBefore : ContextRefsBefore tailRefs tailEmbedding) (high : Nat) (rest : List Nat)
    (tailLaw : DeviationLaw setup leaks horizon scheduler players wholeProfile who tail
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
    (configNoise : DecisionView who Δ → PMF _)
    (law : (phaseJoint setup leaks horizon scheduler players high prior execution).map
        (fun point => (decode point.1 point.2,
          (serviceRuntime setup mode deadline).bindingTraffic leaks who point.2)) =
      ((prior.map source).bind stepSource).bind fun config =>
        (configNoise (config.view who)).map fun extra =>
          (some (lift (ProtocolState.entry tail config)), extra))
    (nextBoundary : ∀ point :
      PhasePoint setup leaks horizon scheduler players high prior execution,
      CompletionBoundary setup leaks scheduler players high point.val.2)
    (nextBounded : ∀ point :
      PhasePoint setup leaks horizon scheduler players high prior execution,
      point.val.2.environmentRecall.length ≤ horizon)
    (nextAligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile tail tailProfile
      tailRefs (nextRevelations seed) (nextRegistry seed) tailEmbedding tailBefore high)
    (nextEffective : ∀ seed player, (tailProfile player).EffectiveDisclosures tail
      (nextRegistry seed) (nextRevelations seed))
    (recover : Option (ProtocolView who program) → Option (ProtocolView who tail))
    (recovers : ∀ state : Option (ProtocolState tail),
      recover ((state.map lift).map (ProtocolState.observe who program)) =
        state.map (ProtocolState.observe who tail))
    (decodeLater : ∀ seed (final : (serviceApplication setup mode deadline leaks).Execution),
      decodeSourcePrefix? program refs (source seed).registry
        (source seed).revelations embedding.ref (eventCount program)
          final.application.config.store (decodeHistory setup.program
            (final.application.config.history.map (setup.eventGraph.fromModeCompletion mode))) =
      (decodeSourcePrefix? tail tailRefs (nextRegistry seed) (nextRevelations seed)
        tailEmbedding.ref (eventCount tail) final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion mode)))).map lift)
    (build : BehavioralPolicy who tail → BehavioralPolicy who program)
    (kernel : ∀ policy config,
      ((fun law => law.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who (build policy))))^[eventCount program]
        (PMF.pure (ProtocolState.entry program config))) =
      ((stepSource config).bind fun next =>
        ((fun law => law.bind (ProtocolState.behavioralStateStep tail
          (Function.update tailProfile who policy)))^[eventCount tail]
          (PMF.pure (ProtocolState.entry tail next)))).map lift) :
    ∃ policy : BehavioralPolicy who program,
      ∃ nextNoise : Option (ProtocolView who program) → PMF _,
        (prior.bind fun seed =>
          (deviationPhases scheduler players horizon (high :: rest) (execution seed)).map
            fun final =>
            (decodeSourcePrefix? program refs (source seed).registry (source seed).revelations
              embedding.ref (eventCount program) final.application.config.store
              (decodeHistory setup.program (final.application.config.history.map
                (setup.eventGraph.fromModeCompletion mode))),
              (serviceRuntime setup mode deadline).bindingTraffic leaks who final)) =
          (prior.bind fun seed =>
            ((fun law => law.bind (ProtocolState.behavioralStateStep program
              (Function.update profile who policy)))^[eventCount program]
              (PMF.pure (ProtocolState.entry program (source seed)))).map some).bind
            fun state => (nextNoise (state.map (ProtocolState.observe who program))).map
              fun extra => (state, extra) := by
  obtain ⟨nextSource, nextCheckpoint, nextRegistryEq, nextRevelationsEq, _nextRead,
    nextMarginal, nextFactor⟩ := reconstruct_service_phase setup leaks who tailRefs high
      nextRegistry nextRevelations
      (phaseJoint setup leaks horizon scheduler players high prior execution)
      (fun config => lift (ProtocolState.entry tail config)) injective decode decodeEq
      (fun point member => (nextBoundary ⟨point, member⟩).ordered)
      ((prior.map source).bind stepSource) configNoise law
  refine DeviationLaw.finish setup leaks horizon scheduler players wholeProfile who program
    profile refs embedding tail tailProfile tailRefs tailEmbedding tailBefore high rest tailLaw
    prior source execution nextSource ?_ nextCheckpoint nextBoundary nextBounded ?_ configNoise
    nextFactor stepSource nextMarginal lift recover recovers ?_ build kernel
  · intro point
    rw [nextRegistryEq, nextRevelationsEq]
    exact nextAligned point.val.1
  · intro point player
    rw [nextRegistryEq, nextRevelationsEq]
    exact nextEffective point.val.1 player
  · intro point final
    rw [nextRegistryEq, nextRevelationsEq]
    exact decodeLater point.val.1 final

end Law

/-- A residual program with no leading commitment, compiled at rank `high`,
starts with a public event, or ends the graph there: a block ends at `high`. -/
theorem CompiledSuffix.blockEnd {setup : Setup (Player := Player) (L := L)}
    {mode : EventGraph.ExecutionMode} {Δ : SourceCtx Player L} {names : Finset VarId}
    {tail : SourceProgram Player L Δ names} (maximal : leadingCommits tail = 0)
    {refs : ContextRefs (graphLayout setup.program) Δ} {revelations : Revelations Δ}
    {registry : Registry Δ}
    {embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) tail}
    {refsBefore : ContextRefsBefore refs embedding} {high : Nat}
    (suffix : CompiledSuffix setup.program tail refs revelations registry embedding refsBefore
      high) : BlockEnd setup mode high := by
  have counted := suffix.countEq
  refine ⟨?_, ?_⟩
  · change high ≤ eventCount setup.program
    omega
  · intro event rank
    have below : event.val < eventCount setup.program := event.isLt
    cases tail with
    | ret _ =>
        simp only [eventCount] at counted
        omega
    | commit => simp [leadingCommits] at maximal
    | @sample _ _ name payload fresh law next =>
        have same : event = embedding.event ⟨0, by simp [eventCount]⟩ := by
          apply Fin.ext
          rw [suffix.rankEq]
          simpa using rank
        have outputEq : (serviceGraph setup mode).outputLayout
            (embedding.event ⟨0, by simp [eventCount]⟩) = .publicData payload := by
          change outputLayout setup.program _ = _
          simpa [outputLayout, eventCount] using embedding.layout_eq ⟨0, by simp [eventCount]⟩
        rw [same, outputEq]
        trivial
    | @reveal _ _ published owner name payload fresh selected unresolved next =>
        have same : event = embedding.event ⟨0, by simp [eventCount]⟩ := by
          apply Fin.ext
          rw [suffix.rankEq]
          simpa using rank
        have outputEq : (serviceGraph setup mode).outputLayout
            (embedding.event ⟨0, by simp [eventCount]⟩) = .publication payload := by
          change outputLayout setup.program _ = _
          simpa [outputLayout, eventCount] using embedding.layout_eq ⟨0, by simp [eventCount]⟩
        rw [same, outputEq]
        trivial

/-- **The deviation law over every phase.** On a barrier-ordered graph, under
the asynchronous contract with timely delays, against the first-turn clients
of a source profile one player follows an arbitrary native policy. Over the
phases of any residual program, the decoded source state has, jointly with the
deviator's traffic, the law of a source run in which the deviator follows one
source behavioral policy and every other player keeps its source policy, the
traffic factoring through the deviator's source observation. -/
theorem asyncDeviation_deviationLaw [Fintype Player]
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (ordered : (serviceGraph setup mode).BarrierOrdered)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    {Γ : SourceCtx Player L} {names : Finset VarId} {program : SourceProgram Player L Γ names}
    {offset : Nat} {ends : List Nat} (phases : PhaseEnds program offset ends) :
    ∀ (profile : BehavioralProfile program) (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding),
      DeviationLaw setup leaks horizon scheduler
        (deviatedTurnProfile bound turns (firstTurnTiming setup turns mode) wholeProfile who
          deviation) wholeProfile who program profile refs embedding refsBefore offset ends := by
  let app := serviceApplication setup mode deadline leaks
  let players := deviatedTurnProfile bound turns (firstTurnTiming setup turns mode) wholeProfile
    who deviation
  induction phases with
  | ret payoffs offset =>
      intro profile refs embedding refsBefore Seed prior source execution _aligned checkpoint
        _boundary _bounded _effective noise factor
      obtain ⟨nextNoise, nextFactor⟩ := ProtocolView.entry_noise_factor (.ret payoffs) who prior
        source (fun seed => (serviceRuntime setup mode deadline).bindingTraffic leaks who
          (execution seed)) noise factor
      refine ⟨profile who, nextNoise, ?_⟩
      dsimp only at nextFactor
      simp only [deviationPhases, eventCount, Function.iterate_zero, id_eq,
        ← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
      simp only [← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
        at nextFactor
      refine Eq.trans (bind_congr_on_support _ fun seed _ => ?_) nextFactor
      rw [(checkpoint seed).decode (.ret payoffs) embedding.ref]
  | @sample Γ names name payload fresh distribution next offset rest _ ih =>
      intro profile refs embedding refsBefore Seed prior source execution aligned checkpoint
        boundary bounded effective noise factor
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
      obtain ⟨configNoise, law⟩ := asyncDeviation_sample_factorization contract turns
        wholeProfile who deviation fresh distribution next profile refs embedding refsBefore
        offset alone prior source execution aligned checkpoint boundary bounded noise factor
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
      refine DeviationLaw.phase setup leaks horizon scheduler players wholeProfile who
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
        ?_ stepSource configNoise ?_ (fun point => (nextFacts point).1)
        (fun point => (nextFacts point).2) ?_ (fun seed player => effective seed player)
        (fun view => view.bind (Sum.elim (fun _ => none) some)) ?_ ?_ (fun policy => policy) ?_
      · intro seed final
        simp only [decodeSourcePrefix?, Option.map_map, Function.comp_def]
        rfl
      · refine Eq.trans ?_ law
        simp only [phaseJoint, PMF.map_bind, PMF.map_comp, Function.comp_def]
        apply bind_congr_on_support _
        intro seed supported
        rw [← stopEq seed supported]
      · intro seed
        simpa only [sampleSuccessor, tailRefs, tailEmbedding, OutputEmbedding.ref] using
          (aligned seed).sampleTail setup.program wholeProfile (_openNames := names)
            fresh distribution next profile refs (source seed).revelations
              (source seed).registry embedding refsBefore offset
      · intro state
        cases state <;> rfl
      · intro seed final
        rfl
      · intro policy config
        change (fun law => law.bind (ProtocolState.behavioralStateStep _
          (Function.update profile who policy)))^[eventCount next + 1]
            (PMF.pure (ProtocolState.entry _ config)) = _
        rw [ProtocolState.behavioralStatePrefix_sample, afterSample_update]
        simp only [stepSource, PMF.bind_map, PMF.map_bind, Function.comp_def]
  | @reveal Γ names published name owner payload fresh binding unresolved next offset rest _
      ih =>
      intro profile refs embedding refsBefore Seed prior source execution aligned checkpoint
        boundary bounded effective noise factor
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
      have nextAligned (seed : Seed) : CompiledPolicySuffix setup.program wholeProfile next
          (afterReveal profile) tailRefs
          (Revelations.reveal (published := published) (source seed).revelations binding)
          (source seed).registry.weaken tailEmbedding tailBefore (offset + 1) := by
        simpa only [revealSuccessor, tailRefs, tailEmbedding, OutputEmbedding.ref] using
          (aligned seed).revealTail (whole := setup.program) (wholeProfile := wholeProfile)
            fresh binding unresolved next profile refs (source seed).revelations
              (source seed).registry embedding refsBefore offset
      have convert {stepSource : Config Player L Γ → PMF (Config Player L
            ((published, .publication payload) :: Γ))}
          {configNoise : DecisionView who ((published, .publication payload) :: Γ) → PMF _}
          (law : (prior.bind fun seed =>
            (app.runUntilHorizon scheduler players
              (fun final => event ∈ final.application.config.cut.completed) horizon
              (execution seed)).map fun final =>
                (decodeSourcePrefix? (.reveal published owner name fresh binding unresolved next)
                  refs (source seed).registry (source seed).revelations embedding.ref 1
                  final.application.config.store (decodeHistory setup.program
                    (final.application.config.history.map
                      (setup.eventGraph.fromModeCompletion mode))),
                  (serviceRuntime setup mode deadline).bindingTraffic leaks who final)) =
            ((prior.map source).bind stepSource).bind fun config =>
              (configNoise (config.view who)).map fun extra =>
                ((some (Sum.inr (ProtocolState.entry next config)) :
                  Option (ProtocolState (.reveal published owner name fresh binding unresolved
                    next))), extra)) :
          (phaseJoint setup leaks horizon scheduler players (offset + 1) prior execution).map
            (fun point => (decodeSourcePrefix?
              (.reveal published owner name fresh binding unresolved next)
                refs (source point.1).registry (source point.1).revelations embedding.ref 1
                point.2.application.config.store (decodeHistory setup.program
                  (point.2.application.config.history.map
                    (setup.eventGraph.fromModeCompletion mode))),
              (serviceRuntime setup mode deadline).bindingTraffic leaks who point.2)) =
            ((prior.map source).bind stepSource).bind fun config =>
              (configNoise (config.view who)).map fun extra =>
                (some (Sum.inr (ProtocolState.entry next config)), extra) := by
        refine Eq.trans ?_ law
        simp only [phaseJoint, PMF.map_bind, PMF.map_comp, Function.comp_def]
        apply bind_congr_on_support _
        intro seed supported
        rw [← stopEq seed supported]
      by_cases own : owner = who
      · subst owner
        obtain ⟨choice, configNoise, law⟩ := asyncDeviator_reveal_factorization contract turns
          wholeProfile who deviation fresh binding unresolved next profile refs embedding
          refsBefore offset alone prior source execution aligned checkpoint boundary bounded
          noise factor
        let stepSource := fun config : Config Player L Γ =>
          (choice (config.view who)).map (revealSuccessor published binding config)
        refine DeviationLaw.phase setup leaks horizon scheduler players wholeProfile who
          (.reveal published who name fresh binding unresolved next) profile refs embedding next
          (afterReveal profile) tailRefs tailEmbedding tailBefore (offset + 1) rest
          (ih (afterReveal profile) tailRefs tailEmbedding tailBefore) prior source execution
          Sum.inr (Sum.inr_injective.comp (ProtocolState.entry_injective next))
          (fun seed => (source seed).registry.weaken)
          (fun seed => Revelations.reveal (published := published) (source seed).revelations
            binding)
          (fun seed final => decodeSourcePrefix?
            (.reveal published who name fresh binding unresolved next) refs
            (source seed).registry (source seed).revelations embedding.ref 1
            final.application.config.store (decodeHistory setup.program
              (final.application.config.history.map (setup.eventGraph.fromModeCompletion mode))))
          ?_ stepSource configNoise (convert law) (fun point => (nextFacts point).1)
          (fun point => (nextFacts point).2) nextAligned
          (fun seed player => (effective seed player).2)
          (fun view => view.bind (Sum.elim (fun _ => none) some)) ?_ ?_
          (fun policy => (fun _ view => choice view, policy)) ?_
        · intro seed final
          simp only [decodeSourcePrefix?, Option.map_map, Function.comp_def]
          rfl
        · intro state
          cases state <;> rfl
        · intro seed final
          rfl
        · intro policy config
          rw [show eventCount (SourceProgram.reveal published who name fresh binding unresolved
              next) = eventCount next + 1 from rfl, ProtocolState.behavioralStatePrefix_reveal,
            afterReveal_update]
          simp only [stepSource, revealKernel, Function.update_self, PMF.bind_map,
            PMF.map_bind, Function.comp_def]
      · obtain ⟨configNoise, law⟩ := asyncDeviation_reveal_factorization contract timely turns
          wholeProfile who deviation own fresh binding unresolved next profile refs embedding
          refsBefore offset alone prior source execution aligned checkpoint boundary bounded
          (fun seed _ => effective seed owner) noise factor
        let stepSource := fun config : Config Player L Γ =>
          (revealKernel profile (config.view owner)).map
            (revealSuccessor published binding config)
        refine DeviationLaw.phase setup leaks horizon scheduler players wholeProfile who
          (.reveal published owner name fresh binding unresolved next) profile refs embedding
          next (afterReveal profile) tailRefs tailEmbedding tailBefore (offset + 1) rest
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
          ?_ stepSource configNoise (convert law) (fun point => (nextFacts point).1)
          (fun point => (nextFacts point).2) nextAligned
          (fun seed player => (effective seed player).2)
          (fun view => view.bind (Sum.elim (fun _ => none) some)) ?_ ?_
          (fun policy => ((profile who).1, policy)) ?_
        · intro seed final
          simp only [decodeSourcePrefix?, Option.map_map, Function.comp_def]
          rfl
        · intro state
          cases state <;> rfl
        · intro seed final
          rfl
        · intro policy config
          rw [show eventCount (SourceProgram.reveal published owner name fresh binding unresolved
              next) = eventCount next + 1 from rfl, ProtocolState.behavioralStatePrefix_reveal,
            afterReveal_update]
          simp only [stepSource, revealKernel, Function.update_of_ne own, PMF.bind_map,
            PMF.map_bind, Function.comp_def]
  | @block Γ names program offset rest count prefixed _ maximal _ ih =>
      intro profile refs embedding refsBefore Seed prior source execution aligned checkpoint
        boundary bounded effective noise factor
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
          (BlockEnd.sealed ordered wall) wall.1 (execution point.val.1) (boundary _ supported)
          (bounded _ supported) _ reached done
        exact ⟨nextBoundary, nextBounded⟩
      obtain ⟨policy, configNoise, law⟩ := asyncDeviation_block_factorization
        ordered.revealRelaxedOrdered wall contract timely turns wholeProfile who deviation bindings
        program profile count prefixed refs embedding refsBefore rfl prior source execution
        aligned checkpoint boundary bounded
        noise factor
      refine DeviationLaw.phase setup leaks horizon scheduler players wholeProfile who program
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
        (kernelChain who count program profile policy prefixed) configNoise ?_
        (fun point => (nextFacts point).1) (fun point => (nextFacts point).2) tailAligned
        (fun seed player => effective_commitTail (who := player) count program prefixed profile
          _ _ (effective seed player))
        (commitTailRecover who count program prefixed)
        (commitTailRecover_spec who count program prefixed) ?_
        (graftPolicy who count program prefixed policy) ?_
      · simp only [phaseJoint, PMF.map_bind, PMF.map_comp, Function.comp_def]
        exact law
      · intro seed final
        have through := decodeSourcePrefix?_commitTail count program prefixed refs
          (source seed).registry (source seed).revelations embedding
          (eventCount (commitTail count program prefixed).tail) final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion mode)))
        rw [eventCount_commitTail] at through
        exact through
      · intro rest config
        have grafted := iterate_graftPolicy who count program profile prefixed policy rest
          (eventCount (commitTail count program prefixed).tail) config
        rw [eventCount_commitTail] at grafted
        rw [PMF.map_bind]
        exact grafted


end Vegas
