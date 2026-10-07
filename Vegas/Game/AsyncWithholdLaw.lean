/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRevealDeviation
import Vegas.Game.ServiceOpeningHonestLaw
import GameTheoryExtensions.Math.Probability.PresentConditional

/-! # The law of one deviation up to withholding

Against the first-turn clients of a source profile that opens effectively, one
player follows an arbitrary native policy. On a reveal-relaxed graph a run of
disclosures completes concurrently, and the deviator may withhold one of its
own effective disclosures after seeing another owner's opening of the same run
(`Vegas.DeviatorWithheld`). Up to that point the run decodes as a source run:
phase by phase, the decoded source state jointly with the deviator's traffic,
restricted to the runs along which the deviator has not withheld, is dominated
by the law of a source run in which the deviator follows one source behavioral
policy that opens effectively at every run of disclosures, and every other
player keeps its source policy (`Vegas.WithholdLaw`). A phase's survivors,
conditioned on survival, keep the traffic factored through the deviator's source
view (`Vegas.WithholdLaw.finish`). Commitments and samples complete no
disclosure, so nobody withholds there (`Vegas.WithholdLaw.phase_exact`); a run
of disclosures decodes to its open chain along the runs without withholding
(`Vegas.asyncDeviation_revealBlock_factorization`). Over all phases of any
residual program the law up to withholding holds
(`Vegas.asyncDeviation_withholdLaw`).
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

/-- The runs of phases in turn reach their final configurations. -/
theorem deviationPhases_configReaches
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (horizon : Nat) :
    ∀ (ends : List Nat)
      (execution final : (serviceApplication setup mode deadline leaks).Execution),
      final ∈ (deviationPhases scheduler players horizon ends execution).support →
      ConfigReaches setup execution.application.config final.application.config
  | [], execution, final, reached => by
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact Relation.ReflTransGen.refl
  | high :: rest, execution, final, reached => by
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact (runUntil_configReaches scheduler players _ _ execution middle moved).trans
        (deviationPhases_configReaches scheduler players horizon rest middle final later)

/-- A run that completes no disclosure keeps the deviator from withholding. -/
theorem not_deviatorWithheld_of_plain {who : Player}
    {before after : (serviceGraph setup mode).Config} (reach : ConfigReaches setup before after)
    (alive : ¬ DeviatorWithheld who before) {low high : Nat}
    (startPrefix : before.cut.IsPrefix low) (stopPrefix : after.cut.IsPrefix high)
    (plain : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val → event.val < high →
      ¬ ((serviceGraph setup mode).outputLayout event).IsPublication) :
    ¬ DeviatorWithheld who after := by
  rintro ⟨event, owned, notOpened⟩
  apply notOpened
  by_cases done : event ∈ before.cut.completed
  · exact OpenedAt.reaches reach done (by
      by_contra notBefore
      exact alive ⟨event, owned, notBefore⟩)
  · unfold OpenedAt
    cases node : nodeView (serviceGraph setup mode) event with
    | bind => trivial
    | sample => trivial
    | resolve owner payload binding checks outputEq codeEq =>
        dsimp only
        intro action member
        have doneAfter := (after.history_exact event).mp (List.mem_map_of_mem member)
        have lower : low ≤ event.val :=
          Nat.le_of_not_gt fun below => done ((startPrefix.2 event).mpr below)
        have upper := (stopPrefix.2 event).mp doneAfter
        exact (plain event lower upper (by rw [outputEq]; trivial)).elim

end Phases

section Law

variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
  (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
  (players : Player → (serviceApplication setup mode deadline leaks).Policy)
  (wholeProfile : BehavioralProfile setup.program) (who : Player)

open Classical in
/-- The decoded state of a residual program jointly with the deviator's
traffic, while the deviator has not withheld an effective disclosure. -/
def withheldGate {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names)
    (refs : ContextRefs (graphLayout setup.program) Γ) (registry : Registry Γ)
    (revelations : Revelations Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (final : (serviceApplication setup mode deadline leaks).Execution) :=
  if DeviatorWithheld who final.application.config then none
  else some (decodeSourcePrefix? program refs registry revelations embedding.ref
      (eventCount program) final.application.config.store
      (decodeHistory setup.program (final.application.config.history.map
        (setup.eventGraph.fromModeCompletion mode))),
    (serviceRuntime setup mode deadline).bindingTraffic leaks who final)

/-- **The deviation law of a residual program up to withholding.** From
completion boundaries at rank `offset` that the source configurations of a seed
law check, at which every player's residual profile opens effectively and the
deviator has not withheld, whenever the deviator's traffic factors through its
source view, the phases `ends` give the decoded state of the residual program
jointly with the deviator's traffic, along the runs on which the deviator does
not withhold, at most the law of a source run in which the deviator follows one
source policy, with the traffic factoring through the deviator's source
observation. -/
def WithholdLaw [Fintype Player] {Γ : SourceCtx Player L} {names : Finset VarId}
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
    (∀ seed, openingResidual program profile (source seed).registry (source seed).revelations) →
    (∀ seed ∈ prior.support, ¬ DeviatorWithheld who (execution seed).application.config) →
    ∀ (noise : DecisionView who Γ → PMF _),
    prior.map (fun seed => (source seed,
        (serviceRuntime setup mode deadline).bindingTraffic leaks who (execution seed))) =
      (prior.map source).bind (fun config =>
        (noise (config.view who)).map fun extra => (config, extra)) →
    ∃ policy : BehavioralPolicy who program,
      ∃ nextNoise : Option (ProtocolView who program) → PMF _,
        ∀ outcome,
          (prior.bind fun seed =>
            (deviationPhases scheduler players horizon ends (execution seed)).map
              (withheldGate setup leaks who program refs (source seed).registry
                (source seed).revelations embedding)) (some outcome) ≤
          ((prior.bind fun seed =>
            ((fun law => law.bind (ProtocolState.behavioralStateStep program
              (Function.update profile who policy)))^[eventCount program]
              (PMF.pure (ProtocolState.entry program (source seed)))).map some).bind
            fun state => (nextNoise (state.map (ProtocolState.observe who program))).map
              fun extra => (state, extra)) outcome

open Classical in
/-- **Finishing a phase up to withholding.** If the first phase of a program,
ending at `high`, gives every point at which the deviator has not withheld a
residual configuration, the states those points reach, jointly with the
deviator's traffic, have the law of a source step kernel with the traffic of a
kernel of the deviator's residual view that may report withholding, and the
residual program has the deviation law up to withholding over the remaining
phases, then the program has it over all of its phases. -/
theorem WithholdLaw.finish [Fintype Player] {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    {Δ : SourceCtx Player L} {tailNames : Finset VarId}
    (tail : SourceProgram Player L Δ tailNames) (tailProfile : BehavioralProfile tail)
    (tailRefs : ContextRefs (graphLayout setup.program) Δ)
    (tailEmbedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      tail)
    (tailBefore : ContextRefsBefore tailRefs tailEmbedding) (high : Nat) (rest : List Nat)
    (tailLaw : WithholdLaw setup leaks horizon scheduler players wholeProfile who tail
      tailProfile tailRefs tailEmbedding tailBefore high rest)
    {Seed : Type} (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution)
    (nextSource : Seed × (serviceApplication setup mode deadline leaks).Execution →
      Config Player L Δ)
    (nextAligned : ∀ point ∈ (phaseJoint setup leaks horizon scheduler players high prior
        execution).support, ¬ DeviatorWithheld who point.2.application.config →
      CompiledPolicySuffix setup.program wholeProfile tail tailProfile tailRefs
        (nextSource point).revelations (nextSource point).registry tailEmbedding tailBefore high)
    (nextCheckpoint : ∀ point ∈ (phaseJoint setup leaks horizon scheduler players high prior
        execution).support, ¬ DeviatorWithheld who point.2.application.config →
      SourceCheckpoint setup (nextSource point) tailRefs high point.2.application.config)
    (nextBoundary : ∀ point ∈ (phaseJoint setup leaks horizon scheduler players high prior
        execution).support,
      CompletionBoundary setup leaks scheduler players high point.2)
    (nextBounded : ∀ point ∈ (phaseJoint setup leaks horizon scheduler players high prior
        execution).support, point.2.environmentRecall.length ≤ horizon)
    (nextOpens : ∀ point ∈ (phaseJoint setup leaks horizon scheduler players high prior
        execution).support, ¬ DeviatorWithheld who point.2.application.config →
      openingResidual tail tailProfile (nextSource point).registry (nextSource point).revelations)
    (absorbing : ∀ point ∈ (phaseJoint setup leaks horizon scheduler players high prior
        execution).support, DeviatorWithheld who point.2.application.config →
      ∀ final ∈ (deviationPhases scheduler players horizon rest point.2).support,
        DeviatorWithheld who final.application.config)
    (stepSource : Config Player L Γ → PMF (Config Player L Δ))
    (kernel : DecisionView who Δ → PMF (Option _))
    (phaseLaw : (phaseJoint setup leaks horizon scheduler players high prior execution).map
        (fun point => if DeviatorWithheld who point.2.application.config then none
          else some (nextSource point,
            (serviceRuntime setup mode deadline).bindingTraffic leaks who point.2)) =
      ((prior.map source).bind stepSource).bind fun config =>
        (kernel (config.view who)).map (Option.map fun extra => (config, extra)))
    (lift : ProtocolState tail → ProtocolState program)
    (recover : Option (ProtocolView who program) → Option (ProtocolView who tail))
    (recovers : ∀ state : Option (ProtocolState tail),
      recover ((state.map lift).map (ProtocolState.observe who program)) =
        state.map (ProtocolState.observe who tail))
    (decodeLater : ∀ point ∈ (phaseJoint setup leaks horizon scheduler players high prior
        execution).support, ¬ DeviatorWithheld who point.2.application.config →
      ∀ final : (serviceApplication setup mode deadline leaks).Execution,
      decodeSourcePrefix? program refs (source point.1).registry
        (source point.1).revelations embedding.ref (eventCount program)
          final.application.config.store (decodeHistory setup.program
            (final.application.config.history.map (setup.eventGraph.fromModeCompletion mode))) =
      (decodeSourcePrefix? tail tailRefs (nextSource point).registry
        (nextSource point).revelations tailEmbedding.ref (eventCount tail)
          final.application.config.store (decodeHistory setup.program
            (final.application.config.history.map
              (setup.eventGraph.fromModeCompletion mode)))).map lift)
    (build : BehavioralPolicy who tail → BehavioralPolicy who program)
    (kernelEq : ∀ policy, ∀ seed ∈ prior.support,
      ((fun law => law.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who (build policy))))^[eventCount program]
        (PMF.pure (ProtocolState.entry program (source seed)))) =
      ((stepSource (source seed)).bind fun next =>
        ((fun law => law.bind (ProtocolState.behavioralStateStep tail
          (Function.update tailProfile who policy)))^[eventCount tail]
          (PMF.pure (ProtocolState.entry tail next)))).map lift) :
    ∃ policy : BehavioralPolicy who program,
      ∃ nextNoise : Option (ProtocolView who program) → PMF _,
        ∀ outcome,
          (prior.bind fun seed =>
            (deviationPhases scheduler players horizon (high :: rest) (execution seed)).map
              (withheldGate setup leaks who program refs (source seed).registry
                (source seed).revelations embedding)) (some outcome) ≤
          ((prior.bind fun seed =>
            ((fun law => law.bind (ProtocolState.behavioralStateStep program
              (Function.update profile who policy)))^[eventCount program]
              (PMF.pure (ProtocolState.entry program (source seed)))).map some).bind
            fun state => (nextNoise (state.map (ProtocolState.observe who program))).map
              fun extra => (state, extra)) outcome := by
  classical
  let app := serviceApplication setup mode deadline leaks
  let joint := phaseJoint setup leaks horizon scheduler players high prior execution
  let traffic := (serviceRuntime setup mode deadline).bindingTraffic leaks who
  let alive := fun point : Seed × app.Execution => ¬ DeviatorWithheld who point.2.application.config
  let continuePoint := fun point : Seed × app.Execution =>
    (deviationPhases scheduler players horizon rest point.2).map
      (withheldGate setup leaks who program refs (source point.1).registry
        (source point.1).revelations embedding)
  have nativeEq : (prior.bind fun seed =>
      (deviationPhases scheduler players horizon (high :: rest) (execution seed)).map
        (withheldGate setup leaks who program refs (source seed).registry
          (source seed).revelations embedding)) = joint.bind continuePoint := by
    simp only [joint, continuePoint, phaseJoint, PMF.bind_bind, PMF.bind_map,
      deviationPhases, PMF.map_bind, Function.comp_def]
  -- A point at which the deviator has withheld contributes nothing that survives.
  have outside : ∀ point ∈ joint.support, ¬ alive point →
      ∀ outcome, continuePoint point (some outcome) = 0 := by
    intro point supported withheld outcome
    rw [PMF.map_apply, ENNReal.tsum_eq_zero.mpr]
    intro final
    split_ifs with reached
    · by_cases member : final ∈ (deviationPhases scheduler players horizon rest point.2).support
      · have gone := absorbing point supported (not_not.mp withheld) final member
        unfold withheldGate at reached
        rw [ite_eq_left gone] at reached
        cases reached
      · exact (PMF.apply_eq_zero_iff _ _).mpr member
    · rfl
  by_cases present : ∃ point ∈ {point | alive point}, point ∈ joint.support
  swap
  · refine ⟨build (tailProfile who),
      fun _ => PMF.pure (traffic (execution prior.support_nonempty.choose)), fun outcome => ?_⟩
    rw [nativeEq]
    have zero : (joint.bind continuePoint) (some outcome) = 0 := by
      rw [PMF.bind_apply, ENNReal.tsum_eq_zero.mpr]
      intro point
      by_cases supported : point ∈ joint.support
      · rw [outside point supported (fun living => present ⟨point, living, supported⟩) outcome,
          mul_zero]
      · rw [(PMF.apply_eq_zero_iff _ _).mpr supported, zero_mul]
    rw [zero]
    exact bot_le
  -- The survivors of the phase, conditioned on survival.
  let cond := joint.filter {point | alive point} present
  let NextSeed := {point // point ∈ cond.support}
  let nextPrior : PMF NextSeed := pmfToSubtype cond (fun _ member => member)
  have facts (point : NextSeed) : point.val ∈ joint.support ∧ alive point.val := by
    have member := (PMF.mem_support_filter_iff present).mp point.property
    exact ⟨member.2, member.1⟩
  let fallback : DecisionView who Δ → PMF _ :=
    fun _ => PMF.pure (traffic (execution prior.support_nonempty.choose))
  let nextNoise := fun view => presentConditional (kernel view) (fallback view)
  let observable := fun point : Seed × app.Execution => (nextSource point, traffic point.2)
  have survivalLaw : joint.map (fun point => if alive point then some (observable point)
      else none) = ((prior.map source).bind stepSource).bind fun config =>
        (kernel (config.view who)).map (Option.map fun extra => (config, extra)) := by
    rw [← phaseLaw]
    apply map_congr_on_support _
    intro point _
    by_cases withheld : DeviatorWithheld who point.2.application.config
    · simp [alive, withheld]
    · simp [alive, withheld, observable, traffic]
  have conditioned := filter_map_factor joint alive observable
    ((prior.map source).bind stepSource) kernel (fun config => config.view who) fallback
    survivalLaw present
  have mapVal {β : Type} (f : Seed × app.Execution → β) :
      nextPrior.map (fun point => f point.val) = cond.map f := by
    rw [show (fun point : NextSeed => f point.val) = f ∘ Subtype.val from rfl, ← PMF.map_comp,
      map_val_pmfToSubtype]
  have nextFactor : nextPrior.map (fun point => (nextSource point.val, traffic point.val.2)) =
      (nextPrior.map fun point => nextSource point.val).bind fun config =>
        (nextNoise (config.view who)).map fun extra => (config, extra) := by
    rw [mapVal observable, mapVal nextSource]
    exact conditioned
  obtain ⟨tailPolicy, tailNoise, tailBound⟩ := tailLaw nextPrior
    (fun point => nextSource point.val) (fun point => point.val.2)
    (fun point => nextAligned point.val (facts point).1 (facts point).2)
    (fun point => nextCheckpoint point.val (facts point).1 (facts point).2)
    (fun point _ => nextBoundary point.val (facts point).1)
    (fun point _ => nextBounded point.val (facts point).1)
    (fun point => nextOpens point.val (facts point).1 (facts point).2)
    (fun point _ => (facts point).2) nextNoise nextFactor
  refine ⟨build tailPolicy, fun view => tailNoise (recover view), fun outcome => ?_⟩
  let mass := ∑' point, ({point | alive point} : Set (Seed × app.Execution)).indicator joint point
  let tailContinue := fun point : NextSeed =>
    (deviationPhases scheduler players horizon rest point.val.2).map
      (withheldGate setup leaks who tail tailRefs (nextSource point.val).registry
        (nextSource point.val).revelations tailEmbedding)
  -- The program's surviving run is the residual's, lifted.
  have lifted : nextPrior.bind (fun point => continuePoint point.val) =
      (nextPrior.bind tailContinue).map (Option.map (Prod.map (Option.map lift) id)) := by
    rw [PMF.map_bind]
    apply bind_congr_on_support _
    intro point _
    rw [PMF.map_comp]
    apply map_congr_on_support _
    intro final _
    simp only [Function.comp_apply, withheldGate]
    split_ifs with withheld
    · rfl
    · simp only [Option.map_some, Prod.map, id]
      rw [decodeLater point.val (facts point).1 (facts point).2 final]
  have nativeBound : (nextPrior.bind fun point => continuePoint point.val) (some outcome) ≤
      (((nextPrior.bind fun point =>
          ((fun law => law.bind (ProtocolState.behavioralStateStep tail
            (Function.update tailProfile who tailPolicy)))^[eventCount tail]
            (PMF.pure (ProtocolState.entry tail (nextSource point.val)))).map some).bind
        fun state => (tailNoise (state.map (ProtocolState.observe who tail))).map
          fun extra => (state, extra)).map (Prod.map (Option.map lift) id)) outcome := by
    rw [lifted]
    exact map_some_apply_le (fun pair => tailBound pair) (Prod.map (Option.map lift) id) outcome
  -- The lifted residual source law, written through the residual configurations.
  let continuation := fun config : Config Player L Δ =>
    (((fun law => law.bind (ProtocolState.behavioralStateStep tail
      (Function.update tailProfile who tailPolicy)))^[eventCount tail]
      (PMF.pure (ProtocolState.entry tail config))).map fun state => some (lift state)).bind
      fun state => (tailNoise (recover (state.map (ProtocolState.observe who program)))).map
        fun extra => (state, extra)
  have sourceTail : (((nextPrior.bind fun point =>
          ((fun law => law.bind (ProtocolState.behavioralStateStep tail
            (Function.update tailProfile who tailPolicy)))^[eventCount tail]
            (PMF.pure (ProtocolState.entry tail (nextSource point.val)))).map some).bind
        fun state => (tailNoise (state.map (ProtocolState.observe who tail))).map
          fun extra => (state, extra)).map (Prod.map (Option.map lift) id)) =
      (nextPrior.map fun point => nextSource point.val).bind continuation := by
    simp only [continuation, Prod.map, PMF.map_bind, PMF.bind_map, PMF.bind_bind, PMF.map_comp,
      Function.comp_def]
    apply bind_congr_on_support _
    intro point _
    apply bind_congr_on_support _
    intro state _
    simp only [Option.map_some]
    have recovered := recovers (some state)
    simp only [Option.map_some] at recovered
    rw [recovered]
    rfl
  have programEq : (prior.bind fun seed =>
      ((fun law => law.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who (build tailPolicy))))^[eventCount program]
        (PMF.pure (ProtocolState.entry program (source seed)))).map some).bind
        (fun state => (tailNoise (recover (state.map (ProtocolState.observe who program)))).map
          fun extra => (state, extra)) =
      ((prior.map source).bind stepSource).bind continuation := by
    simp only [continuation, PMF.bind_bind, PMF.bind_map, Function.comp_def]
    apply bind_congr_on_support _
    intro seed supported
    rw [kernelEq tailPolicy seed supported, PMF.map_bind, PMF.bind_bind]
    apply bind_congr_on_support _
    intro next _
    simp only [PMF.bind_map, Function.comp_def, Option.map_some]
  -- Weighted by the surviving mass, the residual configurations are dominated.
  have dominated (config : Config Player L Δ) :
      mass * (nextPrior.map fun point => nextSource point.val) config ≤
        ((prior.map source).bind stepSource) config := by
    rw [mapVal nextSource]
    exact filter_marginal_le joint alive observable ((prior.map source).bind stepSource) kernel
      (fun config => config.view who) survivalLaw present config
  rw [nativeEq, bind_apply_eq_mass_mul_filter joint {point | alive point} present
      continuePoint (some outcome)
      (fun point supported notAlive => outside point supported notAlive outcome),
    show (cond.bind continuePoint) = nextPrior.bind fun point => continuePoint point.val by
      rw [show (nextPrior.bind fun point => continuePoint point.val) =
          (nextPrior.map Subtype.val).bind continuePoint from
        (PMF.bind_map nextPrior Subtype.val continuePoint).symm, map_val_pmfToSubtype],
    programEq]
  calc mass * (nextPrior.bind fun point => continuePoint point.val) (some outcome)
      ≤ mass * ((nextPrior.map fun point => nextSource point.val).bind continuation) outcome := by
        rw [← sourceTail]
        exact mul_le_mul' le_rfl nativeBound
    _ ≤ (((prior.map source).bind stepSource).bind continuation) outcome :=
        mul_bind_apply_le dominated continuation outcome

/-- **One exact phase, up to withholding.** If the run of the first phase,
ending at `high`, decodes through an injective embedding of residual entry
states, jointly with the deviator's traffic, with the law of a source step
kernel and a noise kernel of the deviator's residual view, keeps every point at
which the deviator has not withheld so, and stops at completion boundaries
within the horizon, then the residual deviation law up to withholding gives the
program's over all of its phases. -/
theorem WithholdLaw.phase_exact [Fintype Player] {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    {Δ : SourceCtx Player L} {tailNames : Finset VarId}
    (tail : SourceProgram Player L Δ tailNames) (tailProfile : BehavioralProfile tail)
    (tailRefs : ContextRefs (graphLayout setup.program) Δ)
    (tailEmbedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      tail)
    (tailBefore : ContextRefsBefore tailRefs tailEmbedding) (high : Nat) (rest : List Nat)
    (tailLaw : WithholdLaw setup leaks horizon scheduler players wholeProfile who tail
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
    (nextBoundary : ∀ point ∈ (phaseJoint setup leaks horizon scheduler players high prior
        execution).support, CompletionBoundary setup leaks scheduler players high point.2)
    (nextBounded : ∀ point ∈ (phaseJoint setup leaks horizon scheduler players high prior
        execution).support, point.2.environmentRecall.length ≤ horizon)
    (nextAligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile tail tailProfile
      tailRefs (nextRevelations seed) (nextRegistry seed) tailEmbedding tailBefore high)
    (nextOpens : ∀ seed, openingResidual tail tailProfile (nextRegistry seed)
      (nextRevelations seed))
    (preserved : ∀ point ∈ (phaseJoint setup leaks horizon scheduler players high prior
        execution).support, ¬ DeviatorWithheld who point.2.application.config)
    (absorbing : ∀ point ∈ (phaseJoint setup leaks horizon scheduler players high prior
        execution).support, DeviatorWithheld who point.2.application.config →
      ∀ final ∈ (deviationPhases scheduler players horizon rest point.2).support,
        DeviatorWithheld who final.application.config)
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
    (kernelEq : ∀ policy, ∀ seed ∈ prior.support,
      ((fun law => law.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who (build policy))))^[eventCount program]
        (PMF.pure (ProtocolState.entry program (source seed)))) =
      ((stepSource (source seed)).bind fun next =>
        ((fun law => law.bind (ProtocolState.behavioralStateStep tail
          (Function.update tailProfile who policy)))^[eventCount tail]
          (PMF.pure (ProtocolState.entry tail next)))).map lift) :
    ∃ policy : BehavioralPolicy who program,
      ∃ nextNoise : Option (ProtocolView who program) → PMF _,
        ∀ outcome,
          (prior.bind fun seed =>
            (deviationPhases scheduler players horizon (high :: rest) (execution seed)).map
              (withheldGate setup leaks who program refs (source seed).registry
                (source seed).revelations embedding)) (some outcome) ≤
          ((prior.bind fun seed =>
            ((fun law => law.bind (ProtocolState.behavioralStateStep program
              (Function.update profile who policy)))^[eventCount program]
              (PMF.pure (ProtocolState.entry program (source seed)))).map some).bind
            fun state => (nextNoise (state.map (ProtocolState.observe who program))).map
              fun extra => (state, extra)) outcome := by
  classical
  let joint := phaseJoint setup leaks horizon scheduler players high prior execution
  obtain ⟨nextSourceOf, nextCheckpoint, nextRegistryEq, nextRevelationsEq, _nextRead,
    nextMarginal, nextFactor⟩ := reconstruct_service_phase setup leaks who tailRefs high
      nextRegistry nextRevelations joint
      (fun config => lift (ProtocolState.entry tail config)) injective decode decodeEq
      (fun point member => (nextBoundary point member).ordered)
      ((prior.map source).bind stepSource) configNoise law
  let nextSource := fun point : Seed × (serviceApplication setup mode deadline leaks).Execution =>
    if member : point ∈ joint.support then nextSourceOf ⟨point, member⟩
    else nextSourceOf ⟨joint.support_nonempty.choose, joint.support_nonempty.choose_spec⟩
  have nextSourceEq (point : {point // point ∈ joint.support}) :
      nextSource point.val = nextSourceOf point := by
    simp only [nextSource, dite_eq_left point.property]
  refine WithholdLaw.finish setup leaks horizon scheduler players wholeProfile who program
    profile refs embedding tail tailProfile tailRefs tailEmbedding tailBefore high rest tailLaw
    prior source execution nextSource ?_ ?_ nextBoundary nextBounded ?_ absorbing stepSource
    (fun view => (configNoise view).map some) ?_ lift recover recovers ?_ build kernelEq
  · intro point member _
    rw [nextSourceEq ⟨point, member⟩, nextRegistryEq, nextRevelationsEq]
    exact nextAligned point.1
  · intro point member _
    rw [nextSourceEq ⟨point, member⟩]
    exact nextCheckpoint ⟨point, member⟩
  · intro point member _
    rw [nextSourceEq ⟨point, member⟩, nextRegistryEq, nextRevelationsEq]
    exact nextOpens point.1
  · have alive : joint.map (fun point => if DeviatorWithheld who point.2.application.config then
          none else some (nextSource point,
            (serviceRuntime setup mode deadline).bindingTraffic leaks who point.2)) =
        (pmfToSubtype joint (fun _ member => member)).map fun point =>
          some (nextSourceOf point,
            (serviceRuntime setup mode deadline).bindingTraffic leaks who point.val.2) := by
      conv_lhs => rw [← map_val_pmfToSubtype joint (fun _ member => member), PMF.map_comp]
      apply map_congr_on_support _
      intro point _
      simp only [Function.comp_apply, ite_eq_right (preserved point.val point.property),
        nextSourceEq point]
    rw [alive, show (fun point : {point // point ∈ joint.support} =>
        some (nextSourceOf point,
          (serviceRuntime setup mode deadline).bindingTraffic leaks who point.val.2)) =
        some ∘ fun point => (nextSourceOf point,
          (serviceRuntime setup mode deadline).bindingTraffic leaks who point.val.2) from rfl,
      ← PMF.map_comp, nextFactor, nextMarginal]
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Option.map_some]
  · intro point member _ final
    rw [nextSourceEq ⟨point, member⟩, nextRegistryEq, nextRevelationsEq]
    exact decodeLater point.1 final

end Law

/-- **The deviation law up to withholding over every phase.** On a
reveal-relaxed graph, under the asynchronous contract with timely delays,
against the first-turn clients of a source profile one player follows an
arbitrary native policy. Over the phases of any residual program, the decoded
source state jointly with the deviator's traffic, along the runs on which the
deviator does not withhold an effective disclosure, is at most the law of a
source run in which the deviator follows one source behavioral policy and every
other player keeps its source policy, the traffic factoring through the
deviator's source observation. -/
theorem asyncDeviation_withholdLaw [Fintype Player]
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (relaxed : (serviceGraph setup mode).RevealRelaxedOrdered)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    {Γ : SourceCtx Player L} {names : Finset VarId} {program : SourceProgram Player L Γ names}
    {offset : Nat} {ends : List Nat} (phases : ConcurrentPhaseEnds program offset ends) :
    ∀ (profile : BehavioralProfile program) (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding),
      WithholdLaw setup leaks horizon scheduler
        (deviatedTurnProfile bound turns (firstTurnTiming setup turns mode) wholeProfile who
          deviation) wholeProfile who program profile refs embedding refsBefore offset ends := by
  classical
  let app := serviceApplication setup mode deadline leaks
  let players := deviatedTurnProfile bound turns (firstTurnTiming setup turns mode) wholeProfile
    who deviation
  have absorbingAll {high : Nat} (rest : List Nat) {Seed : Type} (prior : PMF Seed)
      (execution : Seed → app.Execution) :
      ∀ point ∈ (phaseJoint setup leaks horizon scheduler players high prior execution).support,
        DeviatorWithheld who point.2.application.config →
        ∀ final ∈ (deviationPhases scheduler players horizon rest point.2).support,
          DeviatorWithheld who final.application.config :=
    fun point _ withheld final reached => withheld.reaches
      (deviationPhases_configReaches scheduler players horizon rest point.2 final reached)
  induction phases with
  | ret payoffs offset =>
      intro profile refs embedding refsBefore Seed prior source execution _aligned checkpoint
        _boundary _bounded _opens alive noise factor
      obtain ⟨nextNoise, nextFactor⟩ := ProtocolView.entry_noise_factor (.ret payoffs) who prior
        source (fun seed => (serviceRuntime setup mode deadline).bindingTraffic leaks who
          (execution seed)) noise factor
      refine ⟨profile who, nextNoise, fun outcome => le_of_eq ?_⟩
      let traffic := (serviceRuntime setup mode deadline).bindingTraffic leaks who
      let entries := prior.map fun seed =>
        (some (ProtocolState.entry (.ret payoffs) (source seed)), traffic (execution seed))
      have gateEq (seed : Seed) (supported : seed ∈ prior.support) :
          withheldGate setup leaks who (.ret payoffs) refs (source seed).registry
              (source seed).revelations embedding (execution seed) =
            some (some (ProtocolState.entry (.ret payoffs) (source seed)),
              traffic (execution seed)) := by
        unfold withheldGate
        rw [ite_eq_right (alive seed supported)]
        exact congrArg (fun decoded => some (decoded, traffic (execution seed)))
          ((checkpoint seed).decode (.ret payoffs) embedding.ref)
      have native : (prior.bind fun seed =>
          (deviationPhases scheduler players horizon [] (execution seed)).map
            (withheldGate setup leaks who (.ret payoffs) refs (source seed).registry
              (source seed).revelations embedding)) = entries.map some := by
        rw [PMF.map_comp, ← PMF.bind_pure_comp]
        apply bind_congr_on_support _
        intro seed supported
        simp only [deviationPhases, PMF.pure_map, Function.comp_apply]
        rw [gateEq seed supported]
      have marginal : (prior.bind fun seed =>
          ((fun law => law.bind (ProtocolState.behavioralStateStep (.ret payoffs)
            (Function.update profile who (profile who))))^[eventCount (.ret payoffs)]
            (PMF.pure (ProtocolState.entry (.ret payoffs) (source seed)))).map some) =
          entries.map Prod.fst := by
        rw [PMF.map_comp, ← PMF.bind_pure_comp]
        apply bind_congr_on_support _
        intro seed _
        simp only [eventCount, Function.iterate_zero, id_eq, PMF.pure_map, Function.comp_apply]
      rw [native, pmf_map_apply_of_injective _ (Option.some_injective _), marginal]
      exact congrArg (fun law : PMF _ => law outcome) nextFactor
  | @sample Γ names name payload fresh distribution next offset rest _ ih =>
      intro profile refs embedding refsBefore Seed prior source execution aligned checkpoint
        boundary bounded opens alive noise factor
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
      refine WithholdLaw.phase_exact setup leaks horizon scheduler players wholeProfile who
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
        ?_ stepSource configNoise ?_ (fun point member => (nextFacts ⟨point, member⟩).1)
        (fun point member => (nextFacts ⟨point, member⟩).2) ?_ (fun seed => opens seed) ?_
        (absorbingAll rest prior execution)
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
      · intro point member
        obtain ⟨supported, reached⟩ := phaseJoint_mem setup leaks horizon scheduler players member
        unfold ReactiveApplication.runUntilHorizon at reached
        refine not_deviatorWithheld_of_plain
          (runUntil_configReaches scheduler players _ _ _ _ reached) (alive _ supported)
          (boundary _ supported).ordered (nextFacts ⟨point, member⟩).1.ordered ?_
        intro other lower upper
        have same : other = event := Fin.ext (by omega)
        rw [same, outputEq]
        simp [EventGraph.EventField.IsPublication]
      · intro state
        cases state <;> rfl
      · intro seed final
        rfl
      · intro policy seed _
        change (fun law => law.bind (ProtocolState.behavioralStateStep _
          (Function.update profile who policy)))^[eventCount next + 1]
            (PMF.pure (ProtocolState.entry _ (source seed))) = _
        rw [ProtocolState.behavioralStatePrefix_sample, afterSample_update]
        simp only [stepSource, PMF.bind_map, PMF.map_bind, Function.comp_def]
  | @commits Γ names program offset rest count prefixed _ maximal _ ih =>
      intro profile refs embedding refsBefore Seed prior source execution aligned checkpoint
        boundary bounded opens alive noise factor
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
      obtain ⟨policy, configNoise, law⟩ := asyncDeviation_block_factorization relaxed wall
        contract timely turns wholeProfile who deviation bindings program profile count prefixed
        refs embedding refsBefore rfl prior source execution aligned checkpoint boundary bounded
        noise factor
      refine WithholdLaw.phase_exact setup leaks horizon scheduler players wholeProfile who program
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
        (fun point member => (nextFacts ⟨point, member⟩).1)
        (fun point member => (nextFacts ⟨point, member⟩).2) tailAligned
        (fun seed player => opensEffectively_commitTail (who := player) count program prefixed
          profile _ _ (opens seed player)) ?_ (absorbingAll rest prior execution)
        (commitTailRecover who count program prefixed)
        (commitTailRecover_spec who count program prefixed) ?_
        (graftPolicy who count program prefixed policy) ?_
      · simp only [phaseJoint, PMF.map_bind, PMF.map_comp, Function.comp_def]
        exact law
      · intro point member
        obtain ⟨supported, reached⟩ := phaseJoint_mem setup leaks horizon scheduler players member
        unfold ReactiveApplication.runUntilHorizon at reached
        exact not_deviatorWithheld_of_plain
          (runUntil_configReaches scheduler players _ _ _ _ reached) (alive _ supported)
          (boundary _ supported).ordered (nextFacts ⟨point, member⟩).1.ordered
          (plain_of_bindings bindings)
      · intro seed final
        have through := decodeSourcePrefix?_commitTail count program prefixed refs
          (source seed).registry (source seed).revelations embedding
          (eventCount (commitTail count program prefixed).tail) final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion mode)))
        rw [eventCount_commitTail] at through
        exact through
      · intro rest seed _
        have grafted := iterate_graftPolicy who count program profile prefixed policy rest
          (eventCount (commitTail count program prefixed).tail) (source seed)
        rw [eventCount_commitTail] at grafted
        rw [PMF.map_bind]
        exact grafted
  | @reveals Γ names program offset rest count prefixed positive maximal _ ih =>
      intro profile refs embedding refsBefore Seed prior source execution aligned checkpoint
        boundary bounded opens alive noise factor
      let tailRefs := revealTailRefs setup count program prefixed refs embedding
      let tailEmbedding := revealTailEmbedding setup count program prefixed embedding
      have tailBefore : ContextRefsBefore tailRefs tailEmbedding :=
        revealTailRefsBefore count program prefixed refs embedding refsBefore
      have tailAligned (seed : Seed) := CompiledPolicySuffix.revealTailMany wholeProfile count
        program prefixed profile refs (source seed).revelations (source seed).registry embedding
        refsBefore offset (aligned seed)
      have wall : RevealBlockEnd setup mode (offset + count) :=
        CompiledSuffix.revealBlockEnd maximal
          (tailAligned prior.support_nonempty.choose).graphSuffix
      have publications := prefixed.publications (mode := mode)
        (aligned prior.support_nonempty.choose).graphSuffix
      have nextFacts (point : PhasePoint setup leaks horizon scheduler players (offset + count)
          prior execution) :
          CompletionBoundary setup leaks scheduler players (offset + count) point.val.2 ∧
            point.val.2.environmentRecall.length ≤ horizon := by
        obtain ⟨supported, reached⟩ := phaseJoint_mem setup leaks horizon scheduler players
          point.property
        have done := blockRun_completes contract.completes (offset + count)
          (execution point.val.1) (boundary _ supported) (bounded _ supported) _ reached
        obtain ⟨nextBounded, nextBoundary⟩ := blockRun_boundary (Nat.le_add_right _ _)
          (RevealBlockEnd.sealed relaxed wall publications) wall.1 (execution point.val.1)
          (boundary _ supported) (bounded _ supported) _ reached done
        exact ⟨nextBoundary, nextBounded⟩
      have through (seed : Seed) (player : Player) :=
        BehavioralPolicy.OpensEffectively.through count program prefixed (source seed).registry
          (source seed).revelations (profile player) (opens seed player)
      obtain ⟨decoded, kernel, law⟩ := asyncDeviation_revealBlock_factorization relaxed wall
        contract timely turns wholeProfile who deviation program profile count prefixed positive
        refs embedding refsBefore rfl prior source execution aligned
        (fun seed player => (through seed player).1) checkpoint boundary bounded alive noise
        factor
      let nextSource := fun point : Seed × app.Execution =>
        openChain count program prefixed (source point.1)
      have chainEq (seed : Seed) := openChain_eq count program prefixed (source seed)
      refine WithholdLaw.finish setup leaks horizon scheduler players wholeProfile who program
        profile refs embedding (revealTail count program prefixed).tail
        (revealTailProfile count program prefixed profile) tailRefs tailEmbedding tailBefore
        (offset + count) rest (ih _ tailRefs tailEmbedding tailBefore) prior source execution
        nextSource ?_ ?_ (fun point member => (nextFacts ⟨point, member⟩).1)
        (fun point member => (nextFacts ⟨point, member⟩).2) ?_ (absorbingAll rest prior execution)
        (fun config => PMF.pure (openChain count program prefixed config)) kernel ?_
        (revealTail count program prefixed).lift (revealTailRecover who count program prefixed)
        (revealTailRecover_spec who count program prefixed) ?_
        (fun policy => revealGraft who count program prefixed (profile who) policy) ?_
      · intro point _ _
        simp only [nextSource]
        rw [chainEq point.1]
        exact tailAligned point.1
      · intro point member live
        obtain ⟨supported, reached⟩ := phaseJoint_mem setup leaks horizon scheduler players member
        obtain ⟨agree, history⟩ := revealTail_agrees_of_decode count program prefixed refs _ _
          embedding _ _ _ (decoded point.1 supported point.2 reached live)
        exact ⟨agree, history, (nextFacts ⟨point, member⟩).1.ordered⟩
      · intro point _ _ player
        simp only [nextSource]
        rw [chainEq point.1]
        exact (through point.1 player).2 profile rfl
      · simp only [phaseJoint, PMF.map_bind, PMF.map_comp, Function.comp_def]
        exact law
      · intro point _ _ final
        have later := decodeSourcePrefix?_revealTail count program prefixed refs
          (source point.1).registry (source point.1).revelations embedding
          (eventCount (revealTail count program prefixed).tail) final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion mode)))
        rw [eventCount_revealTail] at later
        simp only [nextSource]
        rw [chainEq point.1]
        exact later
      · intro rest seed supported
        have grafted := iterate_revealGraft who count program profile prefixed rest
          (eventCount (revealTail count program prefixed).tail) (source seed)
          (fun player => (through seed player).1)
        rw [eventCount_revealTail] at grafted
        rw [grafted, PMF.pure_bind]

end Vegas
