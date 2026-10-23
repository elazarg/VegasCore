/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceFactorization
import Vegas.Compile.EventGraphParameterReadout
import GameTheory.Analysis.Protocol.CounterfactualDecomposition
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheory.Protocol.TremblingPlans

/-! # Joint source-state and traffic laws of service prefixes

The factorization uses the existing source protocol observation and the actual
native execution. Original failed disclosure intentions are restored by the
source assessment comparison; they are not inferred from the effective state
read by the native decoder.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime
open GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The actual typed decoder determines the next source configuration. Its
law supplies the source marginal; the ordered cut is supplied by actual
retained-prefix support. -/
theorem reconstruct_service_marginal
    {Seed Encoded : Type} (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}
    {Γ : SourceCtx Player L}
    (refs : ContextRefs (serviceGraph setup mode).layout Γ) (rank : Nat)
    (registry : Seed → Registry Γ) (revelations : Seed → Revelations Γ)
    (joint : PMF (Seed × (serviceApplication setup mode deadline leaks).Execution))
    (encoded : Config Player L Γ → Encoded) (injective : Function.Injective encoded)
    (decode : Seed → (serviceApplication setup mode deadline leaks).Execution → Option Encoded)
    (decodeEq : ∀ seed execution, decode seed execution =
      (decodeState? refs execution.application.config.store).map fun state =>
        encoded ⟨state, registry seed, revelations seed,
          decodeHistory setup.program (execution.application.config.history.map
            (setup.eventGraph.fromModeCompletion mode))⟩)
    (ordered : ∀ point ∈ joint.support, point.2.application.config.cut.IsPrefix rank)
    (marginal : PMF (Config Player L Γ))
    (law : joint.map (fun point => decode point.1 point.2) =
      marginal.map fun source => some (encoded source)) :
    let nextPrior := pmfToSubtype joint (fun _ member => member)
    ∃ source : {point // point ∈ joint.support} → Config Player L Γ,
      (∀ point, SourceCheckpoint setup (source point) refs rank point.val.2.application.config) ∧
      (∀ point, (source point).registry = registry point.val.1) ∧
      (∀ point, @Config.revelations Player L Γ (source point) = @revelations point.val.1) ∧
      (∀ point, decode point.val.1 point.val.2 = some (encoded (source point))) ∧
      nextPrior.map source = marginal := by
  intro nextPrior
  let Point := {point // point ∈ joint.support}
  have available (point : Point) :
      ∃ state, decodeState? refs point.val.2.application.config.store = some state := by
    have member : decode point.val.1 point.val.2 ∈
        (joint.map fun point => decode point.1 point.2).support :=
      PMF.support_map .. ▸ ⟨point.val, point.property, rfl⟩
    rw [law, PMF.support_map] at member
    obtain ⟨source, _, present⟩ := member
    rw [decodeEq] at present
    cases decoded : decodeState? refs point.val.2.application.config.store with
    | none => simp only [decoded, Option.map_none, reduceCtorEq] at present
    | some state => exact ⟨state, rfl⟩
  let source := fun point : Point =>
    (⟨(available point).choose, registry point.val.1, revelations point.val.1,
      decodeHistory setup.program (point.val.2.application.config.history.map
        (setup.eventGraph.fromModeCompletion mode))⟩ : Config Player L Γ)
  have decoded (point : Point) : decode point.val.1 point.val.2 =
      some (encoded (source point)) := by
    rw [decodeEq, (available point).choose_spec]
    rfl
  have marginalEq : nextPrior.map source = marginal := by
    apply pmf_map_injective (f := fun source => some (encoded source))
      (fun _ _ equal => injective (Option.some.inj equal))
    calc
      _ = nextPrior.map (fun point => decode point.val.1 point.val.2) := by
        rw [PMF.map_comp]
        apply map_congr_on_support _
        intro point _
        exact (decoded point).symm
      _ = _ := (map_pmfToSubtype joint (fun _ member => member)
        (fun point => decode point.1 point.2)).trans law
  refine ⟨source, ?_, fun _ => rfl, fun _ => rfl, decoded, marginalEq⟩
  intro point
  exact ⟨decodeState?_agrees refs point.val.2.application.config.store _
    (available point).choose_spec, rfl, ordered point.val point.property⟩

/-- The actual typed decoder determines the next source configuration. Its
joint law supplies both the source marginal and the preceding observation
factor; the ordered cut is supplied by actual retained-prefix support. -/
theorem reconstruct_service_phase
    {Seed Encoded : Type} (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (focal : Player) {Γ : SourceCtx Player L}
    (refs : ContextRefs (serviceGraph setup mode).layout Γ) (rank : Nat)
    (registry : Seed → Registry Γ) (revelations : Seed → Revelations Γ)
    (joint : PMF (Seed × (serviceApplication setup mode deadline leaks).Execution))
    (encoded : Config Player L Γ → Encoded) (injective : Function.Injective encoded)
    (decode : Seed → (serviceApplication setup mode deadline leaks).Execution → Option Encoded)
    (decodeEq : ∀ seed execution, decode seed execution =
      (decodeState? refs execution.application.config.store).map fun state =>
        encoded ⟨state, registry seed, revelations seed,
          decodeHistory setup.program (execution.application.config.history.map
            (setup.eventGraph.fromModeCompletion mode))⟩)
    (ordered : ∀ point ∈ joint.support, point.2.application.config.cut.IsPrefix rank)
    (marginal : PMF (Config Player L Γ))
    (noise : DecisionView focal Γ → PMF _)
    (factor : joint.map (fun point => (decode point.1 point.2,
        (serviceRuntime setup mode deadline).bindingTraffic leaks focal point.2)) =
      marginal.bind fun source => (noise (source.view focal)).map fun extra =>
        (some (encoded source), extra)) :
    let nextPrior := pmfToSubtype joint (fun _ member => member)
    ∃ source : {point // point ∈ joint.support} → Config Player L Γ,
      (∀ point, SourceCheckpoint setup (source point) refs rank point.val.2.application.config) ∧
      (∀ point, (source point).registry = registry point.val.1) ∧
      (∀ point, @Config.revelations Player L Γ (source point) = @revelations point.val.1) ∧
      (∀ point, decode point.val.1 point.val.2 = some (encoded (source point))) ∧
      nextPrior.map source = marginal ∧
      nextPrior.map (fun point => (source point,
          (serviceRuntime setup mode deadline).bindingTraffic leaks focal point.val.2)) =
        (nextPrior.map source).bind fun config =>
          (noise (config.view focal)).map fun extra => (config, extra) := by
  intro nextPrior
  have law : joint.map (fun point => decode point.1 point.2) =
      marginal.map fun source => some (encoded source) := by
    have projected := congrArg (PMF.map Prod.fst) factor
    simpa only [PMF.map_comp, Function.comp_def, PMF.map_bind, pmf_map_fun_const,
      pmf_bind_pure_eq_map] using projected
  obtain ⟨source, checkpoint, registryEq, revelationsEq, decoded, marginalEq⟩ :=
    reconstruct_service_marginal setup refs rank registry revelations joint encoded injective
      decode decodeEq ordered marginal law
  refine ⟨source, checkpoint, registryEq, revelationsEq, decoded, marginalEq, ?_⟩
  have mapped : nextPrior.map (fun point => (some (encoded (source point)),
      (serviceRuntime setup mode deadline).bindingTraffic leaks focal point.val.2)) =
      joint.map (fun point => (decode point.1 point.2,
        (serviceRuntime setup mode deadline).bindingTraffic leaks focal point.2)) := by
    calc
      _ = nextPrior.map (fun point => (decode point.val.1 point.val.2,
          (serviceRuntime setup mode deadline).bindingTraffic leaks focal point.val.2)) := by
        apply map_congr_on_support _
        intro point _
        exact Prod.ext (decoded point).symm rfl
      _ = _ := map_pmfToSubtype joint (fun _ member => member)
        (fun point => (decode point.1 point.2,
          (serviceRuntime setup mode deadline).bindingTraffic leaks focal point.2))
  apply pmf_map_injective (f := fun pair : Config Player L Γ × _ =>
      (some (encoded pair.1), pair.2)) (by
    intro left right same
    apply Prod.ext
    · exact injective (Option.some.inj (congrArg Prod.fst same))
    · exact (Prod.mk.inj same).2)
  have marginalEq' : PMF.map source nextPrior = marginal := marginalEq
  simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def, marginalEq']
    using mapped.trans factor

end Vegas
