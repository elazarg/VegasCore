/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ClientSpecification
import Vegas.Game.OnePacketEquilibriumPreservation
import Vegas.Game.OnePacketRawLaw

/-! # Intended sequential equilibria in the audited native raw runtime

The actual bounded raw menu retains the source equilibrium's joint complete
configuration and settled payoff law. Sequential rationality covers whole
continuation policies in that supplied bounded menu. Supported play has no
public defaults and pays no count-audit charge.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

local notation "Initial" => initialLaw setup

variable {Parameter : Type} {parameter : State L setup.context → Parameter}
  {utility : Parameter × PublicOutcome setup.program → Player → ℝ}
  {excludedPayoff : Player → ℝ}

open Classical in
/-- An intended sequential equilibrium compiles to an actual native assessment
that is sequentially rational against every policy in the supplied bounded raw
menu and preserves the joint complete source configuration and settled payoff. -/
theorem intended_raw_sequentialEquilibrium_preserved
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended) :
    Nonempty (ClientCompilation spec intended) := by
  let := spec.finiteNature
  let := spec.finiteSource
  obtain ⟨native, nativeSE, nativeClear, nativeLaw⟩ :=
    intended_onePacket_sequentialEquilibrium_preserved (timeouts := timeouts) parameter utility
      excludedPayoff spec.wellFormed spec.independent spec.observable spec.opportunity
      spec.inclusion spec.completes spec.timely spec.exitBelow intended equilibrium
      spec.outputValues spec.inputValues spec.capacity
  obtain ⟨target, targetSE, clean, states, joint⟩ :=
    intended_raw_sequentialEquilibrium_of_onePacket (timeouts := timeouts) (initial := Initial)
      parameter utility excludedPayoff intended native nativeSE nativeLaw spec.evidenceService
      spec.observationRate spec.deliveryRate spec.delivery_nonnegative spec.coverage
      spec.lowerUtility spec.upperUtility spec.lower_le spec.le_upper spec.deposit
      spec.deposit_nonnegative spec.funded
  have fullSE := (target.isSequentialEquilibrium_iff_truncated_of_bounded _ _
    ((bounds.rawMenu timeouts leaks).bounded Initial horizon scheduler).wellFoundedHistories
    ((bounds.rawMenu timeouts leaks).bounded Initial horizon scheduler) _).mpr targetSE
  refine ⟨⟨target, fullSE, ?_, clean, joint⟩⟩
  intro final supported control current
  let raw := bounds.rawMenu timeouts leaks
  let normalize := ((reactiveNormalization timeouts) leaks).state
  have represented : normalize final.state ∈
      (((raw.information Initial horizon scheduler).runBehavioral target.strategy
        (2 * horizon + 1)).map (fun history => normalize history.state)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨final, supported, rfl⟩
  rw [states] at represented
  obtain ⟨original, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp represented
  rw [current] at same
  exact nativeClear original reached
    { control with execution :=
      ((reactiveNormalization timeouts) leaks).execution control.execution } same

end Vegas
