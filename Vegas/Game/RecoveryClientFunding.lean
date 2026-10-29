/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryClientCompiler

/-! # Increasing deposits in a certified client specification

Observation rates are declared lower bounds and may be negative. Clamping that
bound to zero preserves coverage and makes deposit monotonicity unconditional.
The audit service, source, runtime and actual observation rule are unchanged.
-/

noncomputable section

namespace Vegas.RecoveryClientSpec

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (recoveryApplication runtime leaks).Scheduler}
  {Parameter : Type} {parameter : State L setup.context → Parameter}
  {utility : Parameter × PublicOutcome setup.program → Player → ℝ}
  {excludedPayoff : Player → ℝ}

/-- Any pointwise larger deposit gives another certified specification for the
same source, runtime and evidence service. No sign assumption on the old observation-rate
lower bound is needed. The resulting completion may differ off path. -/
def withDeposit (spec : RecoveryClientSpec setup runtime leaks bounds horizon scheduler
    parameter utility excludedPayoff) (deposit : Player → ℝ)
    (larger : ∀ who, spec.deposit who ≤ deposit who) :
    RecoveryClientSpec setup runtime leaks bounds horizon scheduler
      parameter utility excludedPayoff where
  __ := spec
  observationRate := fun who => max 0 (spec.observationRate who)
  coverage := by
    intro actual evidence present forbidden
    obtain ⟨observed, delivered⟩ := spec.coverage actual evidence present forbidden
    exact ⟨max_le ENNReal.toReal_nonneg observed, delivered⟩
  deposit := deposit
  deposit_nonnegative := fun who => (spec.deposit_nonnegative who).trans (larger who)
  funded := by
    intro who
    refine (spec.funded who).trans ?_
    calc
      spec.observationRate who * spec.deliveryRate who * spec.deposit who ≤
          max 0 (spec.observationRate who) * spec.deliveryRate who * spec.deposit who :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (spec.delivery_nonnegative who))
          (spec.deposit_nonnegative who)
      _ ≤ max 0 (spec.observationRate who) * spec.deliveryRate who * deposit who :=
        mul_le_mul_of_nonneg_left (larger who)
          (mul_nonneg (le_max_left _ _) (spec.delivery_nonnegative who))

end Vegas.RecoveryClientSpec
