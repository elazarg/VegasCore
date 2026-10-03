/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceSpec
import GameTheoryExtensions.Analysis.FinitePayoffBounds

/-! # Fixed deposits for every scheduler

The deposit is computed from the range of a base payoff over every legal
history of the bounded native menu, up to a horizon and under a scheduler
(`Vegas.asyncAuditDeposit`). The extrema include every effective native
response and every off-path continuation, so the deposit covers the gain
between any two histories (`Vegas.asyncAuditDeposit_covers_gain`), whatever
policies or beliefs produced them. It needs only that the scheduler's nature
branches finitely; no plan or roster enters.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]

local instance : Nonempty ((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
    horizon scheduler).History :=
  ⟨((bounds.menu (runtime setup) leaks).protocol (initialLaw setup) horizon
    scheduler).initHistory⟩

open Classical in
/-- A sufficient fixed deposit from the range of a base payoff over every legal
history up to the horizon under the scheduler. The supplied rate must bound
additional collection at the comparison point. -/
def asyncAuditDeposit (base : (application setup leaks).ProtocolState → Player → ℝ)
    (probability : Player → ℝ) (who : Player) : ℝ :=
  let payoff := fun history : ((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
    horizon scheduler).History => base history.state who
  (FinitePayoffBounds.upper payoff - FinitePayoffBounds.lower payoff) / probability who

theorem asyncAuditDeposit_nonnegative
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (probability : Player → ℝ) (who : Player) (positive : 0 < probability who) :
    0 ≤ asyncAuditDeposit setup leaks bounds horizon scheduler base probability who := by
  classical
  exact div_nonneg (sub_nonneg.mpr (FinitePayoffBounds.lower_le_upper _)) positive.le

/-- **The deposit covers every gain.** For every scheduler with finitely
branching nature and every horizon, the fixed deposit covers the gain between
any two legal histories, independently of the policies or conditional beliefs
that produced them. -/
theorem asyncAuditDeposit_covers_gain
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (probability : Player → ℝ) (who : Player) (positive : 0 < probability who)
    (original repaired : ((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History) :
    base original.state who ≤ base repaired.state who + probability who *
      asyncAuditDeposit setup leaks bounds horizon scheduler base probability who := by
  classical
  let payoff := fun history : ((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
    horizon scheduler).History => base history.state who
  change payoff original ≤ payoff repaired +
    probability who * ((FinitePayoffBounds.upper payoff - FinitePayoffBounds.lower payoff) /
      probability who)
  rw [mul_div_cancel₀ _ positive.ne']
  have first := FinitePayoffBounds.le_upper payoff original
  have second := FinitePayoffBounds.lower_le payoff repaired
  linarith

namespace AsyncServiceSpec

variable (service : AsyncServiceSpec Player L)

/-- The service's fixed deposit, over its horizon and scheduler. -/
def auditDeposit (base : (application service.setup service.leaks).ProtocolState → Player → ℝ)
    (probability : Player → ℝ) (who : Player) : ℝ :=
  asyncAuditDeposit service.setup service.leaks service.bounds service.horizon service.scheduler
    base probability who

/-- The service's deposit covers the gain between any two legal histories. -/
theorem auditDeposit_covers_gain
    (base : (application service.setup service.leaks).ProtocolState → Player → ℝ)
    (probability : Player → ℝ) (who : Player) (positive : 0 < probability who)
    (original repaired : ((service.bounds.menu (runtime service.setup) service.leaks).protocol
      (initialLaw service.setup) service.horizon service.scheduler).History) :
    base original.state who ≤ base repaired.state who + probability who *
      service.auditDeposit base probability who :=
  asyncAuditDeposit_covers_gain service.setup service.leaks service.bounds service.horizon
    service.scheduler base probability who positive original repaired

end AsyncServiceSpec

end Vegas
