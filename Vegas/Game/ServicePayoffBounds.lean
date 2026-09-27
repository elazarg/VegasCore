/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRoster
import GameTheoryExtensions.Analysis.FinitePayoffBounds

/-! # Fixed deposits from all bounded service histories

The extrema include every effective native response and every off-path
continuation. They depend on the game and service, not on a source equilibrium.
For rational payoffs and an explicit finite history enumeration, the generic
finite-payoff checker computes the corresponding range certificate.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
  (network : (runtime setup).NetworkPolicy leaks)

local instance : Nonempty ((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).History :=
  ⟨((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).initHistory⟩

open Classical in
/-- A sufficient fixed deposit from the range of actual effective histories.
The supplied rate must bound additional collection at the comparison point. -/
def rosterAuditDeposit (base : (application setup leaks).ProtocolState → Player → ℝ)
    (probability : Player → ℝ) (who : Player) : ℝ :=
  let payoff := fun history : ((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).History =>
      base history.state who
  (FinitePayoffBounds.upper payoff - FinitePayoffBounds.lower payoff) / probability who

theorem rosterAuditDeposit_nonnegative
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (probability : Player → ℝ) (who : Player) (positive : 0 < probability who) :
    0 ≤ rosterAuditDeposit setup leaks bounds rosters network base probability who := by
  classical
  exact div_nonneg (sub_nonneg.mpr (FinitePayoffBounds.lower_le_upper _)) positive.le

/-- The fixed deposit covers the gain between any two actual histories,
independently of the policies or conditional beliefs that produced them. -/
theorem rosterAuditDeposit_covers_gain
    (base : (application setup leaks).ProtocolState → Player → ℝ)
    (probability : Player → ℝ) (who : Player) (positive : 0 < probability who)
    (original repaired : ((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).History) :
    base original.state who ≤ base repaired.state who + probability who *
      rosterAuditDeposit setup leaks bounds rosters network base probability who := by
  classical
  let payoff := fun history : ((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).History =>
      base history.state who
  change payoff original ≤ payoff repaired +
    probability who * ((FinitePayoffBounds.upper payoff - FinitePayoffBounds.lower payoff) /
      probability who)
  rw [mul_div_cancel₀ _ positive.ne']
  have first := FinitePayoffBounds.le_upper payoff original
  have second := FinitePayoffBounds.lower_le payoff repaired
  linarith

end Vegas.SourceProgram.RevealService
