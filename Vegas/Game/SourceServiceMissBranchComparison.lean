/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceDeposit
import Vegas.Game.SourceServiceAudit
import Vegas.Pending.ReactiveServiceAuditContinuation
import GameTheory.Math.Probability.ExpectationConditioning

/-! # The actual public-miss branch of native continuations

The audit collects one escrow with certainty on a public owner miss. Genuine
observation and delivery rates at most one make the configured range/rate
deposit cover the full native base-payoff range. Every terminal miss outcome
therefore has net payoff at most the base minimum, even under arbitrary later
responses. This uses no watcher coverage or renewed collection.

The same native terminal continuation law splits into its actual public-miss
and no-public-miss fibers. Only the miss fiber is bounded here. A no-miss
fiber can contain late accepted decisions and needs a source continuation
comparison; its value is not supplied or bounded by a desired WAIT inequality.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
local notation "menu" => service.bounds.menu (runtime service.setup) service.leaks
local notation "model" => ReactiveApplication.ResponseMenu.information
  (service.bounds.menu (runtime service.setup) service.leaks)
  (initialLaw service.setup) service.horizon service.scheduler

local instance miss_history_nonempty : Nonempty (((menu).protocol (initialLaw service.setup)
    service.horizon service.scheduler).History) :=
  ⟨((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).initHistory⟩

private theorem deposit_covers_range
    (base : (app).ProtocolState → Player → ℝ) (probability : Player → ℝ)
    (who : Player) (positive : 0 < probability who) (small : probability who ≤ 1) :
    let extremum := fun final : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).History => base final.state who
    FinitePayoffBounds.upper extremum - FinitePayoffBounds.lower extremum ≤
      service.auditDeposit base probability who := by
  intro extremum
  change FinitePayoffBounds.upper extremum - FinitePayoffBounds.lower extremum ≤
    (FinitePayoffBounds.upper extremum - FinitePayoffBounds.lower extremum) / probability who
  apply (le_div_iff₀ positive).mpr
  simpa only [mul_one] using mul_le_mul_of_nonneg_left small
    (sub_nonneg.mpr (FinitePayoffBounds.lower_le_upper extremum))

private theorem missed_utility_le_lower
    (base : (app).ProtocolState → Player → ℝ)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (probability : Player → ℝ) (who : Player)
    (positive : 0 < probability who) (small : probability who ≤ 1)
    (final : ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).History)
    (missed : (final.state.map fun control =>
      control.execution.application.publicView.missedDecisionBy who).getD false = true) :
    TerminalAudit.utility base ((runtime service.setup).serviceAuditObservation service.leaks)
        (sourceServiceAudit service.setup service.leaks sample)
        (service.auditDeposit base probability) final.state who ≤
      FinitePayoffBounds.lower (fun actual : ((menu).protocol (initialLaw service.setup)
        service.horizon service.scheduler).History => base actual.state who) := by
  have sufficient := service.deposit_covers_range base probability who positive small
  have upper := FinitePayoffBounds.le_upper (fun actual : ((menu).protocol
    (initialLaw service.setup) service.horizon service.scheduler).History => base actual.state who)
    final
  have collected : TerminalAudit.charge
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) final.state who = 1 := by
    cases current : final.state with
    | none =>
        simp only [current, Option.map_none, Option.getD_none] at missed
        cases missed
    | some control =>
        simp only [current, Option.map_some, Option.getD_some] at missed
        unfold sourceServiceAudit
        rw [(runtime service.setup).serviceAudit_charge]
        simp only [missed, ↓reduceIte]
  unfold TerminalAudit.utility
  rw [collected, one_mul]
  linarith

open Classical in
/-- The actual bounded native continuation splits by its public owner-miss
record. Valid configured rate bounds make the positive-mass miss fiber worth
at most the finite base minimum. The no-miss fiber is kept exactly, including
all actual late acceptance and subsequent policy choices. -/
theorem public_miss_continuation_decomposition
    (base : (app).ProtocolState → Player → ℝ)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (observationRate deliveryRate : Player → ℝ) (who : Player)
    (observationSmall : observationRate who ≤ 1)
    (deliveryNonnegative : 0 ≤ deliveryRate who) (deliverySmall : deliveryRate who ≤ 1)
    (positive : 0 < observationRate who * deliveryRate who)
    (assessment : (model).BehavioralAssessment) (site : (model).InformationSite who)
    (alternative : (model).BehavioralPolicy who) :
    let certificate := ((menu).bounded (initialLaw service.setup) service.horizon
      service.scheduler).wellFoundedHistories
    let probability := fun player => observationRate player * deliveryRate player
    let payoff := fun final : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).History => TerminalAudit.utility base
        ((runtime service.setup).serviceAuditObservation service.leaks)
        (sourceServiceAudit service.setup service.leaks sample)
        (service.auditDeposit base probability) final.state who
    let context := assessment.continuationContext certificate site payoff
    let law := context.outcome alternative
    let missing := fun final : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).History => (final.state.map fun control =>
        control.execution.application.publicView.missedDecisionBy who).getD false
    let marginal := law.map missing
    let conditional := fun branch => fiberPosterior law missing branch
    context.value alternative =
      (marginal true).toReal * expect (conditional true) payoff +
        (marginal false).toReal * expect (conditional false) payoff ∧
      (true ∈ marginal.support → expect (conditional true) payoff ≤
        FinitePayoffBounds.lower (fun final : ((menu).protocol (initialLaw service.setup)
          service.horizon service.scheduler).History => base final.state who)) := by
  intro certificate probability payoff context law missing marginal conditional
  have small : probability who ≤ 1 := by
    change observationRate who * deliveryRate who ≤ 1
    calc
      _ ≤ 1 * deliveryRate who :=
        mul_le_mul_of_nonneg_right observationSmall deliveryNonnegative
      _ ≤ 1 := by simpa only [one_mul] using deliverySmall
  constructor
  · change expect law payoff = _
    calc
      _ = expect (marginal.bind conditional) payoff :=
        (expect_congr_law (fiberPosterior_reconstruct law missing) payoff).symm
      _ = expect marginal (fun branch => expect (conditional branch) payoff) :=
        expect_bind_of_finite _ _ _
      _ = _ := by
        rw [expect_eq_sum, Fintype.sum_bool]
  · intro possible
    apply expect_le_const _ _ (payoffIntegrable_of_finite _ _)
    intro final supported
    have selected := (mem_support_fiberPosterior possible supported).1
    exact service.missed_utility_le_lower base sample probability who positive small final selected

end Vegas.AsyncServiceSpec
