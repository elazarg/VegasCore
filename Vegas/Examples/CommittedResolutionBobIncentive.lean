/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommittedResolutionBobAudit
import Vegas.Examples.CommittedResolutionBobReadout
import Vegas.Examples.CommittedResolutionForfeit

/-! # Final native disclosure incentives under arbitrary beliefs

In the fixed committed-resolution example, Bob receives one final activation
with immediate inclusion of his truthful opening. Utility uses the complete
typed source decoder, disclosure forfeits, and the actual terminal audit.
Canonical disclosure weakly dominates every raw response at every legal
decision history when its forfeit covers the source payoff range. The result
holds under arbitrary beliefs and future player policies, and gives an
explicit strict gap for publication failure above that range.
-/

noncomputable section

namespace Vegas.Examples.CommittedResolutionBobIncentive

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement
open CommittedResolutionService CommittedResolutionReadout
  CommittedResolutionBobService CommittedResolutionBobAudit
  CommittedResolutionBobReadout CommittedResolutionForfeit

variable {Parameter : Type} (parameter : State simpleExpr initialCtx → Parameter)
  (utility : Parameter × PublicOutcome program → Player → ℝ) (forfeit : ℝ)
  (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
  (deposit : Player → ℝ)

/-- The existing forfeited base utility and terminal audit of this native game. -/
def nativeUtility : app.ProtocolState → Player → ℝ :=
  TerminalAudit.utility (baseUtility setup leaks (fun terminal =>
      forfeitUtility program forfeit utility (setup.parameterOutcome parameter terminal)))
    ((runtime setup).serviceAuditObservation leaks)
    (sourceServiceAudit setup leaks sample) deposit

theorem bob_native_utility_bounded (lower upper : ℝ)
    (within : ∀ terminal : State simpleExpr program.terminalCtx,
      lower ≤ utility (setup.parameterOutcome parameter terminal) bob ∧
        utility (setup.parameterOutcome parameter terminal) bob ≤ upper)
    (state : app.ProtocolState) :
    |nativeUtility parameter utility forfeit sample deposit state bob| ≤
      |lower| + |upper| + |forfeit| + |deposit bob| := by
  have baseBound :
      |baseUtility setup leaks (fun terminal => forfeitUtility program forfeit utility
          (setup.parameterOutcome parameter terminal)) state bob| ≤
        |lower| + |upper| + |forfeit| := by
    change |(sourceReadout setup leaks state).elim 0
      (fun terminal => forfeitUtility program forfeit utility
        (setup.parameterOutcome parameter terminal) bob)| ≤ _
    cases read : sourceReadout setup leaks state with
    | none => simp only [Option.elim_none, abs_zero]; positivity
    | some terminal =>
        simp only [Option.elim_some]
        have count : |(failedReveals program bob (publicOutcome program terminal) : ℝ)| ≤ 1 := by
          rw [bob_failed_reveals]
          split_ifs <;> norm_num
        have plain : |utility (setup.parameterOutcome parameter terminal) bob| ≤
            |lower| + |upper| := by
          apply abs_le.mpr
          constructor
          · linarith [(within terminal).1, neg_abs_le lower, abs_nonneg upper]
          · linarith [(within terminal).2, le_abs_self upper, abs_nonneg lower]
        change |utility (setup.parameterOutcome parameter terminal) bob -
          forfeit * (failedReveals program bob (publicOutcome program terminal) : ℝ)| ≤ _
        calc
          _ ≤ |utility (setup.parameterOutcome parameter terminal) bob| +
              |forfeit * (failedReveals program bob (publicOutcome program terminal) : ℝ)| :=
            abs_sub _ _
          _ ≤ |lower| + |upper| + |forfeit| := by
            rw [abs_mul]
            nlinarith [abs_nonneg forfeit]
  have charged := TerminalAudit.charge_mem_Icc ((runtime setup).serviceAuditObservation leaks)
    (sourceServiceAudit setup leaks sample) state bob
  unfold nativeUtility TerminalAudit.utility
  calc
    _ ≤ |baseUtility setup leaks (fun terminal => forfeitUtility program forfeit utility
          (setup.parameterOutcome parameter terminal)) state bob| +
        |TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
          (sourceServiceAudit setup leaks sample) state bob * deposit bob| := abs_sub _ _
    _ ≤ |lower| + |upper| + |forfeit| + |deposit bob| := by
      rw [abs_mul, abs_of_nonneg charged.1]
      nlinarith [charged.2, abs_nonneg (deposit bob)]

/-- Every failed native publication incurs one source forfeit, and a
nonnegative audit deduction cannot improve its payoff. -/
theorem bob_failed_native_utility_le (upper : ℝ)
    (within : ∀ terminal : State simpleExpr program.terminalCtx,
      utility (setup.parameterOutcome parameter terminal) bob ≤ upper)
    (nonnegative : 0 ≤ deposit bob)
    (players : Player → app.Policy) (control : app.Control)
    (trace : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace (some control))
    (active : control.actor = some bob) (response : app.Action) (final : app.Execution)
    (reached : final ∈ (app.runRounds CommittedResolutionRecovery.scheduler players 5
      (control.execution.respond app bob response)).support)
    (failed : final.application.config.store (.inr bobEvent) = some .failure) :
    nativeUtility parameter utility forfeit sample deposit (app.finished final) bob ≤
      upper - forfeit := by
  obtain ⟨terminal, read⟩ := bob_horizon_readout_exists players control trace active response
    final reached
  have decoded : decodeState? (terminalRefs program) final.application.config.store =
      some terminal := by
    change sourceReadout setup leaks (some ⟨0, none, final⟩) = some terminal at read
    rwa [sourceReadout_eq_decode] at read
  have count := bob_failed_reveals_of_failure final.application terminal decoded failed
  have charged := TerminalAudit.charge_mem_Icc ((runtime setup).serviceAuditObservation leaks)
    (sourceServiceAudit setup leaks sample) (app.finished final) bob
  change (sourceReadout setup leaks (app.finished final)).elim 0 (fun source =>
      forfeitUtility program forfeit utility (setup.parameterOutcome parameter source) bob) -
    TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) (app.finished final) bob * deposit bob ≤ _
  rw [read, Option.elim_some]
  change utility (setup.parameterOutcome parameter terminal) bob -
      forfeit * (failedReveals program bob (publicOutcome program terminal) : ℝ) -
    TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) (app.finished final) bob * deposit bob ≤ _
  rw [count, Nat.cast_one, mul_one]
  nlinarith [within terminal, mul_nonneg charged.1 nonnegative]

/-- The actual canonical response succeeds and is uncharged after every
legal RAW Bob prefix, so it attains the source utility's lower bound. -/
theorem canonical_bob_native_utility_ge (lower : ℝ)
    (within : ∀ terminal : State simpleExpr program.terminalCtx,
      lower ≤ utility (setup.parameterOutcome parameter terminal) bob)
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (control : app.Control)
    (trace : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace (some control))
    (active : control.actor = some bob) :
    ∃ response : app.Action,
      (runtime setup).canonicalServiceDecision leaks bob (control.execution.recall bob)
        (control.execution.observe app bob) bobEvent true = response ∧
      ∀ (players : Player → app.Policy) (final : app.Execution),
        final ∈ (app.runRounds CommittedResolutionRecovery.scheduler
          players 5 (control.execution.respond app bob response)).support →
        final.application.config.store (.inr bobEvent) = some (.success true) ∧
        TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
          (sourceServiceAudit setup leaks sample) (app.finished final) bob = 0 ∧
        lower ≤ nativeUtility parameter utility forfeit sample deposit
          (app.finished final) bob := by
  have baseTrace := app.trace_of_scheduler_support_subset (initialLaw setup)
    CommittedResolutionService.horizon CommittedResolutionRecovery.scheduler
      CommittedResolutionService.scheduler
        CommittedResolutionRecovery.scheduler_support_subset trace
  have budget := bob_activation_remaining control baseTrace active
  rcases control with ⟨remaining, actor, execution⟩
  dsimp only at active budget
  subst actor
  subst remaining
  obtain ⟨material, next, decision, moved, clean⟩ :=
    canonical_bob_audit_clear (fun _ => app.silentPolicy) 4 execution trace sample authentic
  refine ⟨⟨some material⟩, decision, ?_⟩
  intro players final reached
  have cursor : 11 ≤ (execution.respond app bob ⟨some material⟩).environmentRecall.length := by
    rw [app.respond_environmentRecall, (recovery_bob_phase _ trace rfl).1]
  rw [recovery_suffix_policy_independent players (fun _ => app.silentPolicy) 5 _ cursor] at reached
  obtain ⟨terminal, read⟩ := bob_horizon_readout_exists (fun _ => app.silentPolicy)
    ⟨5, some bob, execution⟩ trace rfl ⟨some material⟩ final reached
  have decoded : decodeState? (terminalRefs program) final.application.config.store =
      some terminal := by
    change sourceReadout setup leaks (some ⟨0, none, final⟩) = some terminal at read
    rwa [sourceReadout_eq_decode] at read
  rw [ReactiveApplication.runRounds] at reached
  obtain ⟨first, firstReached, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  rw [moved, PMF.mem_support_pure_iff] at firstReached
  subst first
  obtain ⟨published, uncharged⟩ := clean (fun _ => app.silentPolicy) 4 le_rfl final continued
  have clear : TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) (app.finished final) bob = 0 := by
    change TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) (some ⟨0, none, final⟩) bob = 0
    simpa only [Nat.sub_self] using uncharged
  have count := bob_failed_reveals_of_success final.application terminal decoded published
  refine ⟨published, clear, ?_⟩
  change lower ≤ (sourceReadout setup leaks (app.finished final)).elim 0 (fun source =>
      forfeitUtility program forfeit utility (setup.parameterOutcome parameter source) bob) -
    TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) (app.finished final) bob * deposit bob
  rw [read, Option.elim_some, clear, zero_mul, sub_zero]
  change lower ≤ utility (setup.parameterOutcome parameter terminal) bob -
      forfeit * (failedReveals program bob (publicOutcome program terminal) : ℝ)
  rw [count, Nat.cast_zero, mul_zero, sub_zero]
  exact within terminal

/-- Every final native Bob publication is either failure or the binding's
actual value. Arbitrary raw responses cannot change that value. -/
theorem bob_horizon_result (players : Player → app.Policy) (control : app.Control)
    (trace : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace (some control))
    (active : control.actor = some bob) (response : app.Action) (final : app.Execution)
    (reached : final ∈ (app.runRounds CommittedResolutionRecovery.scheduler players 5
      (control.execution.respond app bob response)).support) :
    final.application.config.store (.inr bobEvent) = some .failure ∨
      final.application.config.store (.inr bobEvent) = some (.success true) := by
  have baseTrace := app.trace_of_scheduler_support_subset (initialLaw setup)
    CommittedResolutionService.horizon CommittedResolutionRecovery.scheduler
      CommittedResolutionService.scheduler
        CommittedResolutionRecovery.scheduler_support_subset trace
  have budget := bob_activation_remaining control baseTrace active
  rcases control with ⟨remaining, actor, execution⟩
  dsimp only at active budget
  subst actor
  subst remaining
  obtain ⟨responded⟩ := app.raw_trace_respond (initialLaw setup)
    CommittedResolutionService.horizon CommittedResolutionRecovery.scheduler 5 execution bob
      response trace
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (initialLaw setup)
    CommittedResolutionService.horizon CommittedResolutionRecovery.scheduler players 0 5
      (execution.respond app bob response) final responded reached
  have completed := CommittedResolutionRecovery.contract.completes ⟨0, none, final⟩
    finalTrace ⟨rfl, rfl⟩
  obtain ⟨result, stored⟩ := Option.isSome_iff_exists.mp
    (final.application.config.store_available_of_terminal completed (.inr bobEvent))
  cases result with
  | failure => exact Or.inl stored
  | success value =>
      have actual := bob_success_true CommittedResolutionRecovery.scheduler
        CommittedResolutionService.horizon ⟨0, none, final⟩ finalTrace value stored
      subst value
      exact Or.inr stored

/-- At every actual final Bob decision, the canonical opening weakly
dominates every raw response and every future policy. The comparison is
pointwise in the hidden history and both physical continuation outcomes.
Failure is strictly worse when the forfeit exceeds the source payoff range. -/
theorem canonical_bob_response_dominates (lower upper : ℝ)
    (within : ∀ terminal : State simpleExpr program.terminalCtx,
      lower ≤ utility (setup.parameterOutcome parameter terminal) bob ∧
        utility (setup.parameterOutcome parameter terminal) bob ≤ upper)
    (enough : upper - lower ≤ forfeit) (nonnegative : 0 ≤ deposit bob)
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (control : app.Control)
    (trace : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace (some control))
    (active : control.actor = some bob) :
    ∃ canonical : app.Action,
      (runtime setup).canonicalServiceDecision leaks bob (control.execution.recall bob)
        (control.execution.observe app bob) bobEvent true = canonical ∧
      ∀ (players future : Player → app.Policy) (response : app.Action)
        (final canonicalFinal : app.Execution),
        final ∈ (app.runRounds CommittedResolutionRecovery.scheduler players 5
          (control.execution.respond app bob response)).support →
        canonicalFinal ∈ (app.runRounds CommittedResolutionRecovery.scheduler future 5
          (control.execution.respond app bob canonical)).support →
        nativeUtility parameter utility forfeit sample deposit (app.finished final) bob ≤
          nativeUtility parameter utility forfeit sample deposit (app.finished canonicalFinal) bob ∧
        (final.application.config.store (.inr bobEvent) = some .failure →
          nativeUtility parameter utility forfeit sample deposit (app.finished final) bob +
            (forfeit - (upper - lower)) ≤
          nativeUtility parameter utility forfeit sample deposit
            (app.finished canonicalFinal) bob) := by
  obtain ⟨canonical, decision, canonicalBounds⟩ :=
    canonical_bob_native_utility_ge parameter utility forfeit sample deposit lower
      (fun terminal => (within terminal).1) authentic control trace active
  refine ⟨canonical, decision, ?_⟩
  intro players future response final canonicalFinal reached canonicalReached
  obtain ⟨published, clear, above⟩ := canonicalBounds future canonicalFinal canonicalReached
  have failedBound (failed : final.application.config.store (.inr bobEvent) = some .failure) :=
    bob_failed_native_utility_le parameter utility forfeit sample deposit upper
      (fun terminal => (within terminal).2) nonnegative players control trace active
        response final reached failed
  have failureGap : final.application.config.store (.inr bobEvent) = some .failure →
      nativeUtility parameter utility forfeit sample deposit (app.finished final) bob +
        (forfeit - (upper - lower)) ≤
      nativeUtility parameter utility forfeit sample deposit (app.finished canonicalFinal) bob := by
    intro failed
    linarith [failedBound failed]
  refine ⟨?_, failureGap⟩
  rcases bob_horizon_result players control trace active response final reached with failed |
    success
  · linarith [failedBound failed]
  · have ready := (recovery_bob_phase control trace active).2.2.2.1
    have same := bob_success_continuation_readout_eq control.execution ready
      players future CommittedResolutionRecovery.scheduler CommittedResolutionRecovery.scheduler
        5 5 response canonical final canonicalFinal reached canonicalReached success published
    have charged := TerminalAudit.charge_mem_Icc ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) (app.finished final) bob
    change (sourceReadout setup leaks (app.finished final)).elim 0 (fun source =>
        forfeitUtility program forfeit utility (setup.parameterOutcome parameter source) bob) -
      TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
        (sourceServiceAudit setup leaks sample) (app.finished final) bob * deposit bob ≤
      (sourceReadout setup leaks (app.finished canonicalFinal)).elim 0 (fun source =>
        forfeitUtility program forfeit utility (setup.parameterOutcome parameter source) bob) -
      TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
        (sourceServiceAudit setup leaks sample) (app.finished canonicalFinal) bob * deposit bob
    rw [same, clear, zero_mul, sub_zero]
    exact sub_le_self _ (mul_nonneg charged.1 nonnegative)

/-- Under any belief over actual Bob decision histories, the expected gain
from canonical disclosure is at least the forfeit's excess over the source
payoff range times the probability of final publication failure.
Responses may even depend on the hidden history; information-feasible
behavioral deviations are included as a special case. All later player
policies are arbitrary. No consistency or reach-probability premise is used. -/
theorem canonical_bob_response_regret {History : Type*} (lower upper : ℝ)
    (within : ∀ terminal : State simpleExpr program.terminalCtx,
      lower ≤ utility (setup.parameterOutcome parameter terminal) bob ∧
        utility (setup.parameterOutcome parameter terminal) bob ≤ upper)
    (enough : upper - lower ≤ forfeit) (nonnegative : 0 ≤ deposit bob)
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (control : History → app.Control)
    (trace : ∀ history, (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace (some (control history)))
    (active : ∀ history, (control history).actor = some bob)
    (belief : PMF History) (responses : History → PMF app.Action)
    (players future : History → Player → app.Policy) :
    (forfeit - (upper - lower)) *
      ((belief.bind fun history => (responses history).bind fun response =>
        app.runRounds CommittedResolutionRecovery.scheduler (players history) 5
          ((control history).execution.respond app bob response)).toOuterMeasure
        {final | final.application.config.store (.inr bobEvent) = some .failure}).toReal ≤
    expect (belief.bind fun history =>
      app.runRounds CommittedResolutionRecovery.scheduler (future history) 5
        ((control history).execution.respond app bob
          ((runtime setup).canonicalServiceDecision leaks bob
            ((control history).execution.recall bob)
            ((control history).execution.observe app bob) bobEvent true)))
      (fun final => nativeUtility parameter utility forfeit sample deposit
        (app.finished final) bob) -
    expect (belief.bind fun history => (responses history).bind fun response =>
      app.runRounds CommittedResolutionRecovery.scheduler (players history) 5
        ((control history).execution.respond app bob response))
      (fun final => nativeUtility parameter utility forfeit sample deposit
        (app.finished final) bob) := by
  classical
  let payoff : app.Execution → ℝ := fun final =>
    nativeUtility parameter utility forfeit sample deposit (app.finished final) bob
  let gap := forfeit - (upper - lower)
  let fails : Set app.Execution :=
    {final | final.application.config.store (.inr bobEvent) = some .failure}
  let augmented : app.Execution → ℝ := fun final =>
    payoff final + gap * if final ∈ fails then 1 else 0
  let rawKernel := fun history => (responses history).bind fun response =>
    app.runRounds CommittedResolutionRecovery.scheduler (players history) 5
      ((control history).execution.respond app bob response)
  let canonicalKernel := fun history =>
    app.runRounds CommittedResolutionRecovery.scheduler (future history) 5
      ((control history).execution.respond app bob
        ((runtime setup).canonicalServiceDecision leaks bob
          ((control history).execution.recall bob)
          ((control history).execution.observe app bob) bobEvent true))
  have integrable (law : PMF app.Execution) : PayoffIntegrable law payoff :=
    payoffIntegrable_of_bounded _ _ fun final =>
      bob_native_utility_bounded parameter utility forfeit sample deposit lower upper within
        (app.finished final)
  have integrableAugmented (law : PMF app.Execution) : PayoffIntegrable law augmented :=
    payoffIntegrable_add (integrable law)
      (payoffIntegrable_const_mul (payoffIntegrable_ite_one_zero law (· ∈ fails)))
  have branch : ∀ history ∈ belief.support,
      expect (rawKernel history) augmented ≤ expect (canonicalKernel history) payoff := by
    intro history _
    obtain ⟨canonical, decision, dominates⟩ := canonical_bob_response_dominates
      parameter utility forfeit sample deposit lower upper within enough nonnegative authentic
        (control history) (trace history) (active history)
    subst canonical
    apply expect_le_const _ augmented (integrableAugmented _)
      (expect (canonicalKernel history) payoff)
    intro final reached
    obtain ⟨response, _chosen, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
    have pointwise : ∀ canonicalFinal ∈ (canonicalKernel history).support,
        augmented final ≤ payoff canonicalFinal := by
      intro canonicalFinal canonicalReached
      have comparison := dominates (players history) (future history) response final canonicalFinal
        continued canonicalReached
      by_cases failed : final ∈ fails
      · simpa only [augmented, failed, ite_true, mul_one, payoff, gap] using comparison.2 failed
      · simpa only [augmented, failed, ite_false, mul_zero, add_zero, payoff] using comparison.1
    have averaged := expect_mono pointwise
      (payoffIntegrable_constant (canonicalKernel history) (augmented final))
      (integrable (canonicalKernel history))
    simpa only [expect_constant] using averaged
  have total := expect_mono branch
    (payoffIntegrable_bind_conditionalExpectation belief rawKernel augmented (integrableAugmented
      _))
    (payoffIntegrable_bind_conditionalExpectation belief canonicalKernel payoff (integrable _))
  rw [← expect_bind_tower belief rawKernel augmented (integrableAugmented _),
    ← expect_bind_tower belief canonicalKernel payoff (integrable _)] at total
  have indicatorIntegrable : PayoffIntegrable (belief.bind rawKernel)
      (fun final => if final ∈ fails then (1 : ℝ) else 0) :=
    payoffIntegrable_ite_one_zero _ _
  have expanded : expect (belief.bind rawKernel) augmented =
      expect (belief.bind rawKernel) payoff +
        gap * ((belief.bind rawKernel).toOuterMeasure fails).toReal := by
    change expect (belief.bind rawKernel)
      (fun final => payoff final + gap * if final ∈ fails then 1 else 0) = _
    rw [expect_add (integrable _) (payoffIntegrable_const_mul indicatorIntegrable),
      expect_const_mul]
    have eventMass : (expect (belief.bind rawKernel)
        (fun final => if final ∈ fails then (1 : ℝ) else 0)) =
        ((belief.bind rawKernel).toOuterMeasure fails).toReal := by
      calc
        _ = expect (belief.bind rawKernel) (fun final =>
            @ite ℝ (final ∈ fails) (Classical.propDecidable _) 1 0) :=
          expect_congr_on_support fun final _ => by
            by_cases failed : final ∈ fails <;> simp only [failed, ite_true, ite_false]
        _ = _ := expect_indicator (belief.bind rawKernel) fails
    exact congrArg (fun mass => expect (belief.bind rawKernel) payoff + gap * mass) eventMass
  rw [expanded] at total
  change gap * ((belief.bind rawKernel).toOuterMeasure fails).toReal ≤
    expect (belief.bind canonicalKernel) payoff - expect (belief.bind rawKernel) payoff
  linarith

end Vegas.Examples.CommittedResolutionBobIncentive
