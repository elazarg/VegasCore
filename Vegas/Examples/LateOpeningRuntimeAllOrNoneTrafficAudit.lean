/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeGame
import Vegas.Examples.LateOpeningRuntimeBobAudit

/-! # Authentic all-or-none traffic auditing

The sampler retains all observed signed traffic with the fixed sampling probability
and otherwise retains none. Public binding omissions remain deterministically
collected by the unchanged service audit. Expected charges and utilities below
do not identify realized settlement laws with deterministic scaled deposits.
-/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeAllOrNoneTrafficAudit
open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Enforcement GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeUtility
abbrev Evidence := SettledEvidence setup .sequential

/-- All authentic signed evidence is retained together
with probability `probability`. Sampling never creates signed evidence. -/
def sample (probability : ℝ) (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (actual : List Evidence) : PMF (List Evidence) :=
  mix probability nonnegative bounded (PMF.pure actual)
    (PMF.pure [])

theorem sample_authentic (probability : ℝ) (nonnegative : 0 ≤ probability)
    (bounded : probability ≤ 1) (actual observed : List Evidence)
    (supported : observed ∈ (sample probability nonnegative bounded actual).support) :
    observed ⊆ actual := by
  classical
  by_cases same : observed = actual
  · subst observed
    exact List.Subset.refl _
  · have filtered : observed = [] := by
      by_contra different
      rw [PMF.mem_support_iff, sample, mix_apply,
        PMF.pure_apply_of_ne _ _ same, PMF.pure_apply_of_ne _ _ different,
        mul_zero, mul_zero, add_zero] at supported
      exact supported rfl
    rw [filtered]
    simp

/-- Every actual envelope shares the same conditional coverage lower bound,
including sender and receiver evidence. -/
theorem sample_coverage (probability : ℝ) (nonnegative : 0 ≤ probability)
    (bounded : probability ≤ 1) (actual : List Evidence) (evidence : Evidence)
    (present : evidence ∈ actual) :
    probability ≤ ((sample probability nonnegative bounded actual).toOuterMeasure
      {observed | evidence ∈ observed}).toReal := by
  classical
  have domination (observed : List Evidence) :
      probability * ((PMF.pure actual) observed).toReal ≤
        ((sample probability nonnegative bounded actual) observed).toReal := by
    rw [sample, mix_apply_toReal]
    exact le_add_of_nonneg_right
      (mul_nonneg (sub_nonneg.mpr bounded) ENNReal.toReal_nonneg)
  have bound := probOf_domination (PMF.pure actual)
    (sample probability nonnegative bounded actual) probability domination
      {observed | evidence ∈ observed}
  simpa only [PMF.toOuterMeasure_pure_apply,
    ite_eq_left (show actual ∈ {observed | evidence ∈ observed} from present),
    ENNReal.toReal_one, mul_one] using bound

/-! Public binding omissions are deterministic evidence outside the traffic lottery.
The identities below concern expected utility; they do not equate realized settlements. -/

/-- Traffic sampling scales signed-evidence charges. Public binding omissions
remain fully collected by the unchanged service audit. -/
theorem charge (probability : ℝ) (nonnegative : 0 ≤ probability)
    (bounded : probability ≤ 1) (control : app.Control) (who : Player) :
    TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks
          (sample probability nonnegative bounded)) (some control) who =
      if control.execution.application.publicView.missedBindingBy who then 1 else
        probability * TerminalAudit.charge
          (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
          (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
          (some control) who := by
  classical
  change TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (LateOpeningRuntimeService.runtime.serviceAudit leaks fun record =>
      app.sampledTrafficAudit (fun traffic => ((record, traffic.envelope) : Evidence))
        (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2)
          (sample probability nonnegative bounded)) (some control) who =
    (if control.execution.application.publicView.missedBindingBy who then 1 else
      probability *
      TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (LateOpeningRuntimeService.runtime.serviceAudit leaks fun record =>
          app.sampledTrafficAudit (fun traffic => ((record, traffic.envelope) : Evidence))
            (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2)
              (fun actual => PMF.pure actual)) (some control) who)
  rw [serviceAudit_charge, serviceAudit_charge]
  by_cases missing : control.execution.application.publicView.missedBindingBy who = true
  · simp [missing]
  · have clear := Bool.eq_false_iff.mpr missing
    simp only [clear, Bool.false_eq_true, ↓reduceIte]
    simp only [ReactiveApplication.sampledTrafficAudit, sample, mix_map, PMF.pure_map]
    rw [mix_apply_toReal]
    simp [PMF.pure_apply]

theorem full_charge_of_omission (control : app.Control) (who : Player)
    (missing : control.execution.application.publicView.missedBindingBy who = true) :
    TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
      (some control) who = 1 := by
  have full := charge 1 (by norm_num) (by norm_num) control who
  have sampler : sample 1 (by norm_num) (by norm_num) =
      (fun actual => PMF.pure actual) := by
    funext actual
    exact mix_one _ _
  rw [sampler] at full
  simpa only [missing, ↓reduceIte] using full

/-- On states without a public omission the expected utility is exactly the
full-audit expected utility at scaled deposits. Realized settlement is not identified. -/
theorem payoff_of_no_omission (probability : ℝ) (nonnegative : 0 ≤ probability)
    (bounded : probability ≤ 1) (reward forfeit : ℝ) (deposit : Player → ℝ)
    (control : app.Control) (who : Player)
    (clear : control.execution.application.publicView.missedBindingBy who = false) :
    LateOpeningRuntimeGame.payoff reward forfeit (sample probability nonnegative bounded)
        deposit (some control) who =
      LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual)
        (fun owner => probability * deposit owner) (some control) who := by
  unfold LateOpeningRuntimeGame.payoff TerminalAudit.utility
  rw [charge]
  simp only [clear, Bool.false_eq_true, ↓reduceIte]
  ring

/-- The public-omission surcharge is the exact obstruction to uniform deposit scaling. -/
theorem payoff (probability : ℝ) (nonnegative : 0 ≤ probability)
    (bounded : probability ≤ 1) (reward forfeit : ℝ) (deposit : Player → ℝ)
    (control : app.Control) (who : Player) :
    LateOpeningRuntimeGame.payoff reward forfeit (sample probability nonnegative bounded)
        deposit (some control) who =
      LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual)
        (fun owner => probability * deposit owner) (some control) who -
      if control.execution.application.publicView.missedBindingBy who then
        (1 - probability) * deposit who else 0 := by
  by_cases missing : control.execution.application.publicView.missedBindingBy who = true
  · have full := full_charge_of_omission control who missing
    unfold LateOpeningRuntimeGame.payoff TerminalAudit.utility
    rw [charge, full]
    simp only [missing, ↓reduceIte]
    ring
  · have clear := Bool.eq_false_iff.mpr missing
    rw [payoff_of_no_omission probability nonnegative bounded reward forfeit deposit
      control who clear]
    simp only [clear, Bool.false_eq_true, ↓reduceIte, sub_zero]

theorem alice_payoff (probability : ℝ) (nonnegative : 0 ≤ probability)
    (bounded : probability ≤ 1) (reward forfeit : ℝ) (deposit : Player → ℝ)
    (control : app.Control) :
    LateOpeningRuntimeGame.payoff reward forfeit (sample probability nonnegative bounded)
        deposit (some control) alice =
      LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual)
        (fun owner => probability * deposit owner) (some control) alice :=
  payoff_of_no_omission probability nonnegative bounded reward forfeit deposit control alice
    (alice_no_binding_omission control.execution.application.publicView)

theorem charge_not_scaled_of_omission
    (probability : ℝ) (nonnegative : 0 ≤ probability) (strict : probability < 1)
    (control : app.Control) (who : Player)
    (missing : control.execution.application.publicView.missedBindingBy who = true) :
    TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks
          (sample probability nonnegative strict.le)) (some control) who ≠
      probability * TerminalAudit.charge
        (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
        (some control) who := by
  rw [charge]
  have collected := full_charge_of_omission control who missing
  rw [collected]
  simp only [missing, ↓reduceIte, mul_one]
  exact strict.ne'

/-- Every actual supported native continuation of a successful Bob binding has
exactly the scaled full-audit expected utility, with every policy unchanged. -/
theorem successful_binding_continuation_payoff
    (probability : ℝ) (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (weight : ℝ) (weightNonnegative : 0 ≤ weight) (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight weightNonnegative)).Trace (some control))
    (answer : Answer)
    (bound : control.execution.application.config.store (.inr bobBindEvent) =
      some (.success answer))
    (players : Player → app.Policy) (count : Nat) (final : app.Execution)
    (reached : final ∈ (app.runRounds
      (LateOpeningRuntimeService.scheduler weight weightNonnegative)
        players count control.execution).support)
    (reward forfeit : ℝ) (deposit : Player → ℝ) (who : Player) :
    LateOpeningRuntimeGame.payoff reward forfeit (sample probability nonnegative bounded)
        deposit (app.finished final) who =
      LateOpeningRuntimeGame.payoff reward forfeit (fun actual => PMF.pure actual)
        (fun owner => probability * deposit owner) (app.finished final) who := by
  have aligned : (app.protocol ((setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := nativeGraph))) LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight weightNonnegative)).Trace (some control) := by
    have same : (setup.initialLaw.map setup.eventInputs).map
        (EventGraphRuntime.State.initial (graph := nativeGraph)) = initial := by
      rw [PMF.map_comp]
      rfl
    rwa [same]
  have valid := LateOpeningRuntimeService.runtime.reactiveBindingInvariant_history leaks
    (setup.initialLaw.map setup.eventInputs) LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight weightNonnegative) aligned
  have invariant := LateOpeningRuntimeService.runtime.reactiveBindingInvariant leaks
  have finalValid := (ReactiveApplication.Invariant.policyInvariant app invariant players).runRounds
    (LateOpeningRuntimeService.scheduler weight weightNonnegative) count _ final valid reached
  have stored := LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks
    (.inr bobBindEvent) (.success answer)
  have finalBound := (ReactiveApplication.Invariant.policyInvariant app stored players).runRounds
    (LateOpeningRuntimeService.scheduler weight weightNonnegative) count _ final bound reached
  change LateOpeningRuntimeGame.payoff _ _ _ _ (some ⟨0, none, final⟩) who = _
  fin_cases who
  · exact alice_payoff probability nonnegative bounded reward forfeit deposit ⟨0, none, final⟩
  · exact payoff_of_no_omission probability nonnegative bounded reward forfeit deposit
      ⟨0, none, final⟩ bob
      (LateOpeningRuntimeBobAudit.no_binding_omission final.application finalValid
        answer finalBound)

end Vegas.Examples.LateOpeningRuntimeAllOrNoneTrafficAudit
