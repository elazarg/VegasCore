/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveSurvival
import GameTheoryExtensions.Analysis.Protocol.PublicationFailureObstruction

/-! # Bounded reactive execution with an explicit service outage

An ordinary public scheduler is mixed with a wait command at each physical
round. Waiting records the round without changing the application or invoking
a player. The resulting native evaluator has a positive finite-horizon error
against any source law that rules out an initially missing publication.
The normal scheduler and every player policy remain unrestricted. This is a
probabilistic service model, not a protected-delivery contract.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability GameTheory.Protocol.PublicationFailure

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- A physical service opportunity can fail while the normal public controller
remains arbitrary and history dependent. -/
def waitOutageScheduler (floor : ℝ) (nonnegative : 0 ≤ floor) (bounded : floor ≤ 1)
    (normal : app.Scheduler) : app.Scheduler := fun past view =>
  mix floor nonnegative bounded (PMF.pure .wait) (normal past view)

/-- Waiting consumes a scheduler round and leaves the application unchanged. -/
def waitOutageExecution (execution : app.Execution) : app.Execution :=
  { execution with environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .wait⟩] }

theorem dispatch_wait (players : Principal → app.Policy) (execution : app.Execution) :
    app.dispatch players .wait execution = PMF.pure (app.waitOutageExecution execution) := by
  simp only [dispatch, Execution.environmentStep, PMF.pure_map, Command.actor?,
    resume, PMF.pure_bind]
  rfl

/-- The native round evaluator derives the outage mixture from the actual
controller commands, rather than assuming a failure probability for its law. -/
theorem waitOutageScheduler_round (floor : ℝ) (nonnegative : 0 ≤ floor)
    (bounded : floor ≤ 1) (normal : app.Scheduler) (players : Principal → app.Policy)
    (execution : app.Execution) :
    app.round (app.waitOutageScheduler floor nonnegative bounded normal) players execution =
      outageKernel floor nonnegative bounded app.waitOutageExecution
        (app.round normal players) execution := by
  unfold round waitOutageScheduler outageKernel
  rw [mix_bind, PMF.pure_bind, app.dispatch_wait]

/-- Evaluate physical rounds from a distribution of actual executions. -/
theorem runRounds_bind_eq_iterate (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (count : Nat) (initial : PMF app.Execution) :
    initial.bind (app.runRounds scheduler players count) =
      (fun law : PMF app.Execution => law.bind (app.round scheduler players))^[count]
        initial := by
  induction count generalizing initial with
  | zero => simp only [runRounds, PMF.bind_pure, Function.iterate_zero, id_eq]
  | succ count induction =>
      change initial.bind (fun execution => (app.round scheduler players execution).bind
        (app.runRounds scheduler players count)) = _
      rw [← PMF.bind_bind, induction, Function.iterate_succ_apply]

/-- The observable obstruction applies to the actual initialization law, with
its ordinary private inputs, rather than to a chosen convenient execution. -/
theorem waitOutage_initial_totalVariation_lower_bound {Outcome : Type*}
    (floor : ℝ) (nonnegative : 0 ≤ floor) (bounded : floor ≤ 1)
    (normal : app.Scheduler) (players : Principal → app.Policy) (initial : PMF app.State)
    (observe : app.State → Outcome) (failed : Set Outcome)
    (source : PMF Outcome) (sourceNeverFails : (source.toOuterMeasure failed).toReal = 0)
    (count : Nat) {error : ℝ}
    (close : PMF.WithinTV error
      ((initial.bind (fun state => app.runRounds
        (app.waitOutageScheduler floor nonnegative bounded normal)
        players count (Execution.initial app state))).map
          (fun final => observe final.application)) source) :
    floor ^ count * (initial.toOuterMeasure (observe ⁻¹' failed)).toReal ≤ error := by
  have represented : initial.bind (fun state => app.runRounds
        (app.waitOutageScheduler floor nonnegative bounded normal) players count
        (Execution.initial app state)) =
      (initial.map (Execution.initial app)).bind
        (app.runRounds (app.waitOutageScheduler floor nonnegative bounded normal) players count) :=
    (PMF.bind_map ..).symm
  have kernel := funext (app.waitOutageScheduler_round floor nonnegative bounded normal players)
  rw [represented, app.runRounds_bind_eq_iterate, kernel] at close
  have lower := outageRun_totalVariation_lower_bound (initial.map (Execution.initial app))
    floor nonnegative bounded app.waitOutageExecution (app.round normal players)
    (fun final => observe final.application) failed (fun _ member => member)
    source sourceNeverFails count close
  rw [PMF.toOuterMeasure_map_apply] at lower
  exact lower

/-- A missing-publication event observable in the application cannot disappear
on the explicit wait branch, even when the normal branch contains arbitrary
adaptive policies, fees, retries, and public observations. -/
theorem waitOutage_runRounds_totalVariation_lower_bound {Outcome : Type*}
    (floor : ℝ) (nonnegative : 0 ≤ floor) (bounded : floor ≤ 1)
    (normal : app.Scheduler) (players : Principal → app.Policy)
    (observe : app.State → Outcome) (failed : Set Outcome)
    (source : PMF Outcome) (sourceNeverFails : (source.toOuterMeasure failed).toReal = 0)
    (count : Nat) (execution : app.Execution) (initial : observe execution.application ∈ failed)
    {error : ℝ}
    (close : PMF.WithinTV error
      ((app.runRounds (app.waitOutageScheduler floor nonnegative bounded normal)
        players count execution).map (fun final => observe final.application)) source) :
    floor ^ count ≤ error := by
  have kernel := funext (app.waitOutageScheduler_round floor nonnegative bounded normal players)
  rw [app.runRounds_eq_iterate, kernel] at close
  have lower := outageRun_totalVariation_lower_bound (PMF.pure execution)
    floor nonnegative bounded app.waitOutageExecution (app.round normal players)
    (fun final => observe final.application) failed (fun _ member => member)
    source sourceNeverFails count close
  have member : execution ∈ (fun final : app.Execution => observe final.application) ⁻¹' failed :=
    initial
  simpa only [PMF.toOuterMeasure_pure_apply, member, ite_true, ENNReal.toReal_one,
    mul_one] using lower

/-- No raw policy profile can realize the source law at a finite horizon when
the application initially has an observable missing publication. -/
theorem waitOutage_runRounds_not_realized {Outcome : Type*}
    (floor : ℝ) (positive : 0 < floor) (bounded : floor ≤ 1)
    (normal : app.Scheduler) (players : Principal → app.Policy)
    (observe : app.State → Outcome) (failed : Set Outcome)
    (source : PMF Outcome) (sourceNeverFails : (source.toOuterMeasure failed).toReal = 0)
    (count : Nat) (execution : app.Execution) (initial : observe execution.application ∈ failed) :
    (app.runRounds (app.waitOutageScheduler floor positive.le bounded normal)
      players count execution).map (fun final => observe final.application) ≠ source := by
  intro same
  have close : PMF.WithinTV 0
      ((app.runRounds (app.waitOutageScheduler floor positive.le bounded normal)
        players count execution).map (fun final => observe final.application)) source := by
    rw [same]
    exact PMF.WithinTV.refl _
  exact (not_le_of_gt (pow_pos positive count))
    (app.waitOutage_runRounds_totalVariation_lower_bound floor positive.le bounded
      normal players observe failed source sourceNeverFails count execution initial close)

end Interaction.ReactiveApplication
