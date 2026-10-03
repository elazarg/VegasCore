/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstTurnCompletes
import Interaction.ScheduledOpening

/-! # Source-prefix law of the global first-turn policy

The pure first-turn timing has no latent uncertainty after any own recall.
At an actual completion boundary the global policy therefore has the same
stopped law as the current event's first-turn profile. The decoded endpoint
has the actual source behavioral step law, including samples and explicit
withholding. This statement concerns the effective source profile and does
not identify a native information posterior.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem firstTurn_phaseProfile (bound : (graph setup).EventId → Nat)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (event : (graph setup).EventId) :
    phaseProfile setup leaks bound turns (firstTurnTiming setup turns) profile event =
      firstTurnProfile setup leaks bound turns profile event := by
  let app := application setup leaks
  cases owned : (graph setup).actor? event with
  | none =>
      rw [phaseProfile_actorless setup leaks bound turns _ profile event owned]
      simp only [firstTurnProfile, owned]
  | some owner =>
      rw [phaseProfile_owned setup leaks bound turns _ profile event owner owned]
      simp only [firstTurnProfile, owned, firstTurnTiming]
      congr 1
      funext past view
      let family := sourceServiceTurnFamily setup leaks bound profile owner event turns
      have fixed := app.policyMixture_posterior_pure_append (PMF.pure 0) family
        [] past 0 rfl
      simp only [List.nil_append] at fixed
      rw [app.policyMixture_policy, fixed, PMF.pure_bind]

/-- From an actual untouched completion boundary, the whole first-turn policy
advances the decoded source prefix by the source behavioral step. -/
theorem sourceServiceTurnPolicy_firstTurn_prefix_law [Fintype Player]
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (event : (graph setup).EventId) (start : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      event.val start)
    (bounded : start.environmentRecall.length ≤ horizon) :
    ∃ before : ProtocolState setup.program,
      sourceServicePrefix? setup event.val start.application.config = some before ∧
      ((application setup leaks).runUntilHorizon scheduler
        (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
        (fun final => event ∈ final.application.config.cut.completed) horizon start).map
          (fun stopped => sourceServicePrefix? setup (event.val + 1)
            stopped.application.config) =
        (ProtocolState.behavioralStateStep setup.program profile before).map some := by
  obtain ⟨rank, ranked, seen⟩ := roundsFrom_ranked setup leaks scheduler _ _ start
    boundary.supported
  have rankEq := isPrefix_unique ranked boundary.ordered
  subst rankEq
  obtain ⟨before, decoded, law⟩ := sourceServiceFirstTurn_prefix_law contract timely
    (firstTurnTiming setup turns) profile effective event start boundary bounded
  refine ⟨before, decoded, ?_⟩
  unfold ReactiveApplication.runUntilHorizon
  rw [runUntil_turnPolicy_eq_phase scheduler bound turns (firstTurnTiming setup turns)
    profile event _ start boundary.ordered seen, firstTurn_phaseProfile]
  exact law

end Vegas
