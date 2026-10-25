/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound

/-! # Stopped laws from paired one-step kernels

A coupling of the actual one-step laws preserves a relation until either run
stops. Related stopped histories need only have the same readout. Their states
and histories may differ, as happens when one application drains automatic
failure steps at the transition into an excluded region.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol

variable {Player : Type*} [Fintype Player]
  {E T : ExecutionProtocol Player} (M : InformationModel E) (N : InformationModel T)

/-- Paired actual one-step laws give equal stopped readout laws. The relation
may identify stopped histories through a common exit classifier; neither a
history embedding nor agreement after the stopping transition is required. -/
theorem runBehavioralUntil_map_eq_of_paired_steps
    (firstCertificate : E.WellFoundedHistories) (secondCertificate : T.WellFoundedHistories)
    (firstProfile : (who : Player) → M.BehavioralPolicy who)
    (secondProfile : (who : Player) → N.BehavioralPolicy who)
    (firstStop : E.History → Prop) (secondStop : T.History → Prop)
    {Outcome : Type*} (firstReadout : E.History → Outcome)
    (secondReadout : T.History → Outcome)
    (related : E.History → T.History → Prop)
    (halting : ∀ first second, related first second →
      (firstStop first ∨ E.terminal first.state ↔ secondStop second ∨ T.terminal second.state))
    (classified : ∀ first second, related first second →
      firstStop first ∨ E.terminal first.state → firstReadout first = secondReadout second)
    (pairedStep : ∀ first second, related first second →
      ¬ firstStop first → ¬ E.terminal first.state →
      ∃ joint : PMF (E.History × T.History),
        joint.map Prod.fst = M.runBehavioralFrom firstProfile 1 first ∧
        joint.map Prod.snd = N.runBehavioralFrom secondProfile 1 second ∧
        ∀ next ∈ joint.support, related next.1 next.2) :
    ∀ first second, related first second →
      (M.runBehavioralUntil firstCertificate firstProfile firstStop first).map firstReadout =
        (N.runBehavioralUntil secondCertificate secondProfile secondStop second).map
          secondReadout := by
  classical
  intro first
  induction first using firstCertificate.induction with
  | _ first ih =>
  intro second linked
  by_cases halt : firstStop first ∨ E.terminal first.state
  · have otherHalt := (halting first second linked).mp halt
    have firstLaw : M.runBehavioralUntil firstCertificate firstProfile firstStop first =
        PMF.pure first := by
      rcases halt with stopped | ended
      · exact M.runBehavioralUntil_of_stopped firstCertificate firstProfile stopped
      · exact M.runBehavioralUntil_of_terminal firstCertificate firstProfile ended
    have secondLaw : N.runBehavioralUntil secondCertificate secondProfile secondStop second =
        PMF.pure second := by
      rcases otherHalt with stopped | ended
      · exact N.runBehavioralUntil_of_stopped secondCertificate secondProfile stopped
      · exact N.runBehavioralUntil_of_terminal secondCertificate secondProfile ended
    rw [firstLaw, secondLaw, PMF.pure_map, PMF.pure_map, classified first second linked halt]
  have firstGoing : ¬ firstStop first := fun stopped => halt (Or.inl stopped)
  have firstRunning : ¬ E.terminal first.state := fun ended => halt (Or.inr ended)
  have otherHalt : ¬ (secondStop second ∨ T.terminal second.state) := fun stopped =>
    halt ((halting first second linked).mpr stopped)
  have secondGoing : ¬ secondStop second := fun stopped => otherHalt (Or.inl stopped)
  have secondRunning : ¬ T.terminal second.state := fun ended => otherHalt (Or.inr ended)
  obtain ⟨joint, firstMarginal, secondMarginal, preserved⟩ :=
    pairedStep first second linked firstGoing firstRunning
  rw [M.runBehavioralUntil_of_running firstCertificate firstProfile firstGoing firstRunning,
    N.runBehavioralUntil_of_running secondCertificate secondProfile secondGoing secondRunning,
    PMF.map_bind, PMF.map_bind, ← firstMarginal, ← secondMarginal,
    PMF.bind_map, PMF.bind_map]
  apply bind_congr_on_support
  intro next supported
  have firstMember : next.1 ∈ (M.runBehavioralFrom firstProfile 1 first).support := by
    rw [← firstMarginal, PMF.mem_support_map_iff]
    exact ⟨next, supported, rfl⟩
  exact ih next.1 (M.mem_support_runBehavioralFrom_one firstProfile firstRunning firstMember).1
    next.2 (preserved next supported)

/-- Exact one-step summary laws determine the whole stopped summary law.
The summary may retain a physical execution while forgetting extra application
metadata; only steps before stopping need to agree. -/
theorem runBehavioralUntil_map_eq_of_step_maps
    (firstCertificate : E.WellFoundedHistories) (secondCertificate : T.WellFoundedHistories)
    (firstProfile : (who : Player) → M.BehavioralPolicy who)
    (secondProfile : (who : Player) → N.BehavioralPolicy who)
    (firstStop : E.History → Prop) (secondStop : T.History → Prop)
    {Summary : Type*} (firstSummary : E.History → Summary)
    (secondSummary : T.History → Summary)
    (halting : ∀ first second, firstSummary first = secondSummary second →
      (firstStop first ∨ E.terminal first.state ↔ secondStop second ∨ T.terminal second.state))
    (stepMaps : ∀ first second, firstSummary first = secondSummary second →
      ¬ firstStop first → ¬ E.terminal first.state →
      (M.runBehavioralFrom firstProfile 1 first).map firstSummary =
        (N.runBehavioralFrom secondProfile 1 second).map secondSummary) :
    ∀ first second, firstSummary first = secondSummary second →
      (M.runBehavioralUntil firstCertificate firstProfile firstStop first).map firstSummary =
        (N.runBehavioralUntil secondCertificate secondProfile secondStop second).map
          secondSummary := by
  classical
  intro first
  induction first using firstCertificate.induction with
  | _ first ih =>
  intro second same
  by_cases halt : firstStop first ∨ E.terminal first.state
  · have otherHalt := (halting first second same).mp halt
    have firstLaw : M.runBehavioralUntil firstCertificate firstProfile firstStop first =
        PMF.pure first := by
      rcases halt with stopped | ended
      · exact M.runBehavioralUntil_of_stopped firstCertificate firstProfile stopped
      · exact M.runBehavioralUntil_of_terminal firstCertificate firstProfile ended
    have secondLaw : N.runBehavioralUntil secondCertificate secondProfile secondStop second =
        PMF.pure second := by
      rcases otherHalt with stopped | ended
      · exact N.runBehavioralUntil_of_stopped secondCertificate secondProfile stopped
      · exact N.runBehavioralUntil_of_terminal secondCertificate secondProfile ended
    rw [firstLaw, secondLaw, PMF.pure_map, PMF.pure_map, same]
  have firstGoing : ¬ firstStop first := fun stopped => halt (Or.inl stopped)
  have firstRunning : ¬ E.terminal first.state := fun ended => halt (Or.inr ended)
  have otherHalt : ¬ (secondStop second ∨ T.terminal second.state) := fun stopped =>
    halt ((halting first second same).mpr stopped)
  have secondGoing : ¬ secondStop second := fun stopped => otherHalt (Or.inl stopped)
  have secondRunning : ¬ T.terminal second.state := fun ended => otherHalt (Or.inr ended)
  rw [M.runBehavioralUntil_of_running firstCertificate firstProfile firstGoing firstRunning,
    N.runBehavioralUntil_of_running secondCertificate secondProfile secondGoing secondRunning,
    PMF.map_bind, PMF.map_bind]
  apply bind_eq_of_map_eq (M.runBehavioralFrom firstProfile 1 first)
    (N.runBehavioralFrom secondProfile 1 second) firstSummary secondSummary
    (stepMaps first second same firstGoing firstRunning)
  intro next member other _otherMember sameSummary
  exact ih next (M.mem_support_runBehavioralFrom_one firstProfile firstRunning member).1
    other sameSummary

end GameTheory.Protocol.InformationModel
