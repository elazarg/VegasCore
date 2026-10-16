/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveHistoryMixtureStep
import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound

/-! # Full stopped histories retain their original private policy members -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

local notation "N" => menu.information initial horizon scheduler
local notation "E" => menu.protocol initial horizon scheduler

/-- The existing stopped history evaluator disintegrates the original complete
private-member profile by actual final own recall. Every signed response and
scheduler transition remains in the same history carrier. -/
theorem runUntil_policyMixtures_joint {Memory : Principal → Type}
    (certificate : (E).WellFoundedHistories)
    (priors : (who : Principal) → PMF (Memory who))
    (members : (who : Principal) → Memory who → app.Policy)
    (covered : ∀ who memory past view action, action ∈ (members who memory past view).support →
      action ∈ menu.actions who past view)
    (stopped : (E).History → Prop) (history : (E).History) :
    (independentProduct (fun who => (app.policyMixture (priors who) (members who)).posterior
      (app.recallAt who history.state))).bind (fun memories =>
        ((N).runBehavioralUntil certificate (fun who =>
          menu.restrictPolicy initial horizon scheduler who (members who (memories who)))
            stopped history).map (fun final => (final, memories))) =
      ((N).runBehavioralUntil certificate (fun who =>
        menu.restrictPolicy initial horizon scheduler who
          (app.policyMixture (priors who) (members who)).policy) stopped history).bind
            fun final => (independentProduct (fun who =>
              (app.policyMixture (priors who) (members who)).posterior
                (app.recallAt who final.state))).map (Prod.mk final) := by
  classical
  let posterior := fun state : app.ProtocolState => independentProduct (fun who =>
    (app.policyMixture (priors who) (members who)).posterior (app.recallAt who state))
  let profile := fun (memories : (who : Principal) → Memory who) who =>
    menu.restrictPolicy initial horizon scheduler who (members who (memories who))
  let realized := fun who => menu.restrictPolicy initial horizon scheduler who
    (app.policyMixture (priors who) (members who)).policy
  change (posterior history.state).bind (fun memories =>
      ((N).runBehavioralUntil certificate (profile memories) stopped history).map
        (fun final => (final, memories))) =
    ((N).runBehavioralUntil certificate realized stopped history).bind fun final =>
      (posterior final.state).map (Prod.mk final)
  induction history using certificate.induction with
  | _ history ih =>
      by_cases halt : stopped history
      · simp only [(N).runBehavioralUntil_of_stopped certificate _ halt, PMF.pure_map,
          PMF.pure_bind]
        exact PMF.bind_pure_comp _ _
      by_cases ended : (E).terminal history.state
      · simp only [(N).runBehavioralUntil_of_terminal certificate _ ended, PMF.pure_map,
          PMF.pure_bind]
        exact PMF.bind_pure_comp _ _
      simp_rw [(N).runBehavioralUntil_of_running certificate _ halt ended]
      simp only [PMF.map_bind]
      have step := menu.run_one_policyMixtures_joint initial horizon scheduler priors members
        covered history (fun final memories =>
          ((N).runBehavioralUntil certificate (profile memories) stopped final).map
            (fun ending => (ending, memories)))
      change (posterior history.state).bind (fun memories =>
        ((N).runBehavioralFrom (profile memories) 1 history).bind (fun final =>
          ((N).runBehavioralUntil certificate (profile memories) stopped final).map
            (fun ending => (ending, memories)))) = _ at step
      rw [step, PMF.bind_bind]
      apply bind_congr_on_support
      intro final member
      exact ih final ((N).mem_support_runBehavioralFrom_one realized ended member).1

/-- Forgetting the original private tags recovers exactly the stopped
behavioral implementation, on the same actual full-history carrier. -/
theorem runUntil_policyMixtures {Memory : Principal → Type}
    (certificate : (E).WellFoundedHistories)
    (priors : (who : Principal) → PMF (Memory who))
    (members : (who : Principal) → Memory who → app.Policy)
    (covered : ∀ who memory past view action, action ∈ (members who memory past view).support →
      action ∈ menu.actions who past view)
    (stopped : (E).History → Prop) (history : (E).History) :
    (independentProduct (fun who => (app.policyMixture (priors who) (members who)).posterior
      (app.recallAt who history.state))).bind (fun memories =>
        (N).runBehavioralUntil certificate (fun who =>
          menu.restrictPolicy initial horizon scheduler who (members who (memories who)))
            stopped history) =
      (N).runBehavioralUntil certificate (fun who =>
        menu.restrictPolicy initial horizon scheduler who
          (app.policyMixture (priors who) (members who)).policy) stopped history := by
  have joint := congrArg (PMF.map Prod.fst) (menu.runUntil_policyMixtures_joint initial
    horizon scheduler certificate priors members covered stopped history)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at joint
  change ((independentProduct (fun who =>
      (app.policyMixture (priors who) (members who)).posterior
        (app.recallAt who history.state))).bind fun memories =>
      (((N).runBehavioralUntil certificate (fun who =>
        menu.restrictPolicy initial horizon scheduler who (members who (memories who)))
          stopped history).map id)) =
    (((N).runBehavioralUntil certificate (fun who =>
      menu.restrictPolicy initial horizon scheduler who
        (app.policyMixture (priors who) (members who)).policy) stopped history).bind fun final =>
          (independentProduct (fun who =>
            (app.policyMixture (priors who) (members who)).posterior
              (app.recallAt who final.state))).map (Function.const _ final)) at joint
  simpa only [PMF.map_id, PMF.map_const, PMF.bind_pure] using joint

end Interaction.ReactiveApplication.ResponseMenu
