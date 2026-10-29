/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveRestrictedContinuation
import Interaction.ReactiveFiniteAssessment

/-! # Whole-continuation rationality against admissible physical policies

The assessment's history beliefs evaluate the actual physical runner. Policy
restriction preserves every admissible unilateral continuation, including those
starting at information sets that prescribed play never reaches.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

omit [Fintype Principal] in
/-- Decoded behavioral policies stay within the menu at every legal decision. -/
theorem decodeProfile_admissible
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Principal) :
    menu.Admissible initial horizon scheduler who
      (menu.decodeProfile initial horizon scheduler profile who) := by
  intro control _ _ response supported
  exact menu.decode_embedPolicy_covered initial horizon scheduler who (profile who)
    _ _ response supported

/-- Agreement of represented strategies at legal histories identifies complete
physical continuations, without obligations at inconsistent callback inputs. -/
theorem run_realized_eq_finish
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (players : Principal → app.Policy)
    (admissible : ∀ who, menu.Admissible initial horizon scheduler who (players who))
    (realizes : ∀ (history : (menu.protocol initial horizon scheduler).History) who,
      menu.restrictPolicy initial horizon scheduler who (players who)
          ((menu.information initial horizon scheduler).infoOf who history.trace) =
        profile who ((menu.information initial horizon scheduler).infoOf who history.trace))
    (history : (menu.protocol initial horizon scheduler).History) :
    ((menu.information initial horizon scheduler).runBehavioralFrom profile
      (2 * horizon + 1) history).map History.state =
      app.finish initial horizon scheduler players history.state := by
  have same := (menu.information initial horizon scheduler).runBehavioralFrom_congr
    (first := fun who => menu.restrictPolicy initial horizon scheduler who (players who))
    (second := profile) (2 * horizon + 1) history (fun later _ _ who => realizes later who)
  rw [← same]
  apply menu.run_restrict_eq_finish initial horizon scheduler players admissible
  have bound := app.trace_bound initial horizon scheduler
    (menu.toRawTrace initial horizon scheduler history.trace)
  exact (Nat.le_add_left _ _).trans bound

/-- Every admissible physical unilateral deviation has exactly its represented
behavioral continuation law, against any physical realization of its opponents. -/
theorem run_deviation_eq_finish
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (players : Principal → app.Policy)
    (admissible : ∀ who, menu.Admissible initial horizon scheduler who (players who))
    (realizes : ∀ (history : (menu.protocol initial horizon scheduler).History) who,
      menu.restrictPolicy initial horizon scheduler who (players who)
          ((menu.information initial horizon scheduler).infoOf who history.trace) =
        profile who ((menu.information initial horizon scheduler).infoOf who history.trace))
    (who : Principal) (alternative : app.Policy)
    (covered : menu.Admissible initial horizon scheduler who alternative)
    (history : (menu.protocol initial horizon scheduler).History) :
    ((menu.information initial horizon scheduler).runBehavioralFrom
      (Profile.update (sig := (menu.information initial horizon scheduler).behavioralSignature)
        profile who (menu.restrictPolicy initial horizon scheduler who alternative))
      (2 * horizon + 1) history).map History.state =
      app.finish initial horizon scheduler (Function.update players who alternative)
        history.state := by
  classical
  have updatedAdmissible : ∀ other, menu.Admissible initial horizon scheduler other
      (Function.update players who alternative other) := by
    intro other
    by_cases same : other = who
    · subst other
      simpa only [Function.update_self] using covered
    · simpa only [Function.update_of_ne same] using admissible other
  apply menu.run_realized_eq_finish initial horizon scheduler _ _ updatedAdmissible _ history
  intro later other
  by_cases same : other = who
  · subst other
    simp only [Function.update_self, Profile.update_same]
  · simp only [Profile.update, Function.update_of_ne same]
    exact realizes later other

/-- Sequential rationality controls every menu-admissible physical continuation
policy under the assessment's belief, including at off-path information sets. -/
theorem sequentiallyRational_finish [app.FiniteNature initial scheduler]
    (assessment : (menu.information initial horizon scheduler).BehavioralAssessment)
    (players : Principal → app.Policy)
    (admissible : ∀ who, menu.Admissible initial horizon scheduler who (players who))
    (realizes : ∀ (history : (menu.protocol initial horizon scheduler).History) who,
      menu.restrictPolicy initial horizon scheduler who (players who)
          ((menu.information initial horizon scheduler).infoOf who history.trace) =
        assessment.strategy who
          ((menu.information initial horizon scheduler).infoOf who history.trace))
    (payoff : Principal → app.ProtocolState → ℝ)
    (rational : assessment.IsSequentiallyRationalFor fun who site =>
      assessment.truncatedContinuationContext site
        (fun final => payoff who final.state) (2 * horizon + 1))
    (who : Principal) (site : (menu.information initial horizon scheduler).InformationSite who)
    (alternative : app.Policy)
    (covered : menu.Admissible initial horizon scheduler who alternative) :
    expect ((assessment.belief who site).bind fun history =>
      app.finish initial horizon scheduler
        (Function.update players who alternative) history.1.state) (payoff who) ≤
      expect ((assessment.belief who site).bind fun history =>
        app.finish initial horizon scheduler
          players history.1.state)
        (payoff who) := by
  let context := assessment.truncatedContinuationContext site
    (fun final => payoff who final.state) (2 * horizon + 1)
  have integrable
      (policy : (menu.information initial horizon scheduler).BehavioralPolicy who) :
      context.IntegrableAt policy :=
    payoffIntegrable_of_finite _ _
  have optimal := (Context.isLocallyOptimal_iff_of_integrable
    (integrable (assessment.strategy who)) (fun policy _ => integrable policy)).mp
      (rational who site) (menu.restrictPolicy initial horizon scheduler who alternative)
      (Set.mem_univ _)
  have deviation := menu.run_deviation_eq_finish initial horizon scheduler
    assessment.strategy players admissible realizes who alternative covered
  have prescribed (history : (menu.protocol initial horizon scheduler).History) :=
    menu.run_realized_eq_finish initial horizon scheduler
      assessment.strategy players admissible realizes history
  dsimp only [context] at optimal
  rw [InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
    InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
    Profile.update_eq_self] at optimal
  have project
      (profile : ∀ other, (menu.information initial horizon scheduler).BehavioralPolicy other) :
      expect ((assessment.belief who site).bind fun history =>
        (menu.information initial horizon scheduler).runBehavioralFrom
          profile (2 * horizon + 1) history.1)
        (fun final => payoff who final.state) =
      expect ((assessment.belief who site).bind fun history =>
        ((menu.information initial horizon scheduler).runBehavioralFrom
          profile (2 * horizon + 1) history.1).map History.state)
        (payoff who) := by
    let run := fun history :
        (menu.information initial horizon scheduler).InformationHistory who site.1 =>
      (menu.information initial horizon scheduler).runBehavioralFrom
        profile (2 * horizon + 1) history.1
    have value := expect_map History.state ((assessment.belief who site).bind run) (payoff who)
    exact value.symm.trans (congrArg (fun law => expect law (payoff who))
      (PMF.map_bind (assessment.belief who site) run History.state))
  rw [project, project] at optimal
  simp only [deviation, prescribed] at optimal
  exact optimal

end Interaction.ReactiveApplication.ResponseMenu
