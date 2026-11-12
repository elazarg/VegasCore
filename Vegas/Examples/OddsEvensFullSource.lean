module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensFairLaw
public import Vegas.Game.IntendedPreservation

@[expose] public section

/-! # The fair equilibrium in the source game allowing failed moves -/

noncomputable section

namespace Vegas.Examples.OddsEvens

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

def publicationOutcome (defaults : DefaultHistory Player)
    (re ro : PublicationResult Bool) : PublicOutcome program :=
  ⟨Env.cons ro (Env.cons re (Env.empty _)), defaults⟩

theorem publicationOutcome_eta (outcome : PublicOutcome program) :
    outcome = publicationOutcome outcome.defaults
      (outcome.values.get (.there .here)) (outcome.values.get .here) := by
  suffices values : outcome.values =
      Env.cons (outcome.values.get .here)
        (Env.cons (outcome.values.get (.there .here)) (Env.empty _)) by
    cases outcome
    exact congrArg (fun cells => PublicOutcome.mk cells _) values
  funext name kind cell
  cases cell with
  | here => rfl
  | there cell =>
      cases cell with
      | here => rfl
      | there absent => cases absent

theorem failedReveals_publicationOutcome (defaults : DefaultHistory Player)
    (re ro : PublicationResult Bool) (who : Player) :
    failedReveals program who (publicationOutcome defaults re ro) =
      if (if who then ro else re).isFailure then 1 else 0 := by
  cases who <;> cases re <;> cases ro <;> rfl

theorem cash_zero_of_failedReveals (result : Unit × PublicOutcome program) (who : Player)
    (failed : 1 ≤ failedReveals program who result.2) : sourceUtility result who = 0 := by
  rcases result with ⟨⟨⟩, outcome⟩
  rw [publicationOutcome_eta outcome] at failed ⊢
  generalize outcome.values.get (.there .here) = re at failed ⊢
  generalize outcome.values.get .here = ro at failed ⊢
  rw [failedReveals_publicationOutcome] at failed
  cases who <;> cases re <;> cases ro
  all_goals
    first
    | solve | norm_num [PublicationResult.isFailure] at failed
    | norm_num [sourceUtility, cash, publicationOutcome, Env.get, Env.cons, even, odd]


abbrev fullAdmission := CommitmentInterface.forfeiture program
abbrev fullProtocol := setup.executionProtocol fullAdmission
abbrev fullModel := setup.informationModel fullAdmission
theorem fullBounded : fullProtocol.BoundedHorizon (instructionCount program + 1) :=
  setup.protocol_bounded fullAdmission

def fullPayoff (who : Player) (final : fullProtocol.History) : ℝ :=
  (setup.protocolReadout final.state).elim 0
    (fun terminal => sourceUtility (setup.parameterOutcome (fun _ => ()) terminal) who)

theorem terminalUtility_nonnegative (who : Player) (history : setup.intendedProtocol.History) :
    0 ≤ terminalUtility who history := by
  unfold terminalUtility
  cases setup.protocolReadout history.state with
  | none => exact le_rfl
  | some value => exact (sourceUtility_bounds _ who).1

open Classical in
theorem full_extra_value_zero (profile : ∀ who, fullModel.BehavioralPolicy who)
    (who : Player) (site : setup.intendedModel.InformationSite who)
    (action : fullModel.Choice who ((setup.intendedRestriction fullAdmission).site who site).1)
    (extra : action ∉ Set.range ((setup.intendedRestriction fullAdmission).choice who site.1))
    (history : setup.intendedModel.InformationHistory who site.1) :
    expect (fullModel.runBehavioralTerminalFrom fullBounded.wellFoundedHistories
      (Profile.update (sig := fullModel.behavioralSignature) profile who
        ((profile who).commit ((setup.intendedRestriction fullAdmission).site who site).1 action))
      ((setup.intendedRestriction fullAdmission).history history.1)) (fullPayoff who) = 0 := by
  classical
  have deviation := setup.deviation_failedReveals_pos fullAdmission wellFormed
    fullBounded.wellFoundedHistories profile who site action extra history
  calc _ = expect _ (fun _ => 0) := by
         apply expect_congr_on_support
         intro final supported
         obtain ⟨terminal, read, failed⟩ := deviation final supported
         unfold fullPayoff
         rw [read]
         exact cash_zero_of_failedReveals _ _ failed
       _ = 0 := expect_zero _

/-- Both a missed commitment and a withheld reveal are legal in this source
game. The unchanged program settlement deters every added move, so the fair
intended assessment extends without an additional penalty mechanism. -/
theorem fair_full_source_equilibrium_exists :
    ∃ target : fullModel.BehavioralAssessment,
      target.IsSequentialEquilibrium (setup.decision_antichain fullAdmission)
        fullBounded.wellFoundedHistories fullPayoff ∧
      (setup.intendedRestriction fullAdmission).ExtendsProfile uniformProfile target.strategy ∧
      (fullModel.runBehavioralTerminalFrom fullBounded.wellFoundedHistories target.strategy
        fullProtocol.initHistory).map
        (fun final => (setup.protocolReadout final.state, fun who => fullPayoff who final)) =
          uniformJointLaw := by
  classical
  let restriction := setup.intendedRestriction fullAdmission
  let sourceCertificate := setup.intended_bounded.wellFoundedHistories
  let targetCertificate := fullBounded.wellFoundedHistories
  have : Finite fullProtocol.History := setup.finite_history finiteBindingTypes fullAdmission
  have matching : ∀ who (history : setup.intendedProtocol.History),
      fullPayoff who (restriction.history history) = terminalUtility who history := by
    intro who history
    rfl
  let comparator : ∀ who (site : setup.intendedModel.InformationSite who),
      fullModel.Choice who (restriction.site who site).1 →
        PMF (setup.intendedModel.Choice who site.1) :=
    fun _ _ _ => PMF.pure (Classical.arbitrary _)
  obtain ⟨target, sequential, extends_, _, _, jointLaw⟩ :=
    restriction.sequentialEquilibrium_extends_of_comparator_unclocked
      setup.intended_decision_antichain sourceCertificate targetCertificate
      (setup.uniformReference finiteBindingTypes fullAdmission)
      (setup.uniformReference_fullyMixed finiteBindingTypes fullAdmission)
      (setup.protocol_decisionRecall fullAdmission) terminalUtility fullPayoff matching comparator
      (by
        intro sourceProfile targetProfile _ who site action extra history
        rw [full_extra_value_zero targetProfile who site action extra history]
        exact expect_nonneg _ _ (fun reached _ => terminalUtility_nonnegative who reached))
      uniformAssessment uniformAssessment_equilibrium
  refine ⟨target, sequential, extends_, ?_⟩
  have readouts := congrArg (PMF.map fun pair => (setup.protocolReadout pair.1.state, pair.2))
    jointLaw
  simp only [PMF.map_comp] at readouts
  change (setup.intendedModel.runBehavioralTerminalFrom sourceCertificate
    uniformProfile setup.intendedProtocol.initHistory).map
      (fun final => (setup.protocolReadout final.state, fun who => terminalUtility who final)) =
    (fullModel.runBehavioralTerminalFrom fullBounded.wellFoundedHistories target.strategy
      fullProtocol.initHistory).map
      (fun final => (setup.protocolReadout final.state,
        fun who => fullPayoff who final)) at readouts
  apply readouts.symm.trans
  rw [setup.intendedModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    sourceCertificate setup.intended_bounded]
  have same : (fun final : setup.intendedProtocol.History =>
      (setup.protocolReadout final.state, fun who => terminalUtility who final)) =
      intendedReadoutExclusion setup (fun _ => ()) sourceUtility (fun _ => 0) := by
    funext final
    apply Prod.ext
    · rfl
    · funext who
      change terminalUtility who final =
        exclusionReadoutUtility setup (fun _ => ()) sourceUtility (fun _ => 0)
          (setup.protocolReadout final.state) who
      exact (setup.intended_exclusionReadoutUtility wellFormed (fun _ => ()) sourceUtility
        (fun _ => 0) final who).symm
  rw [same]
  exact uniform_source_joint_law

end Vegas.Examples.OddsEvens
