/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingPayoffProtocol
import VegasTests.MonitoredGuessingRestrictedEquilibrium
import VegasTests.MonitoredGuessingRestrictedLaw
import VegasTests.MonitoredGuessingRestrictedExtension

/-! # Compilation begins with the program's actual declared utilities

The source assessment belongs to `payoffSetup table`, whose return expressions
encode the table. Equality of its operational protocol with the analyzed source
transports both standard sequential equilibrium and the complete observation
law. The observation retains the initialized private bit, publication results,
and the evaluated return vector.

The theorem concerns this two-reveal family and its fixed bounded native
service, passive observation rule, and receipt/ledger collection interpretation.
-/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def declaredSourceObservation (table : PayoffTable)
    (state : (payoffSetup table).ProtocolState) : Bool × Results × (Player → ℝ) :=
  match (payoffSetup table).protocolReadout state with
  | none => (false, ⟨.failure, .failure⟩, fun _ => 0)
  | some terminal => ((terminal.get (.there (.there .here))).getD false,
      sourceResults terminal, declaredSourceUtility table state)

theorem declaredSourceObservation_eq (table : PayoffTable)
    (state : (payoffSetup table).ProtocolState) :
    declaredSourceObservation table state = Restricted.sourcePayoffObservation table state := by
  cases state with
  | none => rfl
  | some state => cases state with
    | inl config => rfl
    | inr rest => cases rest with
      | inl config => rfl
      | inr config =>
          change (_, _, declaredSourceUtility table (some (.inr (.inr config)))) = _
          rw [declaredSourceUtility_eq_result]
          rfl

private theorem equal_model_assessment
    {E T : ExecutionProtocol.{0, 0, 0} Player}
    {M : InformationModel.{0, 0, 0, 0, 0, 0} E}
    {N : InformationModel.{0, 0, 0, 0, 0, 0} T}
    [sourceFinite : ∀ who (site : M.InformationSite who),
      Fintype (M.InformationHistory who site.1)]
    [targetFinite : ∀ who (site : N.InformationSite who),
      Fintype (N.InformationHistory who site.1)]
    (arena : E = T) (information : HEq M N)
    (sourceAntichain : M.DecisionInformationAntichain)
    (targetAntichain : N.DecisionInformationAntichain)
    (sourceUtility : E.State → Player → ℝ) (targetUtility : T.State → Player → ℝ)
    (utilities : HEq sourceUtility targetUtility)
    {Outcome : Type} (sourceObserve : E.State → Outcome) (targetObserve : T.State → Outcome)
    (observations : HEq sourceObserve targetObserve)
    (source : M.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
      source.continuationContext site (fun history => sourceUtility history.state who) 3)) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibriumFor targetAntichain (fun who site =>
        target.continuationContext site (fun history => targetUtility history.state who) 3) ∧
      ((M.runBehavioral source.strategy 3).map History.state).map sourceObserve =
        ((N.runBehavioral target.strategy 3).map History.state).map targetObserve := by
  cases arena
  cases eq_of_heq information
  cases eq_of_heq utilities
  cases eq_of_heq observations
  have finiteEq : sourceFinite = targetFinite := Subsingleton.elim _ _
  cases finiteEq
  exact ⟨source, equilibrium, rfl⟩

/-- The transported assessment changes no game behavior or information. The
premise uses the literal program's evaluated returns at every continuation. -/
theorem declared_source_assessment (table : PayoffTable)
    (source : ((payoffSetup table).informationModel (payoffAdmission table)).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor (payoffAntichain table) (fun who site =>
      source.continuationContext site
        (fun history => declaredSourceUtility table history.state who) 3)) :
    ∃ target : sourceModel.BehavioralAssessment,
      target.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
        target.continuationContext site
          (Restricted.sourceResultPayoff (Restricted.tableReward table) who) 3) ∧
      ((((payoffSetup table).informationModel (payoffAdmission table)).runBehavioral
        source.strategy 3).map History.state).map (declaredSourceObservation table) =
      ((sourceModel.runBehavioral target.strategy 3).map History.state).map
        (Restricted.sourcePayoffObservation table) := by
  exact equal_model_assessment (payoffSetup_protocol table) (payoffSetup_information table)
    (payoffAntichain table) sourceAntichain (declaredSourceUtility table)
    (Restricted.sourceResultUtility (Restricted.tableReward table))
    (heq_of_eq (funext (declaredSourceUtility_eq_result table)))
    (declaredSourceObservation table) (Restricted.sourcePayoffObservation table)
    (heq_of_eq (funext (declaredSourceObservation_eq table))) source equilibrium

/-- Every sequential equilibrium of this literal two-reveal source program is
implemented in the fixed raw native game for its table. The observation law includes
the private initial bit, public results, and actual net utility vector.

The backend and deposits depend only on the declared table. New-only native
continuations may depend on the source assessment; the conclusion is existence
of a native SE, not a fixed playerwise translation at those information sites. -/
theorem declared_sequential_equilibrium_preserved (table : PayoffTable)
    (watcherZero : ∀ result, table result watcher = 0)
    (source : ((payoffSetup table).informationModel (payoffAdmission table)).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor (payoffAntichain table) (fun who site =>
      source.continuationContext site
        (fun history => declaredSourceUtility table history.state who) 3)) :
    ∃ target : nativeModel.BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        (nativeMenu.decisionInformationAntichain nativeInitialLaw nativeHorizon nativeScheduler)
        (fun who site => target.continuationContext site
          (fun history => Enforcement.stateUtility table history.state who)
          (2 * nativeHorizon + 1)) ∧
      ((nativeModel.runBehavioral target.strategy (2 * nativeHorizon + 1)).map
        History.state).map (Restricted.nativePayoffObservation table) =
      ((((payoffSetup table).informationModel (payoffAdmission table)).runBehavioral
        source.strategy 3).map History.state).map (declaredSourceObservation table) := by
  obtain ⟨canonical, canonicalSE, sourceLaw⟩ := declared_source_assessment table source equilibrium
  obtain ⟨restricted, restrictedStrategy, restrictedSE⟩ :=
    Restricted.source_equilibrium_compiles table watcherZero canonical canonicalSE
  obtain ⟨target, targetSE, targetJointLaw⟩ := Restricted.restricted_raw_equilibrium_extends
    table watcherZero (Restricted.nativePayoffObservation table)
    (Restricted.nativePayoffObservation_normalization table) restricted restrictedSE
  refine ⟨target, targetSE, ?_⟩
  have targetLaw : ((nativeModel.runBehavioral target.strategy
      (2 * nativeHorizon + 1)).map History.state).map
        (Restricted.nativePayoffObservation table) =
      ((Restricted.restrictedModel.runBehavioral restricted.strategy
        (2 * nativeHorizon + 1)).map History.state).map
          (Restricted.nativePayoffObservation table) := by
    have projected := congrArg (FinDist.map Prod.fst) targetJointLaw
    simpa only [FinDist.map_comp, Function.comp_def] using projected
  have compiledLaw := Restricted.compile_joint_law table canonical.strategy
  rw [← restrictedStrategy] at compiledLaw
  exact targetLaw.trans (compiledLaw.symm.trans sourceLaw.symm)

end VegasTests.MonitoredGuessing
