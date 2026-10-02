/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.PayoffProtocol
import Vegas.Examples.MonitoredGuessing.RestrictedEquilibrium
import Vegas.Examples.MonitoredGuessing.RestrictedLaw
import Vegas.Examples.MonitoredGuessing.RestrictedExtension
import Vegas.Examples.MonitoredGuessing.TableSettlement

/-! # Compilation begins with the program's actual declared utilities

The source assessment belongs to `payoffSetup table`, whose return expressions
encode the table. Equality of its operational protocol with the analyzed source
transports both standard sequential equilibrium and the complete observation
law. The observation retains the initialized private bit, publication results,
and the evaluated return vector.

The theorem concerns this two-reveal family and its fixed bounded native
service and passive observation rule. Physical settlement uses the separate
challenge-time report backend and a ledger conformance audit for Bob.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.SourceProgram Interaction GameTheory GameTheory.Protocol
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
    (arena : E = T) (information : HEq M N)
    (sourceAntichain : M.DecisionInformationAntichain)
    (targetAntichain : N.DecisionInformationAntichain)
    (sourceUtility : E.State → Player → ℝ) (targetUtility : T.State → Player → ℝ)
    (utilities : HEq sourceUtility targetUtility)
    {Outcome : Type} (sourceObserve : E.State → Outcome) (targetObserve : T.State → Outcome)
    (observations : HEq sourceObserve targetObserve)
    (source : M.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
      source.truncatedContinuationContext site (fun history => sourceUtility history.state
          who) 3)) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibriumFor targetAntichain (fun who site =>
        target.truncatedContinuationContext site (fun history => targetUtility history.state
            who) 3) ∧
      ((M.runBehavioral source.strategy 3).map History.state).map sourceObserve =
        ((N.runBehavioral target.strategy 3).map History.state).map targetObserve := by
  cases arena
  cases eq_of_heq information
  cases eq_of_heq utilities
  cases eq_of_heq observations
  exact ⟨source, equilibrium, rfl⟩

/-- The transported assessment changes no game behavior or information. The
premise uses the literal program's evaluated returns at every continuation. -/
theorem declared_source_assessment (table : PayoffTable)
    (source : ((payoffSetup table).informationModel (payoffAdmission table)).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor (payoffAntichain table) (fun who site =>
      source.truncatedContinuationContext site
        (fun history => declaredSourceUtility table history.state who) 3)) :
    ∃ target : sourceModel.BehavioralAssessment,
      target.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
        target.truncatedContinuationContext site
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

/-- Every source equilibrium has a native comparison equilibrium for its table.
Physical report inclusion and deposit collection are supplied separately.

The backend and deposits depend only on the declared table. New-only native
continuations may depend on the source assessment; the conclusion is existence
of a native SE, not a fixed playerwise translation at those information sites. -/
theorem declared_comparison_equilibrium_preserved (table : PayoffTable)
    (watcherZero : ∀ result, table result watcher = 0)
    (source : ((payoffSetup table).informationModel (payoffAdmission table)).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor (payoffAntichain table) (fun who site =>
      source.truncatedContinuationContext site
        (fun history => declaredSourceUtility table history.state who) 3)) :
    ∃ target : nativeModel.BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        (nativeMenu.decisionInformationAntichain nativeInitialLaw nativeHorizon nativeScheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun history => Enforcement.comparisonStateUtility table history.state who)
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
    have projected := congrArg (PMF.map Prod.fst) targetJointLaw
    have flattened :
        (nativeModel.runBehavioral target.strategy (2 * nativeHorizon + 1)).map
          (fun history => Restricted.nativePayoffObservation table history.state) =
        (Restricted.restrictedModel.runBehavioral restricted.strategy
          (2 * nativeHorizon + 1)).map
            (fun history => Restricted.nativePayoffObservation table history.state) :=
      (PMF.map_comp _ _ Prod.fst).symm.trans
        (projected.trans (PMF.map_comp _ _ Prod.fst))
    exact (PMF.map_comp (fun history : nativeArena.History => history.state)
      (nativeModel.runBehavioral target.strategy (2 * nativeHorizon + 1))
        (Restricted.nativePayoffObservation table)).trans
      (flattened.trans
        (PMF.map_comp (fun history : Restricted.restrictedArena.History => history.state)
          (Restricted.restrictedModel.runBehavioral restricted.strategy (2 * nativeHorizon + 1))
            (Restricted.nativePayoffObservation table)).symm)
  have compiledLaw := Restricted.compile_joint_law table canonical.strategy
  rw [← restrictedStrategy] at compiledLaw
  exact targetLaw.trans (compiledLaw.symm.trans sourceLaw.symm)

private theorem source_observation_declared (table : PayoffTable)
    (profile : Profile sourceModel.behavioralSignature)
    (observation : Bool × Results × (Player → ℝ))
    (supported : observation ∈ (((sourceModel.runBehavioral profile 3).map History.state).map
      (Restricted.sourcePayoffObservation table)).support) :
    observation.2.2 = fun who => (table observation.2.1 who : ℝ) := by
  obtain ⟨state, reached, rfl⟩ := PMF.support_map .. ▸ supported
  rw [Restricted.source_initialized_states_all] at reached
  obtain ⟨bit, _, guessed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨guess, _, disclosed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ guessed)
  obtain ⟨disclose, _, rfl⟩ := PMF.support_map .. ▸ disclosed
  rw [Restricted.source_done_payoff_observation]
  rfl

private theorem collection_joint_eq (table : PayoffTable) (window : ChallengeWindow) (rate : ℝ)
    (positive : 0 < rate) (bounded : rate ≤ 1)
    (target : Profile nativeModel.behavioralSignature)
    (source : Profile sourceModel.behavioralSignature)
    (comparisonLaw : ((nativeModel.runBehavioral target (2 * nativeHorizon + 1)).map
        History.state).map (Restricted.nativePayoffObservation table) =
      ((sourceModel.runBehavioral source 3).map History.state).map
        (Restricted.sourcePayoffObservation table)) :
    (nativeModel.runBehavioral target (2 * nativeHorizon + 1)).bind
        (fun history => Enforcement.collectedObservation table window rate positive.le bounded
          history.state) =
      ((nativeModel.runBehavioral target (2 * nativeHorizon + 1)).map History.state).map
        (Restricted.nativePayoffObservation table) := by
  refine Eq.trans ?_ (PMF.map_comp
    (fun history : nativeArena.History => history.state)
    (nativeModel.runBehavioral target (2 * nativeHorizon + 1))
    (Restricted.nativePayoffObservation table)).symm
  apply bind_congr_on_support _
  intro history supported
  change Enforcement.collectedObservation table window rate positive.le bounded history.state =
    PMF.pure (Restricted.nativePayoffObservation table history.state)
  have observed : Restricted.nativePayoffObservation table history.state ∈
      (((nativeModel.runBehavioral target (2 * nativeHorizon + 1)).map History.state).map
        (Restricted.nativePayoffObservation table)).support :=
    PMF.support_map .. ▸ ⟨history.state, PMF.support_map .. ▸ ⟨history, supported, rfl⟩, rfl⟩
  rw [comparisonLaw] at observed
  have declared := source_observation_declared table source _ observed
  obtain ⟨execution, state, complete⟩ := native_terminal_history_complete history
    (native_initialized_terminal target history supported)
  have trace : nativeArena.Trace (nativeApp.finished execution) := state ▸ history.trace
  have raw := nativeMenu.toRawTrace nativeInitialLaw nativeHorizon nativeScheduler trace
  have unpenalized (who : Player) : Enforcement.comparisonExecutionUtility table execution who =
      (table (nativeResults execution.application.config) who : ℝ) := by
    rw [state] at declared
    exact congrFun declared who
  rw [state]
  change (Enforcement.collectionLaw table window rate positive.le bounded execution).map _ = _
  rw [Enforcement.collectionLaw_no_loss table window rate positive.le bounded execution
    (nativeReceipts_history _ raw)
    (nativeApp.uniqueIds_history nativeScheduler nativeInitialLaw nativeHorizon _ raw)
    (nativeApp.publishedOnce_history nativeScheduler nativeInitialLaw nativeHorizon raw)
    complete unpenalized, PMF.pure_map]
  simp only [ReactiveApplication.finished, Restricted.nativePayoffObservation,
    Option.elim_some]
  congr 2
  refine Prod.ext rfl ?_
  funext who
  exact (unpenalized who).symm

/-- Every equilibrium of the literal two-reveal program survives the native
game with physical deposits and actual report delivery. The fixed conditional
delivery rate scales escrow; the realized clean-play payoff law remains exact. -/
theorem declared_sequential_equilibrium_preserved (table : PayoffTable)
    (window : ChallengeWindow) (rate : ℝ) (positive : 0 < rate) (bounded : rate ≤ 1)
    (watcherZero : ∀ result, table result watcher = 0)
    (source : ((payoffSetup table).informationModel (payoffAdmission table)).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor (payoffAntichain table) (fun who site =>
      source.truncatedContinuationContext site
        (fun history => declaredSourceUtility table history.state who) 3)) :
    ∃ target : nativeModel.BehavioralAssessment,
      target.IsSequentialEquilibriumFor nativeAntichain (fun who site =>
        target.truncatedContinuationContext site
          (fun history => Enforcement.settledStateUtility table window rate positive.le bounded
            history.state who) (2 * nativeHorizon + 1)) ∧
      (nativeModel.runBehavioral target.strategy (2 * nativeHorizon + 1)).bind
        (fun history => Enforcement.collectedObservation table window rate positive.le bounded
          history.state) =
      ((((payoffSetup table).informationModel (payoffAdmission table)).runBehavioral
        source.strategy 3).map History.state).map (declaredSourceObservation table) := by
  obtain ⟨canonical, _, sourceLaw⟩ := declared_source_assessment table source equilibrium
  obtain ⟨target, targetSE, targetLaw⟩ :=
    declared_comparison_equilibrium_preserved table watcherZero source equilibrium
  refine ⟨target, (Enforcement.settled_equilibrium_iff table window rate positive bounded
    target).mp targetSE, ?_⟩
  have comparisonLaw := targetLaw.trans sourceLaw
  exact (collection_joint_eq table window rate positive bounded target.strategy
    canonical.strategy comparisonLaw).trans targetLaw

end Vegas.Examples.MonitoredGuessing
