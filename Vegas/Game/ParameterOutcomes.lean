/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.InitialState
import Vegas.Game.PendingCompositions

/-! # Strategic preservation for initial parameters and public results

An analysis may use private initial types without assigning utility to internal
commitment choices. The value-binding abstraction preserves the joint law of
any initial parameter and the public result. Composing it with the native
full-store law gives one deviation mixture across the entire private prior.
Nash of this type-contingent policy game is the Bayesian incentive notion;
the theorem also applies to a designated truthful plan.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
variable {Parameter : Type}

/-- Replacing an unopenable binding preserves its correlation with initial data. -/
theorem bindValues_parameterRun_eq {who : Player}
    (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (profile : BehavioralProfile setup.program) (policy : PurePolicy who setup.program) :
    setup.parameterRun parameter (Function.update profile who
        (PurePolicy.toBehavioral setup.program (PurePolicy.bindValues setup.program policy))) =
      setup.parameterRun parameter (Function.update profile who
        (PurePolicy.toBehavioral setup.program policy)) := by
  apply FinDist.bind_congr
  intro initial _
  have h := congrArg (FinDist.map fun result => (parameter initial, result))
    (bindValues_run_publicOutcome_eq setup.program profile policy initial)
  simpa only [FinDist.map_comp, Function.comp_def] using h

namespace Setup

/-- Value-only commitment strategies, with utilities allowed to read initial
parameters jointly with public results. Initial parameters are never chosen by
the policies or made public by this game interpretation. -/
@[reducible] def valueBindingParameterGame (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter) : GameForm Player where
  sig :=
    { Strategy := fun who => ValueBindingPolicy who setup.program
      Outcome := Parameter × PublicOutcome setup.program }
  play profile := setup.parameterRun parameter (valueBindingProfile profile)

/-- The abstraction erases commit-time failure even for type-dependent utility. -/
def valueBindingParameterSimulationOn {Observation : Type}
    (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (observe : Parameter × PublicOutcome setup.program → Observation) :
    GameForm.MixtureSimulationOn (setup.valueBindingParameterGame parameter)
      (setup.parameterGame parameter) observe observe (fun _ _ => True) where
  compileStrategy _ strategy := strategy.val
  honest_law _ := rfl
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    obtain ⟨mixture, hmixture⟩ :=
      exists_pureMixture_run setup (valueBindingProfile profile) replacement
    have joint := congrArg (FinDist.map (setup.parameterOutcome parameter)) hmixture
    simp only [FinDist.map_bind, setup.run_map_parameterOutcome] at joint
    refine ⟨mixture.map fun choice =>
      ⟨PurePolicy.toBehavioral setup.program (PurePolicy.bindValues setup.program choice),
        valueBinding_bindValues setup.program choice⟩, ?_⟩
    change (setup.parameterRun parameter
      (Function.update (valueBindingProfile profile) who replacement)).map observe = _
    rw [joint, FinDist.map_bind, FinDist.bind_map]
    refine FinDist.bind_congr fun choice _ => ?_
    change (setup.parameterRun parameter _).map observe =
      (setup.parameterRun parameter
        (valueBindingProfile (Profile.update profile who _))).map observe
    have updated := valueBindingProfile_update (setup := setup) profile who
      ⟨PurePolicy.toBehavioral setup.program (PurePolicy.bindValues setup.program choice),
        valueBinding_bindValues setup.program choice⟩
    simp only [Profile.update] at updated ⊢
    rw [updated]
    exact congrArg _
      (bindValues_parameterRun_eq setup parameter (valueBindingProfile profile) choice).symm

/-- Semantic analysis readout: an initial parameter and the public source result.
The private parameter is not an observation provided to the other players. -/
def eventPendingParameterOutcome (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (execution : runtime.application.PolicyExecution) :
    Option (Parameter × PublicOutcome setup.program) :=
  (setup.eventPendingOutcome mode runtime execution).map (setup.parameterOutcome parameter)

/-- The full-core native certificate retains initial parameters jointly with
public results, with the same mixture chosen before the setup draw. -/
def parameterPendingSimulation (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    GameForm.MixtureSimulationOn (setup.parameterGame parameter)
      (setup.eventPendingGame mode runtime roster reactionRounds wire order) some
      (setup.eventPendingParameterOutcome parameter mode runtime) (fun _ _ => True) where
  compileStrategy := setup.compileEventPendingStrategy mode runtime
  compiled_considered _ _ := trivial
  honest_law profile := by
    unfold eventPendingParameterOutcome
    have h := congrArg (FinDist.map (Option.map (setup.parameterOutcome parameter)))
      (setup.eventPendingGame_honest_law mode runtime feasible roster reactionRounds wire order
        profile)
    change _ = (setup.parameterRun parameter profile).map some
    rw [← setup.run_map_parameterOutcome parameter profile]
    simpa only [Profile.update, eventPendingParameterOutcome, FinDist.map_comp, Function.comp_def,
      Option.map_some] using h
  deviation_mixture profile who replacement _ := by
    unfold eventPendingParameterOutcome
    obtain ⟨mixture, hmixture⟩ := setup.eventPendingGame_deviation_law mode runtime feasible
      roster reactionRounds wire order profile who replacement
    refine ⟨mixture, ?_⟩
    have h := congrArg (FinDist.map (Option.map (setup.parameterOutcome parameter))) hmixture
    simp only [FinDist.map_bind] at h
    simp only [parameterGame]
    simp_rw [← setup.run_map_parameterOutcome parameter]
    simpa only [Profile.update, eventPendingParameterOutcome, FinDist.map_comp, Function.comp_def,
      Option.map_some] using h

/-- Complete value-only source-to-native certificate for type-dependent results. -/
def valueBindingParameterPendingSimulation (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    GameForm.MixtureSimulationOn (setup.valueBindingParameterGame parameter)
      (setup.eventPendingGame mode runtime roster reactionRounds wire order) some
      (setup.eventPendingParameterOutcome parameter mode runtime) (fun _ _ => True) :=
  (setup.valueBindingParameterSimulationOn parameter some).trans
    (setup.parameterPendingSimulation parameter mode runtime feasible roster reactionRounds
      wire order) (fun _ _ => trivial)

/-- Same-error Bayesian Nash correspondence: utilities can depend on private
initial types and public results, while commitments choose ordinary values.
The approximation bound is ex ante under the specified prior. -/
theorem valueBindingParameterPendingGame_approximate_nash_iff
    (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (missing : Player → ℝ) (ε : ℝ)
    (profile : Profile (setup.valueBindingParameterGame parameter).sig) :
    IsεNash (setup.eventPendingGame mode runtime roster reactionRounds wire order)
        (fun outcome who =>
          (setup.eventPendingParameterOutcome parameter mode runtime outcome).elim
            (missing who) (fun result => utility result who))
        ε (fun who => setup.compileValueBindingPendingProfile mode runtime who (profile who)) ↔
      IsεNash (setup.valueBindingParameterGame parameter) utility ε profile := by
  let optionUtility : Option (Parameter × PublicOutcome setup.program) → Player → ℝ :=
    fun outcome who => outcome.elim (missing who) (fun result => utility result who)
  exact GameForm.MixtureSimulationOn.isεNash_compileProfile_iff
    (setup.valueBindingParameterPendingSimulation parameter mode runtime feasible roster
      reactionRounds wire order) optionUtility ε profile (fun _ _ => trivial)

/-- In particular, a designated truthful plan is Bayesian Nash in the source
exactly when its compilation is Nash against all unilateral native deviations. -/
theorem valueBindingParameterPendingGame_nash_iff
    (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (missing : Player → ℝ)
    (profile : Profile (setup.valueBindingParameterGame parameter).sig) :
    IsNash (setup.eventPendingGame mode runtime roster reactionRounds wire order)
        (euPreference fun outcome who =>
          (setup.eventPendingParameterOutcome parameter mode runtime outcome).elim
            (missing who) (fun result => utility result who))
        (fun who => setup.compileValueBindingPendingProfile mode runtime who (profile who)) ↔
      IsNash (setup.valueBindingParameterGame parameter) (euPreference utility) profile := by
  rw [isNash_iff_isεNash_zero, isNash_iff_isεNash_zero]
  exact setup.valueBindingParameterPendingGame_approximate_nash_iff parameter mode runtime
    feasible roster reactionRounds wire order utility missing 0 profile

end Setup
end Vegas.SourceProgram
