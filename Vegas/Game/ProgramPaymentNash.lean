/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.EventCompilation
import Vegas.Game.ProgramPayoffs
import Vegas.Game.SourceProtocolNash

/-! # Nash correspondence for executable program payments

The compiled utility evaluates the actual compiled payment instructions. Initial
parameters can enter valuation through a derived outcome reader: the source
policies, their observations, and execution remain those of the original setup.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]

/-- Same-error Nash preservation and reflection for quasi-linear utility whose
receipts are the actual compiled program payments. -/
theorem eventGame_payment_approximate_nash_iff
    (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (scheduler : setup.eventGraph.PublicScheduler)
    (valuation : PublicOutcome setup.program → Player → ℝ)
    (ε : ℝ) (profile : BehavioralProfile setup.program) :
    IsεNash (setup.eventGame scheduler)
        (fun outcome who => valuation (setup.eventPublicOutcome outcome) who +
          (transferAmount (terminalPayouts setup.program outcome) who : ℝ))
        ε (compileEventProfile setup.program profile) ↔
      IsεNash setup.gameForm (setup.program.paymentUtility valuation) ε profile := by
  have utility_eq :
      (fun (outcome : (setup.eventGame scheduler).sig.Outcome) who =>
        valuation (setup.eventPublicOutcome outcome) who +
        (transferAmount (terminalPayouts setup.program outcome) who : ℝ)) =
      (fun (outcome : (setup.eventGame scheduler).sig.Outcome) who =>
        setup.program.paymentUtility valuation (setup.eventPublicOutcome outcome) who) := by
    funext outcome who
    simp only [paymentUtility_eq, publicTransfers, eventPublicOutcome,
      publicPayoffs_publicOutcome, terminalPayouts_eq_source]
  rw [utility_eq]
  exact setup.eventGame_approximate_nash_iff finite scheduler
    (setup.program.paymentUtility valuation) ε profile

/-- A derived analysis view of the original execution. The strategies are
unchanged; the outcome retains an initial parameter jointly with the public result. -/
def parameterGameForm {Parameter : Type} (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter) : GameForm Player where
  sig := (SourceProgram.gameSignature setup.program).mapOutcome
    (Parameter × PublicOutcome setup.program)
  play := setup.parameterRun parameter

/-- Retaining an immutable initial parameter is an observation of the original
execution, with exactly the same source strategy space. -/
theorem parameterGameForm_eq_observedGameForm {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter) :
    setup.parameterGameForm parameter =
      setup.observedGameForm (setup.parameterOutcome parameter) := by
  unfold parameterGameForm observedGameForm
  congr 1
  funext profile
  exact (setup.run_map_parameterOutcome parameter profile).symm

/-- The same-error protocol Nash equivalence retains correlated initial
parameters without changing the observations available to any strategy. -/
theorem parameterProtocol_isεNash_iff {Parameter : Type} [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    (allAdmitted : ∀ who (policy : BehavioralPolicy who setup.program),
      policy.Admitted setup.program admission)
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (ε : ℝ)
    (profile : Profile (setup.informationModel admission).behavioralSignature) :
    IsεNash ((setup.informationModel admission).toBehavioralGameForm
        (instructionCount setup.program + 1))
      (fun final who => (setup.protocolReadout final.state).elim 0
        (fun terminal => utility (setup.parameterOutcome parameter terminal) who)) ε profile ↔
    IsεNash (setup.parameterGameForm parameter) utility ε
      (setup.decodeBehavioralProfile admission profile) := by
  have correspondence := setup.protocol_isεNash_iff admission
    (setup.parameterOutcome parameter) allAdmitted utility ε profile
  simp only [IsεNash, isNash_iff, parameterGameForm, observedGameForm] at correspondence ⊢
  simpa only [setup.run_map_parameterOutcome]
    using correspondence

/-- Recover an immutable initial parameter and the public result from a completed
compiled execution, without publishing either to any policy. -/
def eventParameterOutcome {Parameter : Type} (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (outcome : setup.eventGraph.gameSignature.Outcome) :
    Parameter × PublicOutcome setup.program :=
  setup.parameterOutcome parameter (terminalState setup.program outcome)

/-- The parameterized analysis reader factors through the terminal store. -/
def eventParameterDecode {Parameter : Type} (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (store : Vegas.EventGraph.Store setup.eventGraph.layout) :
    Option (Parameter × PublicOutcome setup.program) :=
  (decodeState? (terminalRefs setup.program) store).map (setup.parameterOutcome parameter)

theorem eventParameterDecode_terminalStore {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (outcome : setup.eventGraph.gameSignature.Outcome) :
    setup.eventParameterDecode parameter (setup.eventGraph.terminalStore outcome) =
      some (setup.eventParameterOutcome parameter outcome) := by
  have hdecode : decodeState? (terminalRefs setup.program)
      (setup.eventGraph.terminalStore outcome) =
        some (terminalState setup.program outcome) := (Option.some_get _).symm
  rw [eventParameterDecode, hdecode]
  rfl

/-- The canonical compiler preserves the joint parameter/result law, including
under every unilateral graph deviation. Its backtranslated policy is fixed
before the initial state is drawn. -/
def canonicalParameterEventSimulation {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter) :
    GameForm.MixtureSimulationOn (setup.parameterGameForm parameter)
      setup.canonicalEventGame id (setup.eventParameterOutcome parameter)
      (fun _ _ => True) where
  compileStrategy := compileEventPolicy setup.program
  honest_law profile := by
    have base := congrArg (PMF.map (setup.parameterOutcome parameter))
      (canonical_setup_law setup profile)
    rw [PMF.map_comp, setup.run_map_parameterOutcome] at base
    exact base.trans (PMF.map_id _).symm
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    refine ⟨PMF.pure (backtranslateEventPolicy setup.program who replacement), ?_⟩
    have base := congrArg (PMF.map (setup.parameterOutcome parameter))
      (canonical_setup_deviation_law setup profile who replacement)
    rw [PMF.map_comp, setup.run_map_parameterOutcome] at base
    rw [PMF.pure_bind]
    exact base.trans (PMF.map_id _).symm

/-- Public scheduling preserves the same joint law through a single mixture
of source deviations drawn before private setup. No policy gains an observation. -/
def parameterEventSimulation {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (scheduler : setup.eventGraph.PublicScheduler) :
    GameForm.MixtureSimulationOn (setup.parameterGameForm parameter)
      (setup.eventGame scheduler) id (setup.eventParameterOutcome parameter)
      (fun _ _ => True) :=
  (setup.canonicalParameterEventSimulation parameter).trans
    (setup.eventGraph.eventSchedulingSimulationOn
      (toEventGraph_barrierOrdered setup.program)
      (toEventGraph_finiteActions setup.program finite)
      (setup.initialLaw.map fun initial => setup.eventInputs initial)
      (by rw [PMF.support_map]; exact setup.initialLaw_support_finite.image _) scheduler
      (setup.eventParameterOutcome parameter) (setup.eventParameterDecode parameter)
      (setup.eventParameterDecode_terminalStore parameter))
    (fun _ _ => trivial)

/-- Arbitrary utility of the correlated initial parameter and public result has
the same Nash error before and after compilation. The parameterized source form
is solely an analysis readout of the existing source execution. -/
theorem parameterEventGame_approximate_nash_iff {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (scheduler : setup.eventGraph.PublicScheduler)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (ε : ℝ) (profile : BehavioralProfile setup.program) :
    IsεNash (setup.eventGame scheduler)
        (fun outcome who => utility (setup.eventParameterOutcome parameter outcome) who)
        ε (compileEventProfile setup.program profile) ↔
      IsεNash (setup.parameterGameForm parameter) utility ε profile :=
  ((setup.parameterEventSimulation parameter finite scheduler).isεNash_compileProfile_iff
    utility ε profile (fun _ _ => trivial)).trans (and_iff_left fun _ _ =>
      hasExpectation_of_payoffIntegrable (payoffIntegrable_of_finite_support _ _
        (setup.eventGame_play_support_finite finite scheduler _)))

/-- Parameter-dependent valuation plus actual compiled monetary receipts has
the same Nash error as valuation plus source-program payments. -/
theorem parameterEventGame_payment_approximate_nash_iff {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (scheduler : setup.eventGraph.PublicScheduler)
    (valuation : Parameter × PublicOutcome setup.program → Player → ℝ)
    (ε : ℝ) (profile : BehavioralProfile setup.program) :
    IsεNash (setup.eventGame scheduler)
        (fun outcome who => valuation (setup.eventParameterOutcome parameter outcome) who +
          (transferAmount (terminalPayouts setup.program outcome) who : ℝ))
        ε (compileEventProfile setup.program profile) ↔
      IsεNash (setup.parameterGameForm parameter)
        (setup.program.parameterPaymentUtility valuation) ε profile := by
  have utility_eq :
      (fun (outcome : (setup.eventGame scheduler).sig.Outcome) who =>
        valuation (setup.eventParameterOutcome parameter outcome) who +
        (transferAmount (terminalPayouts setup.program outcome) who : ℝ)) =
      (fun (outcome : (setup.eventGame scheduler).sig.Outcome) who =>
        setup.program.parameterPaymentUtility valuation
        (setup.eventParameterOutcome parameter outcome) who) := by
    funext outcome who
    simp only [parameterPaymentUtility_eq, publicTransfers, eventParameterOutcome,
      parameterOutcome, publicPayoffs_publicOutcome, terminalPayouts_eq_source]
  rw [utility_eq]
  exact setup.parameterEventGame_approximate_nash_iff parameter finite scheduler
    (setup.program.parameterPaymentUtility valuation) ε profile

end Vegas.SourceProgram.Setup
