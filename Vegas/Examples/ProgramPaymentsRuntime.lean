module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.ProgramPaymentsRuntimeService
public import Vegas.Game.ProgramPaymentAsyncNash
public import Vegas.Game.SourceProtocolNash
public import Vegas.Pending.ExclusionAcceptedOutput
public import Vegas.Pending.ExclusionEvidence
public import Vegas.Pending.ReactiveAssociationEvidence
public import Vegas.Compile.EventGraphParameterReadout

@[expose] public section

/-! # Executable payments change equilibrium in an actual native runtime

Alice's clients use the checked roster service and the full bounded raw response
menu. Binding failure and publication withholding remain legal source choices.
Valuation and realized monetary settlement are separate: a positive deposit is
collected by the existing authentic evidence audit only when it is charged.
-/

noncomputable section

namespace Vegas.Examples.ProgramPaymentsRuntime

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open ProgramPayments

/-- Admit every original source binding choice, including irrevocable failure. -/
def admission (bonus : Int) : CommitmentInterface (program bonus) :=
  CommitmentInterface.forfeiture (program bonus)

/-- The protocol interface removes none of the original binding policies. -/
theorem all_permitted (bonus : Int) (who : Player)
    (candidate : BehavioralPolicy who (program bonus)) :
    candidate.Admitted (program bonus) (admission bonus) := by
  constructor
  · intro _ _ _ selected _
    cases selected with
    | none => trivial
    | some result => cases result <;> trivial
  · trivial

theorem profile_permitted (bonus : Int) (choice : Bool) (who : Player) :
    (profile bonus choice who).Admitted (program bonus) (admission bonus) :=
  all_permitted bonus who _

/-- The existing policy equivalence encodes the selected source profile. -/
def sourceProfile (bonus : Int) (choice : Bool) :
    Profile ((setup bonus).informationModel (admission bonus)).behavioralSignature :=
  (setup bonus).encodeBehavioralProfile (admission bonus) (profile bonus choice)
    (profile_permitted bonus choice)

theorem decode_sourceProfile (bonus : Int) (choice : Bool) :
    (setup bonus).decodeBehavioralProfile (admission bonus) (sourceProfile bonus choice) =
      profile bonus choice :=
  (setup bonus).decodeBehavioralProfile_encodeBehavioralProfile (admission bonus)
    (profile bonus choice) (profile_permitted bonus choice)

def parameter (bonus : Int) : State simpleExpr (setup bonus).context → Unit := fun _ => ()

def runtimeValuation (bonus : Int) : Unit × PublicOutcome (program bonus) → Player → ℝ :=
  fun outcome => valuation bonus outcome.2

/-- The authentic audit samples all available settled evidence. -/
def auditSample (bonus : Int) (actual : List (SettledEvidence (setup bonus) .sequential)) :
    PMF (List (SettledEvidence (setup bonus) .sequential)) := PMF.pure actual

theorem audit_authentic (bonus : Int) :
    ∀ actual observed, observed ∈ (auditSample bonus actual).support → observed ⊆ actual := by
  intro actual observed supported
  have same := (PMF.mem_support_pure_iff actual observed).mp supported
  subst observed
  exact List.Subset.refl _

def deposit : Player → ℝ := fun _ => 1

abbrev model (bonus : Int) :=
  (service bonus).rawMenu.information (serviceInitialLaw (setup bonus) .sequential)
    (service bonus).horizon (service bonus).scheduler

abbrev fuel (bonus : Int) := 2 * (service bonus).horizon + 1

def clients (bonus : Int) (choice : Bool) : Profile (model bonus).behavioralSignature :=
  (service bonus).clientProfile (admission bonus) (service bonus).rawMenu
    (firstTurnTiming (setup bonus) 1 .sequential) (sourceProfile bonus choice)

def runtimeGame (bonus : Int) : UtilityGame Player where
  form := (model bonus).toBehavioralGameForm (fuel bonus)
  utility history who := (service bonus).paymentExpectedUtility (parameter bonus)
    (runtimeValuation bonus) (auditSample bonus) deposit history.state who

def sourceGame (bonus : Int) : UtilityGame Player where
  form := ((setup bonus).informationModel (admission bonus)).toBehavioralGameForm
    (instructionCount (program bonus) + 1)
  utility history who := ((setup bonus).protocolReadout history.state).elim 0
    (fun terminal => (setup bonus).parameterPaymentUtility (runtimeValuation bonus)
      ((setup bonus).parameterOutcome (parameter bonus) terminal) who)

abbrev bindingEvent (bonus : Int) : (graph (setup bonus)).EventId :=
  ⟨0, by change 0 < 2; decide⟩
abbrev publicationEvent (bonus : Int) : (graph (setup bonus)).EventId :=
  ⟨1, by change 1 < 2; decide⟩

/-- A successful publication in an initialized raw readout rules out both
possible public failure witnesses of this two-event program. -/
private theorem not_defaulted_of_readout_success (bonus : Int)
    (control : (serviceApplication (setup bonus) .sequential (service bonus).duration
      (leaks bonus)).Control)
    (trace : ((serviceApplication (setup bonus) .sequential (service bonus).duration
      (leaks bonus)).protocol (serviceInitialLaw (setup bonus) .sequential)
        (service bonus).horizon (service bonus).scheduler).Trace (some control))
    (terminal : Config Player simpleExpr (program bonus).terminalCtx)
    (read : serviceSourceReadout (setup bonus) .sequential (service bonus).duration
      (leaks bonus) (some control) = some terminal)
    (published : terminal.state.get .here = .success true) : .alice ∉ terminal.defaulted := by
  let nativeTimeouts := serviceTimeouts (setup bonus) .sequential (service bonus).duration
  let inputs : PMF (graph (setup bonus)).Inputs :=
    (setup bonus).initialLaw.map (setup bonus).eventInputs
  have initialized : inputs.map EventGraphRuntime.State.initial =
      serviceInitialLaw (setup bonus) .sequential := by
    rw [PMF.map_comp]
    rfl
  rw [← initialized] at trace
  have valid := reactive_history_invariant nativeTimeouts (leaks bonus) inputs
    (service bonus).horizon (service bonus).scheduler trace
  obtain ⟨_, _, invariant⟩ := valid
  have bindings := reactiveBindingInvariant_history nativeTimeouts (leaks bonus) inputs
    (service bonus).horizon (service bonus).scheduler trace
  have failures := ExclusionEvidence.history nativeTimeouts (leaks bonus) inputs
    (service bonus).horizon (service bonus).scheduler trace
  have defaults := serviceSourceReadout_defaults (setup bonus) .sequential
    (service bonus).duration (leaks bonus) control terminal read
  rw [serviceSourceReadout_eq_decode, decodeConfig?] at read
  obtain ⟨state, decoded, same⟩ := Option.map_eq_some_iff.mp read
  have states : state = terminal.state := congrArg Config.state same
  have agree : (terminalRefs (program bonus)).Agrees state
      control.execution.application.config.store :=
    decodeState?_agrees _ _ state decoded
  have publication := agree (HasVar.here :
    HasVar (program bonus).terminalCtx 1 (.publication .bool))
  rw [states, published] at publication
  let binding : FieldRef (graph (setup bonus)).layout (.binding Player.alice .bool) :=
    ⟨.inr (bindingEvent bonus), rfl⟩
  obtain ⟨checks, code⟩ : ∃ checks : List (GuardCheck (graph (setup bonus)).layout BaseTy.bool),
      (graph (setup bonus)).nodes (publicationEvent bonus) =
        EventCode.resolve (layout := (graph (setup bonus)).layout)
          Player.alice BaseTy.bool binding checks := by
    refine ⟨?_, ?_⟩
    swap
    rfl
  have bound := invariant.reachable.publication_binding (publicationEvent bonus) .alice .bool
    binding checks rfl code true publication
  have bindingSuccess := outputSucceeded_of_ref _ (bindingEvent bonus) binding rfl bound
    (by intro impossible; cases impossible)
  have publicationSuccess := outputSucceeded_of_ref _ (publicationEvent bonus)
    (⟨.inr (publicationEvent bonus), rfl⟩ :
      FieldRef (graph (setup bonus)).layout (.publication .bool)) rfl publication
    (by intro impossible; cases impossible)
  intro inactive
  have nativeInactive : Player.alice ∈ control.execution.application.config.defaulted := by
    change Player.alice ∈ terminal.defaults.defaulted at inactive
    rw [defaults] at inactive
    exact inactive
  obtain ⟨event, _, failed⟩ := (failures.defaulted_zero .alice).mp nativeInactive
  fin_cases event
  · exact bindingSuccess.not_publicFailure bindings failed
  · exact publicationSuccess.not_publicFailure bindings failed

private theorem transfers_eq_publicTransfers_of_readout (bonus : Int)
    (control : (serviceApplication (setup bonus) .sequential (service bonus).duration
      (leaks bonus)).Control)
    (trace : ((serviceApplication (setup bonus) .sequential (service bonus).duration
      (leaks bonus)).protocol (serviceInitialLaw (setup bonus) .sequential)
        (service bonus).horizon (service bonus).scheduler).Trace (some control))
    (terminal : Config Player simpleExpr (program bonus).terminalCtx)
    (read : serviceSourceReadout (setup bonus) .sequential (service bonus).duration
      (leaks bonus) (some control) = some terminal) :
    (setup bonus).transfers ((program bonus).publicOutcome terminal) =
      (program bonus).publicTransfers ((program bonus).publicOutcome terminal) := by
  funext who
  cases who
  unfold Setup.transfers
  split_ifs with inactive
  · have noTrue := not_defaulted_of_readout_success bonus control trace terminal read
    have published : terminal.state.get .here ≠ .success true := fun success =>
      noTrue success inactive
    have payments : (program bonus).publicPayoffs ((program bonus).publicOutcome terminal) =
        [(Player.alice, if (((program bonus).publicOutcome terminal).values.get .here :
          PublicationResult Bool).getD false then bonus else 0)] := rfl
    change ((0 : Int) : ℝ) =
      (transferAmount ((program bonus).publicPayoffs ((program bonus).publicOutcome terminal))
        Player.alice : ℝ)
    rw [payments]
    change ((0 : Int) : ℝ) = (transferAmount [(Player.alice,
      if (terminal.state.get .here).getD false then bonus else 0)] Player.alice : ℝ)
    cases result : terminal.state.get .here with
    | failure => simp [PublicationResult.getD, transferAmount]
    | success value =>
        cases value with
        | false => simp [PublicationResult.getD, transferAmount]
        | true => exact (published result).elim
  · rfl

/-- Every supported monetary settlement at an initialized raw history satisfies
the same numerical interval, including unfinished readouts and actual charges. -/
theorem realized_payoff_bounds (bonus : Int) :
    (service bonus).SettlementRange (parameter bonus)
      ((setup bonus).parameterPaymentUtility (runtimeValuation bonus)) (auditSample bonus)
      deposit (fun _ => -|(bonus : ℝ) - 1| - 1) (fun _ => 2 * |(bonus : ℝ) - 1| + 1) := by
  intro control trace payoffs supported who
  rw [Enforcement.TerminalAudit.settlement, PMF.support_map] at supported
  obtain ⟨verdict, _, rfl⟩ := supported
  let output := serviceSourceReadout (setup bonus) .sequential (service bonus).duration
    (leaks bonus) (some control)
  change -|(bonus : ℝ) - 1| - 1 ≤ output.elim 0 (fun terminal =>
      (setup bonus).parameterPaymentUtility (runtimeValuation bonus)
        ((setup bonus).parameterOutcome (parameter bonus) terminal) who) -
          (if verdict who then deposit who else 0) ∧
    output.elim 0 (fun terminal => (setup bonus).parameterPaymentUtility
      (runtimeValuation bonus) ((setup bonus).parameterOutcome (parameter bonus) terminal) who) -
      (if verdict who then deposit who else 0) ≤
        (-|(bonus : ℝ) - 1| - 1) + (2 * |(bonus : ℝ) - 1| + 1)
  have nonnegative := abs_nonneg ((bonus : ℝ) - 1)
  have baseBounds : -|(bonus : ℝ) - 1| ≤ output.elim 0 (fun terminal =>
      (setup bonus).parameterPaymentUtility (runtimeValuation bonus)
        ((setup bonus).parameterOutcome (parameter bonus) terminal) who) ∧
      output.elim 0 (fun terminal => (setup bonus).parameterPaymentUtility
        (runtimeValuation bonus) ((setup bonus).parameterOutcome (parameter bonus) terminal)
          who) ≤ |(bonus : ℝ) - 1| := by
    cases read : output with
    | none => simp only [Option.elim_none]; constructor <;> linarith
    | some terminal =>
        have transfers := transfers_eq_publicTransfers_of_readout bonus control trace terminal read
        change -|(bonus : ℝ) - 1| ≤
            valuation bonus ((program bonus).publicOutcome terminal) who +
              (setup bonus).transfers ((program bonus).publicOutcome terminal) who ∧
          valuation bonus ((program bonus).publicOutcome terminal) who +
              (setup bonus).transfers ((program bonus).publicOutcome terminal) who ≤
            |(bonus : ℝ) - 1|
        rw [transfers]
        cases who
        exact abs_le.mp (utility_abs_le bonus ((program bonus).publicOutcome terminal))
  obtain ⟨lower, upper⟩ := baseBounds
  cases verdict who <;> simp only [Bool.false_eq_true, ↓reduceIte, deposit] <;>
    constructor <;> linarith

/-- Exact Nash correspondence for this checked runtime and its actual audit,
against every response in the bounded raw menu. -/
theorem runtime_source_isNash_iff (bonus : Int) (choice : Bool) :
    IsNash (runtimeGame bonus).form (euPreference (runtimeGame bonus).utility)
        (clients bonus choice) ↔
      IsNash (sourceGame bonus).form (euPreference (sourceGame bonus).utility)
        (sourceProfile bonus choice) := by
  have correspondence := (service bonus).payment_firstTurnClientProfile_isεNash_iff
    (admission bonus) (setup bonus).eventGraph.sequentialize_barrierOrdered
    (parameter bonus) (runtimeValuation bonus) (auditSample bonus) (audit_authentic bonus)
    deposit (fun _ => by norm_num [deposit]) 1 (fun _ => -|(bonus : ℝ) - 1| - 1)
    (2 * |(bonus : ℝ) - 1| + 1) (realized_payoff_bounds bonus) 0 (sourceProfile bonus choice)
  rw [← isNash_iff_isεNash_zero, ← isNash_iff_isεNash_zero] at correspondence
  exact correspondence

theorem source_isNash_iff (bonus : Int) (choice : Bool) :
    IsNash (sourceGame bonus).form (euPreference (sourceGame bonus).utility)
        (sourceProfile bonus choice) ↔
      IsNash (game bonus).form (euPreference (game bonus).utility) (profile bonus choice) := by
  let actual := fun (terminal : Config Player simpleExpr (program bonus).terminalCtx) who =>
    (setup bonus).parameterPaymentUtility (runtimeValuation bonus)
      ((setup bonus).parameterOutcome (parameter bonus) terminal) who
  have correspondence := (setup bonus).protocol_isεNash_iff (admission bonus)
    id (all_permitted bonus) actual 0 (sourceProfile bonus choice)
  rw [decode_sourceProfile] at correspondence
  rw [← isNash_iff_isεNash_zero, ← isNash_iff_isεNash_zero] at correspondence
  change IsNash (sourceGame bonus).form (euPreference (sourceGame bonus).utility)
      (sourceProfile bonus choice) ↔
    IsNash ((setup bonus).observedGameForm id) (euPreference actual)
      (profile bonus choice) at correspondence
  have law (players : BehavioralProfile (program bonus)) :
      ((((setup bonus).observedGameForm id).play players).map actual) =
        (((game bonus).form.play players).map (game bonus).utility) := by
    simp only [Setup.observedGameForm, Setup.run, setup, PMF.pure_bind, game,
      SourceProgram.gameForm, PMF.map_comp, Function.comp_def, id_eq]
    apply map_congr_on_support _
    intro terminal supported
    funext who
    change valuation bonus ((program bonus).publicOutcome terminal) who +
        (setup bonus).transfers ((program bonus).publicOutcome terminal) who =
      valuation bonus ((program bonus).publicOutcome terminal) who +
        (program bonus).publicTransfers ((program bonus).publicOutcome terminal) who
    rw [transfers_eq_publicTransfers_of_run bonus players terminal supported]
  have has (players : BehavioralProfile (program bonus)) (who : Player) :
      UtilityHasExpectation actual who (((setup bonus).observedGameForm id).play players) ↔
        UtilityHasExpectation (game bonus).utility who ((game bonus).form.play players) :=
    hasExpectation_observed_law_iff _ _ actual (game bonus).utility
      (fun values : Player → ℝ => values who) (law players)
  have value (players : BehavioralProfile (program bonus)) (who : Player) :
      extendedExpectedUtility actual who (((setup bonus).observedGameForm id).play players) =
        extendedExpectedUtility (game bonus).utility who ((game bonus).form.play players) :=
    extendedExpect_observed_law_eq _ _ actual (game bonus).utility
      (fun values : Player → ℝ => values who) (law players)
  refine correspondence.trans ?_
  rw [isNash_iff, isNash_iff]
  apply forall_congr'
  intro who
  apply forall_congr'
  intro replacement
  exact and_congr (has _ who) (and_congr (has _ who) (by rw [value, value]; rfl))

/-- Changing the executable bonus changes the actual raw-runtime equilibrium.
Both source and runtime quantifiers retain all their legal deviations. -/
theorem runtime_isNash_iff (bonus : Int) (choice : Bool) :
    IsNash (runtimeGame bonus).form (euPreference (runtimeGame bonus).utility)
        (clients bonus choice) ↔
      IsNash (game bonus).form (euPreference (game bonus).utility) (profile bonus choice) :=
  (runtime_source_isNash_iff bonus choice).trans (source_isNash_iff bonus choice)

theorem bonus_true_isNash :
    IsNash (runtimeGame 2).form (euPreference (runtimeGame 2).utility) (clients 2 true) :=
  (runtime_isNash_iff 2 true).mpr ProgramPayments.bonus_true_isNash

theorem zero_false_isNash :
    IsNash (runtimeGame 0).form (euPreference (runtimeGame 0).utility) (clients 0 false) :=
  (runtime_isNash_iff 0 false).mpr ProgramPayments.zero_false_isNash

theorem bonus_false_not_isNash :
    ¬ IsNash (runtimeGame 2).form (euPreference (runtimeGame 2).utility) (clients 2 false) :=
  fun equilibrium => ProgramPayments.bonus_false_not_isNash
    ((runtime_isNash_iff 2 false).mp equilibrium)

theorem zero_true_not_isNash :
    ¬ IsNash (runtimeGame 0).form (euPreference (runtimeGame 0).utility) (clients 0 true) :=
  fun equilibrium => ProgramPayments.zero_true_not_isNash
    ((runtime_isNash_iff 0 true).mp equilibrium)

theorem run_sourceProfile (bonus : Int) (choice : Bool) :
    (setup bonus).run (profile bonus choice) = PMF.pure (final bonus choice) := by
  change (PMF.pure ProgramPayments.initial).bind
    (fun initial => (program bonus).run (profile bonus choice) initial) = _
  rw [PMF.pure_bind, run_profile]

/-- Prescribed native clients preserve typed cells, public default history
and actual cash jointly. The law is proved for both choices and every integer bonus. -/
theorem settlement_law (bonus : Int) (choice : Bool) :
    (((model bonus).runBehavioral (clients bonus choice) (fuel bonus)).bind fun history =>
      ((service bonus).paymentSettlement (auditSample bonus) deposit history.state).map
        fun receipts =>
          ((serviceSourceReadout (setup bonus) .sequential (service bonus).duration
            (leaks bonus) history.state).map (fun config => (config.state, config.defaults)),
            receipts)) =
      PMF.pure (some ((final bonus choice).state, (final bonus choice).defaults),
        fun _ : Player => ((if choice then bonus else 0 : Int) : ℝ)) := by
  have law := (service bonus).payment_firstTurnClientProfile_settlement_law
    (admission bonus) (setup bonus).eventGraph.sequentialize_barrierOrdered
    (auditSample bonus) (audit_authentic bonus) deposit 1 (sourceProfile bonus choice)
  change _ = ((setup bonus).run ((setup bonus).decodeBehavioralProfile (admission bonus)
    (sourceProfile bonus choice))).map (fun terminal =>
      (some (terminal.state, terminal.defaults),
        (setup bonus).transfers ((program bonus).publicOutcome terminal))) at law
  rw [decode_sourceProfile, run_sourceProfile, PMF.pure_map] at law
  have actual := transfers_eq_publicTransfers_of_run bonus (profile bonus choice)
    (final bonus choice) (by rw [run_profile]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  rw [actual] at law
  change _ = PMF.pure (some ((final bonus choice).state, (final bonus choice).defaults), fun who =>
    (transferAmount ((program bonus).evaluatePayoffs (final bonus choice).state) who : ℝ)) at law
  rw [evaluatePayoffs_final] at law
  have receipts : (fun who : Player =>
      (transferAmount [(.alice, if choice then bonus else 0)] who : ℝ)) =
      fun _ : Player => ((if choice then bonus else 0 : Int) : ℝ) := by
    funext who
    cases who
    simp [transferAmount]
  rw [receipts] at law
  exact law

end Vegas.Examples.ProgramPaymentsRuntime
