/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.ProgramPaymentsRuntimeService
import Vegas.Game.ProgramPaymentAsyncNash
import Vegas.Game.SourceProtocolNash

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
  · intro _ _ selected _
    cases selected <;> trivial
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
    (fun terminal => (program bonus).paymentUtility (valuation bonus)
      ((program bonus).publicOutcome terminal) who)

/-- Bounds include every terminal state, unfinished readout and audit verdict,
including those arising after arbitrary legal raw responses. -/
theorem realized_payoff_bounds (bonus : Int) (who : Player)
    (output : Option (State simpleExpr (program bonus).terminalCtx)) (charged : Bool) :
    -|(bonus : ℝ) - 1| - 1 ≤ output.elim 0 (fun terminal =>
      (program bonus).parameterPaymentUtility (runtimeValuation bonus)
        ((setup bonus).parameterOutcome (parameter bonus) terminal) who) -
          (if charged then deposit who else 0) ∧
    output.elim 0 (fun terminal => (program bonus).parameterPaymentUtility
      (runtimeValuation bonus) ((setup bonus).parameterOutcome (parameter bonus) terminal) who) -
      (if charged then deposit who else 0) ≤
        (-|(bonus : ℝ) - 1| - 1) + (2 * |(bonus : ℝ) - 1| + 1) := by
  have nonnegative := abs_nonneg ((bonus : ℝ) - 1)
  have baseBounds : -|(bonus : ℝ) - 1| ≤ output.elim 0 (fun terminal =>
      (program bonus).parameterPaymentUtility (runtimeValuation bonus)
        ((setup bonus).parameterOutcome (parameter bonus) terminal) who) ∧
      output.elim 0 (fun terminal => (program bonus).parameterPaymentUtility
        (runtimeValuation bonus) ((setup bonus).parameterOutcome (parameter bonus) terminal)
          who) ≤ |(bonus : ℝ) - 1| := by
    cases output with
    | none => simp only [Option.elim_none]; constructor <;> linarith
    | some terminal =>
        cases who
        exact abs_le.mp (utility_abs_le bonus ((program bonus).publicOutcome terminal))
  obtain ⟨lower, upper⟩ := baseBounds
  cases charged <;> simp only [Bool.false_eq_true, ↓reduceIte, deposit] <;>
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
  have correspondence := (setup bonus).protocol_isεNash_iff (admission bonus)
    (program bonus).publicOutcome (all_permitted bonus)
    (game bonus).utility 0 (sourceProfile bonus choice)
  rw [decode_sourceProfile] at correspondence
  rw [← isNash_iff_isεNash_zero, ← isNash_iff_isεNash_zero] at correspondence
  rw [isNash_iff, isNash_iff] at correspondence ⊢
  simpa only [sourceGame, game, Setup.gameForm, Setup.observedGameForm, Setup.publicRun,
    Setup.run, setup, SourceProgram.gameForm, PMF.pure_bind] using correspondence

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

/-- Prescribed native clients preserve the complete typed state and actual cash
jointly. The law is proved for both choices and every integer bonus. -/
theorem settlement_law (bonus : Int) (choice : Bool) :
    (((model bonus).runBehavioral (clients bonus choice) (fuel bonus)).bind fun history =>
      ((service bonus).paymentSettlement (auditSample bonus) deposit history.state).map
        fun receipts =>
          (serviceSourceReadout (setup bonus) .sequential (service bonus).deadline
            (leaks bonus) history.state, receipts)) =
      PMF.pure (some (final bonus choice),
        fun _ : Player => ((if choice then bonus else 0 : Int) : ℝ)) := by
  have law := (service bonus).payment_firstTurnClientProfile_settlement_law
    (admission bonus) (setup bonus).eventGraph.sequentialize_barrierOrdered
    (auditSample bonus) (audit_authentic bonus) deposit 1 (sourceProfile bonus choice)
  change _ = ((setup bonus).run ((setup bonus).decodeBehavioralProfile (admission bonus)
    (sourceProfile bonus choice))).map (fun terminal =>
      (some terminal, fun who => (transferAmount ((program bonus).evaluatePayoffs terminal)
        who : ℝ))) at law
  rw [decode_sourceProfile, run_sourceProfile, PMF.pure_map, evaluatePayoffs_final] at law
  have receipts : (fun who : Player =>
      (transferAmount [(.alice, if choice then bonus else 0)] who : ℝ)) =
      fun _ : Player => ((if choice then bonus else 0 : Int) : ℝ) := by
    funext who
    cases who
    simp [transferAmount]
  rw [receipts] at law
  exact law

end Vegas.Examples.ProgramPaymentsRuntime
