module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensSetup
public import Vegas.Examples.OddsEvensFairDecode
public import Vegas.Examples.OddsEvensFairSequential
public import Vegas.Game.IntendedAuthenticOpening
public import GameTheory.Math.Probability.FiniteUniform

@[expose] public section

open GameTheory.Math.Probability

/-! # Exact source execution and the fair payoff in Odds–Evens -/

noncomputable section

namespace Vegas.Examples.OddsEvens

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability

/-- The complete typed store after two successful commitments and openings. -/
def bitTerminal (e o : Bool) : State simpleExpr program.terminalCtx :=
  Env.cons (.success o) (Env.cons (.success e)
    (Env.cons (.success o) (Env.cons (.success e) (Env.empty _))))

def firstConfig : Config Player simpleExpr [] :=
  Config.initial (Env.empty _)

def secondConfig (bit : Bool) :=
  commitSuccessor 0 (acceptGuard even 0) firstConfig (some (.success bit))

/-- The complete source configuration after the two accepted bindings and openings. -/
def bitConfig (e o : Bool) : Config Player simpleExpr program.terminalCtx :=
  revealSuccessor 3 (.there .here)
    (revealSuccessor 2 (.there .here)
      (commitSuccessor 1 (acceptGuard odd 1) (secondConfig e) (some (.success o))) true) true

theorem bitConfig_state (e o : Bool) : (bitConfig e o).state = bitTerminal e o := rfl

/-- Independent commitment laws and compulsory disclosure in the source evaluator. -/
def sourceBitProfile (first second : PMF Bool) : BehavioralProfile program := fun _ =>
  ⟨fun _ _ _ => first.map (some ∘ PublicationResult.success),
    ⟨fun _ _ _ => second.map (some ∘ PublicationResult.success),
      ⟨fun _ _ _ => PMF.pure true, ⟨fun _ _ _ => PMF.pure true, PUnit.unit⟩⟩⟩⟩

theorem secondConfig_view (bit : Bool) :
    (secondConfig bit).view odd = (secondConfig false).view odd := by
  unfold Config.view
  congr 1
  apply sourceObserve_congr
  all_goals
    intro name payload present
    cases present with
    | there absent => cases absent

/-- Source semantics factors through the two commitment laws when disclosure
is compulsory. Odd's commitment kernel is evaluated at its actual masked view. -/
theorem source_run_of_commitKernels (profile : BehavioralProfile program)
    (first second : PMF Bool)
    (firstLaw : commitKernel profile (firstConfig.view even) (by decide) =
      first.map (some ∘ PublicationResult.success))
    (secondLaw : commitKernel (afterCommit profile) ((secondConfig false).view odd) (by decide) =
      second.map (some ∘ PublicationResult.success))
    (disclosing : ∀ who, Disclosing program (profile who)) :
    setup.run profile = first.bind (fun e => second.map (bitConfig e)) := by
  have evenOpen (view) (active) :
      revealKernel (afterCommit (afterCommit profile)) view active = PMF.pure true :=
    eq_pure_true_of_false_not_mem ((disclosing even).1 rfl view active)
  have oddOpen (view) (active) :
      revealKernel (afterReveal (afterCommit (afterCommit profile))) view active = PMF.pure true :=
    eq_pure_true_of_false_not_mem ((disclosing odd).2.1 rfl view active)
  change (PMF.pure (Env.empty (CellVal simpleExpr))).bind
    (fun initial => SourceProgram.run program profile initial) = _
  rw [PMF.pure_bind]
  change runFrom program profile firstConfig = _
  unfold program
  rw [runFrom_commit, dite_eq_right (show even ∉ firstConfig.defaulted by decide),
    firstLaw, PMF.bind_map]
  apply congrArg (PMF.bind first)
  funext e
  change runFrom _ (afterCommit profile) (secondConfig e) = _
  have activeOdd : odd ∉ (secondConfig e).defaulted := by
    change odd ∉ (∅ : Finset Player)
    decide
  have kernelEq : commitKernel (afterCommit profile) ((secondConfig e).view odd) activeOdd =
      commitKernel (afterCommit profile) ((secondConfig false).view odd) (by decide) := by
    congr 1
    exact secondConfig_view e
  rw [runFrom_commit, dite_eq_right activeOdd, kernelEq, secondLaw, PMF.bind_map]
  apply congrArg (PMF.bind second)
  funext o
  change runFrom _ (afterCommit (afterCommit profile))
    (commitSuccessor 1 (acceptGuard odd 1) (secondConfig e) (some (.success o))) =
      PMF.pure (bitConfig e o)
  rw [runFrom_reveal, dite_eq_right (by change even ∉ (∅ : Finset Player); decide),
    evenOpen, PMF.pure_bind, runFrom_reveal,
    dite_eq_right (by change odd ∉ (∅ : Finset Player); decide), oddOpen, PMF.pure_bind]
  rfl

theorem sourceBitProfile_run (first second : PMF Bool) :
    setup.run (sourceBitProfile first second) =
      first.bind (fun e => second.map (bitConfig e)) := by
  apply source_run_of_commitKernels _ _ _ rfl rfl
  intro who
  simp [program, Disclosing, sourceBitProfile]

theorem sourceUtility_bitConfig (e o : Bool) (who : Player) :
    sourceUtility (setup.parameterOutcome (fun _ => ()) (bitConfig e o)) who =
      cash (.success e) (.success o) who := rfl

theorem uniform_opponent_value (bit : Bool) (who : Player) :
    expect (uniformLaw Bool)
      (fun other => (cash (.success bit) (.success other) who : ℝ)) = 100 := by
  rw [expect_eq_sum]
  cases bit <;> cases who <;>
    norm_num [Fintype.sum_bool, uniformLaw_apply, cash, even, odd]

theorem sourceBitProfile_uniform_value (own : PMF Bool) (who : Player) :
    expect (setup.run (sourceBitProfile own (uniformLaw Bool)))
      (fun terminal => sourceUtility (setup.parameterOutcome (fun _ => ()) terminal) who) =
        100 := by
  let payoff : Config Player simpleExpr program.terminalCtx → ℝ := fun terminal =>
    sourceUtility (setup.parameterOutcome (fun _ => ()) terminal) who
  change expect (setup.run (sourceBitProfile own (uniformLaw Bool))) payoff = 100
  rw [sourceBitProfile_run, expect_bind_tower]
  · have inner (e : Bool) :
        expect ((uniformLaw Bool).map (bitConfig e)) payoff = 100 := by
      rw [expect_map]
      exact uniform_opponent_value e who
    simp_rw [inner]
    exact expect_constant own 100
  · apply payoffIntegrable_of_bounded (C := 200)
    intro terminal
    obtain ⟨lower, upper⟩ := sourceUtility_bounds
      (setup.parameterOutcome (fun _ => ()) terminal) who
    rwa [abs_of_nonneg lower]

theorem sourceBitProfile_uniform_first_value (own : PMF Bool) (who : Player) :
    expect (setup.run (sourceBitProfile (uniformLaw Bool) own))
      (fun terminal => sourceUtility (setup.parameterOutcome (fun _ => ()) terminal) who) =
        100 := by
  let payoff : Config Player simpleExpr program.terminalCtx → ℝ := fun terminal =>
    sourceUtility (setup.parameterOutcome (fun _ => ()) terminal) who
  change expect (setup.run (sourceBitProfile (uniformLaw Bool) own)) payoff = 100
  rw [sourceBitProfile_run]
  change expect ((uniformLaw Bool).bind
    (fun e => own.bind (fun o => PMF.pure (bitConfig e o)))) payoff = 100
  rw [PMF.bind_comm, expect_bind_tower]
  · have inner (o : Bool) :
        expect ((uniformLaw Bool).bind fun e => PMF.pure (bitConfig e o))
          payoff = 100 := by
      change expect ((uniformLaw Bool).map (fun e => bitConfig e o)) payoff = 100
      rw [expect_map]
      have swapped (e : Bool) : payoff (bitConfig e o) =
          (cash (.success o) (.success e) who : ℝ) := by
        change (cash (.success e) (.success o) who : ℝ) = _
        simp only [cash, eq_comm]
      calc
        _ = expect (uniformLaw Bool)
            (fun e => (cash (.success o) (.success e) who : ℝ)) :=
          expect_congr_on_support (fun e _ => swapped e)
        _ = 100 := uniform_opponent_value o who
    simp_rw [inner]
    exact expect_constant own 100
  · apply payoffIntegrable_of_bounded (C := 200)
    intro terminal
    obtain ⟨lower, upper⟩ := sourceUtility_bounds
      (setup.parameterOutcome (fun _ => ()) terminal) who
    rwa [abs_of_nonneg lower]

/-- All intended behavioral profiles reduce to the two actual private
commitment laws. In particular, Odd cannot condition its bit on Even's bit. -/
theorem sourceDecoded_bitRun (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    setup.run (sourceDecoded profile) =
      (firstBitLaw profile).bind (fun e => (secondBitLaw profile).map (bitConfig e)) :=
  source_run_of_commitKernels _ _ _ (first_commit_bitLaw profile)
    (second_commit_bitLaw profile) (sourceDecoded_disclosing profile)

theorem uniform_root_value (who : Player) (deviation : setup.intendedModel.BehavioralPolicy who) :
    expect (setup.intendedModel.runBehavioral
      (Profile.update (sig := setup.intendedModel.behavioralSignature) uniformProfile who deviation)
        (instructionCount setup.program + 1)) (terminalUtility who) = 100 := by
  let changed := Profile.update (sig := setup.intendedModel.behavioralSignature)
    uniformProfile who deviation
  let payoff : Config Player simpleExpr program.terminalCtx → ℝ := fun terminal =>
    sourceUtility (setup.parameterOutcome (fun _ => ()) terminal) who
  have expected := congrArg
    (fun law : PMF (Option (Config Player simpleExpr program.terminalCtx)) =>
      expect law (fun terminal => terminal.elim 0 payoff)) (sourceDecoded_run changed)
  simp only [expect_map] at expected
  change expect (setup.intendedModel.runBehavioral changed _)
    (terminalUtility who) = 100
  rw [show expect (setup.intendedModel.runBehavioral changed _)
      (terminalUtility who) = expect (setup.run (sourceDecoded changed)) payoff from expected]
  rw [sourceDecoded_bitRun, ← sourceBitProfile_run]
  cases who with
  | false =>
      have unchanged : secondBitLaw changed = uniformLaw Bool := by
        change secondBitLaw uniformProfile = _
        exact secondBitLaw_uniform
      rw [unchanged]
      exact sourceBitProfile_uniform_value (firstBitLaw changed) even
  | true =>
      have unchanged : firstBitLaw changed = uniformLaw Bool := by
        change firstBitLaw uniformProfile = _
        exact firstBitLaw_uniform
      rw [unchanged]
      exact sourceBitProfile_uniform_first_value (secondBitLaw changed) odd

/-- The explicit uniform-bit assessment, with its consistent Bayesian beliefs,
is a sequential equilibrium of the actual intended source program. -/
theorem uniformAssessment_equilibrium :
    uniformAssessment.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories terminalUtility :=
  uniformAssessment_equilibrium_of_rootValue uniform_root_value

theorem uniform_expected_payoff (who : Player) :
    expect (setup.intendedModel.runBehavioral uniformProfile (instructionCount setup.program + 1))
      (terminalUtility who) = 100 := by
  simpa only [Profile.update_eq_self] using uniform_root_value who (uniformProfile who)

end Vegas.Examples.OddsEvens
