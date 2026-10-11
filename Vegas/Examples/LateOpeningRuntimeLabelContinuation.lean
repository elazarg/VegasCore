/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeLabelBeliefs
import GameTheory.Analysis.Protocol.Sequential
import GameTheoryExtensions.Protocol.ContinuationHorizon
import Vegas.Examples.LateOpeningRuntimeBobBindingInformation
import Vegas.Examples.LateOpeningRuntimeBobIncentive

/-! # Native continuation history laws under uniform Alice reference play -/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeLabelContinuation

open SourceProgram Vegas Interaction GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability GameTheory.Enforcement Filter
open scoped ENNReal
open LateOpeningRuntimeSource LateOpeningRuntimeService
open LateOpeningRuntimeLabelOrbits LateOpeningRuntimeLabelReach LateOpeningRuntimeLabelBeliefs

variable (horizon : Nat) (scheduler : app.Scheduler)
local notation "M" => rawMenu.information initial horizon scheduler
local notation "E" => rawMenu.protocol initial horizon scheduler
local notation "antichain" => rawMenu.decisionInformationAntichain initial horizon scheduler

private theorem uniform_limit
    (sequence : Nat → (M).BehavioralAssessment) (assessment : (M).BehavioralAssessment)
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (uniformAlice : ∀ n, ((sequence n).strategy alice).AgreesAtDecisions
      (rawMenu.uniformPolicy initial horizon scheduler alice)) :
    (assessment.strategy alice).AgreesAtDecisions
      (rawMenu.uniformPolicy initial horizon scheduler alice) := by
  funext site
  ext choice
  have fixed : (fun n => (sequence n).strategy alice site.1 choice) =
      fun _ => rawMenu.uniformPolicy initial horizon scheduler alice site.1 choice := by
    funext n
    exact congrArg (fun law : PMF ((M).Choice alice site.1) => law choice)
      (congrFun (uniformAlice n) site)
  have limiting := converges.1 alice site choice
  rw [fixed] at limiting
  exact tendsto_nhds_unique limiting tendsto_const_nhds

/-- Every whole Bob deviation preserves actual private-label history symmetry
under the coherent uniform-Alice reference sequence, including zero-reach fibers. -/
theorem continuation_law_permutation_of_uniform_sequence
    (sequence : Nat → (M).BehavioralAssessment) (assessment : (M).BehavioralAssessment)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent (M)
      (sequence n) antichain)
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (uniformAlice : ∀ n, ((sequence n).strategy alice).AgreesAtDecisions
      (rawMenu.uniformPolicy initial horizon scheduler alice))
    (site : (M).InformationSite bob) (alternative : (M).BehavioralPolicy bob)
    (payoff : (E).History → ℝ)
    (permutation : Equiv.Perm (Fin 3)) :
    (((assessment.continuationContext
        (rawMenu.bounded initial horizon scheduler).wellFoundedHistories site
          payoff).outcome alternative).map
      (permuteHistory horizon scheduler permutation)) =
      (assessment.continuationContext
        (rawMenu.bounded initial horizon scheduler).wellFoundedHistories site
          payoff).outcome alternative := by
  have uniform := uniform_limit horizon scheduler sequence assessment converges uniformAlice
  have updated : ((GameTheory.Profile.update (sig := (M).behavioralSignature)
      assessment.strategy bob alternative) alice).AgreesAtDecisions
      (rawMenu.uniformPolicy initial horizon scheduler alice) := by
    simpa only [GameTheory.Profile.update_of_ne _ _ (by decide : alice ≠ bob)]
      using uniform
  have orbit : (assessment.belief bob site).map
      (informationHistoryEquiv horizon scheduler permutation site) =
        assessment.belief bob site := by
    ext history
    obtain ⟨before, rfl⟩ :=
      (informationHistoryEquiv horizon scheduler permutation site).surjective history
    rw [pmf_map_apply_of_injective _
      (informationHistoryEquiv horizon scheduler permutation site).injective]
    exact (belief_permutation_of_uniform_sequence horizon scheduler permutation sequence assessment
      mixed bayes converges uniformAlice site before).symm
  change ((assessment.belief bob site).bind fun history =>
    (M).runBehavioralTerminalFrom
      (rawMenu.bounded initial horizon scheduler).wellFoundedHistories
      (GameTheory.Profile.update (sig := (M).behavioralSignature)
        assessment.strategy bob alternative) history.1).map _ = _
  rw [PMF.map_bind]
  have kernel (history : (M).InformationHistory bob site.1) :
      ((M).runBehavioralTerminalFrom
        (rawMenu.bounded initial horizon scheduler).wellFoundedHistories
        (GameTheory.Profile.update (sig := (M).behavioralSignature)
        assessment.strategy bob alternative) history.1).map
          (permuteHistory horizon scheduler permutation) =
      (M).runBehavioralTerminalFrom
        (rawMenu.bounded initial horizon scheduler).wellFoundedHistories
        (GameTheory.Profile.update (sig := (M).behavioralSignature)
          assessment.strategy bob alternative)
          (informationHistoryEquiv horizon scheduler permutation site history).1 := by
    rw [(M).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded _
      (rawMenu.bounded initial horizon scheduler),
      (M).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded _
        (rawMenu.bounded initial horizon scheduler)]
    exact runBehavioralFrom_permutation horizon scheduler permutation _ updated _ history.1
  calc
    _ = (assessment.belief bob site).bind (fun history =>
        (M).runBehavioralTerminalFrom
          (rawMenu.bounded initial horizon scheduler).wellFoundedHistories
          (GameTheory.Profile.update (sig := (M).behavioralSignature)
            assessment.strategy bob alternative)
          (informationHistoryEquiv horizon scheduler permutation site history).1) :=
      bind_congr_on_support _ (fun history _ => kernel history)
    _ = _ := by
      erw [← PMF.bind_map (assessment.belief bob site)
        (informationHistoryEquiv horizon scheduler permutation site)
        (fun history : (M).InformationHistory bob site.1 =>
          (M).runBehavioralTerminalFrom
            (rawMenu.bounded initial horizon scheduler).wellFoundedHistories
            (GameTheory.Profile.update (sig := (M).behavioralSignature)
              assessment.strategy bob alternative) history.1), orbit]
      rfl

private theorem optional_label_publication_factorization
    (law : PMF (Option (Fin 3 × PublicationResult Answer)))
    (invariant : ∀ permutation : Equiv.Perm (Fin 3),
      law.map (Option.map fun result => (permutation result.1, result.2)) = law) :
    law = (law.map (Option.map Prod.snd)).bind (fun result =>
      match result with
      | none => PMF.pure none
      | some answer => (PMF.uniformOfFintype (Fin 3)).map
          fun label => some (label, answer)) := by
  classical
  let := Fintype.ofFinite Answer
  have atoms (label : Fin 3) (answer : PublicationResult Answer) :
      law (some (label, answer)) = law (some (0, answer)) := by
    have injective : Function.Injective (Option.map
        (fun result : Fin 3 × PublicationResult Answer =>
          ((Equiv.swap 0 label) result.1, result.2))) := by
      intro first second same
      cases first with
      | none =>
          cases second with
          | none => rfl
          | some second => cases same
      | some first =>
          cases second with
          | none => cases same
          | some second =>
              have pairs : ((Equiv.swap 0 label) first.1, first.2) =
                  ((Equiv.swap 0 label) second.1, second.2) := Option.some.inj same
              apply congrArg some
              apply Prod.ext
              · exact (Equiv.swap 0 label).injective (congrArg Prod.fst pairs)
              · have secondEq := congrArg Prod.snd pairs
                exact secondEq
    have mass := pmf_map_apply_of_injective law injective (some (0, answer))
    rw [invariant, Option.map_some, Equiv.swap_apply_left] at mass
    exact mass
  have marginal_some (answer : PublicationResult Answer) :
      (law.map (Option.map Prod.snd)) (some answer) =
        (3 : ℝ≥0∞) * law (some (0, answer)) := by
    simp [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, atoms, nsmul_eq_mul]
  ext result
  cases result with
  | none =>
      rw [PMF.bind_apply]
      simp [PMF.map_apply, tsum_fintype]
  | some pair =>
      rcases pair with ⟨label, answer⟩
      have fiber (chosen : PublicationResult Answer) :
          ((PMF.uniformOfFintype (Fin 3)).map fun label => some (label, chosen))
            (some (label, answer)) =
          if answer = chosen then (3 : ℝ≥0∞)⁻¹ else 0 := by
        by_cases same : answer = chosen
        · subst chosen
          rw [pmf_map_apply_of_injective _ (by
            intro first second same
            exact congrArg Prod.fst (Option.some.inj same))]
          simp
        · simp [PMF.map_apply, same]
      rw [PMF.bind_apply, tsum_fintype, Fintype.sum_option]
      simp only [PMF.pure_apply, reduceCtorEq, ite_false, mul_zero, zero_add,
        fiber, marginal_some, mul_ite]
      rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ answer), atoms, mul_right_comm,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- Label-orbit averaging bounds the successful-Alice gross readout, including
missing readouts and failed Bob publications, without independence assumptions. -/
private theorem optional_publication_gross_le (reward : ℝ)
    (law : PMF (Option (Fin 3 × PublicationResult Answer)))
    (invariant : ∀ permutation : Equiv.Perm (Fin 3),
      law.map (Option.map fun result => (permutation result.1, result.2)) = law) :
    expect law (fun result => match result with
      | none => 0
      | some (_, .failure) => 0
      | some (label, .success answer) => grossUtility reward ((false, label),
          publicOutcome program (finalState false label true answer true)) bob) ≤ 2 / 5 := by
  classical
  rw [optional_label_publication_factorization law invariant, expect_bind_of_finite]
  rw [← expect_constant (law.map (Option.map Prod.snd)) ((2 : ℝ) / 5)]
  apply expect_mono _ (payoffIntegrable_of_finite _ _) (payoffIntegrable_constant _ _)
  intro result _
  cases result with
  | none => rw [expect_pure]; norm_num
  | some answer =>
      rw [expect_map]
      cases answer with
      | failure =>
          change expect (PMF.uniformOfFintype (Fin 3)) (fun _ => (0 : ℝ)) ≤ 2 / 5
          rw [expect_constant]
          norm_num
      | success answer =>
          change expect (PMF.uniformOfFintype (Fin 3)) (fun label =>
            grossUtility reward ((false, label),
              publicOutcome program (finalState false label true answer true)) bob) ≤ 2 / 5
          rw [bob_uniform_success_value]
          split
          · exact le_rfl
          · split <;> norm_num

/-- The actual private label and final Bob publication when Alice has published
successfully. Missing states, missing fields and failed Alice publications stay None. -/
def successfulPublicationSummary (history : (E).History) :
    Option (Fin 3 × PublicationResult Answer) :=
  match history.state with
  | none => none
  | some control =>
      match control.execution.application.config.store (.inr aliceEvent),
          control.execution.application.config.store (.inr bobRevealEvent) with
      | some (.success _), some answer =>
          some (LateOpeningRuntimeLabelTrace.inputLabel
            control.execution.application.config.inputs, answer)
      | _, _ => none

/-- Gross successful-Alice readout extracted from the unchanged native state. -/
def successfulPublicationGross (reward : ℝ) (history : (E).History) : ℝ :=
  match successfulPublicationSummary horizon scheduler history with
  | none => 0
  | some (_, .failure) => 0
  | some (label, .success answer) => grossUtility reward ((false, label),
      publicOutcome program (finalState false label true answer true)) bob

private theorem successfulPublicationGross_nonnegative (reward : ℝ) (history : (E).History) :
    0 ≤ successfulPublicationGross horizon scheduler reward history := by
  unfold successfulPublicationGross
  cases successfulPublicationSummary horizon scheduler history with
  | none => exact le_rfl
  | some pair =>
      rcases pair with ⟨label, answer⟩
      cases answer with
      | failure => exact le_rfl
      | success answer => exact (bob_gross_bounds reward _).1

private theorem successfulPublicationSummary_permutation
    (permutation : Equiv.Perm (Fin 3)) (history : (E).History) :
    successfulPublicationSummary horizon scheduler
        (permuteHistory horizon scheduler permutation history) =
      Option.map (fun result => (permutation result.1, result.2))
        (successfulPublicationSummary horizon scheduler history) := by
  cases current : history.state with
  | none =>
      simp only [successfulPublicationSummary, permuteHistory,
        LateOpeningRuntimeLabelTrace.permuteProtocolState, current, Option.map_none]
  | some control =>
      simp only [successfulPublicationSummary, permuteHistory,
        LateOpeningRuntimeLabelTrace.permuteProtocolState, current, Option.map_some]
      change (match control.execution.application.config.store (.inr aliceEvent),
          control.execution.application.config.store (.inr bobRevealEvent) with
        | some (.success _), some answer =>
            some (LateOpeningRuntimeLabelTrace.inputLabel
              (LateOpeningRuntimeLabelTrace.permuteInputs permutation
                control.execution.application.config.inputs), answer)
        | _, _ => none) = _
      rw [LateOpeningRuntimeLabelTrace.inputLabel_permuted]
      cases control.execution.application.config.store (.inr aliceEvent) with
      | none => rfl
      | some result =>
          cases result with
          | failure => rfl
          | success published =>
              cases control.execution.application.config.store (.inr bobRevealEvent) <;> rfl

/-- Every actual whole-policy Bob continuation under the uniform-Alice reference
has successful-Alice gross value at most Safe's value. The bound is obtained from
its full history-orbit law; no independent terminal-label hypothesis is used. -/
theorem continuation_successful_gross_le_of_uniform_sequence
    (sequence : Nat → (M).BehavioralAssessment) (assessment : (M).BehavioralAssessment)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent (M)
      (sequence n) antichain)
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (uniformAlice : ∀ n, ((sequence n).strategy alice).AgreesAtDecisions
      (rawMenu.uniformPolicy initial horizon scheduler alice))
    (site : (M).InformationSite bob) (alternative : (M).BehavioralPolicy bob)
    (payoff : (E).History → ℝ) (reward : ℝ) :
    expect ((assessment.continuationContext
        (rawMenu.bounded initial horizon scheduler).wellFoundedHistories site payoff).outcome
          alternative)
      (successfulPublicationGross horizon scheduler reward) ≤ 2 / 5 := by
  let law := (assessment.continuationContext
    (rawMenu.bounded initial horizon scheduler).wellFoundedHistories site payoff).outcome
      alternative
  have invariant (permutation : Equiv.Perm (Fin 3)) :
      (law.map (successfulPublicationSummary horizon scheduler)).map
        (Option.map fun result => (permutation result.1, result.2)) =
          law.map (successfulPublicationSummary horizon scheduler) := by
    rw [PMF.map_comp]
    have functions : (Option.map (fun result => (permutation result.1, result.2))) ∘
        successfulPublicationSummary horizon scheduler =
      successfulPublicationSummary horizon scheduler ∘
        permuteHistory horizon scheduler permutation := by
      funext history
      exact (successfulPublicationSummary_permutation horizon scheduler permutation history).symm
    rw [functions, ← PMF.map_comp,
      continuation_law_permutation_of_uniform_sequence horizon scheduler sequence assessment
        mixed bayes converges uniformAlice site alternative payoff permutation]
  have bound := optional_publication_gross_le reward
    (law.map (successfulPublicationSummary horizon scheduler)) invariant
  rw [expect_map] at bound
  exact bound

/-- An already stored successful Alice publication persists under every actual
whole behavioral continuation. Initialization is not replayed after this prefix. -/
theorem terminal_alice_publication_persistent
    (profile : ∀ who, (M).BehavioralPolicy who) (history : (E).History)
    (control : app.Control) (current : history.state = some control) (publishedBit : Bool)
    (published : control.execution.application.config.store (.inr aliceEvent) =
      some (.success publishedBit : PublicationResult Bool)) :
    ∀ final ∈ ((M).runBehavioralTerminalFrom
      (rawMenu.bounded initial horizon scheduler).wellFoundedHistories profile history).support,
      ∃ finalControl, final.state = some finalControl ∧
        finalControl.execution.application.config.store (.inr aliceEvent) =
          some (.success publishedBit : PublicationResult Bool) := by
  let closed : app.ProtocolState → Prop := fun state =>
    ∃ actual, state = some actual ∧
      actual.execution.application.config.store (.inr aliceEvent) =
        some (.success publishedBit : PublicationResult Bool)
  have invariant := LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks
    (.inr aliceEvent) (.success publishedBit : PublicationResult Bool)
  apply (M).runBehavioralTerminalFrom_support_closed
    (rawMenu.bounded initial horizon scheduler).wellFoundedHistories profile closed
    ?_ history ⟨control, current, published⟩
  intro state joint _ target valid reached
  obtain ⟨before, rfl, stored⟩ := valid
  change target ∈ (app.transition initial horizon scheduler (some before) joint).support at reached
  rcases before with ⟨remaining, actor, execution⟩
  cases actor with
  | some who =>
      simp only [ReactiveApplication.transition, PMF.mem_support_pure_iff] at reached
      subst target
      exact ⟨_, rfl, invariant.respond execution who _ stored⟩
  | none =>
      cases remaining with
      | zero =>
          simp only [ReactiveApplication.transition, PMF.mem_support_pure_iff] at reached
          subst target
          exact ⟨_, rfl, stored⟩
      | succ remaining =>
          obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
          exact ⟨_, rfl, invariant.environmentStep execution next command stored supported⟩

/-- Successful public Alice output is determined on Bob's entire legal
information fiber, including fibers assigned zero probability by a profile. -/
theorem information_alice_publication
    (site : (M).InformationSite bob)
    (representative : (M).InformationHistory bob site.1)
    (control : app.Control) (current : representative.1.state = some control)
    (publishedBit : Bool)
    (published : control.execution.application.config.store (.inr aliceEvent) =
      some (.success publishedBit : PublicationResult Bool))
    (history : (M).InformationHistory bob site.1) :
    ∃ actual, history.1.state = some actual ∧
      actual.execution.application.config.store (.inr aliceEvent) =
        some (.success publishedBit : PublicationResult Bool) := by
  have active := InformationModel.InformationSite.active (M) site history
  obtain ⟨actual, currentHistory, _⟩ := app.control_of_active initial horizon scheduler
    (rawMenu.toRawHistory _ _ _ history.1) bob active
  change history.1.state = some actual at currentHistory
  have information := representative.2.trans history.2.symm
  change (rawMenu.signals _ _ _).infoOf bob representative.1.trace =
    (rawMenu.signals _ _ _).infoOf bob history.1.trace at information
  rw [rawMenu.info, rawMenu.info] at information
  change app.observe bob representative.1.state = app.observe bob history.1.state at information
  rw [current, currentHistory] at information
  have representativeActive := InformationModel.InformationSite.active (M) site representative
  change app.actor representative.1.state = some bob at representativeActive
  rw [current] at representativeActive
  change control.actor = some bob at representativeActive
  have actualActive := InformationModel.InformationSite.active (M) site history
  change app.actor history.1.state = some bob at actualActive
  rw [currentHistory] at actualActive
  change actual.actor = some bob at actualActive
  simp only [ReactiveApplication.observe, representativeActive, actualActive,
    ↓reduceIte] at information
  have sameView := congrArg Prod.snd (Option.some.inj information)
  change control.execution.observe app bob = actual.execution.observe app bob at sameView
  exact ⟨actual, currentHistory,
    (LateOpeningRuntimeBobBindingInformation.alice_result_same_view _ _ sameView).symm.trans
      published⟩

private theorem payoff_le_successful_publication_gross
    (history : (E).History) (control : app.Control) (current : history.state = some control)
    (publishedBit : Bool)
    (published : control.execution.application.config.store (.inr aliceEvent) =
      some (.success publishedBit : PublicationResult Bool))
    (reward forfeit : ℝ) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit bob)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) :
    LateOpeningRuntimeGame.payoff reward forfeit sample deposit history.state bob ≤
      successfulPublicationGross horizon scheduler reward history := by
  have deduction : 0 ≤ TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks sample) history.state bob *
        deposit bob := mul_nonneg (TerminalAudit.charge_mem_Icc _ _ _ _).1 depositNonnegative
  have baseUpper : LateOpeningRuntimeGame.payoff reward forfeit sample deposit history.state bob ≤
      LateOpeningRuntimeUtility.nativeBaseUtility reward forfeit history.state bob := by
    unfold LateOpeningRuntimeGame.payoff TerminalAudit.utility
    exact sub_le_self _ deduction
  by_cases completed : control.execution.application.config.cut.Terminal
  · have trace := current ▸ rawMenu.toRawTrace initial horizon scheduler history.trace
    obtain ⟨bit, label, valid⟩ := LateOpeningRuntimeReadout.history_initial_invariant
      LateOpeningRuntimeService.runtime leaks horizon scheduler control trace
    have labelEq : LateOpeningRuntimeLabelTrace.inputLabel
        control.execution.application.config.inputs = label := by
      rw [valid.reachable.inputs_eq]
      apply Fin.ext
      exact Int.toNat_natCast _
    obtain ⟨binding, bound⟩ := Option.isSome_iff_exists.mp
      (control.execution.application.config.store_available_of_terminal completed
        (.inr bobBindEvent))
    obtain ⟨publication, output⟩ := Option.isSome_iff_exists.mp
      (control.execution.application.config.store_available_of_terminal completed
        (.inr bobRevealEvent))
    have bitEq := LateOpeningRuntimeReadout.alice_success_from_initialized_bit
      control.execution.application bit label valid publishedBit published
    subst publishedBit
    have decoded := LateOpeningRuntimeReadout.decode_terminalStateOf
      control.execution.application bit label (.success bit) binding publication
      valid.reachable.inputs_eq published bound output
    have readout : serviceSourceReadout setup .sequential deadline leaks history.state =
        some (LateOpeningRuntimeReadout.terminalStateOf bit label (.success bit)
          binding publication) := by
      unfold serviceSourceReadout
      rw [current, Option.bind_some, ite_eq_left completed]
      exact decoded
    rw [LateOpeningRuntimeUtility.nativeBaseUtility_of_readout reward forfeit _ _ readout bob]
      at baseUpper
    cases publication with
    | failure =>
        rw [LateOpeningRuntimeUtility.sourceUtility_bob_failure] at baseUpper
        have grossZero : successfulPublicationGross horizon scheduler reward history = 0 := by
          simp only [successfulPublicationGross, successfulPublicationSummary, current,
            published, output]
        rw [grossZero]
        linarith
    | success answer =>
        have retained := LateOpeningRuntimeReadout.bob_success_from_binding
          control.execution.application _ valid.reachable answer output
        have bindingEq := Option.some.inj (bound.symm.trans retained)
        subst binding
        have terminalEq := LateOpeningRuntimeReadout.terminalStateOf_success bit label answer
        rw [terminalEq, LateOpeningRuntimeUtility.sourceUtility_success] at baseUpper
        have grossEq : successfulPublicationGross horizon scheduler reward history =
            grossUtility reward ((bit, label),
              publicOutcome program (finalState bit label true answer true)) bob := by
          simp only [successfulPublicationGross, successfulPublicationSummary, current,
            published, output, labelEq]
          rfl
        rw [grossEq]
        exact baseUpper
  · have baseZero : LateOpeningRuntimeUtility.nativeBaseUtility reward forfeit
        history.state bob = 0 := by
      unfold LateOpeningRuntimeUtility.nativeBaseUtility serviceBaseUtility serviceSourceReadout
      rw [current, Option.bind_some, ite_eq_right completed]
      rfl
    rw [baseZero] at baseUpper
    exact baseUpper.trans (successfulPublicationGross_nonnegative horizon scheduler reward history)

/-- With the actual successful public Alice output, every whole Bob deviation
has native audited value at most two fifths under the uniform-Alice reference.
Only nonnegative Bob deductions are dropped; the original beliefs and all future
opponent strategies remain in the actual continuation context. -/
theorem continuation_payoff_le_of_uniform_sequence
    (sequence : Nat → (M).BehavioralAssessment) (assessment : (M).BehavioralAssessment)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent (M)
      (sequence n) antichain)
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (uniformAlice : ∀ n, ((sequence n).strategy alice).AgreesAtDecisions
      (rawMenu.uniformPolicy initial horizon scheduler alice))
    (site : (M).InformationSite bob)
    (representative : (M).InformationHistory bob site.1)
    (control : app.Control) (current : representative.1.state = some control)
    (publishedBit : Bool)
    (published : control.execution.application.config.store (.inr aliceEvent) =
      some (.success publishedBit : PublicationResult Bool))
    (alternative : (M).BehavioralPolicy bob)
    (reward forfeit : ℝ) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit bob)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) :
    (assessment.continuationContext
      (rawMenu.bounded initial horizon scheduler).wellFoundedHistories site
        (fun history => LateOpeningRuntimeGame.payoff reward forfeit sample deposit
          history.state bob)).value alternative ≤ 2 / 5 := by
  let payoff := fun history : (E).History =>
    LateOpeningRuntimeGame.payoff reward forfeit sample deposit history.state bob
  let context := assessment.continuationContext
    (rawMenu.bounded initial horizon scheduler).wellFoundedHistories site payoff
  have actualIntegrable : PayoffIntegrable (context.outcome alternative) payoff :=
    payoffIntegrable_of_bounded _ _ (fun history =>
      LateOpeningRuntimeBobIncentive.payoff_bounded reward forfeit sample deposit history.state)
  have grossIntegrable : PayoffIntegrable (context.outcome alternative)
      (successfulPublicationGross horizon scheduler reward) := by
    apply payoffIntegrable_of_bounded _ _ (C := 1)
    intro history
    unfold successfulPublicationGross
    cases successfulPublicationSummary horizon scheduler history with
    | none => simp only [abs_zero, zero_le_one]
    | some pair =>
        rcases pair with ⟨label, publication⟩
        cases publication with
        | failure => simp only [abs_zero, zero_le_one]
        | success answer =>
            rw [abs_of_nonneg (bob_gross_bounds reward _).1]
            exact (bob_gross_bounds reward _).2
  change expect (context.outcome alternative) payoff ≤ 2 / 5
  calc
    _ ≤ expect (context.outcome alternative)
        (successfulPublicationGross horizon scheduler reward) := by
      apply expect_mono _ actualIntegrable grossIntegrable
      intro final supported
      change final ∈ ((assessment.belief bob site).bind fun history =>
        (M).runBehavioralTerminalFrom
          (rawMenu.bounded initial horizon scheduler).wellFoundedHistories
          (GameTheory.Profile.update (sig := (M).behavioralSignature)
            assessment.strategy bob alternative) history.1).support at supported
      obtain ⟨before, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      obtain ⟨beforeControl, beforeCurrent, beforePublished⟩ :=
        information_alice_publication horizon scheduler site representative control current
          publishedBit published before
      obtain ⟨finalControl, finalCurrent, finalPublished⟩ :=
        terminal_alice_publication_persistent horizon scheduler _ before.1 beforeControl
          beforeCurrent publishedBit beforePublished final reached
      exact payoff_le_successful_publication_gross horizon scheduler final finalControl
        finalCurrent publishedBit finalPublished reward forfeit forfeitNonnegative
          deposit depositNonnegative sample
    _ ≤ 2 / 5 := continuation_successful_gross_le_of_uniform_sequence horizon scheduler
      sequence assessment mixed bayes converges uniformAlice site alternative payoff reward

end Vegas.Examples.LateOpeningRuntimeLabelContinuation
