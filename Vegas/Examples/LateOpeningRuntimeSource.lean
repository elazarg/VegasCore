/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.IntendedPlay
import Vegas.Source.InitialState
import Vegas.Expr.Simple
import GameTheoryExtensions.Math.Probability.Uniform
import Vegas.Game.RevealService
import Vegas.Game.IntendedAuditedOutcome
import GameTheory.Analysis.Protocol.SequentialExistence
import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion

/-! # An immutable opening followed by a private answer

The initialized source has an Alice Boolean commitment and an independent
Alice-only label. Its three instructions publish that commitment, bind Bob's
answer, and publish that answer. The label is an ordinary private input and
has no publication obligation.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeSource

open SourceProgram GameTheory.Math.Probability GameTheory.Protocol

abbrev Player := Fin 2
abbrev alice : Player := 0
abbrev bob : Player := 1
abbrev Label := Val (.range 0 2)
abbrev Answer := Val (.range 0 5)
abbrev Parameter := Bool × Fin 3

def labelValue (label : Fin 3) : Label :=
  ⟨(label.val : Int), by have := label.isLt; constructor <;> omega⟩

def answerValue (answer : Fin 6) : Answer :=
  ⟨(answer.val : Int), by have := answer.isLt; constructor <;> omega⟩

abbrev safe : Answer := answerValue 0

def initialCtx : SourceCtx Player simpleExpr :=
  [(0, .commitment alice .bool), (1, .privateInput alice (.range 0 2))]

def answerGuard : SourceGuard simpleExpr ((2, .publication .bool) :: initialCtx)
    bob 3 (.range 0 5) where
  schema := []
  schemaNames := by decide
  subjectFresh := by decide
  code := .constBool true
  reads := fun cell => nomatch cell

def program : SourceProgram Player simpleExpr initialCtx {0} :=
  .reveal 2 alice 0 (by decide) .here (by decide) <|
  .commit 3 bob (by decide) answerGuard <|
  .reveal 4 bob 3 (by decide) .here (by decide) <|
  .ret []

def sourceInitial (bit : Bool) (label : Fin 3) : State simpleExpr initialCtx :=
  Env.cons (.success bit) <| Env.cons (labelValue label) <| Env.empty _

def bitLaw : PMF Bool :=
  mix (9 / 20) (by norm_num) (by norm_num) (PMF.pure true) (PMF.pure false)

def prior : PMF Parameter :=
  bitLaw.bind fun bit => (PMF.uniformOfFintype (Fin 3)).map fun label => (bit, label)

def setup : Setup (Player := Player) (L := simpleExpr) where
  context := initialCtx
  namesNodup := by decide
  initialLaw := prior.map fun parameter => sourceInitial parameter.1 parameter.2
  obligations := {0}
  program := program
  accounts := rfl

abbrev nativeGraph := graph setup
abbrev aliceEvent : nativeGraph.EventId := ⟨0, by decide⟩
abbrev bobBindEvent : nativeGraph.EventId := ⟨1, by decide⟩
abbrev bobRevealEvent : nativeGraph.EventId := ⟨2, by decide⟩

theorem native_actors : nativeGraph.actor? aliceEvent = some alice ∧
    nativeGraph.actor? bobBindEvent = some bob ∧
    nativeGraph.actor? bobRevealEvent = some bob := by
  exact ⟨rfl, rfl, rfl⟩

theorem sourceInitial_injective : Function.Injective
    (fun parameter : Parameter => sourceInitial parameter.1 parameter.2) := by
  rintro ⟨bit, label⟩ ⟨otherBit, otherLabel⟩ same
  have bits := congrArg (fun state : State simpleExpr initialCtx => state.get .here) same
  have labels := congrArg (fun state : State simpleExpr initialCtx =>
    (state.get (.there .here)).val) same
  have sameBit : bit = otherBit := PublicationResult.success.inj bits
  have sameLabel : label = otherLabel := by
    apply Fin.ext
    change (label.val : Int) = (otherLabel.val : Int) at labels
    exact_mod_cast labels
  simp [sameBit, sameLabel]

instance finiteInitial : setup.FiniteInitialLaw where
  support_finite := by
    change (prior.map (fun parameter => sourceInitial parameter.1 parameter.2)).support.Finite
    rw [PMF.support_map]
    exact (Set.toFinite prior.support).image _

theorem initialLaw_support (state : State simpleExpr initialCtx) :
    state ∈ setup.initialLaw.support ↔
      ∃ bit label, state = sourceInitial bit label := by
  change state ∈ (prior.map (fun parameter => sourceInitial parameter.1 parameter.2)).support ↔ _
  rw [PMF.support_map]
  constructor
  · rintro ⟨⟨bit, label⟩, _, rfl⟩
    exact ⟨bit, label, rfl⟩
  · rintro ⟨bit, label, rfl⟩
    refine ⟨(bit, label), ?_, rfl⟩
    simp only [prior, PMF.support_bind, Set.mem_iUnion]
    refine ⟨bit, ?_, ?_⟩
    · cases bit
      · exact mem_support_mix_right (9 / 20) (by norm_num) (by norm_num)
          (by norm_num) (μ := PMF.pure true) (ν := PMF.pure false)
          (a := false) (by simp)
      · exact mem_support_mix_left (9 / 20) (by norm_num) (by norm_num)
          (by norm_num) (μ := PMF.pure true) (ν := PMF.pure false)
          (a := true) (by simp)
    · rw [PMF.support_map]
      exact ⟨label, PMF.mem_support_uniformOfFintype label, rfl⟩

theorem answerGuard_predicts
    (observation : SourceObservation simpleExpr bob ((2, .publication .bool) :: initialCtx))
    (answer : Answer) : answerGuard.predicts observation answer = true := by
  rfl

theorem wellFormed : setup.WellFormed where
  initialValues := by
    intro initial supported name owner payload cell
    obtain ⟨bit, label, rfl⟩ := (initialLaw_support initial).mp supported
    cases cell with
    | here => exact ⟨bit, rfl⟩
    | there cell => cases cell with
      | there cell => cases cell
  guardsSatisfiable := by
    intro initial supported
    change (∃ answer, answerGuard.predicts _ answer = true) ∧ _
    exact ⟨⟨safe, answerGuard_predicts _ _⟩, fun _ _ => trivial⟩

theorem finiteBindingTypes : FiniteBindingTypes program := by
  exact ⟨inferInstance, trivial⟩

abbrev alicePublication : HasVar program.terminalCtx 2 (.publication .bool) :=
  .there (.there .here)

abbrev bobPublication : HasVar program.terminalCtx 4 (.publication (.range 0 5)) := .here

def finalState (bit : Bool) (label : Fin 3) (aliceOpens : Bool)
    (answer : Answer) (bobOpens : Bool) : State simpleExpr program.terminalCtx :=
  Env.cons (if bobOpens then .success answer else .failure) <|
  Env.cons (.success answer) <|
  Env.cons (if aliceOpens then .success bit else .failure) <|
  sourceInitial bit label

def constantProfile (aliceOpens : Bool) (answer : Answer) (bobOpens : Bool) :
    BehavioralProfile program := fun _ =>
  ⟨fun _ _ => PMF.pure aliceOpens,
    ⟨fun _ _ => PMF.pure (.success answer), ⟨fun _ _ => PMF.pure bobOpens, PUnit.unit⟩⟩⟩

def intendedProfile : BehavioralProfile program := constantProfile true safe true

theorem run_constant (bit : Bool) (label : Fin 3) (aliceOpens : Bool)
    (answer : Answer) (bobOpens : Bool) :
    SourceProgram.run program (constantProfile aliceOpens answer bobOpens)
      (sourceInitial bit label) =
      PMF.pure (finalState bit label aliceOpens answer bobOpens) := by
  simp only [SourceProgram.run, runWith, program, constantProfile,
    revealKernel, commitKernel, afterReveal, afterCommit, PMF.pure_bind]
  congr 1
  cases aliceOpens <;> cases bobOpens <;> rfl

theorem run_intended : setup.run intendedProfile =
    prior.map (fun parameter => finalState parameter.1 parameter.2 true safe true) := by
  change (prior.map (fun parameter => sourceInitial parameter.1 parameter.2)).bind
    (fun initial => SourceProgram.run program intendedProfile initial) = _
  rw [PMF.bind_map]
  simp only [Function.comp_def, intendedProfile, run_constant]
  rfl

def parameter (state : State simpleExpr initialCtx) : Parameter :=
  ((state.get .here).getD false,
    ⟨(state.get (.there .here)).val.toNat, by
      have lower := (state.get (.there .here)).property.1
      have upper := (state.get (.there .here)).property.2
      omega⟩)

@[simp] theorem parameter_sourceInitial (bit : Bool) (label : Fin 3) :
    parameter (sourceInitial bit label) = (bit, label) := by
  apply Prod.ext
  · rfl
  · apply Fin.ext
    exact Int.toNat_natCast label.val

def aliceResult (outcome : PublicOutcome program) : PublicationResult Bool :=
  outcome.get (.there .here)

def bobResult (outcome : PublicOutcome program) : PublicationResult Answer :=
  outcome.get .here

def grossUtility (reward : ℝ) (result : Parameter × PublicOutcome program)
    (who : Player) : ℝ :=
  match bobResult result.2 with
  | .failure => 0
  | .success answer =>
      if who = alice then
        if (aliceResult result.2).isSuccess then
          if answer.val = 0 then reward / 2
          else if 1 ≤ answer.val ∧ answer.val ≤ 3 ∧ result.1.2.val < 2 then reward else 0
        else if (result.1.2.val = 0 ∧ answer.val = 5) ∨
            (result.1.2.val = 1 ∧ answer.val = 4) then reward else 0
      else if (aliceResult result.2).isSuccess then
        if answer.val = 0 then 2 / 5
        else if answer.val = (result.1.2.val : Int) + 1 then 1 else 0
      else if answer.val = (if result.1.1 then 5 else 4) then 1 else 0

theorem intended_gross (reward : ℝ) (bit : Bool) (label : Fin 3) :
    grossUtility reward ((bit, label),
      publicOutcome program (finalState bit label true safe true)) alice = reward / 2 ∧
    grossUtility reward ((bit, label),
      publicOutcome program (finalState bit label true safe true)) bob = 2 / 5 := by
  constructor <;> rfl

theorem alice_gross_bounds {reward : ℝ} (nonnegative : 0 ≤ reward)
    (result : Parameter × PublicOutcome program) :
    0 ≤ grossUtility reward result alice ∧ grossUtility reward result alice ≤ reward := by
  unfold grossUtility
  split
  · exact ⟨le_rfl, nonnegative⟩
  · simp only [ite_true]
    split
    · split
      · constructor <;> linarith
      · split <;> simp_all
    · split <;> simp_all

theorem bob_gross_bounds (reward : ℝ) (result : Parameter × PublicOutcome program) :
    0 ≤ grossUtility reward result bob ∧ grossUtility reward result bob ≤ 1 := by
  unfold grossUtility
  split
  · norm_num
  · simp only [show bob ≠ alice by decide, ite_false]
    split
    · split
      · norm_num
      · split <;> norm_num
    · cases result.1.1 <;> simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals split <;> norm_num

theorem bob_success_gross (reward : ℝ) (bit : Bool) (label : Fin 3) (answer : Answer) :
    grossUtility reward ((bit, label),
      publicOutcome program (finalState bit label true answer true)) bob =
        if answer.val = 0 then 2 / 5
        else if answer.val = (label.val : Int) + 1 then 1 else 0 := by
  rfl

/-- Conditional on either published bit, every label guess is worth one third. -/
theorem bob_uniform_success_value (reward : ℝ) (bit : Bool) (answer : Answer) :
    expect (PMF.uniformOfFintype (Fin 3)) (fun label =>
      grossUtility reward ((bit, label),
        publicOutcome program (finalState bit label true answer true)) bob) =
      if answer.val = 0 then 2 / 5
      else if 1 ≤ answer.val ∧ answer.val ≤ 3 then 1 / 3 else 0 := by
  rw [expect_uniformFin]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((if answer.val = 0 then (2 : ℝ) / 5 else if answer.val = 1 then 1 else 0) +
    ((if answer.val = 0 then (2 : ℝ) / 5 else if answer.val = 2 then 1 else 0) +
      (if answer.val = 0 then (2 : ℝ) / 5 else if answer.val = 3 then 1 else 0))) / 3 = _
  have lower := answer.property.1
  have upper := answer.property.2
  have cases : answer.val = 0 ∨ answer.val = 1 ∨ answer.val = 2 ∨
      answer.val = 3 ∨ answer.val = 4 ∨ answer.val = 5 := by omega
  rcases cases with value | value | value | value | value | value <;>
    norm_num [value]

theorem bob_safe_strictly_best (reward : ℝ) (bit : Bool) (answer : Answer)
    (different : answer ≠ safe) :
    expect (PMF.uniformOfFintype (Fin 3)) (fun label =>
      grossUtility reward ((bit, label),
        publicOutcome program (finalState bit label true answer true)) bob) < 2 / 5 := by
  rw [bob_uniform_success_value]
  have nonzero : answer.val ≠ 0 := by
    intro zero
    apply different
    exact Subtype.ext zero
  rw [ite_eq_right nonzero]
  split <;> norm_num

theorem intended_forfeit (reward forfeit : ℝ) (bit : Bool) (label : Fin 3) :
    forfeitUtility program forfeit (grossUtility reward)
      ((bit, label), publicOutcome program (finalState bit label true safe true)) alice =
        reward / 2 ∧
    forfeitUtility program forfeit (grossUtility reward)
      ((bit, label), publicOutcome program (finalState bit label true safe true)) bob =
        2 / 5 := by
  have success : Successful (finalState bit label true safe true) := by
    constructor
    · intro name owner payload cell
      cases cell with
      | there cell => cases cell with
        | here => exact ⟨safe, rfl⟩
        | there cell => cases cell with
          | there cell => cases cell with
            | here => exact ⟨bit, rfl⟩
            | there cell => cases cell with
              | there cell => cases cell
    · intro name payload cell
      cases cell with
      | here => exact ⟨safe, rfl⟩
      | there cell => cases cell with
        | there cell => cases cell with
          | here => exact ⟨bit, rfl⟩
          | there cell => cases cell with
            | there cell => cases cell with
              | there cell => cases cell
  rw [forfeitUtility_of_successful program forfeit (grossUtility reward) _ _ success alice,
    forfeitUtility_of_successful program forfeit (grossUtility reward) _ _ success bob]
  exact intended_gross reward bit label

def intendedFallbackAction (who : Player) (view : setup.ProtocolView who) :
    Option (OwnAction Player simpleExpr) :=
  match view with
  | none => none
  | some (.inl _) => if alice = who then some (.reveal alice 0 true) else none
  | some (.inr (.inl _)) =>
      if bob = who then some (.commit bob 3 (.range 0 5) (.success safe)) else none
  | some (.inr (.inr (.inl _))) =>
      if bob = who then some (.reveal bob 3 true) else none
  | some (.inr (.inr (.inr _))) => none

theorem intendedFallbackAction_mem (who : Player) (view : setup.ProtocolView who) :
    intendedFallbackAction who view ∈ setup.intendedMenu who view := by
  cases view with
  | none => rfl
  | some view =>
      cases view with
      | inl observed =>
          by_cases same : alice = who
          · subst who
            simp only [intendedFallbackAction, ↓reduceIte]
            change some alice = some alice ∧ OwnAction.reveal alice 0 true ∈
              ({OwnAction.reveal alice 0 true} : Set (OwnAction Player simpleExpr))
            exact ⟨rfl, rfl⟩
          · simp only [intendedFallbackAction, same, ↓reduceIte]
            change some alice ≠ some who
            exact fun equality => same (Option.some.inj equality)
      | inr view =>
          cases view with
          | inl observed =>
              by_cases same : bob = who
              · subst who
                simp only [intendedFallbackAction, ↓reduceIte]
                change some bob = some bob ∧ ∃ value ∈ intendedValues bob answerGuard observed.1,
                  (OwnAction.commit bob 3 (BaseTy.range 0 5) (.success safe) :
                    OwnAction Player simpleExpr) =
                    OwnAction.commit bob 3 (BaseTy.range 0 5) (.success value)
                exact ⟨rfl, safe, Or.inl (fun _ => rfl), rfl⟩
              · simp only [intendedFallbackAction, same, ↓reduceIte]
                change some bob ≠ some who
                exact fun equality => same (Option.some.inj equality)
          | inr view =>
              cases view with
              | inl observed =>
                  by_cases same : bob = who
                  · subst who
                    simp only [intendedFallbackAction, ↓reduceIte]
                    change some bob = some bob ∧ OwnAction.reveal bob 3 true ∈
                      ({OwnAction.reveal bob 3 true} : Set (OwnAction Player simpleExpr))
                    exact ⟨rfl, rfl⟩
                  · simp only [intendedFallbackAction, same, ↓reduceIte]
                    change some bob ≠ some who
                    exact fun equality => same (Option.some.inj equality)
              | inr observed =>
                  change none ≠ some who
                  intro equality
                  cases equality

def intendedFallback (who : Player) : setup.intendedModel.Policy who :=
  fun view => ⟨intendedFallbackAction who view, intendedFallbackAction_mem who view⟩

theorem intended_decisionRecall : setup.intendedModel.DecisionRecall :=
  setup.intendedModel.decisionRecall_of_perfectRecall
    ((setup.informationModel _).restrictMenu_perfectRecall _ _
      (setup.protocol_perfectRecall _))

def intendedPayoff (reward : ℝ) (who : Player)
    (history : setup.intendedProtocol.History) : ℝ :=
  (setup.protocolReadout history.state).elim 0 (fun terminal =>
    grossUtility reward (setup.parameterOutcome parameter terminal) who)

/-- The actual initialized three-instruction source game has a sequential
equilibrium under its intended mandatory-publication interface. -/
theorem exists_intended_sequential_equilibrium (reward : ℝ) :
    ∃ assessment : setup.intendedModel.BehavioralAssessment,
      assessment.IsSequentialEquilibrium intended_decisionRecall.decisionInformationAntichain
        setup.intended_bounded.wellFoundedHistories (intendedPayoff reward) := by
  have : Finite setup.intendedProtocol.History := setup.intended_finite_history finiteBindingTypes
  obtain ⟨assessment, rational, consistent⟩ :=
    setup.intendedModel.exists_sequentialEquilibrium intended_decisionRecall intendedFallback
      (intendedPayoff reward) setup.intended_bounded.wellFoundedHistories
  exact ⟨assessment, rational, consistent⟩

def intendedUniformProfile : ∀ who, setup.intendedModel.BehavioralPolicy who := by
  classical
  have : Finite setup.intendedProtocol.History := setup.intended_finite_history finiteBindingTypes
  intro who info
  by_cases decision : setup.intendedModel.IsDecisionInfo who info
  · have : Finite (setup.intendedModel.Choice who
        (⟨info, decision⟩ : setup.intendedModel.InformationSite who).1) :=
      InformationModel.InformationSite.finite_choice setup.intendedModel who ⟨info, decision⟩
    letI : Fintype (setup.intendedModel.Choice who info) := Fintype.ofFinite _
    letI : Nonempty (setup.intendedModel.Choice who info) := ⟨intendedFallback who info⟩
    exact PMF.uniformOfFintype _
  · exact PMF.pure (intendedFallback who info)

theorem intendedUniformProfile_mixed
    (who : Player) (site : setup.intendedModel.InformationSite who)
    (choice : setup.intendedModel.Choice who site.1) :
    choice ∈ (intendedUniformProfile who site.1).support := by
  classical
  have : Finite setup.intendedProtocol.History := setup.intended_finite_history finiteBindingTypes
  have : Finite (setup.intendedModel.Choice who site.1) :=
    InformationModel.InformationSite.finite_choice setup.intendedModel who site
  let : Fintype (setup.intendedModel.Choice who site.1) := Fintype.ofFinite _
  let : Nonempty (setup.intendedModel.Choice who site.1) := ⟨intendedFallback who site.1⟩
  unfold intendedUniformProfile
  rw [dite_eq_left site.2]
  exact PMF.mem_support_uniformOfFintype choice

/-- The prescribed safe policy has a belief completion satisfying the common
fully mixed limiting requirement. Rationality is a separate obligation. -/
theorem exists_consistent_safe_assessment :
    ∃ assessment : setup.intendedModel.BehavioralAssessment,
      assessment.strategy = (fun who info => PMF.pure (intendedFallback who info)) ∧
      assessment.IsSequentiallyConsistent intended_decisionRecall.decisionInformationAntichain := by
  have : Finite setup.intendedProtocol.History := setup.intended_finite_history finiteBindingTypes
  exact InformationModel.BehavioralAssessment.exists_consistent_completion
    (InformationModel.BehavioralAssessment.ofStrategy intendedUniformProfile)
    intendedUniformProfile_mixed intended_decisionRecall.decisionInformationAntichain _

def afterAliceState (bit : Bool) (label : Fin 3) :
    State simpleExpr ((2, .publication .bool) :: initialCtx) :=
  Env.cons (.success bit) (sourceInitial bit label)

theorem bob_afterAlice_observation (bit : Bool) (label other : Fin 3) :
    sourceObserve bob (afterAliceState bit label) =
      sourceObserve bob (afterAliceState bit other) := by
  apply congrArg SourceObservation.mk
  funext name cell member
  cases member with
  | here => rfl
  | there member => cases member with
    | here => rfl
    | there member => cases member with
      | here => rfl
      | there member => cases member

def randomizedAnswerProfile (answers : Bool → PMF Answer) : BehavioralProfile program :=
  fun _ => ⟨fun _ _ => PMF.pure true,
    ⟨fun _ view => (answers ((view.1.cells.get .here).getD false)).map PublicationResult.success,
      ⟨fun _ _ => PMF.pure true, PUnit.unit⟩⟩⟩

theorem run_randomizedAnswer (answers : Bool → PMF Answer) (bit : Bool) (label : Fin 3) :
    SourceProgram.run program (randomizedAnswerProfile answers) (sourceInitial bit label) =
      (answers bit).map (fun answer => finalState bit label true answer true) := by
  simp only [SourceProgram.run, runWith, program, randomizedAnswerProfile,
    revealKernel, commitKernel, afterReveal, afterCommit, PMF.pure_bind]
  change ((answers bit).map PublicationResult.success).bind _ = _
  rw [PMF.bind_map]
  change (answers bit).bind _ = (answers bit).bind _
  congr 1

def drawnState (bit : Bool) (label : Fin 3) : setup.ProtocolState :=
  some (.inl (setup.initialConfig (sourceInitial bit label)))

def openedState (bit : Bool) (label : Fin 3) : setup.ProtocolState :=
  some (.inr (.inl (revealSuccessor 2 .here
    (setup.initialConfig (sourceInitial bit label)) true)))

private theorem initialJointLegal : setup.intendedProtocol.Legal none (fun _ => none) := by
  change ¬ False ∧ ∀ _ : Player, ¬ False
  exact ⟨not_false, fun _ => not_false⟩

private theorem initialDraw_supported (bit : Bool) (label : Fin 3) :
    drawnState bit label ∈
      (setup.intendedProtocol.step none ⟨fun _ => none, initialJointLegal⟩).support := by
  change drawnState bit label ∈
    (setup.initialLaw.map (fun initial => some (ProtocolState.entry program
      (setup.initialConfig initial)))).support
  rw [PMF.support_map]
  exact ⟨sourceInitial bit label, (initialLaw_support _).mpr ⟨bit, label, rfl⟩, rfl⟩

def drawnHistory (bit : Bool) (label : Fin 3) : setup.intendedProtocol.History :=
  setup.intendedProtocol.initHistory.extend initialJointLegal (initialDraw_supported bit label)

private def aliceJoint (who : Player) : Option (OwnAction Player simpleExpr) :=
  if who = alice then some (.reveal alice 0 true) else none

private theorem aliceJointLegal (bit : Bool) (label : Fin 3) :
    setup.intendedProtocol.Legal (drawnState bit label) aliceJoint := by
  refine ⟨?_, ?_⟩
  · change ¬ False
    exact not_false
  · intro who
    fin_cases who
    · change some alice = some alice ∧
        OwnAction.reveal alice 0 true ∈ ({OwnAction.reveal alice 0 true} :
          Set (OwnAction Player simpleExpr))
      exact ⟨rfl, rfl⟩
    · change some alice ≠ some bob
      decide

private theorem opening_supported (bit : Bool) (label : Fin 3) :
    openedState bit label ∈
      (setup.intendedProtocol.step (drawnState bit label)
        ⟨aliceJoint, aliceJointLegal bit label⟩).support := by
  change openedState bit label ∈
    ((PMF.pure (Sum.inr (Sum.inl (revealSuccessor 2 .here
      (setup.initialConfig (sourceInitial bit label)) true)) : ProtocolState program)).map
        some).support
  rw [PMF.pure_map]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

def openedHistory (bit : Bool) (label : Fin 3) : setup.intendedProtocol.History :=
  (drawnHistory bit label).extend (aliceJointLegal bit label) (opening_supported bit label)

def bobBindingInfo (bit : Bool) : setup.ProtocolView bob :=
  some (.inr (.inl (sourceObserve bob (afterAliceState bit 0), [])))

theorem bobBindingInfo_opened (bit : Bool) (label : Fin 3) :
    setup.intendedModel.infoOf bob (openedHistory bit label).trace = bobBindingInfo bit := by
  refine (setup.intended_info bob (openedHistory bit label).trace).trans ?_
  change some (Sum.inr (Sum.inl (sourceObserve bob (afterAliceState bit label), []))) = _
  rw [bob_afterAlice_observation bit label 0]
  rfl

theorem bobBindingInfo_state
    {bit : Bool} (history : setup.intendedModel.InformationHistory bob (bobBindingInfo bit)) :
    ∃ config, history.1.state = some (.inr (.inl config)) := by
  have observed := (setup.intended_info bob history.1.trace).symm.trans history.2
  rcases history with ⟨⟨state, trace⟩, member⟩
  cases state with
  | none => change none = some _ at observed; cases observed
  | some state =>
      cases state with
      | inl config => change some (Sum.inl _) = some (Sum.inr _) at observed; cases observed
      | inr state =>
          cases state with
          | inl config => exact ⟨config, rfl⟩
          | inr state =>
              change some (Sum.inr (Sum.inr _)) = some (Sum.inr (Sum.inl _)) at observed
              cases observed

theorem bobBindingInfo_length
    {bit : Bool} (history : setup.intendedModel.InformationHistory bob (bobBindingInfo bit)) :
    history.1.trace.length = 2 := by
  obtain ⟨config, state⟩ := bobBindingInfo_state history
  have count := setup.protocol_history_length (CommitmentInterface.values program)
    (setup.intendedRestriction.history history.1).trace
  rw [setup.intendedRestriction.length history.1] at count
  have remaining :
      setup.protocolRemaining (setup.intendedRestriction.history history.1).state = 2 :=
    (congrArg setup.protocolRemaining state).trans rfl
  rw [remaining] at count
  change history.1.trace.length + 2 = 4 at count
  omega

private theorem alice_choice_drawn (bit : Bool) (label : Fin 3)
    (choice : setup.intendedModel.Choice alice
      (setup.intendedModel.infoOf alice (drawnHistory bit label).trace)) :
    choice.val = some (.reveal alice 0 true) := by
  have allowed := choice.property
  cases value : choice.val with
  | none =>
      rw [value] at allowed
      change some alice ≠ some alice at allowed
      exact (allowed rfl).elim
  | some action =>
      rw [value] at allowed
      change some alice = some alice ∧
        action ∈ ({OwnAction.reveal alice 0 true} : Set (OwnAction Player simpleExpr)) at allowed
      exact congrArg some allowed.2

private theorem alice_joint_drawn
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) (bit : Bool) (label : Fin 3) :
    setup.intendedModel.behavioralJoint profile (drawnHistory bit label).trace
      (aliceJointLegal bit label).1 =
      PMF.pure ⟨aliceJoint, aliceJointLegal bit label⟩ := by
  classical
  have unique (who : Player) (acts : setup.intendedProtocol.active (drawnState bit label) who) :
      who = alice := by
    change some alice = some who at acts
    exact (Option.some.inj acts).symm
  rw [setup.intendedModel.behavioralJoint_eq_map_of_at_most_one_active profile
    (drawnHistory bit label).trace (aliceJointLegal bit label).1 alice unique]
  apply pmf_eq_pure_of_support_subset_singleton
  intro draw supported
  rw [PMF.support_map] at supported
  obtain ⟨choice, _, rfl⟩ := supported
  apply Subtype.ext
  funext who
  change setup.intendedProtocol.singletonJoint alice choice.val who = aliceJoint who
  by_cases same : who = alice
  · subst who
    simp only [ExecutionProtocol.singletonJoint, ↓reduceDIte]
    exact alice_choice_drawn bit label choice
  · simp [ExecutionProtocol.singletonJoint, same, aliceJoint]

private theorem opening_round
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) (bit : Bool) (label : Fin 3) :
    setup.intendedModel.runBehavioralFrom profile 1 (drawnHistory bit label) =
      PMF.pure (openedHistory bit label) := by
  rw [setup.intendedModel.runBehavioralFrom_succ_of_not_terminal profile 0
      (aliceJointLegal bit label).1,
    alice_joint_drawn, PMF.pure_bind]
  have step : setup.intendedProtocol.step (drawnHistory bit label).state
      ⟨aliceJoint, aliceJointLegal bit label⟩ = PMF.pure (openedState bit label) := by
    change (PMF.pure (Sum.inr (Sum.inl (revealSuccessor 2 .here
      (setup.initialConfig (sourceInitial bit label)) true)) : ProtocolState program)).map some = _
    rw [PMF.pure_map]
    rfl
  apply pmf_eq_pure_of_support_subset_singleton
  intro final supported
  simp only [PMF.support_bindOnSupport, Set.mem_iUnion] at supported
  obtain ⟨target, realized, supported⟩ := supported
  have targetEq : target = openedState bit label :=
    (PMF.mem_support_pure_iff _ _).mp (step ▸ realized)
  subst target
  change final ∈ (PMF.pure (openedHistory bit label)).support at supported
  exact (PMF.mem_support_pure_iff _ _).mp supported

/-- Before Bob's binding, initialized types have their original law under
every intended behavioral strategy. There has been no discretionary action. -/
theorem opening_prefix
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    setup.intendedModel.runBehavioral profile 2 =
      prior.map (fun parameter => openedHistory parameter.1 parameter.2) := by
  have transition : setup.intendedProtocol.step setup.intendedProtocol.init
      ⟨fun _ => none, initialJointLegal⟩ =
      prior.map (fun parameter => drawnState parameter.1 parameter.2) := by
    change (prior.map (fun parameter => sourceInitial parameter.1 parameter.2)).map _ = _
    rw [PMF.map_comp]
    rfl
  change setup.intendedModel.runBehavioralFrom profile (1 + 1)
    setup.intendedProtocol.initHistory = _
  rw [setup.intendedModel.runBehavioralFrom_succ_of_not_terminal profile 1 initialJointLegal.1,
    setup.intendedModel.behavioralJoint_eq_pure_of_no_active profile
      setup.intendedProtocol.initHistory.trace initialJointLegal.1
      (fun _ => not_false), PMF.pure_bind]
  let continuation (target : setup.intendedProtocol.State)
      (supported : target ∈
        (prior.map (fun parameter => drawnState parameter.1 parameter.2)).support) :=
    setup.intendedModel.runBehavioralFrom profile 1
      (setup.intendedProtocol.initHistory.extend initialJointLegal (transition.symm ▸ supported))
  refine (bindOnSupport_congr_measure transition _ continuation
    (fun _ _ _ => rfl)).trans ?_
  rw [bindOnSupport_map]
  change prior.bindOnSupport (fun parameter _ => setup.intendedModel.runBehavioralFrom profile 1
    (drawnHistory parameter.1 parameter.2)) = _
  simp only [opening_round]
  exact PMF.bindOnSupport_eq_bind prior _

theorem openedHistory_injective : Function.Injective
    (fun parameter : Parameter => openedHistory parameter.1 parameter.2) := by
  intro first second same
  have states := congrArg ExecutionProtocol.History.state same
  have initialEq : sourceInitial first.1 first.2 = sourceInitial second.1 second.2 := by
    have configs := Sum.inl.inj (Sum.inr.inj (Option.some.inj states))
    have envs := congrArg (fun config => config.state) configs
    change Env.cons (Val := CellVal (Player := Player) simpleExpr)
        (x := 2) (τ := .publication .bool) (.success first.1)
        (sourceInitial first.1 first.2) =
      Env.cons (Val := CellVal (Player := Player) simpleExpr)
        (x := 2) (τ := .publication .bool) (.success second.1)
        (sourceInitial second.1 second.2) at envs
    funext name cell member
    exact congrArg (fun state => state.get (.there member)) envs
  exact sourceInitial_injective initialEq

def bobBindingSite (bit : Bool) : setup.intendedModel.InformationSite bob :=
  ⟨bobBindingInfo bit, by
    refine ⟨⟨openedHistory bit 0, bobBindingInfo_opened bit 0⟩, ?_,
      OwnAction.commit bob 3 (.range 0 5) (.success safe), ?_⟩
    · change ¬ False
      exact not_false
    · change some bob = some bob ∧ ∃ value ∈ intendedValues bob answerGuard _,
        (OwnAction.commit bob 3 (BaseTy.range 0 5) (.success safe) :
          OwnAction Player simpleExpr) =
          OwnAction.commit bob 3 (BaseTy.range 0 5) (.success value)
      exact ⟨rfl, safe, Or.inl (fun _ => rfl), rfl⟩⟩

end Vegas.Examples.LateOpeningRuntimeSource
