/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.IntendedAuditedOutcome
import Vegas.Source.InitialState
import Vegas.Source.SetupProtocolBehavioral
import Vegas.Expr.Simple
import GameTheory.Analysis.Protocol.SequentialExistence

/-! # A hidden immutable bit and two Boolean commitments

Bob's private input remains in the terminal context and is never published.
Alice commits a guess, Bob commits a helper value, and both publications are
mandatory in the honest source game. Utilities retain the true input jointly
with the public result.
-/

noncomputable section

namespace Vegas.Examples.CommitTimingInformation

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

abbrev Player := Fin 2
abbrev alice : Player := 0
abbrev bob : Player := 1

def initialCtx : SourceCtx Player simpleExpr := [(0, .privateInput bob .bool)]

def acceptGuard {Γ : SourceCtx Player simpleExpr} (who : Player) (name : VarId) :
    SourceGuard simpleExpr Γ who name .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by simp
  code := .constBool true
  reads := fun cell => nomatch cell

def program : SourceProgram Player simpleExpr initialCtx ∅ :=
  .commit 1 alice (by decide) (acceptGuard alice 1) <|
  .commit 2 bob (by decide) (acceptGuard bob 2) <|
  .reveal 3 alice 1 (by decide) (.there .here) (by decide) <|
  .reveal 4 bob 2 (by decide) (.there .here) (by decide) <|
  .ret []

def sourceInitial (bit : Bool) : State simpleExpr initialCtx :=
  Env.cons bit (Env.empty (CellVal simpleExpr))

def initialParameter (state : State simpleExpr initialCtx) : Bool := state.get .here

def bitLaw : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure false) (PMF.pure true)

def setup : Setup (Player := Player) (L := simpleExpr) where
  context := initialCtx
  namesNodup := by decide
  initialLaw := bitLaw.map sourceInitial
  obligations := ∅
  program := program
  accounts := rfl
  exitTransfers := fun _ => 0

@[simp] theorem initialParameter_sourceInitial (bit : Bool) :
    initialParameter (sourceInitial bit) = bit := rfl

theorem sourceInitial_injective : Function.Injective sourceInitial := by
  intro first second same
  exact congrArg initialParameter same

theorem bitLaw_fullSupport (bit : Bool) : bit ∈ bitLaw.support := by
  cases bit
  · exact mem_support_mix_left (1 / 2) (by norm_num) (by norm_num) (by norm_num)
      (μ := PMF.pure false) (ν := PMF.pure true) (a := false) (by simp)
  · exact mem_support_mix_right (1 / 2) (by norm_num) (by norm_num) (by norm_num)
      (μ := PMF.pure false) (ν := PMF.pure true) (a := true) (by simp)

instance finiteInitial : setup.FiniteInitialLaw where
  support_finite := by
    change (bitLaw.map sourceInitial).support.Finite
    rw [PMF.support_map]
    exact (Set.toFinite bitLaw.support).image sourceInitial

theorem initialLaw_support (state : State simpleExpr initialCtx) :
    state ∈ setup.initialLaw.support ↔ ∃ bit, state = sourceInitial bit := by
  change state ∈ (bitLaw.map sourceInitial).support ↔ _
  rw [PMF.support_map]
  constructor
  · rintro ⟨bit, _, rfl⟩
    exact ⟨bit, rfl⟩
  · rintro ⟨bit, rfl⟩
    exact ⟨bit, bitLaw_fullSupport bit, rfl⟩

theorem alice_initial_observation (first second : Bool) :
    sourceObserve alice (sourceInitial first) = sourceObserve alice (sourceInitial second) := by
  apply congrArg SourceObservation.mk
  funext name cell member
  cases member with
  | here => rfl
  | there member => cases member

theorem bob_initial_observation (bit : Bool) :
    (sourceObserve bob (sourceInitial bit)).cells.get .here = some bit := rfl

theorem wellFormed : setup.WellFormed where
  initialValues := by
    intro initial _ name owner payload cell
    cases cell with
    | there cell => cases cell
  guardsSatisfiable := by
    intro initial _
    exact ⟨⟨true, rfl⟩, fun _ _ => ⟨⟨true, rfl⟩, fun _ _ => trivial⟩⟩

theorem finiteBindingTypes : program.FiniteBindingTypes :=
  ⟨inferInstance, inferInstance, trivial⟩

abbrev graph := serviceGraph setup .concurrentReveals

def bindingEvent (owner : Player) : graph.EventId :=
  ⟨owner.val, by have bound := owner.isLt; change owner.val < 4; omega⟩

def revealEvent (owner : Player) : graph.EventId :=
  ⟨owner.val + 2, by have bound := owner.isLt; change owner.val + 2 < 4; omega⟩

theorem event_count : Vegas.eventCount program = 4 := rfl

theorem bindingEvent_layout (owner : Player) :
    graph.layout (.inr (bindingEvent owner)) = .binding owner .bool := by
  fin_cases owner <;> rfl

theorem revealEvent_layout (owner : Player) :
    graph.layout (.inr (revealEvent owner)) = .publication .bool := by
  fin_cases owner <;> rfl

theorem bindingEvent_actor (owner : Player) : graph.actor? (bindingEvent owner) = some owner := by
  fin_cases owner <;> rfl

theorem revealEvent_actor (owner : Player) : graph.actor? (revealEvent owner) = some owner := by
  fin_cases owner <;> rfl

abbrev alicePublication : HasVar program.terminalCtx 3 (.publication .bool) := .there .here

abbrev retainedPrivateBit : HasVar program.terminalCtx 0 (.privateInput bob .bool) :=
  .there (.there (.there (.there .here)))

def terminalParameter (terminal : State simpleExpr program.terminalCtx) : Bool :=
  terminal.get retainedPrivateBit

def utility (terminal : State simpleExpr program.terminalCtx) (who : Player) : ℝ :=
  if who = alice then
    match terminal.get alicePublication with
    | .failure => 0
    | .success guess => if guess = terminalParameter terminal then 1 else 0
  else
    (if terminalParameter terminal then -1 else 1) *
      (if 0 < failedReveals program alice (publicOutcome program terminal) then 1 else 0)

theorem terminalParameter_initialState (terminal : State simpleExpr program.terminalCtx) :
    terminalParameter terminal = initialParameter (initialState program terminal) := rfl

theorem alice_utility_bounds (terminal : State simpleExpr program.terminalCtx) :
    utility terminal alice ∈ Set.Icc (0 : ℝ) 1 := by
  cases result : terminal.get alicePublication with
  | failure => norm_num [utility, result]
  | success guess =>
      by_cases same : guess = terminalParameter terminal <;> norm_num [utility, result, same]

theorem bob_utility_bounds (terminal : State simpleExpr program.terminalCtx) :
    utility terminal bob ∈ Set.Icc (-1 : ℝ) 1 := by
  change (if terminalParameter terminal then (-1 : ℝ) else 1) *
    (if 0 < failedReveals program alice (publicOutcome program terminal) then 1 else 0) ∈ _
  split <;> split <;> norm_num

def finalState (bit guess helper : Bool) : State simpleExpr program.terminalCtx :=
  Env.cons (.success helper) <| Env.cons (.success guess) <|
    Env.cons (.success helper) <| Env.cons (.success guess) <| sourceInitial bit

def constantProfile (guess helper : Bool) : BehavioralProfile program := fun _ =>
  ⟨fun _ _ => PMF.pure (.success guess),
    ⟨fun _ _ => PMF.pure (.success helper),
      ⟨fun _ _ => PMF.pure true, ⟨fun _ _ => PMF.pure true, PUnit.unit⟩⟩⟩⟩

theorem run_constant (bit guess helper : Bool) :
    program.run (constantProfile guess helper) (sourceInitial bit) =
      PMF.pure (finalState bit guess helper) := by
  simp only [SourceProgram.run, program, constantProfile, sourceInitial, runWith,
    commitKernel, revealKernel, afterCommit, afterReveal, PMF.pure_bind]
  rfl

theorem utility_finalState (bit guess helper : Bool) :
    utility (finalState bit guess helper) alice = (if guess = bit then 1 else 0) ∧
      utility (finalState bit guess helper) bob = 0 := by
  constructor
  · rfl
  · change (if bit then (-1 : ℝ) else 1) * (if 0 < 0 then 1 else 0) = 0
    norm_num

theorem setup_run_constant (guess helper : Bool) :
    setup.run (constantProfile guess helper) =
      bitLaw.map (fun bit => finalState bit guess helper) := by
  change (bitLaw.map sourceInitial).bind
    (fun initial => program.run (constantProfile guess helper) initial) = _
  rw [PMF.bind_map]
  change bitLaw.bind (fun bit => program.run (constantProfile guess helper) (sourceInitial bit)) = _
  simp only [run_constant]
  rfl

theorem constant_profile_alice_value (guess helper : Bool) :
    expect (setup.run (constantProfile guess helper)) (fun terminal => utility terminal alice) =
      1 / 2 := by
  rw [setup_run_constant, expect_map]
  change expect bitLaw (fun bit => utility (finalState bit guess helper) alice) = 1 / 2
  have values : (fun bit => utility (finalState bit guess helper) alice) =
      fun bit => if guess = bit then (1 : ℝ) else 0 := by
    funext bit
    exact (utility_finalState bit guess helper).1
  rw [values]
  simp only [bitLaw, expect_mix_of_finite, expect_pure]
  cases guess <;> norm_num

theorem constant_profile_bob_value (guess helper : Bool) :
    expect (setup.run (constantProfile guess helper))
      (fun terminal => utility terminal bob) = 0 := by
  rw [setup_run_constant, expect_map]
  calc
    _ = expect bitLaw (fun _ => (0 : ℝ)) := expect_congr_on_support
      (fun bit _ => (utility_finalState bit guess helper).2)
    _ = 0 := expect_zero _

theorem honest_decisionRecall : setup.intendedModel.DecisionRecall :=
  setup.intendedModel.decisionRecall_of_perfectRecall
    ((setup.informationModel _).restrictMenu_perfectRecall _ _ (setup.protocol_perfectRecall _))

private theorem honestMenu_nonempty (who : Player) (info : setup.ProtocolView who) :
    ∃ choice, choice ∈ setup.intendedMenu who info := by
  classical
  cases info with
  | none => exact ⟨none, rfl⟩
  | some view =>
      rcases view with observed | observed | observed | observed | terminal
      · by_cases same : alice = who
        · subst who
          refine ⟨some (.commit alice 1 .bool (.success false)), ?_⟩
          exact ⟨rfl, false, Or.inl (fun _ => rfl), rfl⟩
        · exact ⟨none, fun equality => same (Option.some.inj equality)⟩
      · by_cases same : bob = who
        · subst who
          refine ⟨some (.commit bob 2 .bool (.success true)), ?_⟩
          exact ⟨rfl, true, Or.inl (fun _ => rfl), rfl⟩
        · exact ⟨none, fun equality => same (Option.some.inj equality)⟩
      · by_cases same : alice = who
        · subst who
          exact ⟨some (.reveal alice 1 true), rfl, rfl⟩
        · exact ⟨none, fun equality => same (Option.some.inj equality)⟩
      · by_cases same : bob = who
        · subst who
          exact ⟨some (.reveal bob 2 true), rfl, rfl⟩
        · exact ⟨none, fun equality => same (Option.some.inj equality)⟩
      · exact ⟨none, fun impossible => by cases impossible⟩

def honestFallback (who : Player) : setup.intendedModel.Policy who := fun info =>
  ⟨(honestMenu_nonempty who info).choose, (honestMenu_nonempty who info).choose_spec⟩

def honestPayoff (who : Player) (history : setup.intendedProtocol.History) : ℝ :=
  (setup.protocolReadout history.state).elim 0 (fun terminal => utility terminal who)

theorem honest_bob_payoff_zero (history : setup.intendedProtocol.History) :
    honestPayoff bob history = 0 := by
  unfold honestPayoff
  cases read : setup.protocolReadout history.state with
  | none => rfl
  | some terminal =>
      change State simpleExpr program.terminalCtx at terminal
      have noFailure := setup.failedReveals_eq_zero_of_intendedState
        (setup.intendedState_trace wellFormed history.trace) alice read
      change failedReveals program alice (publicOutcome program terminal) = 0 at noFailure
      change (if terminalParameter terminal then (-1 : ℝ) else 1) *
        (if 0 < failedReveals program alice (publicOutcome program terminal) then 1 else 0) = 0
      rw [noFailure]
      norm_num

theorem exists_honest_sequentialEquilibrium :
    ∃ assessment : setup.intendedModel.BehavioralAssessment,
      assessment.IsSequentialEquilibrium honest_decisionRecall.decisionInformationAntichain
        setup.intended_bounded.wellFoundedHistories honestPayoff := by
  have : Finite setup.intendedProtocol.History := setup.intended_finite_history finiteBindingTypes
  obtain ⟨assessment, rational, consistent⟩ :=
    setup.intendedModel.exists_sequentialEquilibrium honest_decisionRecall honestFallback
      honestPayoff setup.intended_bounded.wellFoundedHistories
  exact ⟨assessment, rational, consistent⟩

def guessReward (bit : Bool) : PublicationResult Bool → ℝ
  | .failure => 0
  | .success guess => if guess = bit then 1 else 0

/-- Later helper choices and publications cannot affect Alice's score once
her own mandatory opening has published her first declaration. -/
theorem run_alice_payoff (profile : BehavioralProfile program)
    (opening : ∀ view, (profile alice).2.2.1 rfl view = PMF.pure true) (bit : Bool) :
    (program.run profile (sourceInitial bit)).map (fun terminal => utility terminal alice) =
      ((profile alice).1 rfl (sourceObserve alice (sourceInitial false), [])).map
        (guessReward bit) := by
  simp only [SourceProgram.run, program, runWith, commitKernel, revealKernel,
    afterCommit, afterReveal, opening, PMF.pure_bind, PMF.map_bind]
  rw [alice_initial_observation bit false]
  apply bind_congr_on_support _
  intro guess _
  apply pmf_eq_pure_of_support_subset_singleton
  intro reward supported
  simp only [PMF.support_bind, PMF.support_map, PMF.support_pure, Set.mem_iUnion,
    Set.mem_image, Set.mem_singleton_iff] at supported
  rcases supported with ⟨helper, _, disclosed, _, terminal, rfl, rfl⟩
  cases guess <;> cases helper <;> cases disclosed <;> rfl

private def liftedHonestProfile
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    ∀ who, (setup.informationModel (CommitmentInterface.values program)).BehavioralPolicy who :=
  fun who info => (profile who info).map
    ((setup.intendedRestriction (CommitmentInterface.values program)).choice who info)

private def honestSourceProfile
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) : BehavioralProfile program :=
  fun who => ((setup.behavioralPolicyEquiv (CommitmentInterface.values program) who).symm
    (liftedHonestProfile profile who)).1

private theorem honestSourceProfile_admitted
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) (who : Player) :
    (honestSourceProfile profile who).Admitted program (CommitmentInterface.values program) :=
  ((setup.behavioralPolicyEquiv (CommitmentInterface.values program) who).symm
    (liftedHonestProfile profile who)).2

private theorem honestSourceProfile_roundtrip
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) (who : Player) :
    setup.toProtocolBehavioralPolicy (CommitmentInterface.values program) who
      (honestSourceProfile profile who) (honestSourceProfile_admitted profile who) =
        liftedHonestProfile profile who :=
  (setup.behavioralPolicyEquiv (CommitmentInterface.values program) who).apply_symm_apply _

private theorem honestSourceProfile_opens
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) (view) :
    (honestSourceProfile profile alice).2.2.1 rfl view = PMF.pure true := by
  change (((profile alice (some (.inr (.inr (.inl view))))).map
    ((setup.intendedRestriction (CommitmentInterface.values program)).choice alice
      (some (.inr (.inr (.inl view)))))).map
        (fun choice => OwnAction.disclosure choice.1)) = PMF.pure true
  rw [PMF.map_comp]
  calc
    _ = (profile alice (some (.inr (.inr (.inl view))))).map (fun _ => true) := by
      apply map_congr_on_support
      intro choice _
      have allowed := choice.2
      cases action : choice.1 with
      | none =>
          rw [action] at allowed
          change some alice ≠ some alice at allowed
          exact (allowed rfl).elim
      | some material =>
          rw [action] at allowed
          change some alice = some alice ∧
            material ∈ ({OwnAction.reveal alice 1 true} : Set (OwnAction Player simpleExpr))
            at allowed
          change OwnAction.disclosure choice.1 = true
          rw [action, allowed.2]
          rfl
    _ = _ := by simp [← PMF.bind_pure_comp, Function.comp_def]

private theorem honestSourceProfile_alice_value
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    expect (setup.run (honestSourceProfile profile)) (fun terminal => utility terminal alice) =
      1 / 2 := by
  let selected := honestSourceProfile profile
  let guesses := (selected alice).1 rfl (sourceObserve alice (sourceInitial false), [])
  have law : setup.run selected =
      bitLaw.bind (fun bit => program.run selected (sourceInitial bit)) := by
    change (bitLaw.map sourceInitial).bind (fun initial => program.run selected initial) = _
    rw [PMF.bind_map]
    rfl
  have integrable : PayoffIntegrable (setup.run selected)
      (fun terminal => utility terminal alice) :=
    payoffIntegrable_of_bounded _ _ (C := 1) fun terminal => by
      rw [abs_of_nonneg (alice_utility_bounds terminal).1]
      exact (alice_utility_bounds terminal).2
  rw [law] at integrable ⊢
  rw [expect_bind_tower _ _ _ integrable]
  calc
    _ = expect bitLaw (fun bit => expect guesses (guessReward bit)) := by
      apply expect_congr_on_support
      intro bit _
      have readout := congrArg (fun distribution : PMF ℝ => expect distribution id)
        (run_alice_payoff selected (honestSourceProfile_opens profile) bit)
      change expect (program.run selected (sourceInitial bit))
          (fun terminal => utility terminal alice) =
        expect ((selected alice).1 rfl (sourceObserve alice (sourceInitial false), []))
          (fun value => guessReward bit value)
      simpa only [expect_map, Function.comp_def, id_eq] using readout
    _ = expect guesses (fun guess => expect bitLaw (fun bit => guessReward bit guess)) :=
      expect_comm_of_support_finite bitLaw guesses (Set.toFinite _) (Set.toFinite _)
        (fun bit guess => guessReward bit guess)
    _ = expect guesses (fun _ => (1 / 2 : ℝ)) := by
      apply expect_congr_on_support
      intro guess supported
      have admitted := (honestSourceProfile_admitted profile alice).1 rfl
        (sourceObserve alice (sourceInitial false), []) guess supported
      cases guess with
      | failure => cases admitted
      | success value =>
          simp only [guessReward, bitLaw, expect_mix_of_finite, expect_pure]
          cases value <;> norm_num
    _ = 1 / 2 := expect_constant _ _

private theorem honest_protocol_readout
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    (setup.intendedModel.runBehavioral profile 5).map
        (fun history => setup.protocolReadout history.state) =
      (setup.run (honestSourceProfile profile)).map some := by
  let restriction := setup.intendedRestriction (CommitmentInterface.values program)
  have extended : restriction.ExtendsProfile profile (liftedHonestProfile profile) :=
    fun _ _ => rfl
  have transported := congrArg (PMF.map fun history :
      (setup.executionProtocol (CommitmentInterface.values program)).History =>
        setup.protocolReadout history.state)
    (restriction.initialized_law profile (liftedHonestProfile profile) extended 5)
  rw [PMF.map_comp] at transported
  have evaluated := setup.protocol_runBehavioral_eq (CommitmentInterface.values program)
    (honestSourceProfile profile) (honestSourceProfile_admitted profile)
  rw [InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom] at evaluated
  have same : (fun who => setup.toProtocolBehavioralPolicy (CommitmentInterface.values program)
      who (honestSourceProfile profile who) (honestSourceProfile_admitted profile who)) =
        liftedHonestProfile profile := funext (honestSourceProfile_roundtrip profile)
  rw [same] at evaluated
  exact transported.trans evaluated

/-- Every honest behavioral protocol policy has the same initialized Alice
value. Her first choice cannot observe Bob's retained fair private input. -/
theorem honest_alice_value (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    expect (setup.intendedModel.runBehavioralTerminalFrom
      setup.intended_bounded.wellFoundedHistories profile setup.intendedProtocol.initHistory)
        (honestPayoff alice) = 1 / 2 := by
  rw [InformationModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    setup.intendedModel _ setup.intended_bounded]
  change expect (setup.intendedModel.runBehavioral profile 5) (honestPayoff alice) = 1 / 2
  calc
    _ = expect ((setup.intendedModel.runBehavioral profile 5).map
        (fun history => setup.protocolReadout history.state))
      (fun result => result.elim 0 (fun terminal => utility terminal alice)) :=
        (expect_map _ _ _).symm
    _ = expect ((setup.run (honestSourceProfile profile)).map some)
        (fun result => result.elim 0 (fun terminal => utility terminal alice)) := by
      rw [honest_protocol_readout]
    _ = expect (setup.run (honestSourceProfile profile))
        (fun terminal => utility terminal alice) := by rw [expect_map]; rfl
    _ = 1 / 2 := honestSourceProfile_alice_value profile

theorem exists_honest_sequentialEquilibrium_alice_value :
    ∃ assessment : setup.intendedModel.BehavioralAssessment,
      assessment.IsSequentialEquilibrium honest_decisionRecall.decisionInformationAntichain
        setup.intended_bounded.wellFoundedHistories honestPayoff ∧
      expect (setup.intendedModel.runBehavioralTerminalFrom
        setup.intended_bounded.wellFoundedHistories assessment.strategy
          setup.intendedProtocol.initHistory) (honestPayoff alice) = 1 / 2 := by
  obtain ⟨assessment, equilibrium⟩ := exists_honest_sequentialEquilibrium
  exact ⟨assessment, equilibrium, honest_alice_value assessment.strategy⟩

end Vegas.Examples.CommitTimingInformation
