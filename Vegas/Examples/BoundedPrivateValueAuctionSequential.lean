module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.BoundedPrivateValueAuctionEconomic
public import Vegas.Game.IntendedHistory
public import Vegas.Source.FiniteSupport
public import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion

@[expose] public section

/-! # Truthful sequential equilibrium with private values

Truthful reports maximize continuation payoff at every genuine intended history,
including histories off the truthful path. The strategy is therefore sequentially
rational under every belief on those histories. A finite uniform perturbation
supplies a consistent assessment for every prior on the two private values.
-/

noncomputable section

namespace Vegas.Examples.BoundedPrivateValueAuction

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
open CommitRevealAuction (Player)

variable (prior : PMF (Player → Bid))

private theorem bid_mem_intended {Γ : SourceCtx Player simpleExpr}
    (value : Bid) (who owner : Player) (name : VarId)
    (view : SourceObservation simpleExpr who Γ) :
    value ∈ intendedValues who (BoundedPaymentAuction.acceptGuard owner name) view := by
  apply Or.inl
  intro same
  cases same
  unfold SourceGuard.predicts
  refine (GuardCode.accepts_success
    (BoundedPaymentAuction.acceptGuard who name).toGuardCode value _
    (fun _ _ cell _ => by
      cases cell with
      | here => exact value
      | there absent => cases absent) ?_ ?_).trans ?_
  · intro _; rfl
  · intro _ _ cell _; cases cell
  · rfl

def intendedBidAction (value : Bid) (who : Player) (view : (setup prior).ProtocolView who) :
    Option (OwnAction Player simpleExpr) :=
  match view with
  | none => none
  | some (.inl view) => if who = .alice ∧ Player.alice ∉ view.defaulted then
      some (.commit .alice 0 (.range 0 6) (some (.success value))) else none
  | some (.inr (.inl view)) => if who = .bob ∧ Player.bob ∉ view.defaulted then
      some (.commit .bob 1 (.range 0 6) (some (.success value))) else none
  | some (.inr (.inr (.inl view))) => if who = .alice ∧ Player.alice ∉ view.defaulted then
      some (.reveal .alice 0 true) else none
  | some (.inr (.inr (.inr (.inl view)))) => if who = .bob ∧ Player.bob ∉ view.defaulted then
      some (.reveal .bob 1 true) else none
  | some (.inr (.inr (.inr (.inr _)))) => none

theorem intendedBidAction_mem (value : Bid) (who : Player)
    (view : (setup prior).ProtocolView who) :
    intendedBidAction prior value who view ∈ (setup prior).intendedMenu who view := by
  cases who <;> rcases view with _ | (view | (view | (view | (view | view))))
  all_goals
    simp only [intendedBidAction]
    try split_ifs
  all_goals simp_all only [Setup.intendedMenu, Set.ofPred_eq_eq_singleton,
    Set.mem_singleton_iff, setup, program, Finset.insert_empty, Int.reduceNeg,
    true_and, ProtocolView.intendedMenu, ProtocolView.actor, Sum.elim_inl,
    ↓reduceIte, ProtocolView.intendedAvailable, Subtype.exists, Nat.cast_ofNat,
    Int.reduceAdd, zero_add, Set.mem_Icc, Set.mem_ofPred_eq, ne_eq,
    not_true_eq_false, OwnAction.commit.injEq, heq_eq_eq, Option.some.injEq,
    PublicationResult.success.injEq, Subtype.ext_iff, exists_and_right,
    exists_eq_right', Subtype.coe_eta, exists_prop, Decidable.not_not,
    reduceCtorEq, false_and, not_false_eq_true, and_true, Sum.elim_inr,
    Option.ite_none_left_eq_some, and_false, Set.mem_empty_iff_false, and_self]
  all_goals
    exact ⟨value.property, bid_mem_intended value _ _ _ _⟩

def intendedBidChoice (value : Bid) (who : Player) (view : (setup prior).ProtocolView who) :
    (setup prior).intendedModel.Choice who view :=
  ⟨intendedBidAction prior value who view, intendedBidAction_mem prior value who view⟩

theorem intendedBidChoice_surjective (who : Player) (view : (setup prior).ProtocolView who) :
    Function.Surjective (fun value => intendedBidChoice prior value who view) := by
  rintro ⟨selected, legal⟩
  suffices ∃ value, intendedBidAction prior value who view = selected by
    obtain ⟨value, same⟩ := this
    exact ⟨value, Subtype.ext same⟩
  change Option (OwnAction Player simpleExpr) at selected
  change selected ∈ (setup prior).intendedMenu who view at legal
  cases who <;> rcases view with _ | (view | (view | (view | (view | view)))) <;>
    rcases selected with _ | action
  all_goals
    aesop (config := { terminal := false, warnOnNonterminal := false })
      (add simp [Setup.intendedMenu, setup, program, ProtocolView.intendedMenu,
      ProtocolView.actor, ProtocolView.intendedAvailable, intendedBidAction,
      Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_empty_iff_false])

def ownValue (who : Player) (view : (setup prior).ProtocolView who) : Bid :=
  match view with
  | some (.inl view) => (view.observation.cells.get .here).getD default
  | some (.inr (.inl view)) =>
      (view.observation.cells.get (.there (.there .here))).getD default
  | _ => default

def truthfulProfile : (who : Player) → (setup prior).intendedModel.BehavioralPolicy who :=
  fun who view => PMF.pure (intendedBidChoice prior (ownValue prior who view) who view)

def uniformProfile : (who : Player) → (setup prior).intendedModel.BehavioralPolicy who :=
  fun who view => (uniformLaw Bid).map (fun value => intendedBidChoice prior value who view)

theorem uniformProfile_fullSupport (who : Player) (view : (setup prior).ProtocolView who)
    (choice : (setup prior).intendedModel.Choice who view) :
    choice ∈ (uniformProfile prior who view).support := by
  obtain ⟨value, rfl⟩ := intendedBidChoice_surjective prior who view choice
  rw [uniformProfile, PMF.support_map]
  exact ⟨value, mem_support_uniformLaw value, rfl⟩

instance : Finite (setup prior).intendedProtocol.History :=
  (setup prior).intended_finite_history finiteBindingTypes

theorem exists_consistent_truthful_assessment :
    ∃ assessment : (setup prior).intendedModel.BehavioralAssessment,
      assessment.strategy = truthfulProfile prior ∧
        assessment.IsSequentiallyConsistent (setup prior).intended_decision_antichain := by
  let reference := (setup prior).intendedModel.bayesAssessment (uniformProfile prior)
    (fun who site => uniformProfile_fullSupport prior who site.1)
    (setup prior).intended_decision_antichain
  exact InformationModel.BehavioralAssessment.exists_consistent_completion reference
    (fun who site => uniformProfile_fullSupport prior who site.1)
    (setup prior).intended_decision_antichain (truthfulProfile prior)

def truthfulAssessment : (setup prior).intendedModel.BehavioralAssessment :=
  Classical.choose (exists_consistent_truthful_assessment prior)

theorem truthfulAssessment_strategy : (truthfulAssessment prior).strategy = truthfulProfile prior :=
  (Classical.choose_spec (exists_consistent_truthful_assessment prior)).1

theorem truthfulAssessment_consistent : (truthfulAssessment prior).IsSequentiallyConsistent
    (setup prior).intended_decision_antichain :=
  (Classical.choose_spec (exists_consistent_truthful_assessment prior)).2


private def sourceProfile (prior : PMF (Player → Bid))
    (profile : Profile (setup prior).intendedModel.behavioralSignature) :
    BehavioralProfile program :=
  (setup prior).decodeBehavioralProfile (.values program)
    ((setup prior).intendedSourceProfile (.values program) profile)

private theorem sourceProfile_truthful :
    sourceProfile prior (truthfulProfile prior) = truthful := by
  funext who
  cases who
  all_goals
    dsimp only [sourceProfile, Setup.decodeBehavioralProfile, Setup.behavioralPolicyEquiv,
      Equiv.coe_fn_symm_mk, setup, program, BehavioralPolicy.fromProtocol,
      truthful, alicePolicy, bobPolicy]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl)))
  all_goals funext own view active
  all_goals cases own
  all_goals
    simp only [Setup.intendedSourceProfile, truthfulProfile, PMF.pure_map,
      intendedBidChoice, intendedBidAction, ownValue,
      active, not_false_eq_true, and_true, ↓reduceIte, OwnAction.disclosure]
  all_goals
    first
    | exact congrArg PMF.pure (OwnAction.binding_commit _ _ _ _)
    | rfl

private abbrev boundCtx : SourceCtx Player simpleExpr :=
  (1, .commitment .bob (.range 0 6)) ::
    (0, .commitment .alice (.range 0 6)) :: context

private abbrev revealProgram : SourceProgram Player simpleExpr boundCtx {1, 0} :=
  .reveal 2 .alice 0 (by decide) (.there .here) (by decide) <|
  .reveal 3 .bob 1 (by decide) (.there .here) (by decide) <|
  .ret [(.alice, BoundedPaymentAuction.cashExpr 6 .alice (.var 2 (.there .here)) (.var 3 .here)),
    (.bob, BoundedPaymentAuction.cashExpr 6 .bob (.var 2 (.there .here)) (.var 3 .here))]

private theorem reveals_runFrom (profile : BehavioralProfile revealProgram)
    (honest : ∀ who, Honest revealProgram (profile who))
    (config : Config Player simpleExpr boundCtx) (intended : config.Intended {1, 0}) :
    runFrom revealProgram profile config =
      PMF.pure (revealSuccessor 3 (.there .here)
        (revealSuccessor 2 (.there .here) config true) true) := by
  have active := intended.not_defaulted Player.alice
  have after := (intended.reveal (name := 0) (published := 2) (by decide) (.there .here)).1
  have activeAfter := after.not_defaulted Player.bob
  have first : (profile Player.alice).1 rfl (config.view Player.alice) active = PMF.pure true :=
    eq_pure_true_of_false_not_mem ((honest Player.alice).1 rfl (config.view Player.alice) active)
  have second : (profile Player.bob).2.1 rfl
      ((revealSuccessor 2 (.there .here) config true).view Player.bob) activeAfter =
        PMF.pure true :=
    eq_pure_true_of_false_not_mem ((honest Player.bob).2.1 rfl
      ((revealSuccessor 2 (.there .here) config true).view Player.bob) activeAfter)
  simp only [revealProgram, runFrom, revealKernel, afterReveal, dite_eq_right active, first,
    PMF.pure_bind,
    dite_eq_right activeAfter, second]


private def boundTypes (config : Config Player simpleExpr boundCtx) : Player → Bid
  | .alice => config.state.get (.there (.there .here))
  | .bob => config.state.get (.there (.there (.there .here)))

private def terminalPayoff (terminal : Config Player simpleExpr program.terminalCtx)
    (who : Player) : ℝ :=
  utility (values (initialState program terminal.state), publicOutcome program terminal) who

private theorem payoff_of_state (terminal : Config Player simpleExpr program.terminalCtx)
    (config : Config Player simpleExpr boundCtx) (alice bob : Bid)
    (state : terminal.state = Env.cons (x := 3) (τ := .publication (.range 0 6)) (.success bob)
      (Env.cons (x := 2) (τ := .publication (.range 0 6)) (.success alice) config.state))
    (who : Player) : terminalPayoff terminal who =
      surplus (boundTypes config) alice bob who := by
  have initialEq : values (initialState program terminal.state) = boundTypes config := by
    rw [state]
    rfl
  have alicePub : (publicOutcome program terminal).values.get (.there .here) =
      .success alice := by
    change terminal.state.get (.there .here) = .success alice
    rw [state]
    rfl
  have bobPub : (publicOutcome program terminal).values.get .here = .success bob := by
    change terminal.state.get .here = .success bob
    rw [state]
    rfl
  unfold terminalPayoff
  rw [utility_eq_economic, initialEq, alicePub, bobPub]
  cases who <;> rfl

private theorem reveals_payoff (config : Config Player simpleExpr boundCtx)
    (intended : config.Intended {1, 0}) (alice bob : Bid)
    (aliceBound : config.state.get (.there .here) = .success alice)
    (bobBound : config.state.get .here = .success bob) (who : Player) :
    terminalPayoff (revealSuccessor 3 (.there .here)
      (revealSuccessor 2 (.there .here) config true) true) who =
        surplus (boundTypes config) alice bob who := by
  have after := (intended.reveal (name := 0) (published := 2) (by decide) (.there .here)).1
  apply payoff_of_state _ config alice bob
  rw [after.reveal_state, Config.bindingOf, intended.reveal_state]
  simp only [Config.bindingOf, Env.cons_get_there, aliceBound, bobBound]

private theorem accepts_bid {Γ : SourceCtx Player simpleExpr} (who : Player)
    (name : VarId) (state : State simpleExpr Γ) (value : Bid) :
    (BoundedPaymentAuction.acceptGuard who name).predicts
      (sourceObserve who state) value = true := by
  unfold SourceGuard.predicts
  refine (GuardCode.accepts_success
    (BoundedPaymentAuction.acceptGuard who name).toGuardCode value _
    (fun _ _ cell _ => by
      cases cell with
      | here => exact value
      | there absent => cases absent) ?_ ?_).trans ?_
  · intro _; rfl
  · intro _ _ cell _; cases cell
  · rfl

private abbrev aliceCtx : SourceCtx Player simpleExpr :=
  (0, .commitment .alice (.range 0 6)) :: context

private abbrev bobProgram : SourceProgram Player simpleExpr aliceCtx {0} :=
  .commit 1 .bob (by decide) (BoundedPaymentAuction.acceptGuard .bob 1) revealProgram

private def aliceTypes (config : Config Player simpleExpr aliceCtx) : Player → Bid
  | .alice => config.state.get (.there .here)
  | .bob => config.state.get (.there (.there .here))

private theorem bob_payoff_bound (profile : BehavioralProfile bobProgram)
    (honest : ∀ who, Honest bobProgram (profile who))
    (config : Config Player simpleExpr aliceCtx) (intended : config.Intended {0})
    (alice : Bid) (aliceBound : config.state.get .here = .success alice)
    (terminal : Config Player simpleExpr program.terminalCtx)
    (supported : terminal ∈ (runFrom bobProgram profile config).support) :
    terminalPayoff terminal .bob ≤
      surplus (aliceTypes config) alice (aliceTypes config .bob) .bob := by
  have active := intended.not_defaulted Player.bob
  rw [runFrom_commit, dite_eq_right active, PMF.support_bind] at supported
  simp only [Set.mem_iUnion] at supported
  obtain ⟨choice, chosen, continued⟩ := supported
  obtain ⟨value, rfl⟩ := (honest Player.bob).1 rfl (config.view Player.bob) active choice chosen
  have nextIntended := intended.commit (name := 1) (by decide)
    (BoundedPaymentAuction.acceptGuard .bob 1) value (accepts_bid .bob 1 config.state value)
  have nextHonest : ∀ who, Honest revealProgram (afterCommit profile who) :=
    fun who => (honest who).2
  rw [reveals_runFrom _ nextHonest _ nextIntended, PMF.mem_support_pure_iff] at continued
  subst terminal
  rw [reveals_payoff _ nextIntended alice value]
  · exact truthful_bob_payoff_ge (aliceTypes config) value alice
  · simpa only [commitSuccessor, active, ite_false, Env.cons_get_there] using aliceBound
  · simp only [commitSuccessor, active, ite_false, Option.getD_some, Env.cons_get_here]


private theorem truthful_honest (who : Player) : Honest program (truthful who) := by
  cases who with
  | alice =>
      refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩
      · intro own view active choice selected
        exact ⟨_, (PMF.mem_support_pure_iff ..).mp selected⟩
      · intro impossible; cases impossible
      · intro own view active
        simp [truthful, alicePolicy]
      · intro impossible; cases impossible
  | bob =>
      refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩
      · intro impossible; cases impossible
      · intro own view active choice selected
        exact ⟨_, (PMF.mem_support_pure_iff ..).mp selected⟩
      · intro impossible; cases impossible
      · intro own view active
        simp [truthful, bobPolicy]

private theorem bob_runFrom_fixed (profile : BehavioralProfile bobProgram)
    (honest : ∀ who, Honest bobProgram (profile who))
    (config : Config Player simpleExpr aliceCtx) (intended : config.Intended {0})
    (value : Bid)
    (kernel : commitKernel profile (config.view Player.bob) (intended.not_defaulted .bob) =
      PMF.pure (some (.success value))) :
    runFrom bobProgram profile config =
      PMF.pure (revealSuccessor 3 (.there .here)
        (revealSuccessor 2 (.there .here)
          (commitSuccessor 1 (BoundedPaymentAuction.acceptGuard .bob 1) config
            (some (.success value))) true) true) := by
  rw [runFrom_commit, dite_eq_right (intended.not_defaulted .bob), kernel, PMF.pure_bind]
  apply reveals_runFrom _ (fun who => (honest who).2)
  exact intended.commit (name := 1) (by decide) (BoundedPaymentAuction.acceptGuard .bob 1)
    value (accepts_bid .bob 1 config.state value)

private theorem bob_truthful_value (config : Config Player simpleExpr aliceCtx)
    (intended : config.Intended {0}) (alice : Bid)
    (aliceBound : config.state.get .here = .success alice) :
    expect (runFrom bobProgram (afterCommit truthful) config)
      (fun terminal => terminalPayoff terminal .bob) =
        surplus (aliceTypes config) alice (aliceTypes config .bob) .bob := by
  have active := intended.not_defaulted Player.bob
  have nextIntended := intended.commit (name := 1) (by decide)
    (BoundedPaymentAuction.acceptGuard .bob 1) (aliceTypes config .bob)
      (accepts_bid .bob 1 config.state _)
  have nextHonest : ∀ who, Honest revealProgram (afterCommit (afterCommit truthful) who) :=
    fun who => (truthful_honest who).2.2
  rw [runFrom_commit, dite_eq_right active]
  have kernel : commitKernel (afterCommit truthful) (config.view Player.bob) active =
      PMF.pure (some (.success (aliceTypes config .bob))) := rfl
  rw [kernel, PMF.pure_bind, reveals_runFrom _ nextHonest _ nextIntended, expect_pure]
  apply reveals_payoff _ nextIntended alice (aliceTypes config .bob)
  · simpa only [commitSuccessor, active, ite_false, Env.cons_get_there] using aliceBound
  · simp only [commitSuccessor, active, ite_false, Option.getD_some, Env.cons_get_here]

private theorem bob_continuation_optimal (profile : BehavioralProfile bobProgram)
    (honest : ∀ who, Honest bobProgram (profile who))
    (config : Config Player simpleExpr aliceCtx) (intended : config.Intended {0}) :
    expect (runFrom bobProgram profile config) (fun terminal => terminalPayoff terminal .bob) ≤
      expect (runFrom bobProgram (afterCommit truthful) config)
        (fun terminal => terminalPayoff terminal .bob) := by
  obtain ⟨alice, aliceBound⟩ := intended.bound (owner := Player.alice) .here
  rw [bob_truthful_value config intended alice aliceBound]
  apply expect_le_const _ _
    (payoffIntegrable_of_finite_support _ _ (runFrom_support_finite bobProgram profile
      (FiniteBindingTypes.profileFiniteSupport bobProgram
        (show bobProgram.FiniteBindingTypes from ⟨inferInstance, trivial⟩) profile) config))
  exact fun terminal supported => bob_payoff_bound profile honest config intended
    alice aliceBound terminal supported


private theorem alice_runFrom (profile : BehavioralProfile program)
    (config : Config Player simpleExpr context) :
    runFrom program profile config =
      (if inactive : Player.alice ∈ config.defaulted then PMF.pure none
        else commitKernel profile (config.view Player.alice) inactive).bind fun choice =>
          runFrom bobProgram (afterCommit profile)
            (commitSuccessor 0 (BoundedPaymentAuction.acceptGuard .alice 0) config choice) := rfl

private theorem commit_state {Γ : SourceCtx Player simpleExpr} {owner : Player}
    {name : VarId} (guard : SourceGuard simpleExpr Γ owner name (.range 0 6))
    (config : Config Player simpleExpr Γ) (active : owner ∉ config.defaulted) (value : Bid) :
    (commitSuccessor name guard config (some (.success value))).state =
      Env.cons (x := name) (τ := .commitment owner (.range 0 6)) (.success value) config.state := by
  change Env.cons (x := name) (τ := .commitment owner (.range 0 6))
    ((if owner ∈ config.defaulted then (none : Option (PublicationResult Bid)) else
      some (.success value)).getD .failure) config.state = _
  rw [ite_eq_right active]
  rfl

private theorem alice_tail_fixed (profile : BehavioralProfile program)
    (honest : ∀ who, Honest program (profile who))
    (bobTruth : profile .bob = truthful .bob)
    (config : Config Player simpleExpr context) (intended : config.Intended ∅) (value : Bid) :
    runFrom bobProgram (afterCommit profile)
        (commitSuccessor 0 (BoundedPaymentAuction.acceptGuard .alice 0) config
          (some (.success value))) =
      PMF.pure (revealSuccessor 3 (.there .here)
        (revealSuccessor 2 (.there .here)
          (commitSuccessor 1 (BoundedPaymentAuction.acceptGuard .bob 1)
            (commitSuccessor 0 (BoundedPaymentAuction.acceptGuard .alice 0) config
              (some (.success value)))
              (some (.success (values config.state .bob)))) true) true) := by
  have after := intended.commit (name := 0) (by decide)
    (BoundedPaymentAuction.acceptGuard .alice 0) value
    (accepts_bid .alice 0 config.state value)
  apply bob_runFrom_fixed _ (fun who => (honest who).2) _ after (values config.state .bob)
  change (profile Player.bob).2.1 rfl _ _ = _
  rw [bobTruth]
  rfl

private theorem alice_payoff_bound (profile : BehavioralProfile program)
    (honest : ∀ who, Honest program (profile who))
    (bobTruth : profile .bob = truthful .bob)
    (config : Config Player simpleExpr context) (intended : config.Intended ∅)
    (terminal : Config Player simpleExpr program.terminalCtx)
    (supported : terminal ∈ (runFrom program profile config).support) :
    terminalPayoff terminal .alice ≤
      surplus (values config.state) (values config.state .alice) (values config.state .bob)
        .alice := by
  have active := intended.not_defaulted Player.alice
  rw [alice_runFrom, dite_eq_right active, PMF.support_bind] at supported
  obtain ⟨choice, chosen, continued⟩ := Set.mem_iUnion₂.mp supported
  obtain ⟨value, rfl⟩ := (honest Player.alice).1 rfl (config.view Player.alice) active choice chosen
  rw [alice_tail_fixed profile honest bobTruth config intended value,
    PMF.mem_support_pure_iff] at continued
  subst terminal
  have first := intended.commit (name := 0) (by decide)
    (BoundedPaymentAuction.acceptGuard .alice 0) value
    (accepts_bid .alice 0 config.state value)
  have second := first.commit (name := 1) (by decide)
    (BoundedPaymentAuction.acceptGuard .bob 1) (values config.state .bob)
    (accepts_bid .bob 1 _ (values config.state .bob))
  rw [reveals_payoff _ second value (values config.state .bob)]
  · exact truthful_alice_payoff_ge (values config.state) value (values config.state .bob)
  · rw [commit_state _ _ (first.not_defaulted Player.bob), Env.cons_get_there,
      commit_state _ _ active, Env.cons_get_here]
  · rw [commit_state _ _ (first.not_defaulted Player.bob), Env.cons_get_here]

private theorem alice_truthful_value (config : Config Player simpleExpr context)
    (intended : config.Intended ∅) :
    expect (runFrom program truthful config) (fun terminal => terminalPayoff terminal .alice) =
      surplus (values config.state) (values config.state .alice) (values config.state .bob)
        .alice := by
  have active := intended.not_defaulted Player.alice
  have first := intended.commit (name := 0) (by decide)
    (BoundedPaymentAuction.acceptGuard .alice 0) (values config.state .alice)
    (accepts_bid .alice 0 config.state (values config.state .alice))
  have second := first.commit (name := 1) (by decide)
    (BoundedPaymentAuction.acceptGuard .bob 1) (values config.state .bob)
    (accepts_bid .bob 1 _ (values config.state .bob))
  rw [alice_runFrom, dite_eq_right active]
  have kernel : commitKernel truthful (config.view Player.alice) active =
      PMF.pure (some (.success (values config.state .alice))) := rfl
  rw [kernel, PMF.pure_bind, alice_tail_fixed truthful truthful_honest rfl config intended,
    expect_pure]
  apply reveals_payoff _ second (values config.state .alice) (values config.state .bob)
  · rw [commit_state _ _ (first.not_defaulted Player.bob), Env.cons_get_there,
      commit_state _ _ active, Env.cons_get_here]
  · rw [commit_state _ _ (first.not_defaulted Player.bob), Env.cons_get_here]

private theorem alice_continuation_optimal (profile : BehavioralProfile program)
    (honest : ∀ who, Honest program (profile who))
    (bobTruth : profile .bob = truthful .bob)
    (config : Config Player simpleExpr context) (intended : config.Intended ∅) :
    expect (runFrom program profile config) (fun terminal => terminalPayoff terminal .alice) ≤
      expect (runFrom program truthful config)
        (fun terminal => terminalPayoff terminal .alice) := by
  rw [alice_truthful_value config intended]
  apply expect_le_const _ _
    (payoffIntegrable_of_finite_support _ _ (runFrom_support_finite _ profile
      (FiniteBindingTypes.profileFiniteSupport _ finiteBindingTypes profile) config))
  exact fun terminal supported => alice_payoff_bound profile honest bobTruth config intended
    terminal supported


private abbrev openedAliceCtx : SourceCtx Player simpleExpr :=
  (2, .publication (.range 0 6)) :: boundCtx

private abbrev bobRevealProgram : SourceProgram Player simpleExpr openedAliceCtx
    (({1, 0} : Finset VarId).erase 0) :=
  .reveal 3 .bob 1 (by decide) (.there .here) (by decide) <|
  .ret [(.alice, BoundedPaymentAuction.cashExpr 6 .alice (.var 2 (.there .here)) (.var 3 .here)),
    (.bob, BoundedPaymentAuction.cashExpr 6 .bob (.var 2 (.there .here)) (.var 3 .here))]

private theorem bob_reveal_runFrom (profile : BehavioralProfile bobRevealProgram)
    (honest : ∀ who, Honest bobRevealProgram (profile who))
    (config : Config Player simpleExpr openedAliceCtx)
    (intended : config.Intended (({1, 0} : Finset VarId).erase 0)) :
    runFrom bobRevealProgram profile config =
      PMF.pure (revealSuccessor 3 (.there .here) config true) := by
  have active := intended.not_defaulted Player.bob
  have kernel : (profile Player.bob).1 rfl (config.view Player.bob) active = PMF.pure true :=
    eq_pure_true_of_false_not_mem ((honest Player.bob).1 rfl (config.view Player.bob) active)
  simp only [bobRevealProgram, runFrom, revealKernel, dite_eq_right active,
    kernel, PMF.pure_bind]

private theorem source_optimal_of_active (prior : PMF (Player → Bid)) (who : Player)
    (profile : BehavioralProfile program) (honest : ∀ actor, Honest program (profile actor))
    (other : ∀ actor, actor ≠ who → profile actor = truthful actor)
    (state : (setup prior).ProtocolState)
    (active : (setup prior).intendedProtocol.active state who)
    (intended : (setup prior).IntendedState state) :
    expect ((setup prior).continuationDistribution profile state)
        (fun terminal => terminalPayoff terminal who) ≤
      expect ((setup prior).continuationDistribution truthful state)
        (fun terminal => terminalPayoff terminal who) := by
  cases who with
  | alice =>
      rcases state with _ | (config | (config | (config | (config | config))))
      · exact active.elim
      · exact alice_continuation_optimal profile honest (other .bob (by decide)) config intended.1
      · change (if Player.bob ∈ config.defaulted then none else some Player.bob) =
          some Player.alice at active
        split_ifs at active; cases active
      · change expect (runFrom revealProgram (afterCommit (afterCommit profile)) config) _ ≤
          expect (runFrom revealProgram (afterCommit (afterCommit truthful)) config) _
        have leftLaw := reveals_runFrom (afterCommit (afterCommit profile))
          (fun actor => (honest actor).2.2) config intended.1
        have rightLaw := reveals_runFrom (afterCommit (afterCommit truthful))
          (fun actor => (truthful_honest actor).2.2) config intended.1
        exact (congrArg (fun law => expect law (fun terminal => terminalPayoff terminal .alice))
          (leftLaw.trans rightLaw.symm)).le
      · change (if Player.bob ∈ config.defaulted then none else some Player.bob) =
          some Player.alice at active
        split_ifs at active; cases active
      · change none = some Player.alice at active
        cases active
  | bob =>
      rcases state with _ | (config | (config | (config | (config | config))))
      · exact active.elim
      · change (if Player.alice ∈ config.defaulted then none else some Player.alice) =
          some Player.bob at active
        split_ifs at active; cases active
      · exact bob_continuation_optimal (afterCommit profile) (fun actor => (honest actor).2)
          config intended.1
      · change (if Player.alice ∈ config.defaulted then none else some Player.alice) =
          some Player.bob at active
        split_ifs at active; cases active
      · change expect (runFrom bobRevealProgram
            (afterReveal (afterCommit (afterCommit profile))) config) _ ≤
          expect (runFrom bobRevealProgram
            (afterReveal (afterCommit (afterCommit truthful))) config) _
        have leftLaw := bob_reveal_runFrom (afterReveal (afterCommit (afterCommit profile)))
          (fun actor => (honest actor).2.2.2) config intended.2.1
        have rightLaw := bob_reveal_runFrom (afterReveal (afterCommit (afterCommit truthful)))
          (fun actor => (truthful_honest actor).2.2.2) config intended.2.1
        exact (congrArg (fun law => expect law (fun terminal => terminalPayoff terminal .bob))
          (leftLaw.trans rightLaw.symm)).le
      · change none = some Player.bob at active
        cases active


private theorem history_comparison (who : Player)
    (site : (setup prior).intendedModel.InformationSite who)
    (history : (setup prior).intendedModel.InformationHistory who site.val)
    (deviation : (setup prior).intendedModel.BehavioralPolicy who) :
    expect ((setup prior).continuationDistribution (sourceProfile prior
      (Profile.update (truthfulProfile prior) who deviation)) history.val.state)
      (fun terminal => utility ((setup prior).parameterOutcome values terminal) who) ≤
    expect ((setup prior).continuationDistribution truthful history.val.state)
      (fun terminal => utility ((setup prior).parameterOutcome values terminal) who) := by
  apply source_optimal_of_active prior who _
    (fun actor => (setup prior).intendedSourceProfile_honest (.values program) _ actor)
    ?_ history.val.state
    (InformationModel.InformationSite.active (setup prior).intendedModel site history)
    ((setup prior).intendedState_trace (wellFormed prior) history.val.trace)
  intro actor different
  have same : (setup prior).intendedSourceProfile (.values program)
      (Profile.update (truthfulProfile prior) who deviation) actor =
      (setup prior).intendedSourceProfile (.values program) (truthfulProfile prior) actor := by
    funext view
    simp only [Setup.intendedSourceProfile, Profile.update, Function.update_of_ne different]
  have decoded := congrArg
    (fun policy => (((setup prior).behavioralPolicyEquiv (.values program) actor).symm policy).val)
    same
  change sourceProfile prior (Profile.update (truthfulProfile prior) who deviation) actor = _
  exact decoded.trans (congrArg (fun profile => profile actor) (sourceProfile_truthful prior))

def terminalUtility (who : Player) (final : (setup prior).intendedProtocol.History) : ℝ :=
  ((setup prior).protocolReadout final.state).elim 0
    (fun terminal => utility ((setup prior).parameterOutcome values terminal) who)

private theorem intended_continuation_value
    (profile : Profile (setup prior).intendedModel.behavioralSignature)
    (history : (setup prior).intendedProtocol.History) (who : Player) :
    expect ((setup prior).intendedModel.runBehavioralTerminalFrom
      (setup prior).intended_bounded.wellFoundedHistories profile history)
      (terminalUtility prior who) =
    expect ((setup prior).continuationDistribution (sourceProfile prior profile) history.state)
      (fun terminal => utility ((setup prior).parameterOutcome values terminal) who) := by
  let restriction := (setup prior).intendedRestriction (.values program)
  let target := (setup prior).intendedSourceProfile (.values program) profile
  let fuel := instructionCount (setup prior).program + 1
  have enough : (setup prior).protocolRemaining (restriction.history history).state ≤ fuel := by
    have length := (setup prior).protocol_history_length (.values program)
      (restriction.history history).trace
    dsimp only [fuel]
    omega
  have embedding := restriction.runFrom_law profile target
    ((setup prior).intendedSourceProfile_extends (.values program) profile) fuel history
  have readout := congrArg (PMF.map fun final => (setup prior).protocolReadout final.state)
    embedding
  have sourceDistribution := (setup prior).runBehavioralFrom_readout (.values program) target fuel
    (restriction.history history) enough
  have law : ((setup prior).intendedModel.runBehavioralFrom profile fuel history).map
      (fun final => (setup prior).protocolReadout final.state) =
      ((setup prior).continuationDistribution (sourceProfile prior profile)
        history.state).map some := by
    rw [PMF.map_comp] at readout
    exact readout.trans sourceDistribution
  rw [(setup prior).intendedModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    (setup prior).intended_bounded.wellFoundedHistories (setup prior).intended_bounded]
  have valued := congrArg (fun law => expect law (fun terminal => terminal.elim 0
    (fun terminal => utility ((setup prior).parameterOutcome values terminal) who))) law
  simp only [expect_map, Option.elim_some, Function.comp_def] at valued
  exact valued

theorem truthfulProfile_rational
    (assessment : (setup prior).intendedModel.BehavioralAssessment)
    (strategy : assessment.strategy = truthfulProfile prior) :
    assessment.IsSequentiallyRational
      (setup prior).intended_bounded.wellFoundedHistories (terminalUtility prior) := by
  classical
  intro who site
  let context := assessment.continuationContext
    (setup prior).intended_bounded.wellFoundedHistories site (terminalUtility prior who)
  have runIntegrable (alternative : (setup prior).intendedModel.BehavioralPolicy who) :
      PayoffIntegrable ((assessment.belief who site).bind fun history =>
        (setup prior).intendedModel.runBehavioralTerminalFrom
          (setup prior).intended_bounded.wellFoundedHistories
          (Profile.update (sig := (setup prior).intendedModel.behavioralSignature)
            assessment.strategy who alternative) history.val)
        (terminalUtility prior who) :=
    payoffIntegrable_of_finite_support _ _ (Set.toFinite _)
  have integrable (alternative : (setup prior).intendedModel.BehavioralPolicy who) :
      context.IntegrableAt alternative := runIntegrable alternative
  have tower (alternative : (setup prior).intendedModel.BehavioralPolicy who) :
      context.value alternative = expect (assessment.belief who site)
        (fun history => expect ((setup prior).intendedModel.runBehavioralTerminalFrom
          (setup prior).intended_bounded.wellFoundedHistories
          (Profile.update (sig := (setup prior).intendedModel.behavioralSignature)
            assessment.strategy who alternative) history.val)
          (terminalUtility prior who)) := by
    exact expect_bind_tower _ _ _ (runIntegrable alternative)
  apply (Context.isLocallyOptimal_iff_of_integrable
    (integrable (assessment.strategy who))
    (fun alternative _ => integrable alternative)).mpr
  intro deviation _allowed
  rw [tower, tower]
  apply expect_mono ?_
    (payoffIntegrable_of_finite_support _ _ (Set.toFinite _))
    (payoffIntegrable_of_finite_support _ _ (Set.toFinite _))
  intro history _supported
  rw [strategy, Profile.update_eq_self]
  rw [intended_continuation_value, intended_continuation_value, sourceProfile_truthful]
  exact history_comparison prior who site history deviation


theorem truthfulAssessment_equilibrium :
    (setup prior).IntendedSequentialEquilibrium values utility (truthfulAssessment prior) :=
  ⟨truthfulProfile_rational prior (truthfulAssessment prior) (truthfulAssessment_strategy prior),
    truthfulAssessment_consistent prior⟩

theorem truthfulAssessment_readout_distribution :
    ((setup prior).intendedModel.runBehavioral (truthfulAssessment prior).strategy
      (instructionCount program + 1)).map
      (fun final => (setup prior).protocolReadout final.state) =
        prior.map (fun types => some (finalConfig types (types .alice) (types .bob))) := by
  rw [truthfulAssessment_strategy]
  have same := (setup prior).continuationDistribution_eq_of_intended_extension (wellFormed prior)
    (.values program) (truthfulProfile prior)
    ((setup prior).intendedSourceProfile (.values program) (truthfulProfile prior))
    ((setup prior).intendedSourceProfile_extends (.values program) (truthfulProfile prior))
    (setup prior).intendedProtocol.initHistory
  change (setup prior).run (sourceProfile prior (truthfulProfile prior)) =
    (setup prior).run ((setup prior).intendedOpeningProfile (truthfulProfile prior)) at same
  rw [sourceProfile_truthful] at same
  have law := (setup prior).intendedOpeningProfile_run (wellFormed prior) (truthfulProfile prior)
  rw [← same, truthful_source_distribution, PMF.map_comp] at law
  exact law


theorem truthfulAssessment_joint_distribution :
    ((setup prior).intendedModel.runBehavioral (truthfulAssessment prior).strategy
      (instructionCount program + 1)).map (fun final =>
        ((setup prior).protocolReadout final.state, fun who => terminalUtility prior who final)) =
      prior.map (fun types =>
        (some (finalConfig types (types .alice) (types .bob)),
          surplus types (types .alice) (types .bob))) := by
  have valued := congrArg (PMF.map (fun readout : Option
      (Config Player simpleExpr program.terminalCtx) => (readout, fun who => readout.elim 0
        (fun terminal => utility ((setup prior).parameterOutcome values terminal) who))))
    (truthfulAssessment_readout_distribution prior)
  rw [PMF.map_comp, PMF.map_comp] at valued
  refine valued.trans ?_
  apply map_congr_on_support _
  intro types _
  dsimp only [Function.comp_def, Option.elim_some]
  congr 1
  have retained : initialState program (finalConfig types (types .alice) (types .bob)).state =
      initial types := rfl
  change utility (values (initialState program _), publicOutcome program _) = _
  rw [retained, values_initial, finalConfig_public]
  funext who
  exact utility_successful types _ _ who

end Vegas.Examples.BoundedPrivateValueAuction
