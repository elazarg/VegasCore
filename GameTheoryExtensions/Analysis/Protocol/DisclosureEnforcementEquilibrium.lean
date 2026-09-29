/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.DisclosureEnforcementAssessment
import GameTheoryExtensions.Analysis.Protocol.DisclosureEnforcementSourceBeliefs

/-! # Sequential enforcement for finite private-state decision games

The receiver's silent decision must maximize its expected payoff under the
prior, and its response to a disclosed state must be optimal for that state.
The informed sender remains silent if the disclosed response, after the
specified charge, gives no greater reward than the silent decision law.

The charges are utility deductions in this finite protocol. Implementing them
through sampled observations, accountable reports, and collected penalties is
a separate obligation. The result below does not identify private disclosure
with an automatically observable blockchain event.
-/

noncomputable section

namespace GameTheory.Protocol.DisclosureEnforcement

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

variable {Secret Decision : Type}

/-- The receiver cannot improve its prior expected reward by a pure decision.
Finite mixtures then cannot improve it either. -/
def SilentOptimal (prior : PMF Secret) (choices : PMF Decision)
    (receiver : Secret → Decision → ℝ) : Prop :=
  ∀ decision, expect prior (fun secret => receiver secret decision) ≤
    expect prior (fun secret => expect choices (receiver secret))

def DisclosureOptimal (response : Secret → Decision)
    (receiver : Secret → Decision → ℝ) : Prop :=
  ∀ secret decision, receiver secret decision ≤ receiver secret (response secret)

def SenderDeterrence (choices : PMF Decision) (response : Secret → Decision)
    (sender : Secret → Decision → ℝ) (charge : Secret → ℝ) : Prop :=
  ∀ secret, sender secret (response secret) - charge secret ≤ expect choices (sender secret)

theorem silent_optimal_mixture [Finite Secret] [Finite Decision]
    (prior : PMF Secret) (choices : PMF Decision)
    (receiver : Secret → Decision → ℝ) (optimal : SilentOptimal prior choices receiver)
    (alternative : PMF Decision) :
    expect prior (fun secret => expect alternative (receiver secret)) ≤
      expect prior (fun secret => expect choices (receiver secret)) := by
  rw [expect_comm_of_support_finite _ _ (Set.toFinite _) (Set.toFinite _)]
  refine expect_le_const _ _ (payoffIntegrable_of_finite _ _) _ fun decision _ => ?_
  exact optimal decision

/-- A known bound on sender payoff variation gives a sufficient charge that
does not depend on which optimal disclosed response the receiver selects. -/
theorem sender_deterrence_of_range (choices : PMF Decision)
    (response : Secret → Decision) (sender : Secret → Decision → ℝ)
    (charge lower upper : Secret → ℝ)
    (bounded : ∀ secret decision,
      lower secret ≤ sender secret decision ∧ sender secret decision ≤ upper secret)
    (enforced : ∀ secret, upper secret - lower secret ≤ charge secret) :
    SenderDeterrence choices response sender charge := by
  intro secret
  have average : lower secret ≤ expect choices (sender secret) := by
    have integrable : PayoffIntegrable choices (sender secret) :=
      payoffIntegrable_of_bounded _ _ (C := |lower secret| + |upper secret|) fun decision =>
        abs_le.mpr ⟨by linarith [neg_abs_le (lower secret), abs_nonneg (upper secret),
            (bounded secret decision).1],
          by linarith [le_abs_self (upper secret), abs_nonneg (lower secret),
            (bounded secret decision).2]⟩
    have bound := expect_mono (μ := choices) (f := fun _ => lower secret) (g := sender secret)
      (fun decision _ => (bounded secret decision).1) (payoffIntegrable_constant _ _) integrable
    simpa only [expect_constant] using bound
  have ceiling := (bounded secret (response secret)).2
  have amount := enforced secret
  linarith

/-- In a statewise constant-sum decision problem, the receiver's informed
best response is already worst for the sender. No additional charge is needed. -/
theorem sender_deterrence_of_constant_sum [Finite Decision] (choices : PMF Decision)
    (response : Secret → Decision) (sender receiver : Secret → Decision → ℝ)
    (total : Secret → ℝ)
    (constantSum : ∀ secret decision,
      sender secret decision + receiver secret decision = total secret)
    (optimal : DisclosureOptimal response receiver) :
    SenderDeterrence choices response sender (fun _ => 0) := by
  intro secret
  rw [sub_zero]
  have bound := expect_mono (μ := choices)
    (f := fun _ => sender secret (response secret)) (g := sender secret)
    (fun decision _ => by
      have first := constantSum secret (response secret)
      have second := constantSum secret decision
      have best := optimal secret decision
      linarith) (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _)
  simpa only [expect_constant] using bound

theorem exists_disclosure_optimal [Finite Decision] [Nonempty Decision]
    (receiver : Secret → Decision → ℝ) :
    ∃ response, DisclosureOptimal response receiver := by
  classical
  let _ := Fintype.ofFinite Decision
  have best (secret : Secret) : ∃ action, ∀ other,
      receiver secret other ≤ receiver secret action := by
    obtain ⟨action, _, optimal⟩ := Finset.exists_max_image Finset.univ (receiver secret)
      Finset.univ_nonempty
    exact ⟨action, fun other => optimal other (Finset.mem_univ other)⟩
  choose response optimal using best
  exact ⟨response, optimal⟩

theorem exists_silent_optimal [Finite Decision] [Nonempty Decision]
    (prior : PMF Secret) (receiver : Secret → Decision → ℝ) :
    ∃ choices, SilentOptimal prior choices receiver := by
  classical
  let _ := Fintype.ofFinite Decision
  obtain ⟨action, _, optimal⟩ := Finset.exists_max_image Finset.univ
    (fun action => expect prior (fun secret => receiver secret action)) Finset.univ_nonempty
  refine ⟨PMF.pure action, fun other => ?_⟩
  simpa only [expect_pure] using optimal other (Finset.mem_univ other)

/-- The smallest nonnegative utility charge satisfying the sender condition. -/
def requiredCharge (choices : PMF Decision) (response : Secret → Decision)
    (sender : Secret → Decision → ℝ) (secret : Secret) : ℝ :=
  max 0 (sender secret (response secret) - expect choices (sender secret))

theorem requiredCharge_nonnegative (choices : PMF Decision) (response : Secret → Decision)
    (sender : Secret → Decision → ℝ) (secret : Secret) :
    0 ≤ requiredCharge choices response sender secret := le_max_left _ _

theorem requiredCharge_deterrence (choices : PMF Decision) (response : Secret → Decision)
    (sender : Secret → Decision → ℝ) :
    SenderDeterrence choices response sender (requiredCharge choices response sender) := by
  intro secret
  have sufficient := le_max_right (0 : ℝ)
    (sender secret (response secret) - expect choices (sender secret))
  unfold requiredCharge
  linarith

theorem requiredCharge_le_iff (choices : PMF Decision) (response : Secret → Decision)
    (sender : Secret → Decision → ℝ) (charge : Secret → ℝ)
    (nonnegative : ∀ secret, 0 ≤ charge secret) :
    (∀ secret, requiredCharge choices response sender secret ≤ charge secret) ↔
      SenderDeterrence choices response sender charge := by
  simp only [requiredCharge, max_le_iff, nonnegative, true_and, SenderDeterrence]
  constructor <;> intro bound secret <;> have value := bound secret <;> linarith

section Laws

variable [Nonempty Decision] {prior : PMF Secret}

theorem source_initialized_state_law
    (profile : Profile (model (Decision := Decision) prior false).behavioralSignature) :
    ((model prior false).runSingleMoverBehavioralFrom (single prior false) profile 3
      (arena prior false).initHistory).map History.state =
        prior.bind (fun secret => (choiceLaw profile true (some none)).map
          (fun action => State.done secret false action)) := by
  rw [run_initial]
  simp [Bool.false_and, resultLaw]

end Laws

section Rationality

variable [Nonempty Decision] (prior : PMF Secret)
  (full : ∀ secret, secret ∈ prior.support)

theorem silent_context_value [Finite Secret] [Finite Decision] (ambient : Bool)
    (assessment : (model (Decision := Decision) prior ambient).BehavioralAssessment)
    (posterior : assessment.belief true (receiverSilentSite prior full ambient) =
      prior.map (silentHistory prior full ambient))
    (sender receiver : Secret → Decision → ℝ) (charge : Secret → ℝ)
    (alternative : (model prior ambient).BehavioralPolicy true) :
    (assessment.continuationContext (receiverSilentSite prior full ambient)
      (fun history => payoff sender receiver charge history.state true) 3).value alternative =
        expect prior (fun secret =>
          expect (choiceLaw (Profile.update (sig := (model prior ambient).behavioralSignature)
            assessment.strategy true alternative) true (some none)) (receiver secret)) := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value, posterior]
  rw [expect_bind_of_finite, expect_map]
  simp_rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
    (model prior ambient) (single prior ambient)]
  change expect prior (fun secret =>
    expect ((model prior ambient).runSingleMoverBehavioralFrom (single prior ambient)
      (Profile.update (sig := (model prior ambient).behavioralSignature)
        assessment.strategy true alternative) 3
        (receiverHistory prior full ambient secret false))
          (fun history => payoff sender receiver charge history.state true)) = _
  simp_rw [value_receiver prior full _ _ _ (payoff sender receiver charge · true)]
  simp only [resultLaw, Bool.and_false, Bool.false_eq_true, ite_false, expect_map,
    Function.comp_def, payoff]

theorem resultLaw_update_sender {ambient : Bool}
    (profile : Profile (model (Decision := Decision) prior ambient).behavioralSignature)
    (alternative : (model prior ambient).BehavioralPolicy false)
    (secret : Secret) (disclose : Bool) :
    resultLaw (profile.update false alternative) secret disclose =
      resultLaw profile secret disclose := by
  simp [resultLaw, choiceLaw, Profile.update]

theorem silent_profile_choice (ambient : Bool) (choices : PMF Decision)
    (response : Secret → Decision) :
    choiceLaw (silentProfile prior ambient choices response) true (some none) = choices := by
  simp only [choiceLaw, decisionInfo, Option.isSome_some, Set.mem_ofPred_eq, silentProfile,
    receiverRespond, choose, Bool.or_true, Bool.and_self, ↓reduceIte, pmf_bind_pure_eq_map,
    PMF.map_comp, Function.comp_def, Option.getD_some]
  exact PMF.map_id _

theorem silent_branch_value (choices : PMF Decision) (response : Secret → Decision)
    (sender receiver : Secret → Decision → ℝ) (charge : Secret → ℝ)
    (secret : Secret) (disclose : Bool) :
    expect (resultLaw (silentProfile prior true choices response) secret disclose)
        (payoff sender receiver charge · false) =
      if disclose then sender secret (response secret) - charge secret
        else expect choices (sender secret) := by
  cases disclose <;>
    simp [resultLaw, choiceLaw, silentProfile, receiverRespond, choose, decisionInfo,
      expect_map, payoff, PMF.pure_map, pmf_bind_pure_eq_map, Function.comp_def, expect_pure]

theorem disclosed_receiver_value (choices : PMF Decision) (response : Secret → Decision)
    (sender receiver : Secret → Decision → ℝ) (charge : Secret → ℝ) (secret : Secret) :
    expect (resultLaw (silentProfile prior true choices response) secret true)
      (payoff sender receiver charge · true) = receiver secret (response secret) := by
  simp [resultLaw, choiceLaw, silentProfile, receiverRespond, choose, decisionInfo, payoff,
    PMF.pure_map, expect_pure]

theorem source_rational [Finite Secret] [Finite Decision]
    (profile : Profile (model (Decision := Decision) prior false).behavioralSignature)
    (sender receiver : Secret → Decision → ℝ) (charge : Secret → ℝ)
    (optimal : SilentOptimal prior (choiceLaw profile true (some none)) receiver) :
    (assessment prior full false profile).IsSequentiallyRationalWithin
      (fun who history => payoff sender receiver charge history.state who) 3 := by
  intro who site
  refine (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _) fun _ _ =>
      (payoffIntegrable_of_finite _ _)).mpr fun alternative _ => ?_
  cases who
  · exact (source_no_sender_site prior site).elim
  · rw [source_receiver_site_eq prior full site]
    rw [silent_context_value prior full false _ (silent_belief prior full false profile),
      silent_context_value prior full false _ (silent_belief prior full false profile)]
    simp only [assessment, Profile.update_eq_self]
    apply silent_optimal_mixture prior _ receiver optimal

theorem target_rational [Finite Secret] [Finite Decision] (choices : PMF Decision)
    (response : Secret → Decision)
    (sender receiver : Secret → Decision → ℝ) (charge : Secret → ℝ)
    (silentOptimal : SilentOptimal prior choices receiver)
    (disclosedOptimal : DisclosureOptimal response receiver)
    (deterrence : SenderDeterrence choices response sender charge) :
    (assessment prior full true
      (silentProfile prior true choices response)).IsSequentiallyRationalWithin
      (fun who history => payoff sender receiver charge history.state who) 3 := by
  intro who site
  refine (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _) fun _ _ =>
      (payoffIntegrable_of_finite _ _)).mpr fun alternative _ => ?_
  cases who
  · obtain ⟨secret, rfl⟩ := sender_site_eq prior full site
    rw [sender_context prior full _ secret (payoff sender receiver charge · false) alternative,
      sender_context prior full _ secret (payoff sender receiver charge · false) _]
    simp only [assessment, Profile.update_eq_self]
    rw [value_sender prior full _ _ (payoff sender receiver charge · false),
      value_sender prior full _ _ (payoff sender receiver charge · false)]
    simp_rw [Bool.true_and, resultLaw_update_sender, silent_branch_value]
    have silent : choiceLaw (silentProfile prior true choices response) false
        (some (some secret)) = PMF.pure false := by
      simp [choiceLaw, silentProfile, choose, decisionInfo, PMF.pure_map]
    rw [silent, expect_pure]
    simp only [Bool.false_eq_true, ite_false]
    refine expect_le_const _ _ (payoffIntegrable_of_finite _ _) _ fun disclose _ => ?_
    cases disclose
    · exact le_rfl
    · exact deterrence secret
  · rcases target_receiver_site_eq prior full site with rfl | ⟨secret, rfl⟩
    · rw [silent_context_value prior full true _ (silent_belief prior full true _),
        silent_context_value prior full true _ (silent_belief prior full true _)]
      simp only [assessment, Profile.update_eq_self, silent_profile_choice]
      exact silent_optimal_mixture prior choices receiver silentOptimal _
    · rw [disclosed_context prior full _ secret (payoff sender receiver charge · true) alternative,
        disclosed_context prior full _ secret (payoff sender receiver charge · true) _]
      simp only [assessment, Profile.update_eq_self]
      rw [value_receiver prior full _ _ _ (payoff sender receiver charge · true),
        value_receiver prior full _ _ _ (payoff sender receiver charge · true)]
      simp only [Bool.true_and]
      rw [disclosed_receiver_value]
      simp only [resultLaw, expect_map, payoff]
      refine expect_le_const _ _ (payoffIntegrable_of_finite _ _) _ fun action _ => ?_
      exact disclosedOptimal secret action

end Rationality

section Implementation

variable [Nonempty Decision] (prior : PMF Secret)

/-- The prescribed play retains the private state, decision, and absence of a
fine. It does not depend on the receiver's responses to disclosure. -/
theorem target_initialized_state_law (choices : PMF Decision)
    (response : Secret → Decision) :
    ((model prior true).runSingleMoverBehavioralFrom (single prior true)
      (silentProfile prior true choices response) 3 (arena prior true).initHistory).map
        History.state = prior.bind (fun secret =>
          choices.map (fun action => State.done secret false action)) := by
  rw [run_initial]
  simp [choiceLaw, silentProfile, choose, decisionInfo, resultLaw, receiverRespond,
    ← PMF.bind_pure_comp, Function.comp_def]

/-- Each target policy depends only on that player's source policy. The
receiver's off-path responses additionally depend on the chosen payoff analysis. -/
def compile (response : Secret → Decision) (who : Bool)
    (policy : (model (Decision := Decision) prior false).BehavioralPolicy who) :
    (model (Decision := Decision) prior true).BehavioralPolicy who := by
  cases who
  · exact choose prior true false false
  · exact receiverRespond prior true
      ((policy (some none)).map (fun choice => choice.val.getD (fallback true))) response

theorem compiled_profile (response : Secret → Decision)
    (profile : Profile (model (Decision := Decision) prior false).behavioralSignature) :
    Profile.map (target := (model prior true).behavioralSignature)
      (compile prior response) profile =
      silentProfile prior true (choiceLaw profile true (some none)) response := by
  funext who
  cases who <;> rfl

theorem compile_initialized_state_law (response : Secret → Decision)
    (profile : Profile (model (Decision := Decision) prior false).behavioralSignature) :
    ((model prior true).runSingleMoverBehavioralFrom (single prior true)
      (Profile.map (target := (model prior true).behavioralSignature) (compile prior response)
        profile) 3 (arena prior true).initHistory).map History.state =
      ((model prior false).runSingleMoverBehavioralFrom (single prior false) profile 3
        (arena prior false).initHistory).map History.state := by
  rw [compiled_profile, target_initialized_state_law, source_initialized_state_law]

theorem compile_payoff_law (response : Secret → Decision)
    (sender receiver : Secret → Decision → ℝ) (charge : Secret → ℝ)
    (profile : Profile (model (Decision := Decision) prior false).behavioralSignature) :
    (((model prior true).runSingleMoverBehavioralFrom (single prior true)
      (Profile.map (target := (model prior true).behavioralSignature) (compile prior response)
        profile) 3 (arena prior true).initHistory).map History.state).map
          (fun state who => payoff sender receiver charge state who) =
    (((model prior false).runSingleMoverBehavioralFrom (single prior false) profile 3
      (arena prior false).initHistory).map History.state).map
        (fun state who => payoff sender receiver (fun _ => 0) state who) := by
  rw [compile_initialized_state_law, source_initialized_state_law]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply congrArg (fun continuation => prior.bind continuation)
  funext secret
  apply congrArg (fun result => (choiceLaw profile true (some none)).map result)
  funext action who
  cases who <;> rfl

end Implementation

section Sequential

variable [Nonempty Decision] [Finite Decision] [Finite Secret] (prior : PMF Secret)

def IsEquilibrium (ambient : Bool) (sender receiver : Secret → Decision → ℝ)
    (charge : Secret → ℝ)
    (original : (model (Decision := Decision) prior ambient).BehavioralAssessment) : Prop :=
  original.IsSequentialEquilibriumFor (antichain prior ambient) (fun who site =>
    original.continuationContext site
      (fun history => payoff sender receiver charge history.state who) 3)

variable (full : ∀ secret, secret ∈ prior.support)

theorem source_sequential_equilibrium (choices : PMF Decision) (response : Secret → Decision)
    (sender receiver : Secret → Decision → ℝ)
    (optimal : SilentOptimal prior choices receiver) :
    IsEquilibrium prior false sender receiver (fun _ => 0)
      (assessment prior full false (silentProfile prior false choices response)) := by
  constructor
  · apply source_rational prior full
    rwa [silent_profile_choice]
  · exact consistent prior full false choices response

theorem target_sequential_equilibrium (choices : PMF Decision) (response : Secret → Decision)
    (sender receiver : Secret → Decision → ℝ) (charge : Secret → ℝ)
    (silentOptimal : SilentOptimal prior choices receiver)
    (disclosedOptimal : DisclosureOptimal response receiver)
    (deterrence : SenderDeterrence choices response sender charge) :
    IsEquilibrium prior true sender receiver charge
      (assessment prior full true (silentProfile prior true choices response)) :=
  ⟨target_rational prior full choices response sender receiver charge silentOptimal
      disclosedOptimal deterrence,
    consistent prior full true choices response⟩

include full in
/-- Every source sequential equilibrium uses a prior-optimal receiver law.
Consistency forces the prior posterior at its always-reached information set. -/
theorem source_equilibrium_optimal (sender receiver : Secret → Decision → ℝ)
    (original : (model (Decision := Decision) prior false).BehavioralAssessment)
    (equilibrium : IsEquilibrium prior false sender receiver (fun _ => 0) original) :
    SilentOptimal prior (choiceLaw original.strategy true (some none)) receiver := by
  have posterior := source_consistent_belief prior full original equilibrium.2
  intro action
  have comparison :=
      (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _) fun _ _ =>
      (payoffIntegrable_of_finite _ _)).mp
    (equilibrium.1 true (receiverSilentSite prior full false)) (choose prior false true action)
      trivial
  rw [silent_context_value prior full false original posterior,
    silent_context_value prior full false original posterior] at comparison
  simpa [choiceLaw, Profile.update, choose, decisionInfo, PMF.pure_map, expect_pure]
    using comparison

/-- The finite source class is characterized exactly by ordinary prior
optimization. The statement concerns all initialized source equilibrium laws. -/
theorem source_equilibrium_iff (choices : PMF Decision) (response : Secret → Decision)
    (sender receiver : Secret → Decision → ℝ) :
    IsEquilibrium prior false sender receiver (fun _ => 0)
        (assessment prior full false (silentProfile prior false choices response)) ↔
      SilentOptimal prior choices receiver := by
  constructor
  · intro equilibrium
    have optimal := source_equilibrium_optimal prior full sender receiver _ equilibrium
    simpa only [assessment, silent_profile_choice] using optimal
  · exact source_sequential_equilibrium prior full choices response sender receiver

/-- Every actual source sequential equilibrium has a sequentially rational,
consistent target extension with the same complete state and net-payoff laws.
The premise on charges concerns every privately known state. -/
theorem source_equilibrium_implemented (sender receiver : Secret → Decision → ℝ)
    (original : (model (Decision := Decision) prior false).BehavioralAssessment)
    (equilibrium : IsEquilibrium prior false sender receiver (fun _ => 0) original)
    (response : Secret → Decision) (charge : Secret → ℝ)
    (disclosedOptimal : DisclosureOptimal response receiver)
    (deterrence : SenderDeterrence (choiceLaw original.strategy true (some none))
      response sender charge) :
    IsEquilibrium prior true sender receiver charge
      (assessment prior full true
        (Profile.map (sig := (model (Decision := Decision) prior false).behavioralSignature)
          (target := (model prior true).behavioralSignature)
          (compile prior response) original.strategy)) ∧
    ((model prior true).runSingleMoverBehavioralFrom (single prior true)
      (Profile.map (sig := (model (Decision := Decision) prior false).behavioralSignature)
        (target := (model prior true).behavioralSignature)
        (compile prior response) original.strategy) 3 (arena prior true).initHistory).map
        History.state =
      ((model prior false).runSingleMoverBehavioralFrom (single prior false) original.strategy
        3 (arena prior false).initHistory).map History.state ∧
    (((model prior true).runSingleMoverBehavioralFrom (single prior true)
      (Profile.map (sig := (model (Decision := Decision) prior false).behavioralSignature)
        (target := (model prior true).behavioralSignature) (compile prior response)
        original.strategy) 3 (arena prior true).initHistory).map History.state).map
          (fun state who => payoff sender receiver charge state who) =
    (((model prior false).runSingleMoverBehavioralFrom (single prior false) original.strategy 3
      (arena prior false).initHistory).map History.state).map
        (fun state who => payoff sender receiver (fun _ => 0) state who) := by
  refine ⟨?_, compile_initialized_state_law prior response original.strategy,
    compile_payoff_law prior response sender receiver charge original.strategy⟩
  rw [compiled_profile]
  exact target_sequential_equilibrium prior full _ response sender receiver charge
    (source_equilibrium_optimal prior full sender receiver original equilibrium)
    disclosedOptimal deterrence

/-- For finite receiver actions, an optimal disclosed response and a finite
nonnegative charge exist for every source sequential equilibrium. This is a
utility-level implementation theorem; collection of that charge is a premise
of the extension's payoff model. -/
theorem every_source_equilibrium_enforceable (sender receiver : Secret → Decision → ℝ)
    (original : (model (Decision := Decision) prior false).BehavioralAssessment)
    (equilibrium : IsEquilibrium prior false sender receiver (fun _ => 0) original) :
    ∃ (response : Secret → Decision) (charge : Secret → ℝ), (∀ secret, 0 ≤ charge secret) ∧
      IsEquilibrium prior true sender receiver charge
        (assessment prior full true
          (Profile.map (sig := (model (Decision := Decision) prior false).behavioralSignature)
            (target := (model prior true).behavioralSignature)
            (compile prior response) original.strategy)) := by
  obtain ⟨response, optimal⟩ := exists_disclosure_optimal receiver
  let choices := choiceLaw original.strategy true (some none)
  refine ⟨response, requiredCharge choices response sender,
    requiredCharge_nonnegative choices response sender, ?_⟩
  exact (source_equilibrium_implemented prior full sender receiver original equilibrium response
    (requiredCharge choices response sender) optimal
    (requiredCharge_deterrence choices response sender)).1

/-- A fixed game-wide payoff-range bound supplies the same target charges
and the same playerwise compiler for every source equilibrium. The complete
state and payoff-law identities hold for every profile by the compiler laws. -/
theorem source_equilibrium_preserved_of_range (sender receiver : Secret → Decision → ℝ)
    (response : Secret → Decision) (charge lower upper : Secret → ℝ)
    (disclosedOptimal : DisclosureOptimal response receiver)
    (bounded : ∀ secret decision,
      lower secret ≤ sender secret decision ∧ sender secret decision ≤ upper secret)
    (enforced : ∀ secret, upper secret - lower secret ≤ charge secret)
    (original : (model (Decision := Decision) prior false).BehavioralAssessment)
    (equilibrium : IsEquilibrium prior false sender receiver (fun _ => 0) original) :
    IsEquilibrium prior true sender receiver charge
      (assessment prior full true
        (Profile.map (sig := (model (Decision := Decision) prior false).behavioralSignature)
          (target := (model prior true).behavioralSignature)
          (compile prior response) original.strategy)) :=
  (source_equilibrium_implemented prior full sender receiver original equilibrium
    response charge disclosedOptimal
    (sender_deterrence_of_range _ response sender charge lower upper bounded enforced)).1

/-- Zero-sum, and more generally statewise constant-sum, decision games in
this class preserve every source SE under optional disclosure without fines.
The receiver's own optimal informed response supplies the sender incentive. -/
theorem source_equilibrium_preserved_constant_sum (sender receiver : Secret → Decision → ℝ)
    (total : Secret → ℝ)
    (constantSum : ∀ secret decision,
      sender secret decision + receiver secret decision = total secret)
    (response : Secret → Decision) (disclosedOptimal : DisclosureOptimal response receiver)
    (original : (model (Decision := Decision) prior false).BehavioralAssessment)
    (equilibrium : IsEquilibrium prior false sender receiver (fun _ => 0) original) :
    IsEquilibrium prior true sender receiver (fun _ => 0)
      (assessment prior full true
        (Profile.map (sig := (model (Decision := Decision) prior false).behavioralSignature)
          (target := (model prior true).behavioralSignature)
          (compile prior response) original.strategy)) :=
  (source_equilibrium_implemented prior full sender receiver original equilibrium
    response (fun _ => 0) disclosedOptimal
    (sender_deterrence_of_constant_sum _ response sender receiver total constantSum
      disclosedOptimal)).1

end Sequential

end GameTheory.Protocol.DisclosureEnforcement
