/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.StoppedResidual
import GameTheoryExtensions.Math.Probability.Uniform
import GameTheory.Protocol.Context
import GameTheory.Math.Probability.ExpectationMixture
import GameTheory.Math.Probability.Convergence
import GameTheory.Analysis.Protocol.BehavioralBayes
import GameTheory.Analysis.Protocol.Sequential

/-! # Conditional gains with genuinely cancelling stopped residuals

Nature reveals a context before a player chooses. Two later randomized choices
add and subtract a unit reward. Two common fully mixed continuation families
change both later probabilities together. Their signed errors cancel at each
context for every legal local law, although their absolute charges are positive.
-/

noncomputable section

namespace GameTheoryExtensionsTests.StoppedResidual

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

inductive Stage where
  | initial
  | choose (context : Bool)
  | positive (context choice : Bool)
  | negative (context choice plus : Bool)
  | done (context choice plus minus : Bool)
  deriving DecidableEq, Fintype

def depth : Stage → Nat
  | .initial => 0
  | .choose _ => 1
  | .positive _ _ => 2
  | .negative _ _ _ => 3
  | .done _ _ _ _ => 4

def acting : Stage → Prop
  | .choose _ | .positive _ _ | .negative _ _ _ => True
  | _ => False

instance (state : Stage) : Decidable (acting state) := by
  cases state <;> unfold acting <;> infer_instance

def mover : Stage → Bool
  | .choose _ => false
  | _ => true

def advance (state : Stage) (bit : Bool) : Stage := match state with
  | .choose context => .positive context bit
  | .positive context choice => .negative context choice bit
  | .negative context choice plus => .done context choice plus bit
  | _ => state

@[reducible] def arena : ExecutionProtocol Bool where
  State := Stage
  Action _ := Bool
  init := .initial
  active state who := acting state ∧ who = mover state
  available _ _ := Set.univ
  terminal state := depth state = 4
  step state joint := match state with
    | .initial => (PMF.uniformOfFintype Bool).map Stage.choose
    | _ => PMF.pure (advance state ((joint.1 (mover state)).getD false))
  progress state running := by
    by_cases moves : acting state
    · refine ⟨fun who => if who = mover state then some false else none, ?_⟩
      intro who
      by_cases own : who = mover state
      · simp [own, moves]
      · simp [own]
    · exact ⟨fun _ => none, fun _ => fun active => moves active.1⟩

@[reducible] def signals : InfoSignals arena where
  PublicSignal := Stage
  PrivateSignal _ := Unit
  initialPublic := .initial
  initialPrivate _ := ()
  publicSignal event := event.target
  privateSignal _ _ := ()
  InfoState _ := Stage
  initInfo _ _ state := state
  pushInfo _ _ _ _ state := state

theorem info_state (who : Bool) {state} (trace : arena.Trace state) :
    signals.infoOf who trace = state := by
  cases trace <;> rfl

@[reducible] def model : InformationModel arena where
  toInfoSignals := signals
  menu who state := {choice | match choice with
    | none => ¬ arena.active state who
    | some _ => arena.active state who}
  menu_adequate := by
    intro who state trace choice
    rw [info_state]
    cases choice <;> simp [LegalOption, arena]

def policy (laws : Stage → PMF Bool) : ∀ who, model.BehavioralPolicy who := fun who state =>
  if moves : arena.active state who then
    (laws state).map (fun bit => ⟨some bit, moves⟩)
  else PMF.pure ⟨none, moves⟩

theorem step_depth (state target : Stage) (joint : {joint // arena.Legal state joint})
    (supported : target ∈ (arena.step state joint).support) : depth target = depth state + 1 := by
  cases state with
  | initial =>
      obtain ⟨bit, _, rfl⟩ := PMF.support_map .. ▸ supported
      rfl
  | choose context => cases (PMF.mem_support_pure_iff _ _).mp supported; rfl
  | positive context choice => cases (PMF.mem_support_pure_iff _ _).mp supported; rfl
  | negative context choice plus => cases (PMF.mem_support_pure_iff _ _).mp supported; rfl
  | done context choice plus minus => exact (joint.2.1 rfl).elim

theorem trace_depth {state} (trace : arena.Trace state) : trace.length = depth state := by
  induction trace with
  | start => rfl
  | extend prior joint legal realized ih =>
      change prior.length + 1 = _
      rw [ih]
      exact (step_depth _ _ ⟨joint, legal⟩ realized).symm

theorem bounded : arena.BoundedHorizon 4 := by
  intro state trace long
  change depth state = 4
  rw [trace_depth trace] at long
  cases state <;> simp_all [depth]

def decisionHistory (context : Bool) : arena.History :=
  arena.initHistory.extend (joint := fun _ => none)
    ⟨by decide, fun _ => by simp [arena, acting]⟩ (by
      change Stage.choose context ∈ ((PMF.uniformOfFintype Bool).map Stage.choose).support
      exact PMF.support_map .. ▸ ⟨context, PMF.mem_support_uniformOfFintype context, rfl⟩)

def reward (context choice : Bool) : ℝ := if choice = context then 2 else 0

def payoff : Stage → ℝ
  | .done context choice plus minus => reward context choice + (if plus then 1 else 0) -
      (if minus then 1 else 0)
  | _ => 0

theorem payoff_bounded (state : Stage) : |payoff state| ≤ 3 := by
  cases state <;> simp only [payoff]
  all_goals try norm_num
  rename_i context choice plus minus
  cases context <;> cases choice <;> cases plus <;> cases minus <;> norm_num [reward]

/-- The canonical history runner, projected to current states, uses exactly the
specified information-local randomized choice at every actual decision. -/
theorem step_deterministic (state : Stage) (moves : acting state)
    (joint : {joint // arena.Legal state joint}) :
    arena.step state joint = PMF.pure (advance state ((joint.1 (mover state)).getD false)) := by
  cases state <;> simp_all [arena, acting]

theorem step_map_state (laws : Stage → PMF Bool) (history : arena.History)
    (moves : acting history.state) :
    (model.runBehavioralFrom (policy laws) 1 history).map History.state =
      (laws history.state).map (advance history.state) := by
  have running : ¬ arena.terminal history.state := by
    cases eq : history.state <;> simp_all [arena, acting, depth]
  rw [model.runBehavioralFrom_succ_of_not_terminal (policy laws) 0 running, PMF.map_bind]
  calc
    _ = (model.behavioralJoint (policy laws) history.trace running).bind
        (arena.step history.state) := by
      apply bind_congr_on_support
      intro joint _
      rw [map_bindOnSupport]
      calc
        _ = (arena.step history.state joint).bind PMF.pure := by
          apply bindOnSupport_eq_bind_of_eq_on_support
          intro target realized
          change (PMF.pure (history.extend joint.2 realized)).map History.state = PMF.pure target
          rw [PMF.pure_map]
          rfl
        _ = _ := PMF.bind_pure _
    _ = (policy laws (mover history.state) (model.infoOf (mover history.state) history.trace)).map
        (fun choice => advance history.state (choice.1.getD false)) := by
      rw [model.behavioralJoint_eq_map_of_at_most_one_active (policy laws) history.trace
        running (mover history.state) (fun _ active => active.2), PMF.bind_map,
        ← PMF.bind_pure_comp]
      apply bind_congr_on_support
      intro choice _
      dsimp only [Function.comp_def]
      apply (step_deterministic _ moves _).trans
      congr 1
      simp [ExecutionProtocol.singletonJoint]
    _ = _ := by
      change (policy laws (mover history.state)
        (signals.infoOf (mover history.state) history.trace)).map _ = _
      rw [info_state]
      simp only [policy, and_true, dite_eq_left moves, PMF.map_comp]
      rfl


def indicator (bit : Bool) : ℝ := if bit then 1 else 0

def laws (localLaw : Bool → PMF Bool) (tail : PMF Bool) : Stage → PMF Bool
  | .choose context => localLaw context
  | _ => tail

def continuation (localLaw : Bool → PMF Bool) (tail : PMF Bool) : Stage → ℝ
  | .initial => 0
  | .choose context => expect (localLaw context) (reward context)
  | .positive context choice => reward context choice
  | .negative context choice plus => reward context choice + indicator plus - expect tail indicator
  | state@(.done _ _ _ _) => payoff state

theorem step_expect_state (rates : Stage → PMF Bool) (history : arena.History)
    (moves : acting history.state) (value : Stage → ℝ) :
    expect (model.runBehavioralFrom (policy rates) 1 history) (fun next => value next.state) =
      expect (rates history.state) (fun bit => value (advance history.state bit)) := by
  change expect _ (value ∘ (History.state : arena.History → Stage)) = _
  rw [← expect_map (History.state : arena.History → Stage) _ value,
    step_map_state rates history moves, expect_map]
  rfl

theorem continuation_step (localLaw : Bool → PMF Bool) (tail : PMF Bool)
    (history : arena.History) (moves : acting history.state) :
    expect (model.runBehavioralFrom (policy (laws localLaw tail)) 1 history)
        (fun next => continuation localLaw tail next.state) =
      continuation localLaw tail history.state := by
  rw [step_expect_state _ history moves]
  cases stateEq : history.state <;> simp_all only [acting, laws, advance, continuation]
  · rw [expect_sub (payoffIntegrable_of_finite tail _) (payoffIntegrable_constant tail _),
      expect_add (payoffIntegrable_constant tail _) (payoffIntegrable_of_finite tail _)]
    simp only [expect_constant]
    ring
  · change expect tail (fun bit => _ + _ - indicator bit) = _
    rw [expect_sub (payoffIntegrable_constant tail _) (payoffIntegrable_of_finite tail _),
      expect_constant]
    rfl

theorem stopped_value (localLaw : Bool → PMF Bool) (tail : PMF Bool)
    (start : arena.History) (notInitial : start.state ≠ .initial) :
    expect (model.runBehavioralUntil bounded.wellFoundedHistories (policy (laws localLaw tail))
        (fun _ => False) start) (fun final => payoff final.state) =
      continuation localLaw tail start.state := by
  revert notInitial
  induction start using bounded.wellFoundedHistories.induction with
  | _ history ih =>
  intro different
  by_cases ended : arena.terminal history.state
  · rw [model.runBehavioralUntil_of_terminal _ _ ended, expect_pure]
    cases stateEq : history.state <;> simp_all [arena, depth, continuation]
  have moves : acting history.state := by
    cases stateEq : history.state <;> simp_all [arena, acting, depth]
  rw [model.runBehavioralUntil_of_running _ _ (by trivial) ended,
    expect_bind_tower_bounded _ _ _ (fun final : arena.History => payoff_bounded final.state)]
  calc
    _ = expect (model.runBehavioralFrom (policy (laws localLaw tail)) 1 history)
        (fun next => continuation localLaw tail next.state) := by
      apply expect_congr_on_support
      intro next reached
      have step := model.mem_support_runBehavioralFrom_one _ ended reached
      apply ih next step.1
      obtain ⟨joint, legal, realized⟩ := step.1
      have counted := step_depth history.state next.state ⟨joint, legal⟩ realized
      intro initialEq
      rw [initialEq] at counted
      simp only [depth] at counted
      omega
    _ = _ := continuation_step localLaw tail history moves


theorem next_not_initial (strategy : ∀ who, model.BehavioralPolicy who)
    (history next : arena.History) (running : ¬ arena.terminal history.state)
    (reached : next ∈ (model.runBehavioralFrom strategy 1 history).support) :
    next.state ≠ .initial := by
  obtain ⟨⟨joint, legal, realized⟩, _⟩ :=
    model.mem_support_runBehavioralFrom_one strategy running reached
  have counted := step_depth history.state next.state ⟨joint, legal⟩ realized
  intro initialEq
  rw [initialEq] at counted
  simp only [depth] at counted
  omega

def residualCharge (sourceTail targetTail : PMF Bool) : Stage → ℝ
  | .positive _ _ => expect sourceTail indicator - expect targetTail indicator
  | .negative _ _ _ => -(expect sourceTail indicator - expect targetTail indicator)
  | _ => 0

theorem residual_eq (localLaw : Bool → PMF Bool) (sourceTail targetTail : PMF Bool)
    (history : arena.History) (notInitial : history.state ≠ .initial) :
    model.stoppedContinuationResidual bounded.wellFoundedHistories
        (policy (laws localLaw sourceTail)) (policy (laws localLaw targetTail)) (fun _ => False)
        (fun final => payoff final.state) history =
      residualCharge sourceTail targetTail history.state := by
  classical
  by_cases ended : arena.terminal history.state
  · rw [stoppedContinuationResidual, ite_eq_left (Or.inr ended)]
    cases stateEq : history.state <;> simp_all [arena, depth, residualCharge]
  have moves : acting history.state := by
    cases stateEq : history.state <;> simp_all [arena, acting, depth]
  rw [stoppedContinuationResidual, ite_eq_right (by simpa using ended),
    stopped_value localLaw targetTail history notInitial]
  have continuationEq :
      expect (model.runBehavioralFrom (policy (laws localLaw sourceTail)) 1 history)
        (fun next => expect (model.runBehavioralUntil bounded.wellFoundedHistories
          (policy (laws localLaw targetTail)) (fun _ => False) next)
          (fun final => payoff final.state)) =
      expect (model.runBehavioralFrom (policy (laws localLaw sourceTail)) 1 history)
        (fun next => continuation localLaw targetTail next.state) := by
    apply expect_congr_on_support
    intro next reached
    exact stopped_value localLaw targetTail next
      (next_not_initial _ history next ended reached)
  rw [continuationEq, step_expect_state _ history moves]
  cases stateEq : history.state <;>
    simp_all only [acting, laws, advance, continuation, residualCharge]
  · exact sub_self _
  · rw [expect_sub (payoffIntegrable_of_finite sourceTail _)
      (payoffIntegrable_constant sourceTail _),
      expect_add (payoffIntegrable_constant sourceTail _) (payoffIntegrable_of_finite sourceTail _)]
    simp only [expect_constant]
    ring
  · change expect sourceTail (fun bit => _ + _ - indicator bit) - _ = _
    rw [expect_sub (payoffIntegrable_constant sourceTail _)
      (payoffIntegrable_of_finite sourceTail _), expect_constant]
    dsimp only [indicator]
    ring

def measured (absolute : Bool) (value : ℝ) : ℝ := if absolute then |value| else value

def remainingCharge (absolute : Bool) (difference : ℝ) : Stage → ℝ
  | .choose _ | .positive _ _ => measured absolute difference + measured absolute (-difference)
  | .negative _ _ _ => measured absolute (-difference)
  | _ => 0

/-- Both the signed and absolute costs are evaluated by the existing stopped
runner, using the actual two successive residual-producing decisions. -/
theorem expected_residual_charge (localLaw : Bool → PMF Bool) (sourceTail targetTail : PMF Bool)
    (absolute : Bool) (start : arena.History) (notInitial : start.state ≠ .initial) :
    let residual := model.stoppedContinuationResidual bounded.wellFoundedHistories
      (policy (laws localLaw sourceTail)) (policy (laws localLaw targetTail)) (fun _ => False)
      (fun final => payoff final.state)
    model.expectedCharge bounded.wellFoundedHistories (policy (laws localLaw sourceTail))
        (fun _ => False) (fun history => measured absolute (residual history)) start =
      remainingCharge absolute (expect sourceTail indicator - expect targetTail indicator)
        start.state := by
  intro residual
  have chargedBounded : ∀ history, |measured absolute (residual history)| ≤ 6 := by
    intro history
    have boundedResidual := model.stoppedContinuationResidual_abs_le bounded.wellFoundedHistories
      (policy (laws localLaw sourceTail)) (policy (laws localLaw targetTail)) (fun _ => False)
      (fun final => payoff final.state) (by norm_num : (0 : ℝ) ≤ 3)
      (fun final => payoff_bounded final.state) history
    norm_num at boundedResidual
    cases absolute <;> simpa only [measured, Bool.false_eq_true, ↓reduceIte, abs_abs] using
      boundedResidual
  revert notInitial
  induction start using bounded.wellFoundedHistories.induction with
  | _ history ih =>
  intro different
  by_cases ended : arena.terminal history.state
  · rw [expectedCharge, model.runBehavioralUntil_of_terminal _ _ ended, expect_pure, sub_self]
    cases stateEq : history.state <;> simp_all [arena, depth, remainingCharge]
  have moves : acting history.state := by
    cases stateEq : history.state <;> simp_all [arena, acting, depth]
  have drift := model.expectedCharge_drift_of_abs_le bounded bounded.wellFoundedHistories
    (policy (laws localLaw sourceTail)) (fun _ => False)
    (fun current => measured absolute (residual current)) chargedBounded history (by trivial) ended
  have nextEq :
      expect (model.runBehavioralFrom (policy (laws localLaw sourceTail)) 1 history)
          (model.expectedCharge bounded.wellFoundedHistories (policy (laws localLaw sourceTail))
            (fun _ => False) (fun current => measured absolute (residual current))) =
        expect (model.runBehavioralFrom (policy (laws localLaw sourceTail)) 1 history)
          (fun next => remainingCharge absolute
            (expect sourceTail indicator - expect targetTail indicator) next.state) := by
    apply expect_congr_on_support
    intro next reached
    exact ih next (model.mem_support_runBehavioralFrom_one _ ended reached).1
      (next_not_initial _ history next ended reached)
  rw [nextEq, step_expect_state _ history moves] at drift
  rw [← drift]
  change measured absolute (residual history) + _ = _
  rw [show residual history = residualCharge sourceTail targetTail history.state from
    residual_eq localLaw sourceTail targetTail history different]
  cases stateEq : history.state <;>
    simp_all only [acting, laws, advance, residualCharge, remainingCharge]
  all_goals simp only [expect_constant, measured, abs_zero, ite_self, zero_add, add_zero]

theorem conditional_values_equal (localLaw : Bool → PMF Bool) (sourceTail targetTail : PMF Bool)
    (context : Bool) :
    expect (model.runBehavioralUntil bounded.wellFoundedHistories
      (policy (laws localLaw sourceTail))
        (fun _ => False) (decisionHistory context)) (fun final => payoff final.state) =
      expect (model.runBehavioralUntil bounded.wellFoundedHistories
        (policy (laws localLaw targetTail)) (fun _ => False) (decisionHistory context))
        (fun final => payoff final.state) := by
  apply sub_eq_zero.mp
  rw [model.expect_runBehavioralUntil_sub_eq_expectedCharge bounded bounded.wellFoundedHistories
    _ _ (fun _ => False) (fun final => payoff final.state) (by norm_num : (0 : ℝ) ≤ 3)
    (fun final => payoff_bounded final.state)]
  have canceled := expected_residual_charge localLaw sourceTail targetTail false
    (decisionHistory context) (by simp [decisionHistory])
  simpa [decisionHistory, remainingCharge, measured] using canceled


def decisionSite (context : Bool) : model.InformationSite false :=
  ⟨.choose context, ⟨⟨decisionHistory context, info_state _ _⟩,
    by simp [decisionHistory, arena, depth], false, by simp [arena, acting, mover]⟩⟩

def decisionMember (context : Bool) : model.InformationHistory false (decisionSite context).1 :=
  ⟨decisionHistory context, info_state _ _⟩

/-- Alternatives are information-local randomized laws at the two observed
contexts; each is interpreted as an actual legal behavioral policy fragment. -/
def decisionContext (tail : PMF Bool) (context : Bool) :
    Context (Bool → PMF Bool) arena.History :=
  Context.ofBelief (PMF.pure (decisionMember context))
    (fun history alternative => model.runBehavioralUntil bounded.wellFoundedHistories
      (policy (laws alternative tail)) (fun _ => False) history.1)
    (fun final => payoff final.state)

theorem decisionContext_value (tail : PMF Bool) (context : Bool) (alternative : Bool → PMF Bool) :
    (decisionContext tail context).value alternative =
      expect (model.runBehavioralUntil bounded.wellFoundedHistories (policy (laws alternative tail))
        (fun _ => False) (decisionHistory context)) (fun final => payoff final.state) := by
  change expect ((PMF.pure (decisionMember context)).bind _) _ = _
  rw [PMF.pure_bind]
  rfl

/-- Exact conditional gain transport covers every legal information-dependent
randomized alternative, rather than just the initialized or honest choice. -/
theorem conditional_gain_equal (sourceTail targetTail : PMF Bool) (context : Bool)
    (incumbent alternative : Bool → PMF Bool) :
    (decisionContext sourceTail context).value alternative -
        (decisionContext sourceTail context).value incumbent =
      (decisionContext targetTail context).value alternative -
        (decisionContext targetTail context).value incumbent := by
  simp only [decisionContext_value]
  rw [conditional_values_equal alternative sourceTail targetTail context,
    conditional_values_equal incumbent sourceTail targetTail context]

def rate (n : Nat) : ℝ := 1 / ((n : ℝ) + 2)

theorem rate_positive (n : Nat) : 0 < rate n := by unfold rate; positivity

theorem rate_le_half (n : Nat) : rate n ≤ 1 / 2 := by
  unfold rate
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < n + 2) (by norm_num : (0 : ℝ) < 2)]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

def trembling (n : Nat) (half : Bool) (main : Bool) : PMF Bool :=
  mix (if half then rate n / 2 else rate n)
    (by have positive := rate_positive n; split <;> positivity)
    (by split <;> nlinarith [rate_le_half n]) (PMF.uniformOfFintype Bool) (PMF.pure main)

theorem trembling_full (n : Nat) (half main bit : Bool) :
    bit ∈ (trembling n half main).support := by
  apply mem_support_mix_left
  · have positive := rate_positive n
    split <;> positivity
  · exact PMF.mem_support_uniformOfFintype bit

theorem trembling_mean (n : Nat) (half : Bool) :
    expect (trembling n half false) indicator = if half then rate n / 4 else rate n / 2 := by
  rw [trembling, expect_mix _ _ _ _ _ _ (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_pure _ _), expect_uniformOfFintype, expect_pure]
  norm_num [Fintype.sum_bool, indicator]
  split <;> ring

def baselineLaw (n : Nat) (context : Bool) : PMF Bool := trembling n false context

def approximation (n : Nat) (half : Bool) : ∀ who, model.BehavioralPolicy who :=
  policy (laws (baselineLaw n) (trembling n half false))

theorem policy_full (rates : Stage → PMF Bool) (full : ∀ state bit, bit ∈ (rates state).support)
    (who : Bool) (info : model.InfoState who) (choice : model.Choice who info) :
    choice ∈ (policy rates who info).support := by
  rcases choice with ⟨choice, valid⟩
  cases choice with
  | none =>
      change ¬ arena.active info who at valid
      rw [policy, dite_eq_right valid]
      exact (PMF.mem_support_pure_iff _ _).mpr (Subtype.ext rfl)
  | some bit =>
      change arena.active info who at valid
      rw [policy, dite_eq_left valid, PMF.support_map]
      exact ⟨bit, full info bit, Subtype.ext rfl⟩

/-- One common profile is used for both contexts and every local deviation at
an index. Every legal action has positive mass in both approximation families. -/
theorem approximation_full (n : Nat) (half : Bool) (who : Bool) (info : model.InfoState who)
    (choice : model.Choice who info) : choice ∈ (approximation n half who info).support := by
  apply policy_full
  intro state bit
  cases state <;> apply trembling_full

/-- Signed cancellation is strictly better than summing absolute residuals at
each genuine conditional decision, uniformly over all local laws and indices. -/
theorem conditional_cancellation_strict (n : Nat) (context : Bool) (alternative : Bool → PMF Bool) :
    let sourceTail := trembling n false false
    let targetTail := trembling n true false
    let residual := model.stoppedContinuationResidual bounded.wellFoundedHistories
      (policy (laws alternative sourceTail)) (policy (laws alternative targetTail)) (fun _ => False)
      (fun final => payoff final.state)
    model.expectedCharge bounded.wellFoundedHistories (policy (laws alternative sourceTail))
        (fun _ => False) residual (decisionHistory context) = 0 ∧
      model.expectedCharge bounded.wellFoundedHistories (policy (laws alternative sourceTail))
        (fun _ => False) (fun history => |residual history|) (decisionHistory context) =
          rate n / 2 ∧
      0 < rate n / 2 := by
  intro sourceTail targetTail residual
  have signed := expected_residual_charge alternative sourceTail targetTail false
    (decisionHistory context) (by simp [decisionHistory])
  have absolute := expected_residual_charge alternative sourceTail targetTail true
    (decisionHistory context) (by simp [decisionHistory])
  have difference : expect sourceTail indicator - expect targetTail indicator = rate n / 4 := by
    rw [trembling_mean, trembling_mean]
    norm_num
    ring
  rw [difference] at signed absolute
  have positive := rate_positive n
  have nonnegative : 0 ≤ rate n / 4 := by positivity
  simp only [remainingCharge, decisionHistory, History.extend_state, measured, Bool.false_eq_true,
    ↓reduceIte, add_neg_cancel] at signed
  simp only [remainingCharge, decisionHistory, History.extend_state, measured, ↓reduceIte,
    abs_neg, abs_of_nonneg nonnegative] at absolute
  refine ⟨signed, ?_, by positivity⟩
  calc
    _ = rate n / 4 + rate n / 4 := absolute
    _ = _ := by ring

/-- The two nonzero intermediate errors disappear from the entire conditional
gain comparison; the comparison is simultaneous for all legal deviations. -/
theorem approximation_conditional_gains (n : Nat) (context : Bool)
    (alternative : Bool → PMF Bool) :
    (decisionContext (trembling n false false) context).value alternative -
        (decisionContext (trembling n false false) context).value (baselineLaw n) =
      (decisionContext (trembling n true false) context).value alternative -
        (decisionContext (trembling n true false) context).value (baselineLaw n) :=
  conditional_gain_equal _ _ context (baselineLaw n) alternative


def decisionChoice (context bit : Bool) : model.Choice false (.choose context) :=
  ⟨some bit, ⟨trivial, rfl⟩⟩

/-- The local Bool law parameter covers the entire actual legal menu. -/
theorem decision_law_roundtrip (context : Bool) (law : PMF (model.Choice false (.choose context))) :
    (law.map (fun choice => choice.1.getD false)).map (decisionChoice context) = law := by
  rw [PMF.map_comp]
  have identity : (decisionChoice context ∘ fun choice => choice.1.getD false) = id := by
    funext choice
    apply Subtype.ext
    rcases choice with ⟨value, valid⟩
    cases value with
    | none => exact (valid ⟨trivial, rfl⟩).elim
    | some bit => rfl
  rw [identity, PMF.map_id]

def decodedLaw (alternative : model.BehavioralPolicy false) (context : Bool) : PMF Bool :=
  (alternative (.choose context)).map (fun choice => choice.1.getD false)

theorem inactive_policy (who : Bool) (info : Stage) (inactive : ¬ arena.active info who)
    (law : PMF (model.Choice who info)) : law = PMF.pure ⟨none, inactive⟩ := by
  have noneOnly (choice : model.Choice who info) : choice.1 = none := by
    rcases choice with ⟨value, valid⟩
    cases value with
    | none => rfl
    | some bit => exact (inactive valid).elim
  let : Subsingleton (model.Choice who info) := ⟨fun first second =>
    Subtype.ext ((noneOnly first).trans (noneOnly second).symm)⟩
  exact eq_pure_of_subsingleton law _

/-- An arbitrary whole focal policy has no missing tail-deviation obligation:
the other player owns both tail moves, while the focal player acts only at its
observed first context. This is equality of the actual typed profiles. -/
theorem update_eq_decoded (incumbent : Bool → PMF Bool) (tail : PMF Bool)
    (alternative : model.BehavioralPolicy false) :
    Profile.update (sig := model.behavioralSignature) (policy (laws incumbent tail)) false
        alternative = policy (laws (decodedLaw alternative) tail) := by
  funext who info
  cases who
  · rw [Profile.update_same]
    cases info
    case choose context =>
      rw [policy, dite_eq_left (show arena.active (.choose context) false from ⟨trivial, rfl⟩)]
      exact (decision_law_roundtrip context (alternative (.choose context))).symm
    all_goals
      unfold policy
      split
      · rename_i active
        simp [acting, mover] at active
      · rename_i inactive
        exact inactive_policy _ _ inactive _
  · rw [Profile.update_of_ne _ _ (by decide : true ≠ false)]
    cases info <;> rfl

/-- This continuation context evaluates every whole information-local focal
policy under the actual approximation profile and canonical stopped runner. -/
def wholePolicyContext (n : Nat) (half context : Bool) :
    Context (model.BehavioralPolicy false) arena.History :=
  Context.ofBelief (PMF.pure (decisionMember context))
    (fun history alternative => model.runBehavioralUntil bounded.wellFoundedHistories
      (Profile.update (sig := model.behavioralSignature) (approximation n half) false alternative)
      (fun _ => False) history.1) (fun final => payoff final.state)

theorem wholePolicyContext_value (n : Nat) (half context : Bool)
    (alternative : model.BehavioralPolicy false) :
    (wholePolicyContext n half context).value alternative =
      (decisionContext (trembling n half false) context).value (decodedLaw alternative) := by
  change expect ((PMF.pure (decisionMember context)).bind _) _ = _
  rw [PMF.pure_bind]
  change expect (model.runBehavioralUntil _
    (Profile.update (sig := model.behavioralSignature) (policy (laws (baselineLaw n)
      (trembling n half false))) false alternative) _ _) _ = _
  rw [update_eq_decoded, decisionContext_value]
  rfl

theorem decoded_approximation (n : Nat) (half : Bool) :
    decodedLaw (approximation n half false) = baselineLaw n := by
  funext context
  simp only [decodedLaw, approximation, policy, laws,
    dite_eq_left (show arena.active (.choose context) false from ⟨trivial, rfl⟩), PMF.map_comp]
  exact PMF.map_id _

/-- Conditional gain equality is simultaneous for every whole legal focal
policy, at both contexts and every common approximation index. -/
theorem whole_policy_conditional_gains (n : Nat) (context : Bool)
    (alternative : model.BehavioralPolicy false) :
    (wholePolicyContext n false context).value alternative -
        (wholePolicyContext n false context).value (approximation n false false) =
      (wholePolicyContext n true context).value alternative -
        (wholePolicyContext n true context).value (approximation n true false) := by
  simp only [wholePolicyContext_value, decoded_approximation]
  exact approximation_conditional_gains n context (decodedLaw alternative)

/-- The comparison is not a zero-utility indifference example: conditioning
on the observed context creates a strict profitable choice over its opposite. -/
theorem genuine_conditional_incentive (tail : PMF Bool) (context : Bool) :
    (decisionContext tail context).value (fun _ => PMF.pure context) -
        (decisionContext tail context).value (fun _ => PMF.pure (!context)) = 2 := by
  simp only [decisionContext_value]
  rw [stopped_value _ _ _ (by simp [decisionHistory]),
    stopped_value _ _ _ (by simp [decisionHistory])]
  simp [decisionHistory, continuation, expect_pure, reward]


def jointAt (state : Stage) (bit : Bool) : Bool → Option Bool :=
  fun who => if acting state ∧ who = mover state then some bit else none

theorem legal_joint {state : Stage} {joint : Bool → Option Bool}
    (legal : arena.Legal state joint) : ∃ bit, joint = jointAt state bit := by
  by_cases moves : acting state
  · obtain ⟨bit, selected⟩ := LegalOption.exists_eq_some_of_active (E := arena)
      (joint (mover state)) (arena.legalOption_of_legal legal (mover state)) ⟨moves, rfl⟩
    refine ⟨bit, ?_⟩
    funext who
    by_cases own : who = mover state
    · subst who
      simpa [jointAt, moves] using selected
    · have idle := LegalOption.eq_none_of_inactive (E := arena) (joint who)
        (arena.legalOption_of_legal legal who) (fun active => own active.2)
      simpa only [jointAt, own, and_false, ite_false] using idle
  · refine ⟨false, ?_⟩
    have idle := arena.eq_noop_of_legal_of_inactive legal (fun _ active => moves active.1)
    funext who
    simpa [jointAt, moves, ExecutionProtocol.noop] using congrFun idle who

theorem init_not_reached (state : Stage) (joint : Bool → Option Bool)
    (legal : arena.Legal state joint) : arena.init ∉ (arena.step state ⟨joint, legal⟩).support := by
  intro reached
  have impossible := step_depth state arena.init ⟨joint, legal⟩ reached
  change 0 = depth state + 1 at impossible
  omega

theorem predecessor_unique {target first second : Stage}
    {firstJoint secondJoint : Bool → Option Bool}
    (firstLegal : arena.Legal first firstJoint) (secondLegal : arena.Legal second secondJoint)
    (firstReached : target ∈ (arena.step first ⟨firstJoint, firstLegal⟩).support)
    (secondReached : target ∈ (arena.step second ⟨secondJoint, secondLegal⟩).support) :
    first = second ∧ firstJoint = secondJoint := by
  obtain ⟨firstBit, rfl⟩ := legal_joint firstLegal
  obtain ⟨secondBit, rfl⟩ := legal_joint secondLegal
  have firstRunning := firstLegal.1
  have secondRunning := secondLegal.1
  cases first <;> cases second
  case initial.initial =>
    refine ⟨rfl, ?_⟩
    funext who
    simp [jointAt, acting]
  all_goals simp_all [arena, acting, mover, depth, advance, jointAt]

theorem treeShaped : arena.IsTreeShaped :=
  arena.isTreeShaped_of_predecessor_unique init_not_reached predecessor_unique

/-- Public Stage observations retain every actual past move in this finite
example, so the Bayes law on every player's entire information fiber is forced. -/
instance (who : Bool) (info : model.InfoState who) :
    Subsingleton (model.InformationHistory who info) := by
  constructor
  rintro ⟨⟨first, firstTrace⟩, firstObserved⟩ ⟨⟨second, secondTrace⟩, secondObserved⟩
  apply Subtype.ext
  change (⟨first, firstTrace⟩ : arena.History) = ⟨second, secondTrace⟩
  have same : first = second := (info_state who firstTrace).symm.trans
    (firstObserved.trans (secondObserved.symm.trans (info_state who secondTrace)))
  subst second
  have traceEq := (treeShaped first).elim firstTrace secondTrace
  cases traceEq
  rfl

theorem antichain : model.DecisionInformationAntichain := by
  intro who site first second joint legal reached realized fuel path
  have sameState : first.1.state = second.1.state :=
    (info_state who first.1.trace).symm.trans (first.2.trans
      (second.2.symm.trans (info_state who second.1.trace)))
  have monotone := path.trace_length_le
  change first.1.trace.length + 1 ≤ second.1.trace.length at monotone
  rw [trace_depth, trace_depth, sameState] at monotone
  omega

def assessment (n : Nat) (half : Bool) : model.BehavioralAssessment :=
  model.bayesAssessment (approximation n half)
    (fun who site choice => approximation_full n half who site.1 choice) antichain

theorem assessment_belief (n : Nat) (half context : Bool) :
    (assessment n half).belief false (decisionSite context) = PMF.pure (decisionMember context) :=
  eq_pure_of_subsingleton _ _

/-- The concrete Context above is exactly the actual Bayes assessment's
continuation context, including arbitrary whole-policy focal deviations. -/
theorem assessment_context (n : Nat) (half context : Bool) :
    (assessment n half).continuationContextWith
        (fun strategy history => model.runBehavioralUntil bounded.wellFoundedHistories strategy
          (fun _ => False) history) (decisionSite context) (fun final => payoff final.state) =
      wholePolicyContext n half context := by
  unfold BehavioralAssessment.continuationContextWith wholePolicyContext
  rw [assessment_belief]
  rfl

/-- This is the actual conditional gain of two fully supported Bayes
assessment families, simultaneously for all focal whole-policy deviations.
The signed residual theorem, rather than an assumed value law, proves equality. -/
theorem assessment_conditional_gains (n : Nat) (context : Bool)
    (alternative : model.BehavioralPolicy false) :
    let run := fun strategy history =>
      model.runBehavioralUntil bounded.wellFoundedHistories strategy
      (fun _ => False) history
    let source := (assessment n false).continuationContextWith run (decisionSite context)
      (fun final => payoff final.state)
    let target := (assessment n true).continuationContextWith run (decisionSite context)
      (fun final => payoff final.state)
    source.value alternative - source.value ((assessment n false).strategy false) =
      target.value alternative - target.value ((assessment n true).strategy false) := by
  intro run source target
  dsimp only [source, target, run]
  simp only [assessment_context]
  exact whole_policy_conditional_gains n context alternative


open Filter Topology

theorem rate_vanishes : Tendsto rate atTop (nhds 0) := by
  have shifted := (tendsto_add_atTop_iff_nat 1).2
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  change Tendsto (fun n : Nat => 1 / ((n : ℝ) + 2)) atTop (nhds 0)
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using shifted

theorem trembling_converges (half main : Bool) :
    PMFConvergesPointwise (fun n => trembling n half main) (PMF.pure main) := by
  apply pmfConvergesPointwise_mix_zero
  cases half
  · exact rate_vanishes
  · simpa only [↓reduceIte, zero_div] using rate_vanishes.div_const 2

def limitingProfile : ∀ who, model.BehavioralPolicy who :=
  policy (laws (fun context => PMF.pure context) (PMF.pure false))

/-- Both actual fully supported strategy families share a single limiting
strategy. The error cancellation is uniform along the entire common index. -/
theorem approximation_converges (half who : Bool) (info : model.InfoState who) :
    PMFConvergesPointwise (fun n => approximation n half who info) (limitingProfile who info) := by
  by_cases active : arena.active info who
  · have localLimit : PMFConvergesPointwise
        (fun n => laws (baselineLaw n) (trembling n half false) info)
        (laws (fun context => PMF.pure context) (PMF.pure false) info) := by
      cases info <;> apply trembling_converges
    change PMFConvergesPointwise (fun n => policy _ who info) (policy _ who info)
    simpa only [policy, dite_eq_left active] using
      localLimit.map (fun bit => (⟨some bit, active⟩ : model.Choice who info))
  · change PMFConvergesPointwise (fun n => policy _ who info) (policy _ who info)
    simp only [policy, dite_eq_right active]
    exact pmfConvergesPointwise_const _


def limitingAssessment : model.BehavioralAssessment where
  strategy := limitingProfile
  belief := (assessment 0 false).belief

/-- Both concrete Bayes families converge as complete assessments, not merely
as strategy coordinates or beliefs at the initially selected context. -/
theorem assessment_converges (half : Bool) :
    model.BehavioralAssessmentConvergesPointwise (fun n => assessment n half)
      limitingAssessment := by
  constructor
  · intro who site
    exact approximation_converges half who site.1
  · intro who site atom
    have same (n : Nat) : (assessment n half).belief who site =
        limitingAssessment.belief who site :=
      (eq_pure_of_subsingleton _ site.2.choose).trans
        (eq_pure_of_subsingleton _ site.2.choose).symm
    simp only [same]
    exact tendsto_const_nhds

theorem limitingAssessment_consistent : limitingAssessment.IsSequentiallyConsistent antichain := by
  refine ⟨fun n => assessment n false, ?_, assessment_converges false⟩
  intro n
  constructor
  · intro who site choice
    exact approximation_full n false who site.1 choice
  · exact model.bayesAssessment_isBayesConsistent _ _ antichain

/-- The strict signed-versus-absolute improvement also covers every actual
whole-policy focal deviation, using the factual typed profile decoder. -/
theorem whole_policy_cancellation_strict (n : Nat) (context : Bool)
    (alternative : model.BehavioralPolicy false) :
    let source := Profile.update (sig := model.behavioralSignature)
      (approximation n false) false alternative
    let target := Profile.update (sig := model.behavioralSignature)
      (approximation n true) false alternative
    let residual := model.stoppedContinuationResidual bounded.wellFoundedHistories source target
      (fun _ => False) (fun final => payoff final.state)
    model.expectedCharge bounded.wellFoundedHistories source (fun _ => False) residual
        (decisionHistory context) = 0 ∧
      model.expectedCharge bounded.wellFoundedHistories source (fun _ => False)
        (fun history => |residual history|) (decisionHistory context) = rate n / 2 ∧
      0 < rate n / 2 := by
  intro source target residual
  dsimp only [residual, source, target, approximation]
  rw [update_eq_decoded, update_eq_decoded]
  exact conditional_cancellation_strict n context (decodedLaw alternative)

end GameTheoryExtensionsTests.StoppedResidual
