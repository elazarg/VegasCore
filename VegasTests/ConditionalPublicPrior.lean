/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketPublicInitialSignal
import Vegas.Expr.Simple
import GameTheory.Math.Probability.Mixture

/-! # A source prior with private correlation explained by a public bit

The public bit is uniform. Each private bit independently agrees with it with
probability three quarters. Every source state has positive mass, conditional
private-cell independence holds, and unconditional independence fails.
-/

noncomputable section

namespace VegasTests.ConditionalPublicPrior

open Vegas Vegas.SourceProgram GameTheory.Math.Probability

def context : SourceCtx Bool simpleExpr :=
  [(0, .publicData .bool), (1, .privateInput false .bool), (2, .privateInput true .bool)]

def draw (signal alice bob : Bool) : State simpleExpr context :=
  Env.cons signal (Env.cons alice (Env.cons bob (Env.empty (CellVal simpleExpr))))

def fiber (p : Bool) : PMF (State simpleExpr context) :=
  mix (3 / 4) (by norm_num) (by norm_num)
    (mix (3 / 4) (by norm_num) (by norm_num)
      (PMF.pure (draw p p p)) (PMF.pure (draw p p (!p))))
    (mix (3 / 4) (by norm_num) (by norm_num)
      (PMF.pure (draw p (!p) p)) (PMF.pure (draw p (!p) (!p))))

def prior : PMF (State simpleExpr context) :=
  mix (1 / 2) (by norm_num) (by norm_num) (fiber false) (fiber true)

def setup : Setup (Player := Bool) (L := simpleExpr) where
  context := context
  namesNodup := by decide
  initialLaw := prior
  obligations := ∅
  program := .ret []
  accounts := rfl
  exitTransfers := fun _ => 0

def signal (state : State simpleExpr context) : Bool := state.get .here


/-- The actual compiled public inputs reveal the signal used for conditional independence. -/
theorem publicInitialSignal : setup.PublicInitialSignal signal := by
  intro first second agree
  have read := agree ⟨0, by decide⟩ (by trivial)
  change first.get .here = second.get .here at read
  exact read

theorem state_eta (state : State simpleExpr context) :
    state = draw (state.get .here) (state.get (.there .here))
      (state.get (.there (.there .here))) := by
  funext name kind member
  cases member with
  | here => rfl
  | there member =>
      cases member with
      | here => rfl
      | there member =>
          cases member with
          | here => rfl
          | there impossible => nomatch impossible

theorem exists_draw (state : State simpleExpr context) :
    ∃ publicBit alice bob, state = draw publicBit alice bob :=
  ⟨_, _, _, state_eta state⟩

@[simp] theorem draw_eq {p a b q c d : Bool} :
    draw p a b = draw q c d ↔ p = q ∧ a = c ∧ b = d := by
  constructor
  · intro same
    exact ⟨congrArg (fun state : State simpleExpr context => state.get .here) same,
      congrArg (fun state : State simpleExpr context => state.get (.there .here)) same,
      congrArg (fun state : State simpleExpr context => state.get (.there (.there .here))) same⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

@[simp] theorem prior_apply (p a b : Bool) :
    prior (draw p a b) = ENNReal.ofReal
      (((if a = p then 3 else 1) * (if b = p then 3 else 1) : ℝ) / 32) := by
  classical
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top prior _) ENNReal.ofReal_ne_top).mp
  simp only [prior, fiber, mix_apply_toReal, PMF.pure_apply]
  cases p <;> cases a <;> cases b
  all_goals norm_num
  all_goals repeat rw [draw_eq]
  all_goals norm_num

/-- All eight typed states have positive prior probability. -/
theorem full_support (state : State simpleExpr context) : state ∈ setup.initialLaw.support := by
  obtain ⟨p, a, b, rfl⟩ := exists_draw state
  rw [PMF.mem_support_iff]
  change prior (draw p a b) ≠ 0
  rw [prior_apply]
  cases p <;> cases a <;> cases b <;> norm_num

example : prior (draw false false false) = ENNReal.ofReal (9 / 32 : ℝ) ∧
    prior (draw false true true) = ENNReal.ofReal (1 / 32 : ℝ) := by
  constructor <;> rw [prior_apply] <;> congr 1 <;> norm_num

@[simp] theorem splice_alice (p a b q c d : Bool) :
    splice false (draw p a b) (draw q c d) = draw q a d := by
  funext name kind member
  cases member with
  | here => rfl
  | there member =>
      cases member with
      | here => rfl
      | there member =>
          cases member with
          | here => rfl
          | there impossible => nomatch impossible

@[simp] theorem splice_bob (p a b q c d : Bool) :
    splice true (draw p a b) (draw q c d) = draw q c b := by
  funext name kind member
  cases member with
  | here => rfl
  | there member =>
      cases member with
      | here => rfl
      | there member =>
          cases member with
          | here => rfl
          | there impossible => nomatch impossible

/-- The genuinely public coordinate is preserved by each private splice. -/
theorem splice_preserves_signal (who : Bool) (mine others : State simpleExpr context) :
    signal (splice who mine others) = signal others :=
  public_signal_preserved (setup := setup) signal publicInitialSignal who mine others


/-- The private bits are independent, with nondegenerate noise, conditional on
the public bit. The identity covers all source states, not just sampled draws. -/
theorem privateInputsIndependentGiven : setup.PrivateInputsIndependentGiven signal := by
  intro who first second sameSignal
  obtain ⟨p, a, b, rfl⟩ := exists_draw first
  obtain ⟨q, c, d, rfl⟩ := exists_draw second
  change p = q at sameSignal
  subst q
  change prior (splice who (draw p a b) (draw p c d)) *
      prior (splice who (draw p c d) (draw p a b)) = prior (draw p a b) * prior (draw p c d)
  cases who with
  | false =>
      simp only [splice_alice]
      rw [prior_apply p a d, prior_apply p c b, prior_apply p a b, prior_apply p c d]
      apply (ENNReal.toReal_eq_toReal_iff'
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)).mp
      cases p <;> cases a <;> cases b <;> cases c <;> cases d <;>
        norm_num [ENNReal.toReal_mul]
  | true =>
      simp only [splice_bob]
      rw [prior_apply p c b, prior_apply p a d, prior_apply p a b, prior_apply p c d]
      apply (ENNReal.toReal_eq_toReal_iff'
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)).mp
      cases p <;> cases a <;> cases b <;> cases c <;> cases d <;>
        norm_num [ENNReal.toReal_mul]

/-- The same prior fails unconditional independence: exchanging only Alice's
bit across public signals changes the product of the two masses. -/
theorem not_unconditionally_independent : ¬ setup.PrivateInputsIndependent := by
  intro independent
  have impossible := independent false (draw false false false) (draw true true true)
  change prior (splice false (draw false false false) (draw true true true)) *
      prior (splice false (draw true true true) (draw false false false)) =
      prior (draw false false false) * prior (draw true true true) at impossible
  simp only [splice_alice] at impossible
  rw [prior_apply true false true, prior_apply false true false,
    prior_apply false false false, prior_apply true true true] at impossible
  have realImpossible := congrArg ENNReal.toReal impossible
  norm_num [ENNReal.toReal_mul] at realImpossible


/-- These public conditional-prior guards admit a prior rejected by unconditional independence. -/
theorem conditional_scope_is_strict :
    setup.PrivateInputsIndependentGiven signal ∧ setup.PublicInitialSignal signal ∧
      ¬ setup.PrivateInputsIndependent :=
  ⟨privateInputsIndependentGiven, publicInitialSignal, not_unconditionally_independent⟩

end VegasTests.ConditionalPublicPrior
