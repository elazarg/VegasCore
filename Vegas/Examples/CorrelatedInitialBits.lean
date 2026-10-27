/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.OddsEvensSetup
import Vegas.Game.ConditionedSourceBayes
import Vegas.Source.Exclusion

/-! # A common private initial bit in a genuine two-player source game

Each player initially observes its own private copy of one common bit. Both
players subsequently make fresh Boolean commitments and reveal them, with the
Odds–Evens settlement. The bit is never inserted into a public observation.
This file checks prior and information facts, not raw-runtime SE preservation.
-/

noncomputable section

namespace Vegas.Examples.CorrelatedInitialBits

open SourceProgram GameTheory.Protocol GameTheory.Math.Probability
open scoped ENNReal

abbrev Player := Bool

def context : SourceCtx Player simpleExpr :=
  [(0, .privateInput false .bool), (1, .privateInput true .bool)]

def sourceState (first second : Bool) : State simpleExpr context :=
  Env.cons first (Env.cons second (Env.empty _))

def sourceInitial (bit : Bool) := sourceState bit bit

def program : SourceProgram Player simpleExpr context ∅ :=
  .commit 2 false (by decide) (OddsEvens.acceptGuard false 2) <|
  .commit 3 true (by decide) (OddsEvens.acceptGuard true 3) <|
  .reveal 4 false 2 (by decide) (.there .here) (by decide) <|
  .reveal 5 true 3 (by decide) (.there .here) (by decide) <|
  .ret [(false, OddsEvens.cashExpr false (.var 4 (.there .here)) (.var 5 .here)),
    (true, OddsEvens.cashExpr true (.var 4 (.there .here)) (.var 5 .here))]

def setup : Setup (Player := Player) (L := simpleExpr) where
  context := context
  namesNodup := by decide
  initialLaw := mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure (sourceInitial false)) (PMF.pure (sourceInitial true))
  obligations := ∅
  program := program
  accounts := rfl
  exitTransfers := fun _ => 0

def signal (initial : State simpleExpr context) : Bool := initial.get .here

theorem sourceState_eq_iff (first second otherFirst otherSecond : Bool) :
    sourceState first second = sourceState otherFirst otherSecond ↔
      first = otherFirst ∧ second = otherSecond := by
  constructor
  · intro same
    exact ⟨congrArg (fun state : State simpleExpr context => state.get .here) same,
      congrArg (fun state : State simpleExpr context => state.get (.there .here)) same⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem sourceState_exists (initial : State simpleExpr context) :
    ∃ first second, sourceState first second = initial := by
  refine ⟨initial.get .here, initial.get (.there .here), ?_⟩
  funext name kind cell
  cases cell with
  | here => rfl
  | there cell =>
      cases cell with
      | here => rfl
      | there cell => cases cell

theorem splice_false (a b c d : Bool) :
    splice false (sourceState a b) (sourceState c d) = sourceState a d := by
  funext name kind cell
  cases cell with
  | here => rfl
  | there cell =>
      cases cell with
      | here => rfl
      | there cell => cases cell

theorem splice_true (a b c d : Bool) :
    splice true (sourceState a b) (sourceState c d) = sourceState c b := by
  funext name kind cell
  cases cell with
  | here => rfl
  | there cell =>
      cases cell with
      | here => rfl
      | there cell => cases cell

private theorem pure_sourceState_apply (first second otherFirst otherSecond : Bool) :
    (PMF.pure (sourceState otherFirst otherSecond)) (sourceState first second) =
      if first = otherFirst ∧ second = otherSecond then 1 else 0 := by
  classical
  by_cases same : first = otherFirst ∧ second = otherSecond
  · have states := (sourceState_eq_iff first second otherFirst otherSecond).mpr same
    have atom := (congrArg (fun state =>
      (PMF.pure (sourceState otherFirst otherSecond)) state) states).trans
        (PMF.pure_apply_self _)
    exact atom.trans (ite_eq_left same).symm
  · have different : sourceState first second ≠ sourceState otherFirst otherSecond :=
      fun states => same ((sourceState_eq_iff first second otherFirst otherSecond).mp states)
    exact (PMF.pure_apply_of_ne _ _ different).trans (ite_eq_right same).symm

theorem initialLaw_apply (first second : Bool) :
    setup.initialLaw (sourceState first second) = if first = second then 1 / 2 else 0 := by
  classical
  calc
    _ = ENNReal.ofReal (1 / 2 : ℝ) *
        (PMF.pure (sourceInitial false)) (sourceState first second) +
      ENNReal.ofReal (1 - 1 / 2 : ℝ) *
        (PMF.pure (sourceInitial true)) (sourceState first second) := rfl
    _ = ENNReal.ofReal (1 / 2 : ℝ) *
        (if first = false ∧ second = false then 1 else 0) +
      ENNReal.ofReal (1 - 1 / 2 : ℝ) *
        (if first = true ∧ second = true then 1 else 0) :=
      congrArg₂ (fun x y => ENNReal.ofReal (1 / 2 : ℝ) * x +
        ENNReal.ofReal (1 - 1 / 2 : ℝ) * y)
        (pure_sourceState_apply first second false false)
        (pure_sourceState_apply first second true true)
    _ = _ := by
      have half : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
      cases first <;> cases second <;> norm_num [half]

theorem initialLaw_support (initial : State simpleExpr context)
    (member : initial ∈ setup.initialLaw.support) : ∃ bit, sourceInitial bit = initial := by
  obtain ⟨first, second, rfl⟩ := sourceState_exists initial
  have same : first = second := by
    by_contra different
    have nonzero := (PMF.mem_support_iff _ _).mp member
    exact nonzero ((initialLaw_apply first second).trans (ite_eq_right different))
  subst second
  exact ⟨first, rfl⟩

theorem signal_supported (bit : Bool) : bit ∈ (setup.initialLaw.map signal).support := by
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨sourceInitial bit, ?_, rfl⟩
  rw [PMF.mem_support_iff]
  change setup.initialLaw (sourceState bit bit) ≠ 0
  exact ne_of_eq_of_ne (initialLaw_apply bit bit) (by norm_num)

theorem not_independent : ¬ setup.PrivateInputsIndependentGiven (fun _ => ()) := by
  intro independent
  have forbidden := independent false (sourceState false false) (sourceState true true) rfl
  have left : setup.initialLaw (splice false (sourceState false false) (sourceState true true)) *
      setup.initialLaw (splice false (sourceState true true) (sourceState false false)) = 0 := by
    calc
      _ = setup.initialLaw (sourceState false true) *
          setup.initialLaw (sourceState true false) := congrArg₂ (· * ·)
        (congrArg (fun state => setup.initialLaw state) (splice_false false false true true))
        (congrArg (fun state => setup.initialLaw state) (splice_false true true false false))
      _ = (0 : ℝ≥0∞) * 0 :=
        congrArg₂ (· * ·) (initialLaw_apply false true) (initialLaw_apply true false)
      _ = 0 := by simp
  have right : setup.initialLaw (sourceState false false) *
      setup.initialLaw (sourceState true true) = (1 / 2 : ℝ≥0∞) * (1 / 2) :=
    congrArg₂ (· * ·) (initialLaw_apply false false) (initialLaw_apply true true)
  have impossible := left.symm.trans (forbidden.trans right)
  norm_num at impossible

private theorem no_public_initial_input (input : (graph setup).InputId) :
    ¬ (graph setup).fieldPublic (.inl input) := by
  intro visible
  fin_cases input <;> change False at visible <;> exact visible

/-- The actual public initializer has no cells carrying the common bit. -/
theorem publicSignal_constant {Public : Type*} (observed : State simpleExpr context → Public)
    (observable : setup.PublicInitialSignal observed) (first second : State simpleExpr context) :
    observed first = observed second :=
  observable first second (fun input visible => False.elim (no_public_initial_input input visible))

theorem signal_not_public : ¬ setup.PublicInitialSignal signal := by
  intro observable
  have impossible := publicSignal_constant signal observable
    (sourceInitial false) (sourceInitial true)
  cases impossible

/-- No alternative signal determined by the existing public initial inputs
can make this prior satisfy the retained independence hypothesis. -/
theorem not_independent_of_publicSignal {Public : Type*}
    (observed : State simpleExpr context → Public)
    (observable : setup.PublicInitialSignal observed) :
    ¬ setup.PrivateInputsIndependentGiven observed := by
  intro independent
  apply not_independent
  intro who first second _
  exact independent who first second (publicSignal_constant observed observable first second)

theorem conditioned_initialLaw (bit : Bool) :
    (setup.conditionInitial signal bit).initialLaw = PMF.pure (sourceInitial bit) := by
  apply pmf_eq_pure_of_support_subset_singleton
  intro initial member
  have info := mem_support_fiberPosterior (signal_supported bit) member
  obtain ⟨other, rfl⟩ := initialLaw_support initial info.2
  have same := info.1
  change other = bit at same
  cases same
  rfl

theorem conditioned_independent (bit : Bool) :
    (setup.conditionInitial signal bit).PrivateInputsIndependentGiven (fun _ => ()) := by
  classical
  intro who first second _
  obtain ⟨a, b, rfl⟩ := sourceState_exists first
  obtain ⟨c, d, rfl⟩ := sourceState_exists second
  simp only [conditioned_initialLaw]
  have factor (first second : Bool) :
      (PMF.pure (sourceInitial bit)) (sourceState first second) =
        (if first = bit then (1 : ℝ≥0∞) else 0) *
          (if second = bit then 1 else 0) := by
    exact (pure_sourceState_apply first second bit bit).trans (by
      by_cases hfirst : first = bit <;> by_cases hsecond : second = bit <;>
        simp [hfirst, hsecond])
  cases who
  · calc
      _ = (PMF.pure (sourceInitial bit)) (sourceState a d) *
          (PMF.pure (sourceInitial bit)) (sourceState c b) := congrArg₂ (· * ·)
        (congrArg (fun state => (PMF.pure (sourceInitial bit)) state) (splice_false a b c d))
        (congrArg (fun state => (PMF.pure (sourceInitial bit)) state) (splice_false c d a b))
      _ = _ := by
        have first := congrArg₂ (· * ·) (factor a d) (factor c b)
        have second := congrArg₂ (· * ·) (factor a b) (factor c d)
        refine first.trans (Eq.trans ?_ second.symm)
        ac_rfl
  · calc
      _ = (PMF.pure (sourceInitial bit)) (sourceState c b) *
          (PMF.pure (sourceInitial bit)) (sourceState a d) := congrArg₂ (· * ·)
        (congrArg (fun state => (PMF.pure (sourceInitial bit)) state) (splice_true a b c d))
        (congrArg (fun state => (PMF.pure (sourceInitial bit)) state) (splice_true c d a b))
      _ = _ := by
        have first := congrArg₂ (· * ·) (factor c b) (factor a d)
        have second := congrArg₂ (· * ·) (factor a b) (factor c d)
        refine first.trans (Eq.trans ?_ second.symm)
        ac_rfl

theorem conditioned_observable (bit : Bool) :
    (setup.conditionInitial signal bit).PublicInitialSignal (fun _ => ()) := by
  intro _ _ _
  rfl

instance : setup.FiniteInitialLaw where
  support_finite := (Set.finite_range sourceInitial).subset fun initial member =>
    initialLaw_support initial member

theorem finiteBindingTypes : program.FiniteBindingTypes :=
  ⟨inferInstance, inferInstance, trivial⟩

instance : Finite setup.intendedProtocol.History := setup.intended_finite_history finiteBindingTypes

theorem wellFormed : setup.WellFormed where
  initialValues := by
    intro initial _ name owner payload cell
    cases cell with
    | there cell =>
        cases cell with
        | there cell => cases cell
  guardsSatisfiable := by
    intro initial _
    exact ⟨⟨false, rfl⟩, fun _ _ => ⟨⟨false, rfl⟩, fun _ _ => trivial⟩⟩

/-- Each player's actual initial observation determines the common bit on
the prior's support, despite the absence of public initial cells. -/
theorem signal_eq_of_initial_observe_eq (who : Player)
    {first second : State simpleExpr context}
    (firstMember : first ∈ setup.initialLaw.support)
    (secondMember : second ∈ setup.initialLaw.support)
    (observed : sourceObserve who first = sourceObserve who second) :
    signal first = signal second := by
  obtain ⟨first, rfl⟩ := initialLaw_support first firstMember
  obtain ⟨second, rfl⟩ := initialLaw_support second secondMember
  cases who
  · have bits := congrArg (fun view : SourceObservation simpleExpr false context =>
      view.cells 0 (.privateInput false .bool) .here) observed
    exact Option.some.inj bits
  · have bits := congrArg (fun view : SourceObservation simpleExpr true context =>
      view.cells 1 (.privateInput true .bool) (.there .here)) observed
    exact Option.some.inj bits

end Vegas.Examples.CorrelatedInitialBits
