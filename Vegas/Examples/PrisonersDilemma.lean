/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Examples.DependencySemantics

/-!
# Prisoner's Dilemma

Build-tested checked-program examples for the canonical frontier EventGraph
semantics.
-/

namespace Vegas
namespace Examples

open GameTheory
open ToEventGraph

/-! ## Prisoner's Dilemma -/

namespace PrisonersDilemma

inductive Player where
  | row
  | col
deriving DecidableEq, Repr, Fintype

def rowSecret : VarId := 0
def colSecret : VarId := 1
def rowPublic : VarId := 2
def colPublic : VarId := 3

abbrev Γ0 : VCtx Player L := []
abbrev Γ2 : VCtx Player L :=
  [(colSecret, .sealed Player.col .bool),
   (rowSecret, .sealed Player.row .bool)]
abbrev Γ3 : VCtx Player L :=
  [(rowPublic, .pub .bool),
   (colSecret, .sealed Player.col .bool),
   (rowSecret, .sealed Player.row .bool)]
abbrev Γ4 : VCtx Player L :=
  [(colPublic, .pub .bool),
   (rowPublic, .pub .bool),
   (colSecret, .sealed Player.col .bool),
   (rowSecret, .sealed Player.row .bool)]

def hRowSecretΓ2 :
    VHasVar Γ2 rowSecret (.sealed Player.row .bool) :=
  .there .here

def hColSecretΓ3 :
    VHasVar Γ3 colSecret (.sealed Player.col .bool) :=
  .there .here

def hColPublicPayoff :
    HasVar (erasePubVCtx Γ4) colPublic .bool :=
  .here

def hRowPublicPayoff :
    HasVar (erasePubVCtx Γ4) rowPublic .bool :=
  .there .here

def rowChoice : Expr (erasePubVCtx Γ4) .bool :=
  .var rowPublic hRowPublicPayoff

def colChoice : Expr (erasePubVCtx Γ4) .bool :=
  .var colPublic hColPublicPayoff

/-- Row payoff: `(C,C)=2`, `(C,D)=0`, `(D,C)=3`, `(D,D)=1`. -/
def rowPayoff : Expr (erasePubVCtx Γ4) .int :=
  .ite rowChoice
    (.ite colChoice (.constInt 2) (.constInt 0))
    (.ite colChoice (.constInt 3) (.constInt 1))

/-- Column payoff: `(C,C)=2`, `(C,D)=3`, `(D,C)=0`, `(D,D)=1`. -/
def colPayoff : Expr (erasePubVCtx Γ4) .int :=
  .ite rowChoice
    (.ite colChoice (.constInt 2) (.constInt 3))
    (.ite colChoice (.constInt 0) (.constInt 1))

def payoffEnv (row col : Bool) :
    Env simpleExpr.Val (erasePubVCtx Γ4) :=
  Env.cons (x := colPublic) col
    (Env.cons (x := rowPublic) row (Env.empty simpleExpr.Val))

theorem payoff_table (row col : Bool) :
    (evalExpr rowPayoff (payoffEnv row col),
      evalExpr colPayoff (payoffEnv row col)) =
      match row, col with
      | true, true => (2, 2)
      | true, false => (0, 3)
      | false, true => (3, 0)
      | false, false => (1, 1) := by
  cases row <;> cases col <;> rfl

theorem row_defect_payoff_gt_cooperate (col : Bool) :
    evalExpr rowPayoff (payoffEnv false col) >
      evalExpr rowPayoff (payoffEnv true col) := by
  cases col <;> decide

theorem col_defect_payoff_gt_cooperate (row : Bool) :
    evalExpr colPayoff (payoffEnv row false) >
      evalExpr colPayoff (payoffEnv row true) := by
  cases row <;> decide

abbrev ActionProfile := Player → Bool

def actionPayoff (σ : ActionProfile) : Player → Int
  | Player.row =>
      evalExpr rowPayoff (payoffEnv (σ Player.row) (σ Player.col))
  | Player.col =>
      evalExpr colPayoff (payoffEnv (σ Player.row) (σ Player.col))

def IsActionNash (σ : ActionProfile) : Prop :=
  ∀ who alt, actionPayoff σ who ≥
    actionPayoff (Function.update σ who alt) who

def defectProfile : ActionProfile
  | Player.row => false
  | Player.col => false

theorem defectProfile_actionNash : IsActionNash defectProfile := by
  intro who alt
  cases who <;> cases alt <;> decide

theorem actionNash_eq_defectProfile
    (σ : ActionProfile) (hσ : IsActionNash σ) :
    σ = defectProfile := by
  have hrowFalse : σ Player.row = false := by
    cases hrow : σ Player.row
    · rfl
    · cases hcol : σ Player.col
      · have hdev := hσ Player.row false
        have hbad :
            evalExpr rowPayoff (payoffEnv false false) ≤
              evalExpr rowPayoff (payoffEnv true false) := by
          simpa [actionPayoff, hrow, hcol] using hdev
        exact False.elim
          ((not_le_of_gt (row_defect_payoff_gt_cooperate false)) hbad)
      · have hdev := hσ Player.row false
        have hbad :
            evalExpr rowPayoff (payoffEnv false true) ≤
              evalExpr rowPayoff (payoffEnv true true) := by
          simpa [actionPayoff, hrow, hcol] using hdev
        exact False.elim
          ((not_le_of_gt (row_defect_payoff_gt_cooperate true)) hbad)
  have hcolFalse : σ Player.col = false := by
    cases hcol : σ Player.col
    · rfl
    · have hdev := hσ Player.col false
      have hbad :
          evalExpr colPayoff (payoffEnv false false) ≤
            evalExpr colPayoff (payoffEnv false true) := by
        simpa [actionPayoff, hrowFalse, hcol] using hdev
      exact False.elim
        ((not_le_of_gt (col_defect_payoff_gt_cooperate false)) hbad)
  funext who
  cases who <;> simp [defectProfile, hrowFalse, hcolFalse]

theorem actionNash_iff_defectProfile (σ : ActionProfile) :
    IsActionNash σ ↔ σ = defectProfile := by
  constructor
  · exact actionNash_eq_defectProfile σ
  · intro h
    subst σ
    exact defectProfile_actionNash

def core : VegasCore Player L Γ0 :=
  .commit rowSecret Player.row (trueGuard (x := rowSecret))
    (.commit colSecret Player.col (trueGuard (x := colSecret))
      (.reveal rowPublic Player.row rowSecret hRowSecretΓ2
        (.reveal colPublic Player.col colSecret hColSecretΓ3
          (.ret [(Player.row, rowPayoff), (Player.col, colPayoff)]))))

noncomputable def graphProgram : GraphProgram Player L where
  Γ := Γ0
  prog := core
  env := VEnv.empty L
  wctx := WFCtx_nil
  fresh := by
    decide
  normalized := by
    trivial

noncomputable def checkedProgram : WFProgram Player L where
  core := graphProgram
  reveals := by
    decide
  legal := by
    constructor
    · intro _env
      exact ⟨true, rfl⟩
    · constructor
      · intro _env
        exact ⟨true, rfl⟩
      · trivial

noncomputable instance instFiniteDomains : FiniteDomains checkedProgram where
  context := inferInstanceAs (FiniteVCtx Γ0)
  program :=
    { proof :=
        .commit inferInstance
          (.commit inferInstance
            (.reveal inferInstance
              (.reveal inferInstance .ret))) }

noncomputable def compiled : CompiledProgram Player L :=
  compile graphProgram

noncomputable def semantics :
    FrontierGameSemantics checkedProgram :=
  canonicalFrontierGameSemantics checkedProgram

theorem mixedPureToBehavioral_realizable :
    MixedPureToBehavioralOutcomeKernelRealizable checkedProgram :=
  MixedPureToBehavioralOutcomeKernelRealizable.canonical checkedProgram

noncomputable example : KernelGame Player :=
  semantics.pureGame

noncomputable example : KernelGame Player :=
  semantics.behavioralGame

noncomputable def plainEFG : EFG.EFGGame :=
  checkedProgram.frontierPlainEFG

noncomputable def plainEFGMachinePayoffKernelGame : KernelGame Player :=
  checkedProgram.frontierPlainEFGMachinePayoffKernelGame

theorem plainEFGMachinePayoffKernel_udist
    (behavioralProfile : semantics.behavioralGame.Profile) :
    checkedProgram.frontierPlainEFGMachinePayoffKernelGame.udist
        (checkedProgram.frontierPlainEFGTranslateProfile
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            checkedProgram.frontierSemantics.behavioral.view
            checkedProgram.frontierSemantics.horizon (fun _ => 0)
            behavioralProfile).extend) =
      checkedProgram.behavioralFrontierGame.udist behavioralProfile :=
  checkedProgram
    |>.frontierPlainEFGMachinePayoffKernelGame_udist_behavioralGame
      behavioralProfile

theorem plainEFGMachinePayoffKernel_udist_pure
    (pureProfile : semantics.pureGame.Profile) :
    checkedProgram.frontierPlainEFGMachinePayoffKernelGame.udist
        (checkedProgram.frontierPlainEFGTranslateProfile
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            checkedProgram.frontierSemantics.behavioral.view
            checkedProgram.frontierSemantics.horizon (fun _ => 0)
            ((checkedProgram.frontierSemantics.behavioral.view).legalPureToBehavioral
              checkedProgram.frontierSemantics.horizon pureProfile)).extend) =
      checkedProgram.pureFrontierGame.udist pureProfile :=
  checkedProgram
    |>.frontierPlainEFGMachinePayoffKernelGame_udist_pureGame pureProfile

noncomputable example (player : Player) :
    Fintype (semantics.pureGame.Strategy player) :=
  semantics.pureStrategyFintype player

noncomputable example : KernelGame Player :=
  semantics.mixedPureGame

abbrev MixedNashProfiles : Type :=
  { σ : semantics.mixedPureGame.Profile //
    semantics.mixedPureGame.IsNash σ }

/-- The compiled Prisoner's Dilemma frontier game has a mixed pure Nash
equilibrium. -/
theorem mixedPureFrontierNash_exists :
    ∃ mixed : checkedProgram.MixedPureFrontierProfile,
      checkedProgram.MixedPureFrontierNash mixed :=
  checkedProgram.mixedPureFrontier_nash_exists

/-- The compiled Prisoner's Dilemma frontier game has a behavioral Nash
equilibrium by finite mixed Nash existence plus the canonical Kuhn
deviation-simulation bridge. -/
theorem behavioralFrontierNash_exists :
    ∃ behavioral : checkedProgram.BehavioralFrontierProfile,
      checkedProgram.BehavioralFrontierNash behavioral :=
  checkedProgram.behavioralFrontier_nash_exists

/-- The compiled Prisoner's Dilemma frontier games satisfy the two-direction
outcome-kernel Kuhn schema. -/
theorem frontierCompleteOutcomeKuhn :
    GameTheory.Theorems.KuhnCompleteViaOutcome
      checkedProgram.BehavioralFrontierProfile
      (∀ player, PMF (checkedProgram.PureFrontierStrategy player))
      checkedProgram.PureFrontierProfile
      checkedProgram.pureFrontierGame.Outcome
      (fun behavioral =>
        Math.PMFProduct.pmfPi
          (checkedProgram.behavioralFrontierToMixedPure behavioral))
      Math.PMFProduct.pmfPi
      checkedProgram.behavioralFrontierGame.outcomeKernel
      checkedProgram.pureFrontierGame.outcomeKernel :=
  checkedProgram.frontierCompleteOutcomeKuhn

example : MixedPureToBehavioralOutcomeKernelRealizable checkedProgram :=
  mixedPureToBehavioral_realizable

theorem behavioralToCorrelatedPure
    (behavioralProfile : semantics.behavioralGame.Profile) :
    ∃ correlated : PMF semantics.pureGame.Profile,
      semantics.behavioralGame.outcomeKernel behavioralProfile =
        correlated.bind fun pureProfile =>
          semantics.pureGame.outcomeKernel pureProfile :=
  semantics.behavioralToCorrelatedPure behavioralProfile

theorem behavioralToMixedPure_outcomeKernel
    (behavioralProfile : semantics.behavioralGame.Profile) :
    semantics.behavioralGame.outcomeKernel behavioralProfile =
      semantics.mixedPureGame.outcomeKernel
        (semantics.behavioralToMixedPure behavioralProfile) :=
  semantics.behavioralToMixedPureOutcomeKernel behavioralProfile

theorem compiled_nodeCount :
    compiled.graph.nodeCount = 4 := by
  simp [compiled, compile, graphProgram, core, trueGuard, compileCore,
    EventGraph.Graph.nodeCount]

noncomputable def node (n : Nat) (h : n < 4) :
    Fin compiled.graph.nodeCount :=
  ⟨n, by
    rw [compiled_nodeCount]
    exact h⟩

noncomputable def node0 : Fin compiled.graph.nodeCount := node 0 (by decide)
noncomputable def node1 : Fin compiled.graph.nodeCount := node 1 (by decide)
noncomputable def node2 : Fin compiled.graph.nodeCount := node 2 (by decide)
noncomputable def node3 : Fin compiled.graph.nodeCount := node 3 (by decide)

example :
    compiled.graph.prereqs node1 = ∅ := by
  decide

example :
    compiled.graph.prereqs node2 = {node0, node1} := by
  decide

example :
    compiled.graph.prereqs node3 = {node0, node1} := by
  decide

example :
    compiled.payoffs.length = 2 := by
  simp [compiled, compile, graphProgram, core, trueGuard, compileCore]

end PrisonersDilemma

end Examples
end Vegas
