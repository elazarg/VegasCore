/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Examples.DependencySemantics

/-!
# Battle of the Sexes

Build-tested checked-program examples for the canonical frontier EventGraph
semantics.
-/

namespace Vegas
namespace Examples

open GameTheory
open ToEventGraph

/-! ## Battle of the Sexes -/

namespace BattleOfTheSexes

inductive Player where
  | operaFan
  | footballFan
deriving DecidableEq, Repr, Fintype

def operaFanSecret : VarId := 0
def footballFanSecret : VarId := 1
def operaFanPublic : VarId := 2
def footballFanPublic : VarId := 3

abbrev Γ0 : VCtx Player L := []
abbrev Γ2 : VCtx Player L :=
  [(footballFanSecret, .sealed Player.footballFan .bool),
   (operaFanSecret, .sealed Player.operaFan .bool)]
abbrev Γ3 : VCtx Player L :=
  [(operaFanPublic, .pub .bool),
   (footballFanSecret, .sealed Player.footballFan .bool),
   (operaFanSecret, .sealed Player.operaFan .bool)]
abbrev Γ4 : VCtx Player L :=
  [(footballFanPublic, .pub .bool),
   (operaFanPublic, .pub .bool),
   (footballFanSecret, .sealed Player.footballFan .bool),
   (operaFanSecret, .sealed Player.operaFan .bool)]

def hOperaFanSecretΓ2 :
    VHasVar Γ2 operaFanSecret (.sealed Player.operaFan .bool) :=
  .there .here

def hFootballFanSecretΓ3 :
    VHasVar Γ3 footballFanSecret (.sealed Player.footballFan .bool) :=
  .there .here

def hFootballFanPublicPayoff :
    HasVar (erasePubVCtx Γ4) footballFanPublic .bool :=
  .here

def hOperaFanPublicPayoff :
    HasVar (erasePubVCtx Γ4) operaFanPublic .bool :=
  .there .here

def operaFanChoice : Expr (erasePubVCtx Γ4) .bool :=
  .var operaFanPublic hOperaFanPublicPayoff

def footballFanChoice : Expr (erasePubVCtx Γ4) .bool :=
  .var footballFanPublic hFootballFanPublicPayoff

def sameVenue : Expr (erasePubVCtx Γ4) .bool :=
  .eq operaFanChoice footballFanChoice

def operaFanPayoff : Expr (erasePubVCtx Γ4) .int :=
  .ite sameVenue
    (.ite operaFanChoice (.constInt 2) (.constInt 1))
    (.constInt 0)

def footballFanPayoff : Expr (erasePubVCtx Γ4) .int :=
  .ite sameVenue
    (.ite operaFanChoice (.constInt 1) (.constInt 2))
    (.constInt 0)

def payoffEnv (operaFan footballFan : Bool) :
    Env simpleExpr.Val (erasePubVCtx Γ4) :=
  Env.cons (x := footballFanPublic) footballFan
    (Env.cons (x := operaFanPublic) operaFan (Env.empty simpleExpr.Val))

theorem payoff_table (operaFan footballFan : Bool) :
    (evalExpr operaFanPayoff (payoffEnv operaFan footballFan),
      evalExpr footballFanPayoff (payoffEnv operaFan footballFan)) =
      match operaFan, footballFan with
      | true, true => (2, 1)
      | true, false => (0, 0)
      | false, true => (0, 0)
      | false, false => (1, 2) := by
  cases operaFan <;> cases footballFan <;> rfl

theorem mismatch_payoff (operaFan footballFan : Bool)
    (h : operaFan ≠ footballFan) :
    evalExpr operaFanPayoff (payoffEnv operaFan footballFan) = 0 ∧
      evalExpr footballFanPayoff (payoffEnv operaFan footballFan) = 0 := by
  cases operaFan <;> cases footballFan <;>
    simp_all [payoffEnv, operaFanPayoff, footballFanPayoff, sameVenue,
      operaFanChoice, footballFanChoice, hOperaFanPublicPayoff,
      hFootballFanPublicPayoff, Env.get, Env.cons, evalExpr]

theorem operaFan_match_opera_gt :
    evalExpr operaFanPayoff (payoffEnv true true) >
      evalExpr operaFanPayoff (payoffEnv false true) := by
  decide

theorem operaFan_match_football_gt :
    evalExpr operaFanPayoff (payoffEnv false false) >
      evalExpr operaFanPayoff (payoffEnv true false) := by
  decide

theorem footballFan_match_opera_gt :
    evalExpr footballFanPayoff (payoffEnv true true) >
      evalExpr footballFanPayoff (payoffEnv true false) := by
  decide

theorem footballFan_match_football_gt :
    evalExpr footballFanPayoff (payoffEnv false false) >
      evalExpr footballFanPayoff (payoffEnv false true) := by
  decide

abbrev ActionProfile := Player → Bool

def actionPayoff (σ : ActionProfile) : Player → Int
  | Player.operaFan =>
      evalExpr operaFanPayoff
        (payoffEnv (σ Player.operaFan) (σ Player.footballFan))
  | Player.footballFan =>
      evalExpr footballFanPayoff
        (payoffEnv (σ Player.operaFan) (σ Player.footballFan))

def IsActionNash (σ : ActionProfile) : Prop :=
  ∀ who alt, actionPayoff σ who ≥
    actionPayoff (Function.update σ who alt) who

def operaProfile : ActionProfile
  | Player.operaFan => true
  | Player.footballFan => true

def footballProfile : ActionProfile
  | Player.operaFan => false
  | Player.footballFan => false

theorem operaProfile_actionNash : IsActionNash operaProfile := by
  intro who alt
  cases who <;> cases alt <;> decide

theorem footballProfile_actionNash : IsActionNash footballProfile := by
  intro who alt
  cases who <;> cases alt <;> decide

theorem actionNash_eq_opera_or_football
    (σ : ActionProfile) (hσ : IsActionNash σ) :
    σ = operaProfile ∨ σ = footballProfile := by
  cases hopera : σ Player.operaFan <;>
    cases hfootball : σ Player.footballFan
  · right
    funext who
    cases who <;> simp [footballProfile, hopera, hfootball]
  · have hdev := hσ Player.operaFan true
    have hbad :
        evalExpr operaFanPayoff (payoffEnv true true) ≤
          evalExpr operaFanPayoff (payoffEnv false true) := by
      simpa [actionPayoff, hopera, hfootball] using hdev
    exact False.elim ((not_le_of_gt operaFan_match_opera_gt) hbad)
  · have hdev := hσ Player.footballFan true
    have hbad :
        evalExpr footballFanPayoff (payoffEnv true true) ≤
          evalExpr footballFanPayoff (payoffEnv true false) := by
      simpa [actionPayoff, hopera, hfootball] using hdev
    exact False.elim ((not_le_of_gt footballFan_match_opera_gt) hbad)
  · left
    funext who
    cases who <;> simp [operaProfile, hopera, hfootball]

theorem actionNash_iff_opera_or_football (σ : ActionProfile) :
    IsActionNash σ ↔ σ = operaProfile ∨ σ = footballProfile := by
  constructor
  · exact actionNash_eq_opera_or_football σ
  · intro h
    rcases h with h | h
    · subst σ
      exact operaProfile_actionNash
    · subst σ
      exact footballProfile_actionNash

def core : VegasCore Player L Γ0 :=
  .commit operaFanSecret Player.operaFan (trueGuard (x := operaFanSecret))
    (.commit footballFanSecret Player.footballFan
      (trueGuard (x := footballFanSecret))
      (.reveal operaFanPublic Player.operaFan
        operaFanSecret hOperaFanSecretΓ2
        (.reveal footballFanPublic Player.footballFan
          footballFanSecret hFootballFanSecretΓ3
          (.ret [(Player.operaFan, operaFanPayoff),
            (Player.footballFan, footballFanPayoff)]))))

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

end BattleOfTheSexes

end Examples
end Vegas
