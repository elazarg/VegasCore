import Vegas.Strategic.BehavioralPMF

/-!
# Matching Pennies

A checked Vegas encoding of Matching Pennies. The Boolean commitments use
`true` for heads and `false` for tails.
-/

namespace Vegas
namespace Examples
namespace MatchingPennies

inductive Player where
  | matcher
  | mismatcher
deriving DecidableEq, Repr, Fintype

abbrev Ctx := VCtx Player simpleExpr
abbrev Prog (Γ : Ctx) := VegasCore Player simpleExpr Γ

def matcherSecret : VarId := 0
def mismatcherSecret : VarId := 1
def matcherPublic : VarId := 2
def mismatcherPublic : VarId := 3

abbrev Γ0 : Ctx := []
abbrev Γ2 : Ctx :=
  [(mismatcherSecret, .hidden Player.mismatcher .bool),
   (matcherSecret, .hidden Player.matcher .bool)]
abbrev Γ3 : Ctx :=
  [(matcherPublic, .pub .bool),
   (mismatcherSecret, .hidden Player.mismatcher .bool),
   (matcherSecret, .hidden Player.matcher .bool)]
abbrev Γ4 : Ctx :=
  [(mismatcherPublic, .pub .bool),
   (matcherPublic, .pub .bool),
   (mismatcherSecret, .hidden Player.mismatcher .bool),
   (matcherSecret, .hidden Player.matcher .bool)]

def hMatcherSecretΓ2 :
    VHasVar Γ2 matcherSecret (.hidden Player.matcher .bool) :=
  .there .here

def hMismatcherSecretΓ3 :
    VHasVar Γ3 mismatcherSecret (.hidden Player.mismatcher .bool) :=
  .there .here

def hMismatcherPublicPayoff :
    HasVar (erasePubVCtx Γ4) mismatcherPublic .bool :=
  .here

def hMatcherPublicPayoff :
    HasVar (erasePubVCtx Γ4) matcherPublic .bool :=
  .there .here

def matcherChoice : Expr (erasePubVCtx Γ4) .bool :=
  .var matcherPublic hMatcherPublicPayoff

def mismatcherChoice : Expr (erasePubVCtx Γ4) .bool :=
  .var mismatcherPublic hMismatcherPublicPayoff

def choicesMatch : Expr (erasePubVCtx Γ4) .bool :=
  .eq matcherChoice mismatcherChoice

def matcherPayoff : Expr (erasePubVCtx Γ4) .int :=
  .ite choicesMatch (.constInt 1) (.constInt (-1))

def mismatcherPayoff : Expr (erasePubVCtx Γ4) .int :=
  .ite choicesMatch (.constInt (-1)) (.constInt 1)

def payoffEnv (matcher mismatcher : Bool) :
    Env simpleExpr.Val (erasePubVCtx Γ4) :=
  Env.cons (x := mismatcherPublic) mismatcher
    (Env.cons (x := matcherPublic) matcher (Env.empty simpleExpr.Val))

theorem payoffs_zero_sum (matcher mismatcher : Bool) :
    evalExpr matcherPayoff (payoffEnv matcher mismatcher) +
      evalExpr mismatcherPayoff (payoffEnv matcher mismatcher) = 0 := by
  cases matcher <;> cases mismatcher <;>
    rfl

/-- Complete payoff table of the source-level Boolean choices. -/
theorem payoff_table (matcher mismatcher : Bool) :
    (evalExpr matcherPayoff (payoffEnv matcher mismatcher),
      evalExpr mismatcherPayoff (payoffEnv matcher mismatcher)) =
      match matcher, mismatcher with
      | true, true => (1, -1)
      | true, false => (-1, 1)
      | false, true => (-1, 1)
      | false, false => (1, -1) := by
  cases matcher <;> cases mismatcher <;> rfl

theorem mismatcher_switch_from_match_gt (choice : Bool) :
    evalExpr mismatcherPayoff (payoffEnv choice (!choice)) >
      evalExpr mismatcherPayoff (payoffEnv choice choice) := by
  cases choice <;> decide

theorem matcher_switch_from_mismatch_gt
    (matcher mismatcher : Bool) (h : matcher ≠ mismatcher) :
    evalExpr matcherPayoff (payoffEnv mismatcher mismatcher) >
      evalExpr matcherPayoff (payoffEnv matcher mismatcher) := by
  cases matcher <;> cases mismatcher <;> simp at h <;> decide

abbrev ActionProfile := Player → Bool

def actionPayoff (σ : ActionProfile) : Player → Int
  | Player.matcher =>
      evalExpr matcherPayoff
        (payoffEnv (σ Player.matcher) (σ Player.mismatcher))
  | Player.mismatcher =>
      evalExpr mismatcherPayoff
        (payoffEnv (σ Player.matcher) (σ Player.mismatcher))

def IsActionNash (σ : ActionProfile) : Prop :=
  ∀ who alt, actionPayoff σ who ≥
    actionPayoff (Function.update σ who alt) who

theorem no_actionNash (σ : ActionProfile) :
    ¬ IsActionNash σ := by
  intro hσ
  by_cases hmatch : σ Player.matcher = σ Player.mismatcher
  · have hdev := hσ Player.mismatcher (!(σ Player.mismatcher))
    have hbad :
        evalExpr mismatcherPayoff
            (payoffEnv (σ Player.matcher) (!(σ Player.mismatcher))) ≤
          evalExpr mismatcherPayoff
            (payoffEnv (σ Player.matcher) (σ Player.mismatcher)) := by
      simpa [actionPayoff, hmatch] using hdev
    exact
      (not_le_of_gt
        (by
          simpa [hmatch] using
            mismatcher_switch_from_match_gt (σ Player.mismatcher))) hbad
  · have hdev := hσ Player.matcher (σ Player.mismatcher)
    have hbad :
        evalExpr matcherPayoff
            (payoffEnv (σ Player.mismatcher) (σ Player.mismatcher)) ≤
          evalExpr matcherPayoff
            (payoffEnv (σ Player.matcher) (σ Player.mismatcher)) := by
      simpa [actionPayoff] using hdev
    exact
      (not_le_of_gt
        (matcher_switch_from_mismatch_gt
          (σ Player.matcher) (σ Player.mismatcher) hmatch)) hbad

noncomputable abbrev program : Prog Γ0 :=
  .commit matcherSecret Player.matcher (b := .bool) (.constBool true)
    (.commit mismatcherSecret Player.mismatcher (b := .bool) (.constBool true)
      (.reveal matcherPublic Player.matcher matcherSecret hMatcherSecretΓ2
        (.reveal mismatcherPublic Player.mismatcher
          mismatcherSecret hMismatcherSecretΓ3
          (.ret [(Player.matcher, matcherPayoff),
            (Player.mismatcher, mismatcherPayoff)]))))

def viewScoped : ViewScoped program := by
  dsimp [program, ViewScoped]
  constructor
  · intro z hz
    simp [simpleExpr, exprDeps] at hz
  · constructor
    · intro z hz
      simp [simpleExpr, exprDeps] at hz
    · trivial

def legal : Legal program := by
  dsimp [program, Legal]
  constructor
  · intro _env
    exact ⟨true, rfl⟩
  · constructor
    · intro _env
      exact ⟨true, rfl⟩
    · trivial

def wf : WF program :=
  ⟨by decide, by decide, viewScoped⟩

def normalized : NormalizedDists program := by
  simp [NormalizedDists]

noncomputable def game : WFProgram Player simpleExpr where
  Γ := Γ0
  prog := program
  env := VEnv.empty simpleExpr
  wctx := WFCtx_nil
  wf := wf
  normalized := normalized
  legal := legal

noncomputable instance instFiniteDomains : FiniteDomains game where
  context := inferInstanceAs (FiniteVCtx Γ0)
  program := inferInstanceAs (FiniteProgram program)

noncomputable def pureGame : GameTheory.KernelGame Player :=
  pureKernelGame game

noncomputable def behavioralGame : GameTheory.KernelGame Player :=
  pmfBehavioralKernelGame game

theorem pureGame_outcomeKernel
    (σ : pureGame.Profile) :
    pureGame.outcomeKernel σ = pureOutcomeKernelAt game σ := rfl

theorem behavioralGame_outcomeKernel
    (σ : behavioralGame.Profile) :
    behavioralGame.outcomeKernel σ = behavioralOutcomeKernelPMFAt game σ := rfl

/-! ## Generated graph reveal-barrier regression -/

/-- The source node for the matcher's initial sealed commitment. -/
noncomputable def matcherCommitNode : ProgramNode program :=
  .commitHere

/-- The source node for the mismatcher's initial sealed commitment. -/
noncomputable def mismatcherCommitNode : ProgramNode program :=
  .commitTail .commitHere

/-- The source node for revealing the matcher's sealed commitment. -/
noncomputable def matcherRevealNode : ProgramNode program :=
  .commitTail (.commitTail .revealHere)

/-- The source node for revealing the mismatcher's sealed commitment. -/
noncomputable def mismatcherRevealNode : ProgramNode program :=
  .commitTail (.commitTail (.revealTail .revealHere))

theorem matcherRevealNode_isReveal :
    (ProgramNode.sem game.obligations matcherRevealNode).isReveal = true := by
  decide

theorem mismatcherRevealNode_isReveal :
    (ProgramNode.sem game.obligations mismatcherRevealNode).isReveal = true := by
  decide

theorem matcherCommitNode_isCommit :
    (ProgramNode.sem game.obligations matcherCommitNode).isCommit = true := by
  decide

theorem mismatcherCommitNode_isCommit :
    (ProgramNode.sem game.obligations mismatcherCommitNode).isCommit = true := by
  decide

/-- Regression guard: the first reveal waits for the other player's prior
commit, even though it does not read that commit's payload. -/
theorem mismatcherCommit_prereq_matcherReveal :
    mismatcherCommitNode ∈
      (programEventGraph game).prereqs matcherRevealNode := by
  classical
  change mismatcherCommitNode ∈
    ProgramNode.prereqs game.obligations matcherRevealNode
  unfold ProgramNode.prereqs
  refine Finset.mem_filter.mpr ⟨
    ProgramNode.mem_finset program mismatcherCommitNode, ?_, ?_⟩
  · decide
  · right
    constructor
    · exact matcherRevealNode_isReveal
    · exact mismatcherCommitNode_isCommit

/-- Regression guard: the second reveal still depends on the earlier matcher
commit through the phase barrier. -/
theorem matcherCommit_prereq_mismatcherReveal :
    matcherCommitNode ∈
      (programEventGraph game).prereqs mismatcherRevealNode := by
  classical
  change matcherCommitNode ∈
    ProgramNode.prereqs game.obligations mismatcherRevealNode
  unfold ProgramNode.prereqs
  refine Finset.mem_filter.mpr ⟨
    ProgramNode.mem_finset program matcherCommitNode, ?_, ?_⟩
  · decide
  · right
    constructor
    · exact mismatcherRevealNode_isReveal
    · exact matcherCommitNode_isCommit

theorem mismatcherCommit_not_frontier_with_matcherReveal
    (cfg : (programEventGraph game).Configuration)
    (hcommit : mismatcherCommitNode ∈ cfg.frontier)
    (hreveal : matcherRevealNode ∈ cfg.frontier) :
    False :=
  (EventGraph.Configuration.not_prereq_of_mem_frontier
    hcommit hreveal) mismatcherCommit_prereq_matcherReveal

theorem matcherCommit_not_frontier_with_mismatcherReveal
    (cfg : (programEventGraph game).Configuration)
    (hcommit : matcherCommitNode ∈ cfg.frontier)
    (hreveal : mismatcherRevealNode ∈ cfg.frontier) :
    False :=
  (EventGraph.Configuration.not_prereq_of_mem_frontier
    hcommit hreveal) matcherCommit_prereq_mismatcherReveal

end MatchingPennies
end Examples
end Vegas
