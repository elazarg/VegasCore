/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.IntendedAuditedOutcome
import Vegas.Expr.Simple
import GameTheory.Analysis.Protocol.SequentialExistence

/-! # Three Boolean owners with a fixed exclusion loss exceeding the reward range -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

abbrev Player := Fin 3
abbrev alice : Player := 0
abbrev bob : Player := 1
abbrev carol : Player := 2

/-- Every Boolean satisfies each commitment's deferred guard. -/
def acceptGuard {Γ : SourceCtx Player simpleExpr} (who : Player) (name : VarId) :
    SourceGuard simpleExpr Γ who name .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by simp
  code := .constBool true
  reads := fun h => nomatch h

/-- All three in-game Boolean commitments precede all three publications. -/
def program : SourceProgram Player simpleExpr [] ∅ :=
  .commit 0 alice (by decide) (acceptGuard alice 0) <|
  .commit 1 bob (by decide) (acceptGuard bob 1) <|
  .commit 2 carol (by decide) (acceptGuard carol 2) <|
  .reveal 3 alice 0 (by decide) (.there (.there .here)) (by decide) <|
  .reveal 4 bob 1 (by decide) (.there (.there .here)) (by decide) <|
  .reveal 5 carol 2 (by decide) (.there (.there .here)) (by decide) <|
  .ret []

def setup : Setup (Player := Player) (L := simpleExpr) where
  context := []
  namesNodup := by decide
  initialLaw := PMF.pure (Env.empty (CellVal simpleExpr))
  obligations := ∅
  program := program
  accounts := rfl

instance finiteInitial : setup.FiniteInitialLaw where
  support_finite := by
    change (PMF.pure (Env.empty (CellVal simpleExpr))).support.Finite
    rw [PMF.support_pure]
    exact Set.finite_singleton _

theorem wellFormed : setup.WellFormed where
  initialValues := by
    intro initial _ name owner payload cell
    cases cell
  guardsSatisfiable := by
    intro initial _
    refine ⟨⟨true, rfl⟩, fun _ _ => ⟨⟨true, rfl⟩, fun _ _ => ?_⟩⟩
    exact ⟨⟨true, rfl⟩, fun _ _ => trivial⟩

abbrev graph := serviceGraph setup .concurrentReveals

def bindingEvent (owner : Player) : graph.EventId :=
  ⟨owner.val, by have bound := owner.isLt; change owner.val < 6; omega⟩

def revealEvent (owner : Player) : graph.EventId :=
  ⟨owner.val + 3, by have bound := owner.isLt; change owner.val + 3 < 6; omega⟩

theorem bindingEvent_layout (owner : Player) :
    graph.layout (.inr (bindingEvent owner)) = .binding owner .bool := by
  fin_cases owner <;> rfl

theorem revealEvent_layout (owner : Player) :
    graph.layout (.inr (revealEvent owner)) = .publication .bool := by
  fin_cases owner <;> rfl

open Classical in
/-- A surviving player earns one exactly when some other owner's reveal fails. -/
def grossUtility (outcome : PublicOutcome program) (who : Player) : ℝ :=
  if ∃ other : Player, other ≠ who ∧ 0 < failedReveals program other outcome then 1 else 0

def utility (terminal : State simpleExpr program.terminalCtx) (who : Player) : ℝ :=
  grossUtility (publicOutcome program terminal) who

def excludedPayoff (_ : Player) : ℝ := -(3 / 2)

def deposit (_ : Player) : ℝ := 3

theorem grossUtility_mem_Icc (outcome : PublicOutcome program) (who : Player) :
    grossUtility outcome who ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  unfold grossUtility
  split <;> constructor <;> norm_num

theorem utility_mem_Icc (terminal : State simpleExpr program.terminalCtx) (who : Player) :
    utility terminal who ∈ Set.Icc (0 : ℝ) 1 := grossUtility_mem_Icc _ who

theorem excludedPayoff_lt_utility (terminal : State simpleExpr program.terminalCtx)
    (who : Player) : excludedPayoff who < utility terminal who := by
  have lower := (utility_mem_Icc terminal who).1
  unfold excludedPayoff
  linarith

/-- The fixed loss strictly exceeds the entire range of nonexcluded rewards. -/
theorem exclusion_loss_exceeds_range (who : Player) :
    (1 : ℝ) - 0 < 0 - excludedPayoff who := by norm_num [excludedPayoff]

theorem collateral_gap (who : Player) :
    (1 : ℝ) - deposit who < excludedPayoff who := by norm_num [deposit, excludedPayoff]

theorem finiteBindingTypes : program.FiniteBindingTypes :=
  ⟨inferInstance, inferInstance, inferInstance, trivial⟩

theorem honest_decisionRecall : setup.intendedModel.DecisionRecall :=
  setup.intendedModel.decisionRecall_of_perfectRecall
    ((setup.informationModel _).restrictMenu_perfectRecall _ _
      (setup.protocol_perfectRecall _))

private theorem honestMenu_nonempty (who : Player) (info : setup.ProtocolView who) :
    ∃ choice, choice ∈ setup.intendedMenu who info := by
  classical
  cases info with
  | none => exact ⟨none, rfl⟩
  | some view =>
      rcases view with observed | observed | observed | observed | observed | observed | terminal
      · by_cases same : alice = who
        · subst who
          obtain ⟨value, allowed⟩ := intendedValues_nonempty alice
            (acceptGuard alice 0) observed.1
          refine ⟨some (.commit alice 0 .bool (.success value)), ?_⟩
          change some alice = some alice ∧ ∃ chosen ∈ intendedValues alice
            (acceptGuard alice 0) observed.1,
              OwnAction.commit (L := simpleExpr) alice 0 .bool (.success value) =
                OwnAction.commit (L := simpleExpr) alice 0 .bool (.success chosen)
          exact ⟨rfl, value, allowed, rfl⟩
        · refine ⟨none, ?_⟩
          change some alice ≠ some who
          exact fun equality => same (Option.some.inj equality)
      · by_cases same : bob = who
        · subst who
          obtain ⟨value, allowed⟩ := intendedValues_nonempty bob
            (acceptGuard bob 1) observed.1
          refine ⟨some (.commit bob 1 .bool (.success value)), ?_⟩
          change some bob = some bob ∧ ∃ chosen ∈ intendedValues bob
            (acceptGuard bob 1) observed.1,
              OwnAction.commit (L := simpleExpr) bob 1 .bool (.success value) =
                OwnAction.commit (L := simpleExpr) bob 1 .bool (.success chosen)
          exact ⟨rfl, value, allowed, rfl⟩
        · refine ⟨none, ?_⟩
          change some bob ≠ some who
          exact fun equality => same (Option.some.inj equality)
      · by_cases same : carol = who
        · subst who
          obtain ⟨value, allowed⟩ := intendedValues_nonempty carol
            (acceptGuard carol 2) observed.1
          refine ⟨some (.commit carol 2 .bool (.success value)), ?_⟩
          change some carol = some carol ∧ ∃ chosen ∈ intendedValues carol
            (acceptGuard carol 2) observed.1,
              OwnAction.commit (L := simpleExpr) carol 2 .bool (.success value) =
                OwnAction.commit (L := simpleExpr) carol 2 .bool (.success chosen)
          exact ⟨rfl, value, allowed, rfl⟩
        · refine ⟨none, ?_⟩
          change some carol ≠ some who
          exact fun equality => same (Option.some.inj equality)
      · by_cases same : alice = who
        · subst who
          refine ⟨some (.reveal alice 0 true), ?_⟩
          change some alice = some alice ∧
            OwnAction.reveal alice 0 true ∈
              ({OwnAction.reveal alice 0 true} : Set (OwnAction Player simpleExpr))
          exact ⟨rfl, rfl⟩
        · refine ⟨none, ?_⟩
          change some alice ≠ some who
          exact fun equality => same (Option.some.inj equality)
      · by_cases same : bob = who
        · subst who
          refine ⟨some (.reveal bob 1 true), ?_⟩
          change some bob = some bob ∧
            OwnAction.reveal bob 1 true ∈
              ({OwnAction.reveal bob 1 true} : Set (OwnAction Player simpleExpr))
          exact ⟨rfl, rfl⟩
        · refine ⟨none, ?_⟩
          change some bob ≠ some who
          exact fun equality => same (Option.some.inj equality)
      · by_cases same : carol = who
        · subst who
          refine ⟨some (.reveal carol 2 true), ?_⟩
          change some carol = some carol ∧
            OwnAction.reveal carol 2 true ∈
              ({OwnAction.reveal carol 2 true} : Set (OwnAction Player simpleExpr))
          exact ⟨rfl, rfl⟩
        · refine ⟨none, ?_⟩
          change some carol ≠ some who
          exact fun equality => same (Option.some.inj equality)
      · refine ⟨none, ?_⟩
        change none ≠ some who
        intro impossible
        cases impossible

def honestFallback (who : Player) : setup.intendedModel.Policy who := fun info =>
  ⟨(honestMenu_nonempty who info).choose, (honestMenu_nonempty who info).choose_spec⟩

def honestPayoff (who : Player) (history : setup.intendedProtocol.History) : ℝ :=
  (setup.protocolReadout history.state).elim 0 (fun terminal => utility terminal who)

/-- Every genuine honest source history has zero payoff for all three owners. -/
theorem honestPayoff_eq_zero (who : Player) (history : setup.intendedProtocol.History) :
    honestPayoff who history = 0 := by
  classical
  unfold honestPayoff
  cases read : setup.protocolReadout history.state with
  | none => rfl
  | some terminal =>
      change State simpleExpr program.terminalCtx at terminal
      have noFailure (other : Player) :
          failedReveals program other (publicOutcome program terminal) = 0 :=
        setup.failedReveals_eq_zero_of_intendedState
          (setup.intendedState_trace wellFormed history.trace) other read
      change (if ∃ other : Player, other ≠ who ∧
        0 < failedReveals program other (publicOutcome program terminal) then 1 else 0) = 0
      simp only [noFailure, lt_self_iff_false, and_false, exists_const, ite_false]

/-- The initialized finite honest source game has an actual sequential equilibrium. -/
theorem exists_honest_sequentialEquilibrium :
    ∃ assessment : setup.intendedModel.BehavioralAssessment,
      assessment.IsSequentialEquilibrium honest_decisionRecall.decisionInformationAntichain
        setup.intended_bounded.wellFoundedHistories honestPayoff := by
  have : Finite setup.intendedProtocol.History := setup.intended_finite_history finiteBindingTypes
  obtain ⟨assessment, rational, consistent⟩ :=
    setup.intendedModel.exists_sequentialEquilibrium honest_decisionRecall honestFallback
      honestPayoff setup.intended_bounded.wellFoundedHistories
  exact ⟨assessment, rational, consistent⟩

end Vegas.Examples.CommitSeedBroadcast
