/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.OnePacketCommitRevealHypotheses
import GameTheory.Analysis.Protocol.SequentialExistence

/-! # Honest Boolean commitments with rewards for another owner's failed reveal

Both owners may commit either Boolean. A surviving owner earns three when
the other reveal fails, and zero otherwise. Every intended history has no
failed reveals, so its payoff is zero. The initialized intended game has a
genuine sequential equilibrium by the finite decision-recall existence theorem.
-/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

def opponent (who : Player) : Player := if who = alice then bob else alice

theorem opponent_ne (who : Player) : opponent who ≠ who := by
  fin_cases who <;> decide

/-- Gross utility ignores both committed values. -/
def grossUtility (outcome : PublicOutcome program) (who : Player) : ℝ :=
  if failedReveals program (opponent who) outcome = 0 then 0 else 3

def utility (terminal : State simpleExpr program.terminalCtx) (who : Player) : ℝ :=
  grossUtility (publicOutcome program terminal) who

def excludedPayoff (_ : Player) : ℝ := -1

def deposit (_ : Player) : ℝ := 5

theorem grossUtility_mem_Icc (outcome : PublicOutcome program) (who : Player) :
    grossUtility outcome who ∈ Set.Icc (0 : ℝ) 3 := by
  unfold grossUtility
  split <;> constructor <;> norm_num

theorem utility_mem_Icc (terminal : State simpleExpr program.terminalCtx) (who : Player) :
    utility terminal who ∈ Set.Icc (0 : ℝ) 3 :=
  grossUtility_mem_Icc _ who

theorem excludedPayoff_lt_utility (terminal : State simpleExpr program.terminalCtx)
    (who : Player) : excludedPayoff who < utility terminal who := by
  have lower := (utility_mem_Icc terminal who).1
  unfold excludedPayoff
  linarith

theorem collateral_gap (who : Player) :
    (3 : ℝ) - deposit who < excludedPayoff who := by
  norm_num [deposit, excludedPayoff]

theorem finiteBindingTypes : program.FiniteBindingTypes :=
  ⟨inferInstance, inferInstance, trivial⟩

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
      cases view with
      | inl observed =>
          by_cases same : alice = who
          · subst who
            obtain ⟨value, allowed⟩ := intendedValues_nonempty alice
              (OnePacketCommitRevealHypotheses.acceptGuard alice 0) observed.1
            refine ⟨some (.commit alice 0 .bool (.success value)), ?_⟩
            change some alice = some alice ∧ ∃ chosen ∈ intendedValues alice
              (OnePacketCommitRevealHypotheses.acceptGuard alice 0) observed.1,
                OwnAction.commit (L := simpleExpr) alice 0 .bool (.success value) =
                  OwnAction.commit (L := simpleExpr) alice 0 .bool (.success chosen)
            exact ⟨rfl, value, allowed, rfl⟩
          · refine ⟨none, ?_⟩
            change some alice ≠ some who
            exact fun equality => same (Option.some.inj equality)
      | inr rest =>
          cases rest with
          | inl observed =>
              by_cases same : bob = who
              · subst who
                obtain ⟨value, allowed⟩ := intendedValues_nonempty bob
                  (OnePacketCommitRevealHypotheses.acceptGuard bob 1) observed.1
                refine ⟨some (.commit bob 1 .bool (.success value)), ?_⟩
                change some bob = some bob ∧ ∃ chosen ∈ intendedValues bob
                  (OnePacketCommitRevealHypotheses.acceptGuard bob 1) observed.1,
                    OwnAction.commit (L := simpleExpr) bob 1 .bool (.success value) =
                      OwnAction.commit (L := simpleExpr) bob 1 .bool (.success chosen)
                exact ⟨rfl, value, allowed, rfl⟩
              · refine ⟨none, ?_⟩
                change some bob ≠ some who
                exact fun equality => same (Option.some.inj equality)
          | inr rest =>
              cases rest with
              | inl _observed =>
                  by_cases same : alice = who
                  · subst who
                    refine ⟨some (.reveal alice 0 true), ?_⟩
                    change some alice = some alice ∧
                      OwnAction.reveal alice 0 true ∈
                        ({OwnAction.reveal alice 0 true} : Set (OwnAction Player simpleExpr))
                    exact ⟨rfl, rfl⟩
                  · refine ⟨none, ?_⟩
                    change some alice ≠ some who
                    exact fun equality => same (Option.some.inj equality)
              | inr rest =>
                  cases rest with
                  | inl _observed =>
                      by_cases same : bob = who
                      · subst who
                        refine ⟨some (.reveal bob 1 true), ?_⟩
                        change some bob = some bob ∧
                          OwnAction.reveal bob 1 true ∈
                            ({OwnAction.reveal bob 1 true} : Set (OwnAction Player simpleExpr))
                        exact ⟨rfl, rfl⟩
                      · refine ⟨none, ?_⟩
                        change some bob ≠ some who
                        exact fun equality => same (Option.some.inj equality)
                  | inr _terminal =>
                      refine ⟨none, ?_⟩
                      change none ≠ some who
                      intro impossible
                      cases impossible

def honestFallback (who : Player) : setup.intendedModel.Policy who := fun info =>
  ⟨(honestMenu_nonempty who info).choose, (honestMenu_nonempty who info).choose_spec⟩

def honestPayoff (who : Player) (history : setup.intendedProtocol.History) : ℝ :=
  (setup.protocolReadout history.state).elim 0 (fun terminal => utility terminal who)

/-- No raw timing, candidate or audit data is present in this honest assessment. -/
theorem honestPayoff_eq_zero (who : Player) (history : setup.intendedProtocol.History) :
    honestPayoff who history = 0 := by
  unfold honestPayoff
  cases read : setup.protocolReadout history.state with
  | none => rfl
  | some terminal =>
      have noFailure := setup.failedReveals_eq_zero_of_intendedState
        (setup.intendedState_trace OnePacketCommitRevealHypotheses.wellFormed history.trace)
        (opponent who) read
      change failedReveals program (opponent who) (publicOutcome program terminal) = 0 at noFailure
      simp only [Option.elim_some, utility, grossUtility, noFailure, ↓reduceIte]

/-- The fixed initialized honest game supplies an actual source SE. -/
theorem exists_honest_sequentialEquilibrium :
    ∃ assessment : setup.intendedModel.BehavioralAssessment,
      assessment.IsSequentialEquilibrium honest_decisionRecall.decisionInformationAntichain
        setup.intended_bounded.wellFoundedHistories honestPayoff := by
  have : Finite setup.intendedProtocol.History := setup.intended_finite_history finiteBindingTypes
  obtain ⟨assessment, rational, consistent⟩ :=
    setup.intendedModel.exists_sequentialEquilibrium honest_decisionRecall honestFallback
      honestPayoff setup.intended_bounded.wellFoundedHistories
  exact ⟨assessment, rational, consistent⟩

end Vegas.Examples.CommitSeedSignalling
