/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Expr.Simple
import Vegas.Game.SourcePhaseObservation

/-! # Full source history valuation does not factor through terminal cash

An initially unusable commitment may be withheld or submitted for publication.
Both legal initialized source histories end in the same complete typed store,
exclusion and cash. Original own disclosure choices remain distinct. A valuation
of that remembered choice therefore cannot be read from TerminalObservation.
-/

noncomputable section

namespace Vegas.Examples.SourcePhaseValuation

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

abbrev Player := Unit
abbrev owner : Player := ()

def context : SourceCtx Player simpleExpr := [(0, .commitment owner .bool)]

def program : SourceProgram Player simpleExpr context {0} :=
  .reveal 1 owner 0 (by decide) .here (by decide) (.ret [])

def initial : State simpleExpr context := Env.cons .failure (Env.empty _)

def setup : Setup (Player := Player) (L := simpleExpr) where
  context := context
  namesNodup := by decide
  initialLaw := PMF.pure initial
  obligations := {0}
  program := program
  accounts := rfl
  exitTransfers := fun _ => -1

def entry : CommitRecoveryState program :=
  .atPoint (ProtocolState.entry program (setup.initialConfig initial)) ∅ 0

def choice (disclose : Bool) : Player → Option (CommitRecoveryMove Player simpleExpr) :=
  fun _ => some ⟨.reveal owner 0 disclose, false⟩

private def finalConfig (disclose : Bool) :=
  revealSuccessor 1 (.here : HasVar context 0 (.commitment owner .bool))
    (setup.initialConfig initial) disclose

def terminal (disclose : Bool) : CommitRecoveryState program :=
  .atPoint (.inr (finalConfig disclose)) {owner} 0

private theorem draw_legal : setup.commitRecoveryProtocol.Legal none (fun _ => none) :=
  ⟨fun impossible => impossible, fun _ impossible => impossible⟩

private def draw : setup.commitRecoveryProtocol.Trace (some entry) :=
  .extend .start (fun _ => none) draw_legal (by
    change some entry ∈ ((PMF.pure initial).map _).support
    rw [PMF.pure_map, PMF.mem_support_pure_iff]
    rfl)

private theorem choice_legal (disclose : Bool) :
    setup.commitRecoveryProtocol.Legal (some entry) (choice disclose) := by
  refine ⟨fun impossible => impossible, ?_⟩
  intro who
  refine ⟨⟨by cases who; rfl, Finset.notMem_empty _⟩, ?_⟩
  exact ⟨⟨disclose, rfl⟩, rfl⟩

private theorem choice_raw (disclose : Bool) :
    ProtocolState.recoveryStep program entry.point entry.excluded (choice disclose) =
      PMF.pure ((.inr (finalConfig disclose) : ProtocolState program), {owner}) := by
  cases disclose <;> rfl

private theorem choice_supported (disclose : Bool) :
    terminal disclose ∈ (entry.step (choice disclose)).support := by
  obtain ⟨next, supported⟩ := (entry.step (choice disclose)).support_nonempty
  obtain ⟨result, raw, equal⟩ := entry.step_raw_result _ next supported
  rw [choice_raw, PMF.mem_support_pure_iff] at raw
  have same : result = ⟨((.inr (finalConfig disclose) : ProtocolState program), {owner}),
      Finset.empty_subset _⟩ := Subtype.ext raw
  subst result
  have closed :
      (entry.install ((.inr (finalConfig disclose) : ProtocolState program), {owner})
        (Finset.empty_subset _)).close = terminal disclose := by
    let installed := entry.install ((.inr (finalConfig disclose) : ProtocolState program),
      {owner}) (Finset.empty_subset _)
    have notCommit : ProtocolState.atCommit program installed.saved = false := rfl
    have notFinished : ¬ installed.Finished := by
      intro finished
      have committed := finished.1
      rw [notCommit] at committed
      cases committed
    change installed.close = terminal disclose
    rw [CommitRecoveryState.close, ite_eq_right notFinished, notCommit]
    rfl
  rw [equal, closed] at supported
  exact supported

/-- Both histories start at the actual setup draw and take a legal reveal. -/
def history (disclose : Bool) : setup.commitRecoveryProtocol.History :=
  ⟨some (terminal disclose), .extend draw (choice disclose) (choice_legal disclose)
    ((PMF.mem_support_map_iff _ _ _).mpr
      ⟨terminal disclose, choice_supported disclose, rfl⟩)⟩

def valuation (history : setup.commitRecoveryProtocol.History) (_who : Player) : ℝ :=
  if history.state.elim false (fun state =>
      (ProtocolState.history program state.point owner).any fun action =>
        match action with
        | .reveal _ _ disclose => disclose
        | .commit .. => false)
    then 1 else 0

theorem history_terminal (disclose : Bool) :
    setup.commitRecoveryProtocol.terminal (history disclose).state := by trivial

theorem observation_eq :
    setup.sourcePhaseObservation (history true) =
      setup.sourcePhaseObservation (history false) := rfl

theorem valuation_true : valuation (history true) owner = 1 := rfl

theorem valuation_false : valuation (history false) owner = 0 := rfl

/-- Exact utility preservation through the common terminal observation needs
a valuation-factorization hypothesis even for legal completed source paths. -/
theorem utility_does_not_factor_through_terminal_observation :
    ¬ ∃ read : TerminalObservation setup → Player → ℝ,
      ∀ history : setup.commitRecoveryProtocol.History,
        setup.commitRecoveryProtocol.terminal history.state →
        read (setup.sourcePhaseObservation history) owner =
          (setup.sourcePhaseGame valuation).utility history owner := by
  rintro ⟨read, represents⟩
  have first := represents (history true) (history_terminal true)
  have second := represents (history false) (history_terminal false)
  rw [observation_eq] at first
  have cash (disclose : Bool) : setup.sourcePhaseCash (history disclose) owner = -1 :=
    setup.sourcePhaseCash_of_excluded _ _ rfl owner (Finset.mem_singleton_self _)
  change read _ owner = valuation (history true) owner + _ at first
  change read _ owner = valuation (history false) owner + _ at second
  rw [valuation_true, cash] at first
  rw [valuation_false, cash] at second
  linarith

end Vegas.Examples.SourcePhaseValuation
