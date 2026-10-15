/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledCommitPhase
import Mathlib.Data.Nat.Find
import Mathlib.Data.List.Chain

/-! # Complete phase partitions of compiled source programs -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId}

/-- Compiled executable outputs are commitments, publications, or chance data. -/
theorem outputLayout_phaseKind (program : SourceProgram Player L Γ O)
    (index : Fin (eventCount program)) :
    ∃ kind : RuntimePhaseKind, kind.Matches (outputLayout program index) := by
  induction program with
  | ret => exact Fin.elim0 index
  | sample _ _ _ next ih =>
      refine Fin.cases ?_ (fun later => ih later) index
      exact ⟨.sample, _, rfl⟩
  | commit _ owner _ _ next ih =>
      refine Fin.cases ?_ (fun later => ih later) index
      exact ⟨.commitment, owner, _, rfl⟩
  | reveal _ _ _ _ _ _ next ih =>
      refine Fin.cases ?_ (fun later => ih later) index
      exact ⟨.reveal, _, rfl⟩

variable (program : SourceProgram Player L Γ O) (mode : EventGraph.ExecutionMode)

private def compiledPhaseKind (index : Fin (eventCount program)) : RuntimePhaseKind :=
  (outputLayout_phaseKind program index).choose

private theorem compiledPhaseKind_matches (index : Fin (eventCount program)) :
    (compiledPhaseKind program index).Matches (outputLayout program index) :=
  (outputLayout_phaseKind program index).choose_spec

private def PhaseEnd (low : Nat) (kind : RuntimePhaseKind) (high : Nat) : Prop :=
  (kind = .sample → high ≤ low + 1) ∧
    ∀ event : Fin (eventCount program), low ≤ event.val → event.val < high →
      kind.Matches (outputLayout program event)

private theorem phaseEnd_one (low : Nat) (active : low < eventCount program) :
    PhaseEnd program low (compiledPhaseKind program ⟨low, active⟩) (low + 1) := by
  refine ⟨fun _ => le_rfl, ?_⟩
  intro event lower upper
  have same : event = ⟨low, active⟩ := Fin.ext (by change event.val = low; omega)
  rw [same]
  exact compiledPhaseKind_matches program _

open Classical in
/-- The maximal same-kind interval from a compiled source rank; chance is singleton. -/
def compiledPhaseAt (low : Nat) (active : low < eventCount program) :
    RuntimePhase ((toEventGraph program).withMode mode) :=
  let kind := compiledPhaseKind program ⟨low, active⟩
  let ending := Nat.findGreatest (PhaseEnd program low kind) (eventCount program)
  have one := phaseEnd_one program low active
  have later : low + 1 ≤ ending := Nat.le_findGreatest (by omega) one
  have valid : PhaseEnd program low kind ending := Nat.findGreatest_spec (by omega) one
  { kind := kind
    low := low
    high := ending
    nonempty := by omega
    bounded := Nat.findGreatest_le _
    fields := valid.2
    sample_singleton := fun sampled => by have := valid.1 sampled; omega }

/-- Adjacent maximal intervals differ in kind, unless the first is a chance barrier. -/
theorem compiledPhaseAt_boundary (low : Nat) (active : low < eventCount program)
    (next : RuntimePhase ((toEventGraph program).withMode mode))
    (starts : next.low = (compiledPhaseAt program mode low active).high) :
    (compiledPhaseAt program mode low active).kind ≠ next.kind ∨
      (compiledPhaseAt program mode low active).kind = .sample := by
  classical
  let phase := compiledPhaseAt program mode low active
  have nextLow : next.low = phase.high := starts
  by_cases sampled : phase.kind = .sample
  · exact Or.inr sampled
  left
  intro same
  have highBelow : phase.high < eventCount program := by
    have positive := next.nonempty
    have bounded : next.high ≤ eventCount program := next.bounded
    omega
  have extended : PhaseEnd program low phase.kind (phase.high + 1) := by
    refine ⟨fun impossible => (sampled impossible).elim, ?_⟩
    intro event lower upper
    by_cases earlier : event.val < phase.high
    · exact phase.fields event lower earlier
    · have atEnd : event.val = phase.high := by omega
      rw [same]
      exact next.fields event (by omega) (by have := next.nonempty; omega)
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self phase.high) (by omega) extended

/-- Every compiled program has a finite, ordered, gap-free runtime phase plan. -/
theorem exists_compiledRuntimePhasePlan :
    ∃ plan : RuntimePhasePlan ((toEventGraph program).withMode mode),
      plan.phases.IsChain (fun before after => before.kind ≠ after.kind ∨
        before.kind = .sample) := by
  classical
  have suffixes : ∀ remaining low, eventCount program - low = remaining →
      low ≤ eventCount program →
      ∃ phases : List (RuntimePhase ((toEventGraph program).withMode mode)),
        phases.IsChain (fun before after => before.high = after.low) ∧
        phases.IsChain (fun before after => before.kind ≠ after.kind ∨
          before.kind = .sample) ∧
        (∀ phase ∈ phases.head?, phase.low = low) ∧
        (∀ phase ∈ phases.getLast?, phase.high = eventCount program) ∧
        (phases = [] → low = eventCount program) := by
    intro remaining
    induction remaining using Nat.strong_induction_on with
    | h remaining ih =>
        intro low counted bounded
        by_cases active : low < eventCount program
        · let phase := compiledPhaseAt program mode low active
          have starts : phase.low = low := rfl
          obtain ⟨rest, chain, maximal, first, last, empty⟩ :=
            ih (eventCount program - phase.high) (by have := phase.nonempty; omega)
              phase.high rfl phase.bounded
          refine ⟨phase :: rest, ?_, ?_, ?_, ?_, ?_⟩
          · exact chain.cons (fun next member => (first next member).symm)
          · exact maximal.cons (fun next member =>
              compiledPhaseAt_boundary program mode low active next (first next member))
          · intro next member
            have same : next = phase := by
              symm
              simpa only [List.head?_cons, Option.mem_some_iff] using member
            exact same ▸ starts
          · cases rest with
            | nil =>
                intro next member
                have same : next = phase := by
                  symm
                  simpa only [List.getLast?_singleton, Option.mem_some_iff] using member
                exact same ▸ empty rfl
            | cons next rest =>
                intro final member
                exact last final (by simpa only [List.getLast?_cons_cons] using member)
          · intro impossible
            cases impossible
        · have finished : low = eventCount program := by omega
          refine ⟨[], ?_, ?_, ?_, ?_, fun _ => finished⟩ <;> simp
  obtain ⟨phases, adjacent, maximal, first, last, empty⟩ :=
    suffixes (eventCount program) 0 (by omega)
    (Nat.zero_le _)
  exact ⟨⟨phases, adjacent, first, last, fun absent => (empty absent).symm⟩, maximal⟩

/-- The compiled program chooses its phase partition without a runtime hypothesis. -/
def compiledRuntimePhasePlan : RuntimePhasePlan ((toEventGraph program).withMode mode) :=
  (exists_compiledRuntimePhasePlan program mode).choose

/-- Adjacent commitment and disclosure blocks are never artificially split. -/
theorem compiledRuntimePhasePlan_maximal :
    (compiledRuntimePhasePlan program mode).phases.IsChain
      (fun before after => before.kind ≠ after.kind ∨ before.kind = .sample) :=
  (exists_compiledRuntimePhasePlan program mode).choose_spec

end Vegas
