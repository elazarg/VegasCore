/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryDebt

/-! # Every published source failure belongs to a permanently excluded player -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- Only already processed publications are checked. Unusable private bindings
remain latent until an actual reveal fails. -/
def FailuresCovered : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → Finset Player → ProtocolState program → Prop
  | _, _, .ret _, _, _ => True
  | _, _, .sample _ _ _ next, excluded, point =>
      point.elim (fun _ => True) (FailuresCovered next excluded)
  | _, _, .commit _ _ _ _ next, excluded, point =>
      point.elim (fun _ => True) (FailuresCovered next excluded)
  | _, _, .reveal _ owner _ _ _ _ next, excluded, point =>
      point.elim (fun _ => True) (fun rest =>
        ((base next rest).get .here = .failure → owner ∈ excluded) ∧
          FailuresCovered next excluded rest)

theorem failuresCovered_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (excluded : Finset Player)
    (config : Config Player L Γ) : FailuresCovered program excluded (entry program config) := by
  cases program <;> trivial

theorem FailuresCovered.mono : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) {before after : Finset Player}
    (point : ProtocolState program), before ⊆ after →
    FailuresCovered program before point → FailuresCovered program after point
  | _, _, .ret _, _, _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, _, _, point, subset, covered => by
      cases point with
      | inl _ => trivial
      | inr point => exact FailuresCovered.mono next point subset covered
  | _, _, .commit _ _ _ _ next, _, _, point, subset, covered => by
      cases point with
      | inl _ => trivial
      | inr point => exact FailuresCovered.mono next point subset covered
  | _, _, .reveal _ _ _ _ _ _ next, _, _, point, subset, covered => by
      cases point with
      | inl _ => trivial
      | inr point =>
          exact ⟨fun failure => subset (covered.1 failure),
            FailuresCovered.mono next point subset covered.2⟩

theorem failuresCovered_withHistory : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (excluded : Finset Player)
    (point : ProtocolState program) (past : History Player L),
    FailuresCovered program excluded (withHistory program point past) ↔
      FailuresCovered program excluded point
  | _, _, .ret _, _, _, _ => Iff.rfl
  | _, _, .sample _ _ _ next, excluded, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => exact failuresCovered_withHistory next excluded point past
  | _, _, .commit _ _ _ _ next, excluded, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => exact failuresCovered_withHistory next excluded point past
  | _, _, .reveal _ _ _ _ _ _ next, excluded, point, past => by
      cases point with
      | inl _ => rfl
      | inr point =>
          change (_ ∧ FailuresCovered next excluded (withHistory next point past)) ↔
            (_ ∧ FailuresCovered next excluded point)
          rw [base_withHistory, failuresCovered_withHistory next excluded point past]

theorem failuresCovered_automaticCommitBlock :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (excluded : Finset Player)
    (point : ProtocolState program), FailuresCovered program excluded point →
      FailuresCovered program excluded (automaticCommitBlock program point)
  | _, _, .ret _, _, _, covered => covered
  | _, _, .sample _ _ _ next, excluded, point, covered => by
      cases point with
      | inl _ => exact covered
      | inr point => exact failuresCovered_automaticCommitBlock next excluded point covered
  | _, _, .commit _ _ _ _ next, excluded, point, covered => by
      cases point with
      | inl config =>
          exact failuresCovered_automaticCommitBlock next excluded _
            (failuresCovered_entry next excluded _)
      | inr point => exact failuresCovered_automaticCommitBlock next excluded point covered
  | _, _, .reveal _ _ _ _ _ _ next, excluded, point, covered => by
      cases point with
      | inl _ => exact covered
      | inr point =>
          exact ⟨fun failed => covered.1 (by simpa only [base_automaticCommitBlock] using failed),
            failuresCovered_automaticCommitBlock next excluded point covered.2⟩

/-- Actual reveal failure inserts its owner before any automatic phase closure. -/
theorem failuresCovered_recoveryStep : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L))
    (result : ProtocolState program × Finset Player),
    FailuresCovered program excluded point →
    result ∈ (recoveryStep program point excluded joint).support →
      FailuresCovered program result.2 result.1
  | _, _, .ret _, _, _, _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, point, excluded, joint, result, covered, reached => by
      cases point with
      | inl config =>
          obtain ⟨value, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          exact failuresCovered_entry next excluded _
      | inr point =>
          obtain ⟨after, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          exact failuresCovered_recoveryStep next point excluded joint after covered supported
  | _, _, .commit _ _ _ _ next, point, excluded, joint, result, covered, reached => by
      cases point with
      | inl config =>
          simp only [recoveryStep, Sum.elim_inl] at reached
          split at reached <;> rw [PMF.mem_support_pure_iff] at reached <;> cases reached <;>
            exact failuresCovered_entry next _ _
      | inr point =>
          obtain ⟨after, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          exact failuresCovered_recoveryStep next point excluded joint after covered supported
  | _, _, .reveal published owner _ _ source _ next, point, excluded, joint, result,
      covered, reached => by
      cases point with
      | inl config =>
          simp only [recoveryStep, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          cases reached
          constructor
          · intro failure
            simp only [base_entry] at failure
            dsimp only at failure ⊢
            split at failure
            · next inactive => simp only [inactive, ↓reduceIte, failure, Finset.mem_insert_self]
            · next active => simp only [active, ↓reduceIte, failure, Finset.mem_insert_self]
          · exact failuresCovered_entry next _ _
      | inr point =>
          obtain ⟨after, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          exact ⟨fun failure => recoveryStep_excluded_monotone next point excluded joint after
              supported (covered.1 (by
                rw [← base_recoveryStep next point excluded joint after supported]
                exact failure)),
            failuresCovered_recoveryStep next point excluded joint after covered.2 supported⟩

/-- A nonexcluded player's terminal store contains no failed own publication. -/
theorem failedReveals_eq_zero_of_failuresCovered (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (excluded : Finset Player), FailuresCovered program excluded point → who ∉ excluded →
    {terminal : State L program.terminalCtx} → readout program point = some terminal →
      failedReveals program who (publicOutcome program terminal) = 0
  | _, _, .ret _, _, _, _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, point, excluded, covered, active, terminal, read => by
      cases point with
      | inl _ => cases read
      | inr point =>
          exact failedReveals_eq_zero_of_failuresCovered who next point excluded covered active read
  | _, _, .commit _ _ _ _ next, point, excluded, covered, active, terminal, read => by
      cases point with
      | inl _ => cases read
      | inr point =>
          exact failedReveals_eq_zero_of_failuresCovered who next point excluded covered active read
  | _, _, .reveal _ owner _ _ _ _ next, point, excluded, covered, active, terminal, read => by
      cases point with
      | inl _ => cases read
      | inr point =>
          have rest := failedReveals_eq_zero_of_failuresCovered who next point excluded
            covered.2 active read
          by_cases own : owner = who
          · have nonfailure : (base next point).get .here ≠ .failure := by
              intro failed
              exact active (own ▸ covered.1 failed)
            cases opened : (base next point).get .here with
            | failure => exact False.elim (nonfailure opened)
            | success value =>
                have holds : terminal.get (terminalRef next .here) = .success value :=
                  (terminalRef_get next terminal .here).trans
                    ((congrArg (fun state => state.get .here)
                      (initialState_of_readout next point read)).trans opened)
                rw [failedReveals_reveal_of_not_failed who _
                  (RevealCell.failed_publicOutcome_of_success next _ terminal holds)]
                exact rest
          · simp only [failedReveals, revealCells, List.filter_cons, own, decide_false,
              Bool.false_and, Bool.false_eq_true, ↓reduceIte]
            exact rest

end ProtocolState

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}

theorem close_failuresCovered (state : CommitRecoveryState program)
    (saved : ProtocolState.FailuresCovered program state.excluded state.saved)
    (live : ProtocolState.FailuresCovered program state.excluded state.point) :
    ProtocolState.FailuresCovered program state.close.excluded state.close.saved ∧
      ProtocolState.FailuresCovered program state.close.excluded state.close.point := by
  rw [close_excluded]
  unfold close
  split
  · split
    · split
      · have kept := (ProtocolState.failuresCovered_withHistory program state.excluded state.saved
          (ProtocolState.history program state.point)).mpr saved
        exact ⟨kept, kept⟩
      · have kept := ProtocolState.failuresCovered_automaticCommitBlock program state.excluded _
          ((ProtocolState.failuresCovered_withHistory program state.excluded state.saved
            (ProtocolState.history program state.point)).mpr saved)
        exact ⟨kept, kept⟩
    · exact ⟨live, live⟩
  · split
    · exact ⟨saved, live⟩
    · exact ⟨live, live⟩

theorem step_failuresCovered (state : CommitRecoveryState program)
    (saved : ProtocolState.FailuresCovered program state.excluded state.saved)
    (live : ProtocolState.FailuresCovered program state.excluded state.point)
    (joint : Player → Option (CommitRecoveryMove Player L)) (next : CommitRecoveryState program)
    (supported : next ∈ (state.step joint).support) :
    ProtocolState.FailuresCovered program next.excluded next.saved ∧
      ProtocolState.FailuresCovered program next.excluded next.point := by
  obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have raw : result.1 ∈
      (ProtocolState.recoveryStep program state.point state.excluded joint).support := by
    rw [← map_val_pmfToSubtype
      (ProtocolState.recoveryStep program state.point state.excluded joint)
      (fun result supported => ProtocolState.recoveryStep_excluded_monotone program state.point
        state.excluded joint result supported)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
  exact (state.install result.1 result.2).close_failuresCovered
    (ProtocolState.FailuresCovered.mono program state.saved result.2 saved)
    (ProtocolState.failuresCovered_recoveryStep program state.point state.excluded joint
      result.1 live raw)

end CommitRecoveryState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- Both actual source checkpoints cover every processed failed publication,
including histories with arbitrary private failures, foreign actions and resets. -/
theorem commitRecovery_failuresCovered {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    ∀ current, state = some current →
      ProtocolState.FailuresCovered setup.program current.excluded current.saved ∧
        ProtocolState.FailuresCovered setup.program current.excluded current.point := by
  induction trace with
  | start => intro current impossible; cases impossible
  | @extend before after prior joint _ supported ih =>
      intro current equality
      cases before with
      | none =>
          obtain ⟨inputs, _member, target⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          have same := Option.some.inj (target.trans equality)
          subst current
          exact ⟨ProtocolState.failuresCovered_entry _ _ _,
            ProtocolState.failuresCovered_entry _ _ _⟩
      | some previous =>
          obtain ⟨next, member, target⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          have same := Option.some.inj (target.trans equality)
          subst current
          exact previous.step_failuresCovered (ih previous rfl).1 (ih previous rfl).2
            joint next member

/-- Latent debt at an actual terminal recovery history has become permanent
exclusion. This endpoint uses actual history coverage, not an intended invariant. -/
theorem commitRecovery_terminal_excluded_of_owesFailure
    {state : setup.commitRecoveryProtocol.State} (trace : setup.commitRecoveryProtocol.Trace state)
    (current : CommitRecoveryState setup.program) (equality : state = some current)
    (who : Player) (owed : ProtocolState.OwesFailure who setup.program current.point)
    (stopped : ProtocolState.terminal setup.program current.point) : who ∈ current.excluded := by
  by_contra active
  obtain ⟨terminal, read⟩ := ProtocolState.exists_readout_of_terminal _ _ stopped
  have positive := ProtocolState.failedReveals_pos_of_owesFailure who _ _ owed read
  have zero := ProtocolState.failedReveals_eq_zero_of_failuresCovered who _ _ _
    (setup.commitRecovery_failuresCovered trace current equality).2 active read
  omega

end Setup
end Vegas.SourceProgram
