/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryValueMenu

/-! # Legal source failure flags independent of ordinary domain draws -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem failure_action_unique (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (view : SourceProgram.ProtocolView who program) → (first second : OwnAction Player L) →
    first ∈ ProtocolView.available who program admission view →
    second ∈ ProtocolView.available who program admission view →
    first.IsFailure → second.IsFailure → first = second
  | _, _, .ret _, _, _, _, _, offered, _, _, _ => by cases offered
  | _, _, .sample _ _ _ next, admission, view, first, second, left, right, lf, rf => by
      cases view with
      | inl _ => cases left
      | inr later =>
          exact failure_action_unique who next admission later first second left right lf rf
  | _, _, .commit _ _ _ _ next, admission, view, first, second, left, right, lf, rf => by
      cases view with
      | inl _ =>
          obtain ⟨firstValue, _, rfl⟩ := left
          obtain ⟨secondValue, _, rfl⟩ := right
          change firstValue = .failure at lf
          change secondValue = .failure at rf
          rw [lf, rf]
      | inr later =>
          exact failure_action_unique who next (fun site => admission (some site)) later
            first second left right lf rf
  | _, _, .reveal _ _ _ _ _ _ next, admission, view, first, second, left, right, lf, rf => by
      cases view with
      | inl _ =>
          obtain ⟨firstValue, rfl⟩ := left
          obtain ⟨secondValue, rfl⟩ := right
          change firstValue = false at lf
          change secondValue = false at rf
          rw [lf, rf]
      | inr later =>
          exact failure_action_unique who next admission later first second left right lf rf

/-- At every ambient query there is a legal failure choice. Only a binding
can carry a missing marker; a reveal failure is withholding. -/
theorem commitRecovery_failureChoice_exists (who : Player)
    (info : setup.commitRecoveryModel.InfoState who) (omitted : Bool) :
    ∃ choice : setup.commitRecoveryModel.Choice who info,
      ∀ move, choice.val = some move → move.action.IsFailure ∧
        move.missing = (info.1.1.1.elim false (ProtocolView.atCommit who setup.program) &&
          omitted) := by
  classical
  by_cases active : setup.commitRecoveryActive who info.1.1
  · cases current : info.1.1.1 with
    | none => simp only [commitRecoveryActive, current, Option.elim_none] at active
    | some view =>
        have acting := active
        simp only [commitRecoveryActive, current, Option.elim_some] at acting
        obtain ⟨choice, legal, failed⟩ := ProtocolView.exists_failure_menu who setup.program
          (CommitmentInterface.forfeiture setup.program) (fun _ => rfl) view
        cases choice with
        | none => exact (legal acting.1).elim
        | some action =>
            let missing := ProtocolView.atCommit who setup.program view && omitted
            have offered : some (⟨action, missing⟩ : CommitRecoveryMove Player L) ∈
                setup.commitRecoveryModel.menu who info := by
              refine ⟨active, ?_⟩
              simp only [current, Option.elim_some]
              refine ⟨legal.2, ?_⟩
              cases committing : ProtocolView.atCommit who setup.program view
              · simp only [committing, Bool.false_eq_true, ↓reduceIte, missing,
                  Bool.false_and]
              · exact fun _ => failed action rfl
            refine ⟨⟨some ⟨action, missing⟩, offered⟩, ?_⟩
            intro move selected
            cases Option.some.inj selected
            exact ⟨failed action rfl, by simp only [Option.elim_some, missing]⟩
  · refine ⟨⟨none, active⟩, ?_⟩
    intro move impossible
    cases impossible

/-- The selected failed action is fixed by its query and public omission bit,
before any ordinary value or equilibrium is chosen. -/
def commitRecoveryFailureChoice (who : Player)
    (info : setup.commitRecoveryModel.InfoState who) (omitted : Bool) :
    setup.commitRecoveryModel.Choice who info :=
  Classical.choose (setup.commitRecovery_failureChoice_exists who info omitted)

theorem commitRecoveryFailureChoice_spec (who : Player)
    (info : setup.commitRecoveryModel.InfoState who) (omitted : Bool)
    (move : CommitRecoveryMove Player L)
    (selected : (setup.commitRecoveryFailureChoice who info omitted).val = some move) :
    move.action.IsFailure ∧
      move.missing = (info.1.1.1.elim false (ProtocolView.atCommit who setup.program) && omitted) :=
  Classical.choose_spec (setup.commitRecovery_failureChoice_exists who info omitted) move selected

theorem commitRecoveryFailureChoice_eq_of_failure_move (who : Player)
    (info : setup.commitRecoveryModel.InfoState who) (omitted : Bool)
    (choice : setup.commitRecoveryModel.Choice who info) (move : CommitRecoveryMove Player L)
    (selected : choice.val = some move) (failed : move.action.IsFailure)
    (missing : move.missing =
      (info.1.1.1.elim false (ProtocolView.atCommit who setup.program) && omitted)) :
    setup.commitRecoveryFailureChoice who info omitted = choice := by
  have legal := choice.property
  change setup.commitRecoveryMenu who info choice.val at legal
  rw [selected] at legal
  have otherLegal := (setup.commitRecoveryFailureChoice who info omitted).property
  change setup.commitRecoveryMenu who info
    (setup.commitRecoveryFailureChoice who info omitted).val at otherLegal
  cases chosen : (setup.commitRecoveryFailureChoice who info omitted).val with
  | none =>
      rw [chosen] at otherLegal
      exact (otherLegal legal.1).elim
  | some other =>
      rw [chosen] at otherLegal
      have properties := setup.commitRecoveryFailureChoice_spec who info omitted other chosen
      have actions : other.action = move.action := by
        cases current : info.1.1.1 with
        | none =>
            simp only [commitRecoveryMenu, current, Option.elim_none] at legal
            exact legal.2.elim
        | some view =>
            have offered := legal.2
            have otherOffered := otherLegal.2
            simp only [current, Option.elim_some] at offered otherOffered
            exact failure_action_unique who setup.program
              (CommitmentInterface.forfeiture setup.program) view other.action move.action
              otherOffered.1 offered.1 properties.1 failed
      have moves : other = move :=
        congrArg₂ CommitRecoveryMove.mk actions (properties.2.trans missing.symm)
      apply Subtype.ext
      rw [chosen, selected, moves]

/-- Decode independent source flags and an ordinary domain coordinate into
the original full source choice menu. Accepted failure is used only at commits. -/
def commitRecoveryValueFlags (who : Player) (info : setup.commitRecoveryModel.InfoState who)
    (omitted bad : Bool) (value : setup.CommitRecoveryValueChoice who info) :
    setup.commitRecoveryModel.Choice who info :=
  if omitted then setup.commitRecoveryFailureChoice who info true
  else if info.1.1.1.elim false (ProtocolView.atCommit who setup.program) && bad then
    setup.commitRecoveryFailureChoice who info false
  else value.val

/-- A fixed source omission coin and a distinct accepted-failure coin leave
only the ordinary conditional domain law available for optimization. -/
def commitRecoveryValueTremble (who : Player) (info : setup.commitRecoveryModel.InfoState who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : PMF (setup.CommitRecoveryValueChoice who info)) :
    PMF (setup.commitRecoveryModel.Choice who info) :=
  mix omission omissionNonnegative omissionBounded
    (PMF.pure (setup.commitRecoveryFailureChoice who info true))
    (if info.1.1.1.elim false (ProtocolView.atCommit who setup.program) then
      mix bad badNonnegative badBounded
        (PMF.pure (setup.commitRecoveryFailureChoice who info false))
        (values.map Subtype.val)
    else values.map Subtype.val)

/-- Positive source flags and a fully supported domain component support
every legal ambient source choice, including withholding at reveal sites. -/
theorem commitRecoveryValueTremble_fullSupport (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (omission : ℝ) (omissionPositive : 0 < omission) (omissionSmall : omission < 1)
    (bad : ℝ) (badPositive : 0 < bad) (badSmall : bad < 1)
    (values : PMF (setup.CommitRecoveryValueChoice who info)) (full : FullSupport values) :
    FullSupport (setup.commitRecoveryValueTremble who info
      omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le values) := by
  intro choice
  have legal := choice.property
  change setup.commitRecoveryMenu who info choice.val at legal
  cases selected : (choice.val : Option (CommitRecoveryMove Player L)) with
  | none =>
      rw [selected] at legal
      have equal : setup.commitRecoveryFailureChoice who info true = choice := by
        apply Subtype.ext
        rw [selected]
        have otherLegal := (setup.commitRecoveryFailureChoice who info true).property
        cases chosen : (setup.commitRecoveryFailureChoice who info true).val with
        | none => rfl
        | some move =>
            change setup.commitRecoveryMenu who info _ at otherLegal
            rw [chosen] at otherLegal
            exact (legal otherLegal.1).elim
      rw [commitRecoveryValueTremble, ← equal]
      exact mem_support_mix_left _ _ _ omissionPositive
        ((PMF.mem_support_pure_iff _ _).mpr rfl)
  | some move =>
      rw [selected] at legal
      have marker : if info.1.1.1.elim false (ProtocolView.atCommit who setup.program) then
          move.missing = true → move.action.IsFailure else move.missing = false := by
        have offered := legal.2
        change info.1.1.1.elim False
          (fun view => move ∈ ProtocolView.recoveryAvailable who setup.program view) at offered
        cases current : info.1.1.1 with
        | none =>
            rw [current] at offered
            exact offered.elim
        | some view =>
            rw [current] at offered
            simpa only [current, Option.elim_some] using offered.2
      by_cases failed : move.action.IsFailure
      · cases committing : info.1.1.1.elim false (ProtocolView.atCommit who setup.program)
        · have missing : move.missing = false := by simpa [committing] using marker
          have equal := setup.commitRecoveryFailureChoice_eq_of_failure_move who info true
            choice move selected failed
            (by simpa only [committing, Bool.false_and] using missing)
          rw [commitRecoveryValueTremble, ← equal]
          exact mem_support_mix_left _ _ _ omissionPositive
            ((PMF.mem_support_pure_iff _ _).mpr rfl)
        · cases omitted : move.missing
          · have equal := setup.commitRecoveryFailureChoice_eq_of_failure_move who info false
              choice move selected failed
              (by simpa only [committing, Bool.true_and] using omitted)
            rw [commitRecoveryValueTremble, committing]
            simp only [↓reduceIte]
            apply mem_support_mix_right _ _ _ omissionSmall
            rw [← equal]
            exact mem_support_mix_left _ _ _ badPositive
              ((PMF.mem_support_pure_iff _ _).mpr rfl)
          · have equal := setup.commitRecoveryFailureChoice_eq_of_failure_move who info true
              choice move selected failed
              (by simpa only [committing, Bool.true_and] using omitted)
            rw [commitRecoveryValueTremble, ← equal]
            exact mem_support_mix_left _ _ _ omissionPositive
              ((PMF.mem_support_pure_iff _ _).mpr rfl)
      · have missing : move.missing = false := by
          cases committing : info.1.1.1.elim false (ProtocolView.atCommit who setup.program)
          · simpa [committing] using marker
          · have forces : move.missing = true → move.action.IsFailure := by
              simpa [committing] using marker
            cases omitted : move.missing
            · rfl
            · exact (failed (forces omitted)).elim
        let ordinary : setup.CommitRecoveryValueChoice who info :=
          ⟨choice, fun other same => by
            have equal := Option.some.inj (selected.symm.trans same)
            cases equal
            exact ⟨missing, failed⟩⟩
        have supported : choice ∈ (values.map Subtype.val).support :=
          (PMF.mem_support_map_iff _ _ _).mpr ⟨ordinary, full ordinary, rfl⟩
        rw [commitRecoveryValueTremble]
        apply mem_support_mix_right _ _ _ omissionSmall
        cases committing : info.1.1.1.elim false (ProtocolView.atCommit who setup.program)
        · exact supported
        · exact mem_support_mix_right bad badPositive.le badSmall.le badSmall supported

/-- Independent flags followed by the original domain draw realize exactly
the prescribed full-menu source law. Neither flag is a native RAW tier. -/
theorem commitRecoveryValueFlags_law (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : PMF (setup.CommitRecoveryValueChoice who info)) :
    ((mix omission omissionNonnegative omissionBounded (PMF.pure true) (PMF.pure false)).bind
      fun omitted =>
        (mix bad badNonnegative badBounded (PMF.pure true) (PMF.pure false)).bind
          fun failed => values.map (setup.commitRecoveryValueFlags who info omitted failed)) =
      setup.commitRecoveryValueTremble who info omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded values := by
  have omittedLaw : values.map (fun _ => setup.commitRecoveryFailureChoice who info true) =
      PMF.pure (setup.commitRecoveryFailureChoice who info true) := PMF.map_const _ _
  have failedLaw : values.map (fun _ => setup.commitRecoveryFailureChoice who info false) =
      PMF.pure (setup.commitRecoveryFailureChoice who info false) := PMF.map_const _ _
  unfold commitRecoveryValueFlags
  simp only [mix_bind, PMF.pure_bind]
  cases committing : info.1.1.1.elim false (ProtocolView.atCommit who setup.program)
  · simp only [committing, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      commitRecoveryValueTremble, mix_self]
    rw [omittedLaw]
  · simp only [committing, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      commitRecoveryValueTremble, mix_self]
    rw [omittedLaw, failedLaw]

variable {Γ : SourceCtx Player L} {O : Finset VarId} {owner : Player} {name : VarId}
  {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
  {guard : SourceGuard L Γ owner name payload}
  {next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O)}
  {lift : SourceProgram.ProtocolState (.commit name owner fresh guard next) →
    SourceProgram.ProtocolState setup.program}

end Vegas.SourceProgram.Setup
