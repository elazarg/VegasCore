/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryContinuingMenu
import Vegas.Source.ProtocolSuffix
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Domain-valued source recovery moves with separate failure trembles

An accepted failed binding and a missing binding are different legal source
actions. Ordinary source value components use actual payloads and true
openings. Their full-support perturbations retain both failure atoms with
separate probabilities; neither atom is silently removed by conditioning.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- Ordinary source moves use domain values and open, with no omission.
Unlike `CommitRecoveryContinuingChoice`, this excludes accepted failed
bindings from the value component. -/
def CommitRecoveryValueChoice (who : Player) (info : setup.commitRecoveryModel.InfoState who) :=
  {choice : setup.commitRecoveryModel.Choice who info //
    ∀ move, choice.1 = some move → move.missing = false ∧ ¬ move.action.IsFailure}

theorem commitRecoveryValueChoice_nonempty (who : Player)
    (info : setup.commitRecoveryModel.InfoState who) :
    Nonempty (setup.CommitRecoveryValueChoice who info) := by
  classical
  by_cases active : setup.commitRecoveryActive who info.1.1
  · cases current : info.1.1.1 with
    | none => simp only [commitRecoveryActive, current, Option.elim_none] at active
    | some view =>
        have acting := active
        simp only [commitRecoveryActive, current, Option.elim_some] at acting
        obtain ⟨choice, legal, moves⟩ := ProtocolView.exists_move_menu who setup.program
          (CommitmentInterface.forfeiture setup.program) view
        cases choice with
        | none => exact (legal acting.1).elim
        | some action =>
            have offered : some (⟨action, false⟩ : CommitRecoveryMove Player L) ∈
                setup.commitRecoveryModel.menu who info := by
              refine ⟨active, ?_⟩
              simp only [current, Option.elim_some]
              exact ⟨legal.2, by simp only [Bool.false_eq_true, false_implies, ite_self]⟩
            refine ⟨⟨⟨some ⟨action, false⟩, offered⟩, ?_⟩⟩
            intro move selected
            cases Option.some.inj selected
            exact ⟨rfl, moves action rfl⟩
  · refine ⟨⟨⟨none, active⟩, ?_⟩⟩
    intro move impossible
    cases impossible

theorem commitRecoveryValueChoice_finite (finite : setup.program.FiniteBindingTypes)
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    Finite (setup.CommitRecoveryValueChoice who info) := by
  let := setup.commitRecovery_finite_choice finite who info
  exact Finite.of_injective Subtype.val Subtype.val_injective

/-- Ordinary value choices embed into the actual continuing source menu. -/
def commitRecoveryValueChoice (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    setup.CommitRecoveryValueChoice who info ↪ setup.CommitRecoveryContinuingChoice who info :=
  ⟨fun choice => ⟨choice.1, fun move selected =>
      ⟨(choice.2 move selected).1, fun _ => (choice.2 move selected).2⟩⟩,
    fun _ _ same => Subtype.ext
      (congrArg (fun choice : setup.CommitRecoveryContinuingChoice who info => choice.1) same)⟩

end Setup

namespace CommitRecoveryMove

/-- A binding has one atom for each payload and two distinct failed atoms:
accepted failure (`false`) and omission (`true`). -/
def bindingAtom (owner : Player) (name : VarId) (payload : L.Ty) :
    L.Val payload ⊕ Bool → CommitRecoveryMove Player L
  | .inl value => ⟨.commit owner name payload (.success value), false⟩
  | .inr omitted => ⟨.commit owner name payload .failure, omitted⟩

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem bindingAtom_injective (owner : Player) (name : VarId) (payload : L.Ty) :
    Function.Injective (bindingAtom owner name payload) := by
  intro first second same
  cases first <;> cases second <;>
    simp_all [bindingAtom, CommitRecoveryMove.mk.injEq, OwnAction.commit.injEq, heq_eq_eq]

/-- Every binding atom belongs to the actual full recovery source menu. -/
theorem bindingAtom_available {Γ : SourceCtx Player L} {O : Finset VarId}
    (owner : Player) (name : VarId) (payload : L.Ty) (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (view : DecisionView owner Γ) (atom : L.Val payload ⊕ Bool) :
    bindingAtom owner name payload atom ∈ ProtocolView.recoveryAvailable owner
      (.commit name owner fresh guard next) (.inl view) := by
  cases atom with
  | inl value =>
      refine ⟨⟨.success value, trivial, rfl⟩, ?_⟩
      intro impossible
      cases impossible
  | inr omitted => exact ⟨⟨.failure, rfl, rfl⟩, fun _ => rfl⟩

/-- The three binding classes exhaust the actual recovery menu. This keeps
accepted failure separate from both ordinary values and omissions. -/
theorem exists_bindingAtom_of_available {Γ : SourceCtx Player L} {O : Finset VarId}
    (owner : Player) (name : VarId) (payload : L.Ty) (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (view : DecisionView owner Γ) (move : CommitRecoveryMove Player L)
    (offered : move ∈ ProtocolView.recoveryAvailable owner
      (.commit name owner fresh guard next) (.inl view)) :
    ∃ atom, bindingAtom owner name payload atom = move := by
  obtain ⟨⟨result, _admitted, action⟩, missing⟩ := offered
  cases result with
  | failure =>
      refine ⟨.inr move.missing, ?_⟩
      exact congrArg (fun action => (⟨action, move.missing⟩ : CommitRecoveryMove Player L))
        action.symm
  | success value =>
      have noMiss : move.missing = false := by
        cases flag : move.missing with
        | false => rfl
        | true =>
            have failed := missing flag
            rw [action] at failed
            cases failed
      refine ⟨.inl value, ?_⟩
      exact congrArg₂ CommitRecoveryMove.mk action.symm noMiss.symm

/-- Sample omission before the distinct accepted-failure tremble, then the
ordinary payload. Both rates are source perturbations. -/
def bindingValueLaw (owner : Player) (name : VarId) (payload : L.Ty)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : PMF (L.Val payload)) : PMF (CommitRecoveryMove Player L) :=
  mix omission omissionNonnegative omissionBounded
    (PMF.pure (bindingAtom owner name payload (.inr true)))
    (mix bad badNonnegative badBounded
      (PMF.pure (bindingAtom owner name payload (.inr false)))
      (values.map (fun value => bindingAtom owner name payload (.inl value))))

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Omission is the prescribed source coin, independent of the payload law
and of the separate accepted-failure tremble. -/
theorem bindingValueLaw_missing (owner : Player) (name : VarId) (payload : L.Ty)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : PMF (L.Val payload)) :
    (bindingValueLaw owner name payload omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded values).map (·.missing) =
      mix omission omissionNonnegative omissionBounded (PMF.pure true) (PMF.pure false) := by
  simp only [bindingValueLaw, mix_map, PMF.pure_map, PMF.map_comp, bindingAtom, Function.comp_def]
  rw [show values.map (fun _ => false) = PMF.pure false from PMF.map_const _ _]
  exact congrArg (mix omission omissionNonnegative omissionBounded (PMF.pure true))
    (mix_self _ _ _ _)

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Positive source trembles and a fully supported domain law support every
legal binding atom, including the accepted failed binding. -/
theorem bindingValueLaw_atom_supported (owner : Player) (name : VarId) (payload : L.Ty)
    (omission : ℝ) (omissionPositive : 0 < omission) (omissionSmall : omission < 1)
    (bad : ℝ) (badPositive : 0 < bad) (badSmall : bad < 1)
    (values : PMF (L.Val payload)) (full : FullSupport values)
    (atom : L.Val payload ⊕ Bool) :
    bindingAtom owner name payload atom ∈
      (bindingValueLaw owner name payload omission omissionPositive.le omissionSmall.le
        bad badPositive.le badSmall.le values).support := by
  cases atom with
  | inl value =>
      apply mem_support_mix_right _ _ _ omissionSmall
      apply mem_support_mix_right _ _ _ badSmall
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨value, full value, rfl⟩
  | inr omitted =>
      cases omitted with
      | true =>
          exact mem_support_mix_left _ _ _ omissionPositive
            ((PMF.mem_support_pure_iff _ _).mpr rfl)
      | false =>
          apply mem_support_mix_right _ _ _ omissionSmall
          exact mem_support_mix_left _ _ _ badPositive
            ((PMF.mem_support_pure_iff _ _).mpr rfl)

end CommitRecoveryMove

namespace ProtocolSuffix

/-- A genuine syntactic suffix preserves the actual full recovery menu. -/
theorem recoveryAvailable {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) (who : Player) :
    ∀ point, ProtocolView.recoveryAvailable who whole
        (ProtocolState.observe who whole (lift point)) =
      ProtocolView.recoveryAvailable who program (ProtocolState.observe who program point) := by
  induction origin with
  | initial => intro point; rfl
  | sampleTail _ _ _ _ ih => intro point; exact ih (.inr point)
  | commitTail _ _ _ _ ih => intro point; exact ih (.inr point)
  | revealTail _ _ _ _ _ ih => intro point; exact ih (.inr point)

/-- The actor of a genuine syntactic suffix is the original source actor. -/
theorem actor_lift {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) :
    ∀ point, ProtocolState.actor whole (lift point) = ProtocolState.actor program point := by
  induction origin with
  | initial => intro point; rfl
  | sampleTail _ _ _ _ ih => intro point; exact ih (.inr point)
  | commitTail _ _ _ _ ih => intro point; exact ih (.inr point)
  | revealTail _ _ _ _ _ ih => intro point; exact ih (.inr point)

end ProtocolSuffix

namespace Setup

open GameTheory.Protocol

variable (setup : Setup (Player := Player) (L := L))
  {Γ : SourceCtx Player L} {O : Finset VarId} {owner : Player} {name : VarId}
  {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
  {guard : SourceGuard L Γ owner name payload}
  {next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O)}
  {lift : SourceProgram.ProtocolState (.commit name owner fresh guard next) →
    SourceProgram.ProtocolState setup.program}

/-- Embed each of the three binding classes at the actual complete source
query, retaining all its prior signals and original own-play tags. -/
def commitRecoveryBindingAtom
    (origin : ProtocolSuffix setup.program (.commit name owner fresh guard next) lift)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current)) (config : Config Player L Γ)
    (atPoint : current.point = lift (.inl config)) (survives : owner ∉ current.excluded) :
    L.Val payload ⊕ Bool ↪
      setup.commitRecoveryModel.Choice owner (setup.commitRecoveryModel.infoOf owner trace) where
  toFun atom := ⟨some (CommitRecoveryMove.bindingAtom owner name payload atom), by
    have observed : (setup.commitRecoveryModel.infoOf owner trace).1.1 =
        (some (ProtocolState.observe owner setup.program current.point),
          setup.commitRecoveryPublic (some current)) := by
      change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf owner trace).1.1 = _
      rw [InfoSignals.withOwnPlayRecall_infoOf]
      exact setup.commitRecoverySignals_current owner trace
    change setup.commitRecoveryMenu owner (setup.commitRecoveryModel.infoOf owner trace)
      (some (CommitRecoveryMove.bindingAtom owner name payload atom))
    refine ⟨?_, ?_⟩
    · unfold commitRecoveryActive
      rw [observed]
      change ProtocolView.actor owner setup.program
        (ProtocolState.observe owner setup.program current.point) = some owner ∧
        owner ∉ current.excluded
      rw [ProtocolState.actor_observe_eq, atPoint, origin.actor_lift]
      exact ⟨rfl, survives⟩
    · rw [congrArg Prod.fst observed]
      change CommitRecoveryMove.bindingAtom owner name payload atom ∈
        ProtocolView.recoveryAvailable owner setup.program
          (ProtocolState.observe owner setup.program current.point)
      rw [atPoint, origin.recoveryAvailable]
      exact CommitRecoveryMove.bindingAtom_available owner name payload fresh guard next
        (config.view owner) atom⟩
  inj' first second same :=
    CommitRecoveryMove.bindingAtom_injective owner name payload
      (Option.some.inj (congrArg Subtype.val same))

/-- The three binding classes cover the entire genuine full-information
choice menu, rather than only a chosen supported subset. -/
theorem commitRecoveryBindingAtom_surjective
    (origin : ProtocolSuffix setup.program (.commit name owner fresh guard next) lift)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current)) (config : Config Player L Γ)
    (atPoint : current.point = lift (.inl config)) (survives : owner ∉ current.excluded) :
    Function.Surjective
      (setup.commitRecoveryBindingAtom origin current trace config atPoint survives) := by
  intro choice
  have legal := (setup.commitRecoveryMenu_adequate owner trace choice.1).mp choice.2
  cases selected : choice.1 with
  | none =>
      rw [selected] at legal
      change ¬ current.Active owner at legal
      apply (legal _).elim
      refine ⟨?_, survives⟩
      rw [atPoint, origin.actor_lift]
      rfl
  | some move =>
      rw [selected] at legal
      have offered : move ∈ current.available owner := legal.2
      rw [CommitRecoveryState.available, atPoint, origin.recoveryAvailable] at offered
      obtain ⟨atom, same⟩ := CommitRecoveryMove.exists_bindingAtom_of_available
        owner name payload fresh guard next (config.view owner) move offered
      refine ⟨atom, Subtype.ext ?_⟩
      change some (CommitRecoveryMove.bindingAtom owner name payload atom) = choice.1
      rw [selected, same]

/-- The concrete three-class binding component is a law on the actual
full-information choice type, rather than a raw law waiting for a legality
premise. No initial draw, prior history or source query is replaced. -/
def commitRecoveryBindingValueLaw
    (origin : ProtocolSuffix setup.program (.commit name owner fresh guard next) lift)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current)) (config : Config Player L Γ)
    (atPoint : current.point = lift (.inl config)) (survives : owner ∉ current.excluded)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : PMF (L.Val payload)) :
    PMF (setup.commitRecoveryModel.Choice owner (setup.commitRecoveryModel.infoOf owner trace)) :=
  let encode := setup.commitRecoveryBindingAtom origin current trace config atPoint survives
  mix omission omissionNonnegative omissionBounded (PMF.pure (encode (.inr true)))
    (mix bad badNonnegative badBounded (PMF.pure (encode (.inr false)))
      (values.map fun value => encode (.inl value)))

/-- The actual source-choice law realizes the original payload draw and both
distinct failure flags exactly. -/
theorem commitRecoveryBindingValueLaw_raw
    (origin : ProtocolSuffix setup.program (.commit name owner fresh guard next) lift)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current)) (config : Config Player L Γ)
    (atPoint : current.point = lift (.inl config)) (survives : owner ∉ current.excluded)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : PMF (L.Val payload)) :
    (setup.commitRecoveryBindingValueLaw origin current trace config atPoint survives
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded values).map
        Subtype.val =
      (CommitRecoveryMove.bindingValueLaw owner name payload
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded values).map
        some := by
  simp only [commitRecoveryBindingValueLaw, CommitRecoveryMove.bindingValueLaw, mix_map,
    PMF.pure_map, PMF.map_comp, commitRecoveryBindingAtom, Function.comp_def]
  rfl

/-- Positive omission and accepted-failure source trembles, together with a
fully supported domain law, make the actual complete query fully mixed. -/
theorem commitRecoveryBindingValueLaw_fullSupport
    (origin : ProtocolSuffix setup.program (.commit name owner fresh guard next) lift)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current)) (config : Config Player L Γ)
    (atPoint : current.point = lift (.inl config)) (survives : owner ∉ current.excluded)
    (omission : ℝ) (omissionPositive : 0 < omission) (omissionSmall : omission < 1)
    (bad : ℝ) (badPositive : 0 < bad) (badSmall : bad < 1)
    (values : PMF (L.Val payload)) (full : FullSupport values) :
    FullSupport (setup.commitRecoveryBindingValueLaw origin current trace config atPoint survives
      omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le values) := by
  intro choice
  obtain ⟨atom, rfl⟩ := setup.commitRecoveryBindingAtom_surjective origin current trace config
    atPoint survives choice
  cases atom with
  | inl value =>
      apply mem_support_mix_right omission omissionPositive.le omissionSmall.le omissionSmall
      apply mem_support_mix_right bad badPositive.le badSmall.le badSmall
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨value, full value, rfl⟩
  | inr omitted =>
      cases omitted with
      | true =>
          exact mem_support_mix_left omission omissionPositive.le omissionSmall.le omissionPositive
            ((PMF.mem_support_pure_iff _ _).mpr rfl)
      | false =>
          apply mem_support_mix_right omission omissionPositive.le omissionSmall.le omissionSmall
          exact mem_support_mix_left bad badPositive.le badSmall.le badPositive
            ((PMF.mem_support_pure_iff _ _).mpr rfl)

end Setup
end Vegas.SourceProgram
