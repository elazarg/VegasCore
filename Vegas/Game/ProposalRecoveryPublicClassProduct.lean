/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryClassRows
import Vegas.Source.ProposalRecoveryPreparationRepairMoves
import Vegas.Source.CommitRecoveryWordMass
import GameTheoryExtensions.Analysis.Protocol.ContinuationOwnPlay
import GameTheoryExtensions.Analysis.Protocol.OwnPlayReach

/-! # Actual foreign source row products and their literal disclosure causes -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open scoped ENNReal

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- The actual one-step source observable and its conditional atom multiply
back to the original atom, including zero-probability target coordinates. -/
private theorem foreign_cause_atom_reconstruct
    (profile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (focal : Player) (before after : setup.proposalRecoveryProtocol.History) :
    let law := setup.proposalRecoveryModel.runBehavioralFrom profile 1 before
    let observe := setup.proposalRecoveryForeignCauseRead focal
    (law.map observe) (observe after) * fiberPosterior law observe (observe after) after =
      law after := by
  classical
  intro law observe
  by_cases present : observe after ∈ (law.map observe).support
  · rw [fiberPosterior_apply law observe (observe after) present]
    rw [Set.indicator_of_mem (show after ∈ {point | observe point = observe after} from rfl)]
    calc
      _ = law after * ((law.map observe) (observe after) *
          ((law.map observe) (observe after))⁻¹) := by ac_rfl
      _ = law after := by
        rw [ENNReal.mul_inv_cancel ((PMF.mem_support_iff _ _).mp present)
          (PMF.apply_ne_top _ _), mul_one]
  · have marginalZero : (law.map observe) (observe after) = 0 :=
      (PMF.apply_eq_zero_iff _ _).mpr present
    have targetZero : law after = 0 := by
      apply (PMF.apply_eq_zero_iff _ _).mpr
      intro supported
      exact present ((PMF.mem_support_map_iff _ _ _).mpr ⟨after, supported, rfl⟩)
    rw [marginalZero, targetZero, zero_mul]

/-- One literal foreign row supplies its class, ordinary domain atom, and
conditional source cause. BAD is kept as its own actual nonmissing class.
Nature, initialization, focal rows and automatic NONE rows supply ones. -/
def proposalRecoveryForeignRowFactors
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1) (focal : Player)
    (before : setup.proposalRecoveryProtocol.History)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before.state joint)
    {target : setup.proposalRecoveryProtocol.State}
    (supported : target ∈ (setup.proposalRecoveryProtocol.step before.state
      ⟨joint, legal⟩).support) : ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ :=
  match before.state with
  | none => (1, 1, 1)
  | some current =>
      match ProtocolState.actor setup.program current.point with
      | none => (1, 1, 1)
      | some owner =>
          if owner = focal then (1, 1, 1) else
            match joint owner with
            | none => (1, 1, 1)
            | some move =>
                match move.semantic.action with
                | .commit _ _ _ binding =>
                    if move.semantic.missing then (ENNReal.ofReal omission.val, 1, 1) else
                      match binding with
                      | .failure => (ENNReal.ofReal ((1 - omission.val) * bad.val), 1, 1)
                      | .success _ =>
                          let ordinary := setup.proposalRecoveryNormalizedTrembledProfile
                            0 le_rfl zero_le_one 0 le_rfl zero_le_one
                              0 le_rfl zero_le_one values
                          (ENNReal.ofReal ((1 - omission.val) * (1 - bad.val)),
                            ((ordinary owner (setup.proposalRecoveryModel.infoOf owner
                              before.trace)).map Subtype.val) (some move), 1)
                | .reveal _ _ _ =>
                    let profile := setup.proposalRecoveryNormalizedTrembledProfile
                      omission.val omission.property.1 omission.property.2
                      bad.val bad.property.1 bad.property.2
                      delivery.val delivery.property.1 delivery.property.2 values
                    let law := setup.proposalRecoveryModel.runBehavioralFrom profile 1 before
                    let after := before.extend legal supported
                    let observe := setup.proposalRecoveryForeignCauseRead focal
                    ((law.map observe) (observe after), 1,
                      fiberPosterior law observe (observe after) after)

/-- These products fold the existing finite source Trace. The complete past
and every historical accepted value stay literal; no later completion row
is included beyond this trace's endpoint. -/
def proposalRecoveryForeignProducts
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1) (focal : Player) :
    ∀ {state : setup.proposalRecoveryProtocol.State},
      setup.proposalRecoveryProtocol.Trace state → ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞
  | _, .start => (1, 1, 1)
  | _, .extend prior joint legal supported =>
      let previous := proposalRecoveryForeignProducts values omission bad delivery focal prior
      let row := setup.proposalRecoveryForeignRowFactors values omission bad delivery focal
        ⟨_, prior⟩ joint legal supported
      (previous.1 * row.1, previous.2.1 * row.2.1, previous.2.2 * row.2.2)

@[simp] theorem proposalRecoveryForeignProducts_start
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1) (focal : Player) :
    setup.proposalRecoveryForeignProducts values omission bad delivery focal
        (.start : setup.proposalRecoveryProtocol.Trace setup.proposalRecoveryProtocol.init) =
      (1, 1, 1) := rfl

/-- The actual foreign publication row keeps the exact one-step posterior
used in source refinement, rather than replacing it with receipt identity. -/
theorem proposalRecoveryForeignRowFactors_reveal_reconstruct
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1) (focal : Player)
    (before : setup.proposalRecoveryProtocol.History)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before.state joint)
    {target : setup.proposalRecoveryProtocol.State}
    (supported : target ∈ (setup.proposalRecoveryProtocol.step before.state
      ⟨joint, legal⟩).support)
    (current : CommitRecoveryState setup.program) (state : before.state = some current)
    (owner : Player) (acting : ProtocolState.actor setup.program current.point = some owner)
    (foreign : owner ≠ focal) (move : ProposalRecoveryMove Player L)
    (selected : joint owner = some move)
    (author : Player) (name : VarId) (disclosed : Bool)
    (revealing : move.semantic.action = .reveal author name disclosed) :
    let profile := setup.proposalRecoveryNormalizedTrembledProfile
      omission.val omission.property.1 omission.property.2
      bad.val bad.property.1 bad.property.2
      delivery.val delivery.property.1 delivery.property.2 values
    let row := setup.proposalRecoveryForeignRowFactors values omission bad delivery focal
      before joint legal supported
    row.1 * row.2.2 =
      setup.proposalRecoveryModel.runBehavioralFrom profile 1 before
        (before.extend legal supported) := by
  intro profile row
  have identity := foreign_cause_atom_reconstruct setup profile focal before
    (before.extend legal supported)
  simpa only [row, proposalRecoveryForeignRowFactors, state, acting, foreign,
    ite_false, selected, revealing] using identity


omit [Fintype Player] in
/-- The original source component assigns a proper ordinary atom exactly its
ordinary domain mass times the two commitment flag survival factors. This
keeps zero domain atoms rather than dividing them out. -/
theorem proposalRecoveryComponentTrembledLaw_ordinary_commit_atom
    (owner : Player) (key : setup.ProposalRecoveryComponent owner)
    (committing : key.1.1.1.1.elim false
      (ProtocolView.atCommit owner setup.program) = true)
    (omission bad delivery : Set.Icc (0 : ℝ) 1)
    (values : PMF (setup.CommitRecoveryValueChoice owner key.1))
    (value : setup.CommitRecoveryValueChoice owner key.1)
    (move : CommitRecoveryMove Player L) (selected : value.val.val = some move) :
    setup.proposalRecoveryComponentTrembledLaw owner key
        omission.val omission.property.1 omission.property.2
        bad.val bad.property.1 bad.property.2
        delivery.val delivery.property.1 delivery.property.2 values
          (setup.proposalRecoveryComponentLabelChoice owner key false value.val) =
      ENNReal.ofReal ((1 - omission.val) * (1 - bad.val)) * values value := by
  classical
  let encode := fun ordinary : setup.CommitRecoveryValueChoice owner key.1 =>
    setup.proposalRecoveryComponentLabelChoice owner key false ordinary.val
  have injective : Function.Injective encode := by
    intro first second same
    have semantic := congrArg (setup.proposalRecoveryComponentSemanticChoice owner key) same
    simp only [encode, setup.proposalRecoveryComponentLabelChoice_semantic] at semantic
    exact Subtype.ext semantic
  let coin := mix delivery.val delivery.property.1 delivery.property.2
    (PMF.pure true) (PMF.pure false)
  have failureZero (omitted : Bool) :
      (coin.map fun requested => setup.proposalRecoveryComponentLabelChoice owner key requested
        (setup.commitRecoveryFailureChoice owner key.1 omitted)) (encode value) = 0 := by
    apply (PMF.apply_eq_zero_iff _ _).mpr
    intro supported
    obtain ⟨requested, _member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    have semantic := congrArg (setup.proposalRecoveryComponentSemanticChoice owner key) equal
    simp only [encode, setup.proposalRecoveryComponentLabelChoice_semantic] at semantic
    have failureSelected : (setup.commitRecoveryFailureChoice owner key.1 omitted).val =
        some move := (congrArg Subtype.val semantic).trans selected
    exact (value.property move selected).2
      (setup.commitRecoveryFailureChoice_spec owner key.1 omitted move failureSelected).1
  have ordinaryLaw :
      ((values.map Subtype.val).bind fun choice =>
        coin.map fun requested =>
          setup.proposalRecoveryComponentLabelChoice owner key requested choice) =
        values.map encode := by
    rw [PMF.bind_map]
    trans values.bind (fun ordinary => PMF.pure (encode ordinary))
    · apply bind_congr_on_support
      intro ordinary _supported
      calc
        _ = coin.map (fun _ => encode ordinary) := by
          apply congrArg (PMF.map · _)
          funext requested
          exact setup.proposalRecoveryComponentLabelChoice_value owner key ordinary requested
        _ = _ := PMF.map_const _ _
    · exact PMF.bind_pure_comp _ _
  have decomposition : setup.proposalRecoveryComponentTrembledLaw owner key
        omission.val omission.property.1 omission.property.2
        bad.val bad.property.1 bad.property.2
        delivery.val delivery.property.1 delivery.property.2 values =
      mix omission.val omission.property.1 omission.property.2
        (coin.map fun requested => setup.proposalRecoveryComponentLabelChoice owner key requested
          (setup.commitRecoveryFailureChoice owner key.1 true))
        (mix bad.val bad.property.1 bad.property.2
          (coin.map fun requested =>
            setup.proposalRecoveryComponentLabelChoice owner key requested
              (setup.commitRecoveryFailureChoice owner key.1 false))
          (values.map encode)) := by
    simp only [proposalRecoveryComponentTrembledLaw, commitRecoveryValueTremble, committing,
      ite_true, mix_bind, PMF.pure_bind]
    rw [ordinaryLaw]
  change setup.proposalRecoveryComponentTrembledLaw owner key
    omission.val omission.property.1 omission.property.2
    bad.val bad.property.1 bad.property.2
    delivery.val delivery.property.1 delivery.property.2 values (encode value) = _
  rw [decomposition, mix_apply, failureZero true, mix_apply, failureZero false,
    pmf_map_apply_of_injective values injective value]
  simp only [mul_zero, zero_add, ENNReal.ofReal_mul
    (sub_nonneg.mpr omission.property.2), mul_assoc]

omit [Fintype Player] in
private theorem component_commit_semantic_fiber
    (owner : Player) (key : setup.ProposalRecoveryComponent owner)
    (choice other : setup.ProposalRecoveryComponentChoice owner key)
    (move : ProposalRecoveryMove Player L) (selected : choice.val = some move)
    (author : Player) (name : VarId) (payload : L.Ty)
    (binding : PublicationResult (L.Val payload))
    (committing : move.semantic.action = .commit author name payload binding)
    (same : setup.proposalRecoveryComponentSemanticChoice owner key other =
      setup.proposalRecoveryComponentSemanticChoice owner key choice) : other = choice := by
  have raw := congrArg Subtype.val same
  change other.val.map (·.semantic) = choice.val.map (·.semantic) at raw
  rw [selected, Option.map_some] at raw
  cases picked : other.val with
  | none => simp only [picked, Option.map_none, reduceCtorEq] at raw
  | some alternate =>
      rw [picked, Option.map_some, Option.some.injEq] at raw
      have valid := other.property.2
      have originalValid := choice.property.2
      rw [picked] at valid
      rw [selected] at originalValid
      have noLabel (candidate : ProposalRecoveryMove Player L) (valid : candidate.Valid)
          (action : candidate.semantic.action = .commit author name payload binding) :
          candidate.proposed = false := by
        cases flag : candidate.proposed with
        | false => rfl
        | true =>
            obtain ⟨revealer, published, impossible⟩ := valid flag
            rw [action] at impossible
            cases impossible
      have equal : alternate = move :=
        congrArg₂ ProposalRecoveryMove.mk raw
          ((noLabel alternate valid ((congrArg (·.action) raw).trans committing)).trans
            (noLabel move originalValid committing).symm)
      apply Subtype.ext
      rw [picked, selected, equal]

omit [Fintype Player] in
/-- A commitment has no additional disclosure-label preimage. Its original
component atom is its exact semantic atom, even for a missing or BAD move. -/
theorem proposalRecoveryComponentTrembledLaw_commit_semantic_atom
    (owner : Player) (key : setup.ProposalRecoveryComponent owner)
    (omission bad delivery : Set.Icc (0 : ℝ) 1)
    (values : PMF (setup.CommitRecoveryValueChoice owner key.1))
    (choice : setup.ProposalRecoveryComponentChoice owner key)
    (move : ProposalRecoveryMove Player L) (selected : choice.val = some move)
    (author : Player) (name : VarId) (payload : L.Ty)
    (binding : PublicationResult (L.Val payload))
    (committing : move.semantic.action = .commit author name payload binding) :
    setup.proposalRecoveryComponentTrembledLaw owner key
        omission.val omission.property.1 omission.property.2
        bad.val bad.property.1 bad.property.2
        delivery.val delivery.property.1 delivery.property.2 values choice =
      setup.commitRecoveryValueTremble owner key.1
        omission.val omission.property.1 omission.property.2
        bad.val bad.property.1 bad.property.2 values
          (setup.proposalRecoveryComponentSemanticChoice owner key choice) := by
  classical
  let law := setup.proposalRecoveryComponentTrembledLaw owner key
    omission.val omission.property.1 omission.property.2
    bad.val bad.property.1 bad.property.2
    delivery.val delivery.property.1 delivery.property.2 values
  have mapped := setup.proposalRecoveryComponentTrembledLaw_semantic owner key
    omission.val omission.property.1 omission.property.2
    bad.val bad.property.1 bad.property.2
    delivery.val delivery.property.1 delivery.property.2 values
  have atom := congrArg
    (fun p => p (setup.proposalRecoveryComponentSemanticChoice owner key choice)) mapped
  have unique : (law.map (setup.proposalRecoveryComponentSemanticChoice owner key))
      (setup.proposalRecoveryComponentSemanticChoice owner key choice) = law choice := by
    rw [PMF.map_apply, tsum_eq_single choice]
    · simp
    · intro other different
      have unequal : setup.proposalRecoveryComponentSemanticChoice owner key choice ≠
          setup.proposalRecoveryComponentSemanticChoice owner key other := by
        intro same
        exact different (component_commit_semantic_fiber setup owner key choice other move
          selected author name payload binding committing same.symm)
      simp only [unequal, ite_false]
  exact unique.symm.trans atom

omit [Fintype Player] in
/-- Missing and accepted BAD are the two distinct actual failed atoms. The
ordinary component contributes zero to both, without a support assumption. -/
theorem commitRecoveryValueTremble_failed_commit_atom
    (owner : Player) (key : setup.ProposalRecoveryComponent owner)
    (committing : key.1.1.1.1.elim false
      (ProtocolView.atCommit owner setup.program) = true)
    (omission bad : Set.Icc (0 : ℝ) 1)
    (values : PMF (setup.CommitRecoveryValueChoice owner key.1))
    (choice : setup.commitRecoveryModel.Choice owner key.1)
    (move : CommitRecoveryMove Player L) (selected : choice.val = some move)
    (failed : move.action.IsFailure) (omitted : Bool) (missing : move.missing = omitted) :
    setup.commitRecoveryValueTremble owner key.1
        omission.val omission.property.1 omission.property.2
        bad.val bad.property.1 bad.property.2 values choice =
      ENNReal.ofReal (if omitted then omission.val else (1 - omission.val) * bad.val) := by
  classical
  have selectedFailure := setup.commitRecoveryFailureChoice_eq_of_failure_move owner key.1
    omitted choice move selected failed (by simpa only [committing, Bool.true_and] using missing)
  have otherFailure (marker : Bool) (different : marker ≠ omitted) :
      setup.commitRecoveryFailureChoice owner key.1 marker ≠ choice := by
    intro same
    have actual := setup.commitRecoveryFailureChoice_spec owner key.1 marker move
      (congrArg Subtype.val same |>.trans selected)
    have flags : omitted = marker := by
      simpa only [committing, Bool.true_and, missing] using actual.2
    exact different flags.symm
  have ordinaryZero : (values.map Subtype.val) choice = 0 := by
    apply (PMF.apply_eq_zero_iff _ _).mpr
    intro supported
    obtain ⟨ordinary, _member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact (ordinary.property move ((congrArg Subtype.val same).trans selected)).2 failed
  cases omitted with
  | true =>
      have different := otherFailure false (by decide)
      simp only [commitRecoveryValueTremble, committing, ite_true, mix_apply,
        PMF.pure_apply, selectedFailure, Ne.symm different, ite_false, ordinaryZero, mul_zero,
        mul_one, add_zero]
  | false =>
      have different := otherFailure true (by decide)
      simp only [commitRecoveryValueTremble, committing, ite_true, mix_apply,
        PMF.pure_apply, selectedFailure, Ne.symm different, ite_false, ordinaryZero, mul_zero,
        mul_one, zero_add, add_zero, Bool.false_eq_true]
      exact (ENNReal.ofReal_mul (sub_nonneg.mpr omission.property.2)).symm

omit [Fintype Player] in
/-- Every failed commitment atom uses its actual omission marker, with no
assumption that the domain component assigns positive mass anywhere. -/
theorem proposalRecoveryComponentTrembledLaw_failed_commit_atom
    (owner : Player) (key : setup.ProposalRecoveryComponent owner)
    (atCommit : key.1.1.1.1.elim false
      (ProtocolView.atCommit owner setup.program) = true)
    (omission bad delivery : Set.Icc (0 : ℝ) 1)
    (values : PMF (setup.CommitRecoveryValueChoice owner key.1))
    (choice : setup.ProposalRecoveryComponentChoice owner key)
    (move : ProposalRecoveryMove Player L) (selected : choice.val = some move)
    (author : Player) (name : VarId) (payload : L.Ty)
    (committing : move.semantic.action = .commit author name payload .failure) :
    setup.proposalRecoveryComponentTrembledLaw owner key
        omission.val omission.property.1 omission.property.2
        bad.val bad.property.1 bad.property.2
        delivery.val delivery.property.1 delivery.property.2 values choice =
      ENNReal.ofReal (if move.semantic.missing then omission.val else
        (1 - omission.val) * bad.val) := by
  rw [setup.proposalRecoveryComponentTrembledLaw_commit_semantic_atom owner key
    omission bad delivery values choice move selected author name payload .failure committing]
  apply setup.commitRecoveryValueTremble_failed_commit_atom owner key atCommit omission bad values
    (setup.proposalRecoveryComponentSemanticChoice owner key choice) move.semantic
    (by change choice.val.map (·.semantic) = _; rw [selected]; rfl)
    (by rw [committing]; rfl) move.semantic.missing rfl

omit [Fintype Player] in
/-- A proper commitment atom is its literal zero-flag atom times the two
flag survival factors. This applies at arbitrary legal normalized keys. -/
theorem proposalRecoveryComponentTrembledLaw_proper_commit_atom
    (owner : Player) (key : setup.ProposalRecoveryComponent owner)
    (atCommit : key.1.1.1.1.elim false
      (ProtocolView.atCommit owner setup.program) = true)
    (omission bad delivery : Set.Icc (0 : ℝ) 1)
    (values : PMF (setup.CommitRecoveryValueChoice owner key.1))
    (choice : setup.ProposalRecoveryComponentChoice owner key)
    (move : ProposalRecoveryMove Player L) (selected : choice.val = some move)
    (author : Player) (name : VarId) (payload : L.Ty) (value : L.Val payload)
    (committing : move.semantic.action = .commit author name payload (.success value))
    (notMissing : move.semantic.missing = false) :
    setup.proposalRecoveryComponentTrembledLaw owner key
        omission.val omission.property.1 omission.property.2
        bad.val bad.property.1 bad.property.2
        delivery.val delivery.property.1 delivery.property.2 values choice =
      ENNReal.ofReal ((1 - omission.val) * (1 - bad.val)) *
        setup.proposalRecoveryComponentTrembledLaw owner key
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values choice := by
  let semantic := setup.proposalRecoveryComponentSemanticChoice owner key choice
  have selectedSemantic : semantic.val = some move.semantic := by
    change choice.val.map (·.semantic) = _
    rw [selected]
    rfl
  let ordinary : setup.CommitRecoveryValueChoice owner key.1 := ⟨semantic, by
    intro candidate picked
    have same : candidate = move.semantic := Option.some.inj (picked.symm.trans selectedSemantic)
    subst candidate
    exact ⟨notMissing, by rw [committing]; intro impossible; cases impossible⟩⟩
  have reconstruction :
      setup.proposalRecoveryComponentLabelChoice owner key false ordinary.val = choice := by
    apply component_commit_semantic_fiber setup owner key choice _ move selected
      author name payload (.success value) committing
    exact setup.proposalRecoveryComponentLabelChoice_semantic owner key false semantic
  have actual := setup.proposalRecoveryComponentTrembledLaw_ordinary_commit_atom owner key
    atCommit omission bad delivery values ordinary move.semantic selectedSemantic
  have zero := setup.proposalRecoveryComponentTrembledLaw_ordinary_commit_atom owner key
    atCommit ⟨0, le_rfl, zero_le_one⟩ ⟨0, le_rfl, zero_le_one⟩
      ⟨0, le_rfl, zero_le_one⟩ values ordinary move.semantic selectedSemantic
  rw [reconstruction] at actual zero
  simp only [sub_zero, mul_one, ENNReal.ofReal_one, one_mul] at zero
  rw [actual, zero]

end Vegas.SourceProgram.Setup
