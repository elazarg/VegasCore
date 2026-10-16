/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Protocol.TracePrefix
import GameTheory.Analysis.Protocol.CounterfactualReach

/-! # Actual continuation atoms and the new own-action suffixes -/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open ExecutionProtocol GameTheory.Math.Probability

/-- The exact product of the recorded atoms of a finite indexed own-action list. -/
theorem ownPlayReachProbability_ofFn
    {Player : Type} {Protocol : GameTheory.Protocol.ExecutionProtocol Player}
    (model : GameTheory.Protocol.InformationModel Protocol)
    (who : Player) (policy : model.BehavioralPolicy who)
    {count : Nat} (records : Fin count → model.InfoState who × Protocol.Action who) :
    model.ownPlayReachProbability policy (List.ofFn records) =
      ∏ index, (((policy (records index).1).map Subtype.val)
        (some (records index).2)).toReal := by
  induction count with
  | zero => simp [InformationModel.ownPlayReachProbability]
  | succ count ih =>
      rw [List.ofFn_succ, InformationModel.ownPlayReachProbability, Fin.prod_univ_succ]
      rw [ih]

variable {Player : Type*} {E : ExecutionProtocol Player}
  (model : InformationModel E)

private theorem inactive_step_atom
    (profile : ∀ who, model.BehavioralPolicy who) (who : Player)
    {state : E.State} (trace : E.Trace state)
    (joint : { action : ∀ player, Option (E.Action player) // E.Legal state action })
    (absent : joint.1 who = none) : model.playerStepProb profile who trace joint = 1 := by
  classical
  have inactive : ¬ E.active state who := by
    have legal := E.legalOption_of_legal joint.2 who
    simpa [absent, LegalOption] using legal
  let : Subsingleton (model.Choice who (model.infoOf who trace)) :=
    ⟨fun first second => by
      apply Subtype.ext
      have firstLegal := (model.menu_adequate who trace first.1).mp first.2
      have secondLegal := (model.menu_adequate who trace second.1).mp second.2
      rw [LegalOption.eq_none_of_inactive first.1 firstLegal inactive,
        LegalOption.eq_none_of_inactive second.1 secondLegal inactive]⟩
  unfold playerStepProb
  rw [eq_pure_of_subsingleton (profile who (model.infoOf who trace))
    (model.choicesOfLegal trace joint who)]
  simp

private theorem new_own_step_atom
    (profile : ∀ who, model.BehavioralPolicy who) (who : Player)
    {state : E.State} (trace : E.Trace state)
    (joint : { action : ∀ player, Option (E.Action player) // E.Legal state action })
    (records : List (model.InfoState who × E.Action who)) :
    model.ownPlayReachProbability (profile who)
        (match joint.1 who with
        | none => records
        | some action => (model.infoOf who trace, action) :: records) =
      model.ownPlayReachProbability (profile who) records *
        model.playerStepProb profile who trace joint := by
  classical
  cases selected : joint.1 who with
  | none => rw [inactive_step_atom model profile who trace joint selected, mul_one]
  | some action =>
      rw [ownPlayReachProbability]
      have value : (model.choicesOfLegal trace joint who).1 = some action := selected
      have atom := pmf_map_apply_of_injective
        (profile who (model.infoOf who trace)) Subtype.val_injective
          (model.choicesOfLegal trace joint who)
      rw [value] at atom
      unfold playerStepProb
      rw [atom]
      exact mul_comm _ _

/-- An actual trace extension determines exactly the new own-action records.
The existing continuation runner's point mass factors into their behavioral
atoms and a single nonnegative transition coefficient common to ALL profiles.
The complete original entry trace and its old own records are retained. -/
theorem exists_continuation_ownPlay_factor [Fintype Player]
    {first second : E.State} (entry : E.Trace first) (final : E.Trace second)
    (isPrefix : TracePrefix entry final) :
    ∃ records : ∀ who, List (model.InfoState who × E.Action who),
      (∀ who, model.ownPlay who final = records who ++ model.ownPlay who entry) ∧
      (∀ who record, record ∈ records who →
        ∃ (before : E.History) (joint : ∀ player, Option (E.Action player))
          (legal : E.Legal before.state joint) (next : E.State)
          (realized : next ∈ (E.step before.state ⟨joint, legal⟩).support),
          TracePrefix entry before.trace ∧
          TracePrefix (before.trace.extend joint legal realized) final ∧
          model.infoOf who before.trace = record.1 ∧ joint who = some record.2) ∧
      ∃ chance : ℝ, 0 ≤ chance ∧
        ∀ profile : ∀ who, model.BehavioralPolicy who,
          ((model.runBehavioralFrom profile (final.length - entry.length)
            ⟨first, entry⟩) ⟨second, final⟩).toReal =
            chance * ∏ who, model.ownPlayReachProbability (profile who) (records who) := by
  classical
  induction isPrefix with
  | refl =>
      refine ⟨fun _ => [], ?_, ?_, 1, zero_le_one, ?_⟩
      · intro who
        exact (List.nil_append _).symm
      · intro who record member
        cases member
      · intro profile
        simp [runBehavioralFrom, ownPlayReachProbability]
  | @extend source target prior earlier joint legal realized ih =>
      obtain ⟨records, recordEq, provenance, chance, nonnegative, factor⟩ := ih
      let newer := fun who => match joint who with
        | none => records who
        | some action => (model.infoOf who prior, action) :: records who
      refine ⟨newer, ?_, ?_, chance * ((E.step source ⟨joint, legal⟩) target).toReal,
        mul_nonneg nonnegative ENNReal.toReal_nonneg, ?_⟩
      · intro who
        rw [InfoSignals.ownPlay_extend, recordEq]
        dsimp only [newer]
        cases joint who <;> rfl
      · intro who record member
        have old (member : record ∈ records who) :
            ∃ (before : E.History) (earlierJoint : ∀ player, Option (E.Action player))
              (earlierLegal : E.Legal before.state earlierJoint) (next : E.State)
              (moved : next ∈ (E.step before.state ⟨earlierJoint, earlierLegal⟩).support),
              TracePrefix entry before.trace ∧
              TracePrefix (before.trace.extend earlierJoint earlierLegal moved)
                (prior.extend joint legal realized) ∧
              model.infoOf who before.trace = record.1 ∧ earlierJoint who = some record.2 := by
          obtain ⟨before, earlierJoint, earlierLegal, next, moved, priorPrefix, afterPrefix,
            observed, selected⟩ := provenance who record member
          exact ⟨before, earlierJoint, earlierLegal, next, moved, priorPrefix,
            .extend afterPrefix joint legal realized, observed, selected⟩
        dsimp only [newer] at member
        cases selected : joint who with
        | none => exact old (by simpa only [selected] using member)
        | some action =>
            rw [selected, List.mem_cons] at member
            rcases member with equal | member
            · subst record
              exact ⟨⟨source, prior⟩, joint, legal, target, realized, earlier, .refl, rfl,
                selected⟩
            · exact old member
      · intro profile
        have lengths : (prior.extend joint legal realized).length - entry.length =
            (prior.length - entry.length) + 1 := by
          have bounded := earlier.length_le
          simp only [Trace.length]
          omega
        have one := model.runBehavioralFrom_one_prob_extend profile ⟨source, prior⟩ legal.1
          ⟨joint, legal⟩ target realized
        change ((model.runBehavioralFrom profile 1 ⟨source, prior⟩)
          ⟨target, prior.extend joint legal realized⟩).toReal =
          model.stepProb profile prior ⟨joint, legal⟩ target at one
        have last := E.runRandomizedFor_apply_of_trace_succ (model.randomizedChooser profile)
          (prior.length - entry.length) ⟨first, entry⟩
            ⟨target, prior.extend joint legal realized⟩ (by
              have bounded := earlier.length_le
              simp only [Trace.length]
              omega)
        change model.runBehavioralFrom profile ((prior.length - entry.length) + 1)
          ⟨first, entry⟩ ⟨target, prior.extend joint legal realized⟩ =
          model.runBehavioralFrom profile (prior.length - entry.length)
            ⟨first, entry⟩ ⟨source, prior⟩ *
          model.runBehavioralFrom profile 1 ⟨source, prior⟩
            ⟨target, prior.extend joint legal realized⟩ at last
        rw [lengths, last, ENNReal.toReal_mul, factor, one]
        rw [stepProb, model.behavioralJoint_prob_eq_prod profile prior legal.1]
        have product :
            (∏ who, model.ownPlayReachProbability (profile who) (newer who)) =
            (∏ who, model.ownPlayReachProbability (profile who) (records who)) *
              ∏ who, model.playerStepProb profile who prior ⟨joint, legal⟩ := by
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun who _ =>
            new_own_step_atom model profile who prior ⟨joint, legal⟩ (records who)
        rw [product]
        simp only [playerStepProb]
        ring

end GameTheory.Protocol.InformationModel
