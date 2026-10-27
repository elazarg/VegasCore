/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.OddsEvensEquilibrium
import GameTheory.Analysis.Protocol.BehavioralBayes

/-! # The uniform-bit profile and its Bayesian assessment in Odds–Evens -/

noncomputable section

namespace Vegas.Examples.OddsEvens

open SourceProgram GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

private theorem bit_mem_intended {Γ : SourceCtx Player simpleExpr}
    (bit : Bool) (who owner : Player) (name : VarId)
    (view : SourceObservation simpleExpr who Γ) :
    bit ∈ intendedValues who (acceptGuard owner name) view := by
  apply Or.inl
  intro same
  cases same
  unfold SourceGuard.predicts
  refine (GuardCode.accepts_success (acceptGuard who name).toGuardCode bit _
    (fun _ _ cell _ => by
    cases cell with
    | here => exact bit
    | there absent => cases absent) ?_ ?_).trans ?_
  · intro _; rfl
  · intro _ _ cell _; cases cell
  · rfl

def intendedBitAction (bit : Bool) (who : Player) (view : setup.ProtocolView who) :
    Option (OwnAction Player simpleExpr) :=
  match view with
  | none => none
  | some (.inl _) => if who = even then some (.commit even 0 .bool (.success bit)) else none
  | some (.inr (.inl _)) => if who = odd then some (.commit odd 1 .bool (.success bit)) else none
  | some (.inr (.inr (.inl _))) => if who = even then some (.reveal even 0 true) else none
  | some (.inr (.inr (.inr (.inl _)))) => if who = odd then some (.reveal odd 1 true) else none
  | some (.inr (.inr (.inr (.inr _)))) => none

theorem intendedBitAction_mem (bit : Bool) (who : Player) (view : setup.ProtocolView who) :
    intendedBitAction bit who view ∈ setup.intendedMenu who view := by
  cases bit <;> cases who <;> rcases view with _ | (view | (view | (view | (view | view))))
  all_goals
    first
    | solve | simp [intendedBitAction, Setup.intendedMenu, setup, program,
        ProtocolView.intendedMenu, ProtocolView.actor, ProtocolView.intendedAvailable,
        even, odd]
    | simpa [intendedBitAction, Setup.intendedMenu, setup, program,
        ProtocolView.intendedMenu, ProtocolView.actor, ProtocolView.intendedAvailable,
        even, odd] using (bit_mem_intended false false false 0 view.1)
    | simpa [intendedBitAction, Setup.intendedMenu, setup, program,
        ProtocolView.intendedMenu, ProtocolView.actor, ProtocolView.intendedAvailable,
        even, odd] using (bit_mem_intended false true true 1 view.1)
    | simpa [intendedBitAction, Setup.intendedMenu, setup, program,
        ProtocolView.intendedMenu, ProtocolView.actor, ProtocolView.intendedAvailable,
        even, odd] using (bit_mem_intended true false false 0 view.1)
    | simpa [intendedBitAction, Setup.intendedMenu, setup, program,
        ProtocolView.intendedMenu, ProtocolView.actor, ProtocolView.intendedAvailable,
        even, odd] using (bit_mem_intended true true true 1 view.1)

def intendedBitChoice (bit : Bool) (who : Player) (view : setup.ProtocolView who) :
    setup.intendedModel.Choice who view :=
  ⟨intendedBitAction bit who view, intendedBitAction_mem bit who view⟩

theorem intendedBitChoice_surjective (who : Player) (view : setup.ProtocolView who) :
    Function.Surjective (fun bit => intendedBitChoice bit who view) := by
  rintro ⟨selected, legal⟩
  change selected ∈ setup.intendedMenu who view at legal
  cases who <;> rcases view with _ | (view | (view | (view | (view | view)))) <;>
    rcases selected with _ | action
  all_goals
    first
    | exact ⟨false, rfl⟩
    | solve | cases legal
    | exact (legal rfl).elim
    | solve | cases legal.1
    | obtain ⟨bit, _, same⟩ := legal.2
      exact ⟨bit, Subtype.ext (congrArg some same.symm)⟩
    | have same : action = .reveal even 0 true := legal.2
      subst action
      exact ⟨false, rfl⟩
    | have same : action = .reveal odd 1 true := legal.2
      subst action
      exact ⟨false, rfl⟩

def uniformProfile : ∀ who, setup.intendedModel.BehavioralPolicy who :=
  fun who view => (PMF.uniformOfFintype Bool).map (fun bit => intendedBitChoice bit who view)

theorem uniformProfile_map_val (who : Player) (view : setup.ProtocolView who) :
    (uniformProfile who view).map Subtype.val =
      (PMF.uniformOfFintype Bool).map (fun bit => intendedBitAction bit who view) := by
  rw [uniformProfile, PMF.map_comp]
  rfl

theorem uniformProfile_fullSupport (who : Player) (view : setup.ProtocolView who)
    (choice : setup.intendedModel.Choice who view) :
    choice ∈ (uniformProfile who view).support := by
  obtain ⟨bit, rfl⟩ := intendedBitChoice_surjective who view choice
  rw [uniformProfile, PMF.support_map]
  exact ⟨bit, PMF.mem_support_uniformOfFintype bit, rfl⟩

def uniformAssessment : setup.intendedModel.BehavioralAssessment :=
  setup.intendedModel.bayesAssessment uniformProfile
    (fun who site => uniformProfile_fullSupport who site.1) setup.intended_decision_antichain

theorem uniformAssessment_consistent :
    uniformAssessment.IsSequentiallyConsistent setup.intended_decision_antichain := by
  apply BehavioralAssessment.IsSequentiallyConsistent.of_fullyMixed_bayes
  · exact fun who site => uniformProfile_fullSupport who site.1
  · exact setup.intendedModel.bayesAssessment_isBayesConsistent uniformProfile
      (fun who site => uniformProfile_fullSupport who site.1) setup.intended_decision_antichain

end Vegas.Examples.OddsEvens
